// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

package org.apache.doris.nereids.rules.rewrite;

import org.apache.doris.analysis.ColumnAccessPath;
import org.apache.doris.analysis.ColumnAccessPathType;
import org.apache.doris.common.Pair;
import org.apache.doris.nereids.StatementContext;
import org.apache.doris.nereids.properties.OrderKey;
import org.apache.doris.nereids.rules.Rule;
import org.apache.doris.nereids.rules.RuleType;
import org.apache.doris.nereids.trees.expressions.Alias;
import org.apache.doris.nereids.trees.expressions.Expression;
import org.apache.doris.nereids.trees.expressions.NamedExpression;
import org.apache.doris.nereids.trees.expressions.Slot;
import org.apache.doris.nereids.trees.expressions.SlotReference;
import org.apache.doris.nereids.trees.expressions.functions.scalar.StructElement;
import org.apache.doris.nereids.trees.expressions.literal.IntegerLiteral;
import org.apache.doris.nereids.trees.expressions.literal.Literal;
import org.apache.doris.nereids.trees.plans.Plan;
import org.apache.doris.nereids.trees.plans.logical.LogicalAggregate;
import org.apache.doris.nereids.trees.plans.logical.LogicalJoin;
import org.apache.doris.nereids.trees.plans.logical.LogicalProject;
import org.apache.doris.nereids.trees.plans.logical.LogicalTopN;
import org.apache.doris.nereids.types.StructField;
import org.apache.doris.nereids.types.StructType;
import org.apache.doris.nereids.util.ExpressionUtils;
import org.apache.doris.nereids.util.PlanUtils;

import com.google.common.collect.ImmutableList;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Pull up Project under TopN.
 */
public class PullUpProjectUnderTopN extends OneRewriteRuleFactory {
    @Override
    public Rule build() {
        return logicalTopN(logicalProject()
                .whenNot(p -> p.isAllSlots())
                .whenNot(LogicalProject::containsNoneMovableFunction)
                .whenNot(PullUpProjectUnderTopN::hasRootNestedLazySlotAlias)
                .when(p -> canPullUpProject(p.child())))
                .thenApply(ctx -> pullUpProject(ctx.root, ctx.statementContext))
                .toRule(RuleType.PULL_UP_PROJECT_UNDER_TOPN);
    }

    private static boolean canPullUpProject(Plan child) {
        if (child instanceof LogicalAggregate) {
            return false;
        }
        if (child instanceof LogicalJoin) {
            LogicalJoin<?, ?> join = (LogicalJoin<?, ?>) child;
            return join.getJoinType().isLeftRightOuterOrCrossJoin()
                    || join.getJoinType().isAsofOuterJoin();
        }
        return true;
    }

    private static boolean hasRootNestedLazySlotAlias(LogicalProject<? extends Plan> project) {
        for (NamedExpression projectExpr : project.getProjects()) {
            if (projectExpr instanceof Alias && projectExpr.child(0) instanceof SlotReference
                    && ((SlotReference) projectExpr.child(0)).getAllAccessPaths().isPresent()) {
                return true;
            }
        }
        return false;
    }

    private static Plan pullUpProject(LogicalTopN<LogicalProject<Plan>> topN, StatementContext context) {
        LogicalProject<Plan> project = topN.child();
        Map<Slot, Expression> slotMap = ExpressionUtils.generateReplaceMap(project.getProjects());
        Set<Slot> childOutputs = project.child().getOutputSet();
        Set<Slot> topNRequiredSlots = new LinkedHashSet<>();
        List<OrderKey> newOrderKeys = new ArrayList<>();

        for (OrderKey orderKey : topN.getOrderKeys()) {
            if (!(orderKey.getExpr() instanceof Slot)) {
                return null;
            }
            Slot orderSlot = (Slot) orderKey.getExpr();
            if (childOutputs.contains(orderSlot)) {
                newOrderKeys.add(orderKey);
                topNRequiredSlots.add(orderSlot);
                continue;
            }

            Expression expression = slotMap.get(orderSlot);
            if (expression instanceof Slot) {
                Slot childOrderSlot = (Slot) expression;
                newOrderKeys.add(orderKey.withExpression(childOrderSlot));
                topNRequiredSlots.add(childOrderSlot);
            } else {
                return null;
            }
        }

        Map<Expression, Alias> nestedLazyAliases = new LinkedHashMap<>();
        List<NamedExpression> newProjects = new ArrayList<>();
        for (NamedExpression projectExpr : project.getProjects()) {
            if (projectExpr instanceof Alias) {
                Expression newChild = replaceStructElementByNestedLazySlot(projectExpr.child(0),
                        nestedLazyAliases, context);
                newProjects.add((NamedExpression) projectExpr.withChildren(ImmutableList.of(newChild)));
            } else {
                newProjects.add(projectExpr);
            }
        }

        Set<Slot> nestedLazyAliasSlots = new LinkedHashSet<>();
        for (Alias alias : nestedLazyAliases.values()) {
            nestedLazyAliasSlots.add(alias.toSlot());
        }

        Set<Slot> allUsedSlots = new LinkedHashSet<>();
        for (NamedExpression projectExpr : newProjects) {
            for (Slot slot : projectExpr.getInputSlots()) {
                if (!nestedLazyAliasSlots.contains(slot)) {
                    allUsedSlots.add(slot);
                }
            }
        }
        allUsedSlots.addAll(topNRequiredSlots);

        Set<NamedExpression> childProjects = new LinkedHashSet<>(allUsedSlots);
        childProjects.addAll(nestedLazyAliases.values());

        LogicalTopN<Plan> newTopN = topN.withOrderKeys(newOrderKeys);
        if (nestedLazyAliases.isEmpty() && childOutputs.equals(allUsedSlots)) {
            return project.withChildren(newTopN.withChildren(project.child()));
        }

        Plan columnProject = PlanUtils.projectOrSelf(ImmutableList.copyOf(childProjects), project.child());
        return project.withProjectsAndChild(newProjects, newTopN.withChildren(columnProject));
    }

    private static Expression replaceStructElementByNestedLazySlot(
            Expression expression, Map<Expression, Alias> aliases, StatementContext context) {
        return expression.rewriteDownShortCircuit(expr -> {
            if (expr instanceof StructElement) {
                Optional<Pair<SlotReference, Expression>> lazySlot = toNestedLazySlot((StructElement) expr);
                if (lazySlot.isPresent()) {
                    Alias alias = aliases.computeIfAbsent(expr,
                            key -> new Alias(context.getNextExprId(), lazySlot.get().first));
                    return expr.withChildren(ImmutableList.of(alias.toSlot(), lazySlot.get().second));
                }
            }
            return expr;
        });
    }

    private static Optional<Pair<SlotReference, Expression>> toNestedLazySlot(StructElement structElement) {
        List<Expression> arguments = structElement.getArguments();
        Expression struct = arguments.get(0);
        Expression fieldName = arguments.get(1);
        if (!(struct instanceof SlotReference) || !(fieldName instanceof Literal)
                || !(struct.getDataType() instanceof StructType)) {
            return Optional.empty();
        }

        Literal fieldLiteral = (Literal) fieldName;
        StructType structType = (StructType) struct.getDataType();
        Optional<StructField> field = Optional.empty();
        Expression rewrittenFieldName = fieldName;
        if (fieldName.getDataType().isIntegerLikeType()) {
            int fieldIndex = ((Number) fieldLiteral.getValue()).intValue();
            if (fieldIndex >= 1 && fieldIndex <= structType.getFields().size()) {
                field = Optional.of(structType.getFields().get(fieldIndex - 1));
                rewrittenFieldName = new IntegerLiteral(1);
            }
        } else if (fieldName.getDataType().isStringLikeType()) {
            String name = fieldLiteral.getStringValue();
            field = structType.getFields().stream()
                    .filter(structField -> structField.getName().equalsIgnoreCase(name))
                    .findFirst();
        }
        if (!field.isPresent()) {
            return Optional.empty();
        }

        SlotReference structSlot = (SlotReference) struct;
        String rootName = structSlot.getOriginalColumn()
                .map(column -> column.getName())
                .orElse(structSlot.getName());
        String fieldNameLowerCase = field.get().getName().toLowerCase();
        StructType prunedType = new StructType(ImmutableList.of(field.get()));
        List<ColumnAccessPath> allAccessPaths = ImmutableList.of(
                new ColumnAccessPath(ColumnAccessPathType.DATA, ImmutableList.of(rootName, fieldNameLowerCase)));
        SlotReference lazySlot = (SlotReference) structSlot.withNullableAndDataType(
                structSlot.nullable(), prunedType);
        lazySlot = lazySlot.withAccessPaths(allAccessPaths, ImmutableList.of());
        return Optional.of(Pair.of(lazySlot, rewrittenFieldName));
    }
}
