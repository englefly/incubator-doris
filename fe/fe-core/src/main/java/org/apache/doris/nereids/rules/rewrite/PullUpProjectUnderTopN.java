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

import org.apache.doris.nereids.properties.OrderKey;
import org.apache.doris.nereids.rules.Rule;
import org.apache.doris.nereids.rules.RuleType;
import org.apache.doris.nereids.trees.expressions.Expression;
import org.apache.doris.nereids.trees.expressions.NamedExpression;
import org.apache.doris.nereids.trees.expressions.Slot;
import org.apache.doris.nereids.trees.plans.Plan;
import org.apache.doris.nereids.trees.plans.logical.LogicalAggregate;
import org.apache.doris.nereids.trees.plans.logical.LogicalJoin;
import org.apache.doris.nereids.trees.plans.logical.LogicalProject;
import org.apache.doris.nereids.trees.plans.logical.LogicalTopN;
import org.apache.doris.nereids.util.ExpressionUtils;
import org.apache.doris.nereids.util.PlanUtils;

import com.google.common.collect.ImmutableList;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
                .when(p -> canPullUpProject(p.child())))
                .then(PullUpProjectUnderTopN::pullUpProject)
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

    private static Plan pullUpProject(LogicalTopN<LogicalProject<Plan>> topN) {
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

        Set<Slot> allUsedSlots = new LinkedHashSet<>();
        for (NamedExpression projectExpr : project.getProjects()) {
            allUsedSlots.addAll(projectExpr.getInputSlots());
        }
        allUsedSlots.addAll(topNRequiredSlots);

        LogicalTopN<Plan> newTopN = topN.withOrderKeys(newOrderKeys);
        if (childOutputs.equals(allUsedSlots)) {
            return project.withChildren(newTopN.withChildren(project.child()));
        }

        Plan columnProject = PlanUtils.projectOrSelf(ImmutableList.copyOf(allUsedSlots), project.child());
        return project.withChildren(newTopN.withChildren(columnProject));
    }
}
