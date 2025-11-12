/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        initializeForward(cfg, result);
        Queue<Node> workList = new LinkedList<>();
        for (Node node : cfg.getNodes()) {
            if (node == cfg.getEntry()) continue;
            workList.add(node);
        }
        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact inFact = result.getInFact(node);
            for (Node pred : cfg.getPredsOf(node)) {
                Fact predOutFact = result.getOutFact(pred);
                analysis.meetInto(predOutFact, inFact);
            }
            Fact outFact = result.getOutFact(node);
            if (analysis.transferNode(node, inFact, outFact)) {
                workList.addAll(cfg.getSuccsOf(node));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        initializeBackward(cfg, result);
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Node node: cfg) {
                if (node == cfg.getExit()) continue;
                Fact outFact = analysis.newInitialFact();
                Fact inFact = result.getInFact(node);
                for (Node succ: cfg.getSuccsOf(node)) {
                    Fact inFactSucc = result.getInFact(succ);
                    analysis.meetInto(inFactSucc, outFact);
                }
                result.setOutFact(node, outFact);
                changed |= analysis.transferNode(node, inFact, outFact);
            }
        }
    }
}
