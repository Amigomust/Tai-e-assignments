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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    private Set<Stmt> getReachableNodeFromIf(If node, DataflowResult<Stmt, CPFact> constants, Set<Edge<Stmt>> nextEdges) {
        Set<Stmt> reachable = new HashSet<>();
        CPFact inFact = constants.getInFact(node);
        ConditionExp condExp = node.getCondition();
        Value value = ConstantPropagation.evaluate(condExp, constants.getInFact(node));

        if (value.isConstant()) {
            boolean conditionHolds = value.getConstant() != 0;
            for (Edge<Stmt> edge: nextEdges) {
                if (edge.getKind() == Edge.Kind.IF_TRUE && conditionHolds) {
                    reachable.add(edge.getTarget());
                } else if (edge.getKind() == Edge.Kind.IF_FALSE && !conditionHolds) {
                    reachable.add(edge.getTarget());
                }
            }
        } else {
            for (Edge<Stmt> edge: nextEdges) {
                reachable.add(edge.getTarget());
            }
        }
        return reachable;
    }

    private Set<Stmt> getReachableNodeFromSwitch(SwitchStmt node, DataflowResult<Stmt, CPFact> constants, Set<Edge<Stmt>> nextEdges) {
        Set<Stmt> reachable = new HashSet<>();
        CPFact inFact = constants.getInFact(node);
        Var switchVar = node.getVar();
        Value switchConst = inFact.get(switchVar);

        if (switchConst.isConstant()) {
            int switchInt = switchConst.getConstant();
            boolean caseMatched = false;
            for (Edge<Stmt> cfgEdge: nextEdges) {
                if (cfgEdge.isSwitchCase()) {
                    Stmt target = cfgEdge.getTarget();
                    int caseValue = cfgEdge.getCaseValue();
                    if (caseValue == switchInt) {
                        reachable.add(target);
                        caseMatched = true;
                    }
                }
            }
            if (!caseMatched) {
                for (Edge<Stmt> cfgEdge: nextEdges) {
                    if (cfgEdge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                        reachable.add(cfgEdge.getTarget());
                    }
                }
            }
        } else {
            for (Edge<Stmt> cfgEdge: nextEdges) {
                reachable.add(cfgEdge.getTarget());
            }
        }
        return reachable;
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Unreachable code detection
        Set<Stmt> visited = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        visited.add(cfg.getEntry());
        visited.add(cfg.getExit());
        List<Stmt> queue = new LinkedList<>();

        // bfs traversal
        queue.add(cfg.getEntry());
        while (!queue.isEmpty()) {
            Stmt stmt = queue.remove(0);
            Set<Stmt> nextStmts = cfg.getSuccsOf(stmt);
            if (stmt instanceof SwitchStmt) {
                nextStmts = getReachableNodeFromSwitch((SwitchStmt) stmt, constants, cfg.getOutEdgesOf(stmt));
            } else if (stmt instanceof If) {
                nextStmts = getReachableNodeFromIf((If) stmt, constants, cfg.getOutEdgesOf(stmt));
            }
            for (Stmt nextStmt : nextStmts) {
                if (!visited.contains(nextStmt)) {
                    visited.add(nextStmt);
                    queue.add(nextStmt);
                }
            }
        }

        for (Stmt stmt : cfg.getNodes()) {
            if (!visited.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

        // Dead assignment detection
        for (Stmt stmt : cfg.getNodes()) {
            if (stmt instanceof AssignStmt<?,?> assignStmt) {
                LValue defOpt = assignStmt.getLValue();
                RValue useExp = assignStmt.getRValue();
                SetFact<Var> outFact = liveVars.getOutFact(stmt);
                if (defOpt instanceof Var && !outFact.contains((Var) defOpt) && hasNoSideEffect(useExp)) {
                    deadCode.add(stmt);
                }
            }
        }

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
