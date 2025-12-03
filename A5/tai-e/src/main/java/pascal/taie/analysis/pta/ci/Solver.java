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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.awt.*;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            method.getIR().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            Var lvalue = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            PointsToSet pts = new PointsToSet(obj);
            Pointer ptr = pointerFlowGraph.getVarPtr(lvalue);
            workList.addEntry(ptr, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lvalue = stmt.getLValue();
            Var rvalue = stmt.getRValue();
            Pointer dstPtr = pointerFlowGraph.getVarPtr(lvalue);
            Pointer srcPtr = pointerFlowGraph.getVarPtr(rvalue);
            addPFGEdge(srcPtr, dstPtr);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                if (method == null) return null;
                Edge<Invoke, JMethod> edge = new Edge<>(CallKind.STATIC, stmt, method);
                if (callGraph.addEdge(edge)) {
                    for (int i = 0; i < method.getParamCount(); i ++) {
                        Var arg = stmt.getInvokeExp().getArg(i);
                        Var param = method.getIR().getParam(i);
                        Pointer argPtr = pointerFlowGraph.getVarPtr(arg);
                        Pointer paramPtr = pointerFlowGraph.getVarPtr(param);
                        addPFGEdge(argPtr, paramPtr);
                    }

                    Var lv = stmt.getLValue();
                    if (lv != null) {
                        for (Var returnVar : method.getIR().getReturnVars()) {
                            Pointer retPtr = pointerFlowGraph.getVarPtr(returnVar);
                            Pointer lvPtr = pointerFlowGraph.getVarPtr(lv);
                            addPFGEdge(retPtr, lvPtr);
                        }
                    }

                    addReachable(method);
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            Var lvalue = stmt.getLValue();
            FieldAccess rvalue = stmt.getRValue();
            JField rField = rvalue.getFieldRef().resolve();
            if (rField.isStatic()) {
                Pointer srcPtr = pointerFlowGraph.getStaticField(rField);
                Pointer dstPtr = pointerFlowGraph.getVarPtr(lvalue);
                addPFGEdge(srcPtr, dstPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            Var rValue = stmt.getRValue();
            FieldAccess lValue = stmt.getLValue();
            JField rField = lValue.getFieldRef().resolve();
            if (rField.isStatic()) {
                Pointer srcPtr = pointerFlowGraph.getVarPtr(rValue);
                Pointer dstPtr = pointerFlowGraph.getStaticField(rField);
                addPFGEdge(srcPtr, dstPtr);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        pointerFlowGraph.addEdge(source, target);
        PointsToSet pts = new PointsToSet();
        for (Obj obj : source.getPointsToSet()) {
            pts.addObject(obj);
        }
        if (!pts.isEmpty())
            workList.addEntry(target, pts);
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        initialize();
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet diff = propagate(pointer, pointsToSet);
            if (diff.isEmpty()) continue;
            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();

                // process instance field loads
                var.getLoadFields().forEach(load -> {
                    FieldAccess fieldAccess = load.getFieldAccess();
                    Var lValue = load.getLValue();
                    Pointer lValuePtr = pointerFlowGraph.getVarPtr(lValue);
                    for (Obj baseObj : diff) {
                        JField field = fieldAccess.getFieldRef().resolve();
                        Pointer fieldPtr = pointerFlowGraph.getInstanceField(baseObj, field);
                        addPFGEdge(fieldPtr, lValuePtr);
                    }
                });

                // process instance field stores
                var.getStoreFields().forEach(store -> {
                    FieldAccess fieldAccess = store.getFieldAccess();
                    Var rValue = store.getRValue();
                    Pointer rValuePtr = pointerFlowGraph.getVarPtr(rValue);
                    for (Obj baseObj : diff) {
                        JField field = fieldAccess.getFieldRef().resolve();
                        Pointer fieldPtr = pointerFlowGraph.getInstanceField(baseObj, field);
                        addPFGEdge(rValuePtr, fieldPtr);
                    }
                });

                // process array loads
                var.getLoadArrays().forEach(loadArray -> {
                    Var lValue = loadArray.getLValue();
                    Pointer lValuePtr = pointerFlowGraph.getVarPtr(lValue);
                    for (Obj arrayObj : diff) {
                        Pointer arrayIndexPtr = pointerFlowGraph.getArrayIndex(arrayObj);
                        addPFGEdge(arrayIndexPtr, lValuePtr);
                    }
                });

                // process array stores
                var.getStoreArrays().forEach(storeArray -> {
                    Var rValue = storeArray.getRValue();
                    Pointer rValuePtr = pointerFlowGraph.getVarPtr(rValue);
                    for (Obj arrayObj : diff) {
                        Pointer arrayIndexPtr = pointerFlowGraph.getArrayIndex(arrayObj);
                        addPFGEdge(rValuePtr, arrayIndexPtr);
                    }
                });

                // process instance calls
                for (Obj recv : diff) {
                    processCall(var, recv);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet ptaSet = pointer.getPointsToSet();
        PointsToSet diffSet = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (!ptaSet.contains(obj)) {
                ptaSet.addObject(obj);
                diffSet.addObject(obj);
            }
        }
        if (diffSet.isEmpty()) {
            return diffSet;
        }
        for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(succ, diffSet);
        }
        return diffSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(invoke -> {
            JMethod callee = resolveCallee(recv, invoke);
            if (callee != null) {
                Edge<Invoke, JMethod> edge = null;
                if (invoke.isInterface()) {
                    edge = new Edge<>(CallKind.INTERFACE, invoke, callee);
                } else if (invoke.isVirtual()) {
                    edge = new Edge<>(CallKind.VIRTUAL, invoke, callee);
                } else if (invoke.isSpecial()) {
                    edge = new Edge<>(CallKind.SPECIAL, invoke, callee);
                } else if (invoke.isDynamic()) {
                    edge = new Edge<>(CallKind.DYNAMIC, invoke, callee);
                }
                Pointer thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
                workList.addEntry(thisPtr, new PointsToSet(recv));

                if (callGraph.addEdge(edge)) {
                    for (int i = 0; i < callee.getParamCount(); i ++) {
                        Var arg = invoke.getInvokeExp().getArg(i);
                        Var param = callee.getIR().getParam(i);
                        Pointer argPtr = pointerFlowGraph.getVarPtr(arg);
                        Pointer paramPtr = pointerFlowGraph.getVarPtr(param);
                        addPFGEdge(argPtr, paramPtr);
                    }
                    Var lValue = invoke.getLValue();
                    if (lValue != null) {
                        Pointer lPtr = pointerFlowGraph.getVarPtr(lValue);
                        for (Var returnVar : callee.getIR().getReturnVars()) {
                            Pointer retPtr = pointerFlowGraph.getVarPtr(returnVar);
                            addPFGEdge(retPtr, lPtr);
                        }
                    }

                    addReachable(callee);
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
