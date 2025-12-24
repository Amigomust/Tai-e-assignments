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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.plugin.taint.TaintFlow;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    public void addToWorkList(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            StmtProcessor processor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().forEach(stmt -> stmt.accept(processor));
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            Var lvalue = stmt.getLValue();
            CSVar csVar = csManager.getCSVar(context, lvalue);
            Obj obj = heapModel.getObj(stmt);
            Context newContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(newContext, obj);
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lValue = stmt.getLValue();
            Var rValue = stmt.getRValue();
            CSVar csLVar = csManager.getCSVar(context, lValue);
            CSVar csRVar = csManager.getCSVar(context, rValue);
            addPFGEdge(csRVar, csLVar);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {

            // Static invoke may be a source.
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);
                if (method == null) return null;
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context newContext = contextSelector.selectContext(csCallSite, method);
                CSMethod csMethod = csManager.getCSMethod(newContext, method);
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i ++) {
                    Var argVar = stmt.getInvokeExp().getArg(i);
                    Var param = method.getIR().getParam(i);
                    CSVar csVar = csManager.getCSVar(context, argVar);
                    CSVar csRVar = csManager.getCSVar(csMethod.getContext(), param);
                    addPFGEdge(csVar, csRVar);
                }

                if (stmt.getLValue() != null) {
                    CSVar lValue = csManager.getCSVar(context, stmt.getLValue());
                    for (Var var : method.getIR().getReturnVars()) {
                        CSVar retVar = csManager.getCSVar(csMethod.getContext(), var);
                        addPFGEdge(retVar, lValue);
                    }
                }
                taintAnalysis.handleCall(null, null, csCallSite, method);

                Edge<CSCallSite, CSMethod> edge =
                        new Edge<>(CallKind.STATIC, csCallSite, csMethod);
                if (csCallSite.addEdge(edge)) {
                    addReachable(csMethod);
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            FieldRef lValue = stmt.getLValue().getFieldRef();
            Var rValue = stmt.getRValue();
            if (lValue.isStatic()) {
                StaticField staticField = csManager.getStaticField(lValue.resolve());
                CSVar csVar = csManager.getCSVar(context, rValue);
                addPFGEdge(csVar, staticField);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            Var lValue = stmt.getLValue();
            FieldRef rValue = stmt.getRValue().getFieldRef();
            if (rValue.isStatic()) {
                StaticField staticField = csManager.getStaticField(rValue.resolve());
                CSVar csVar = csManager.getCSVar(context, lValue);
                addPFGEdge(staticField, csVar);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet diffSet = propagate(pointer, pointsToSet);
            if (diffSet.isEmpty()) {
                continue;
            }
            // process the propagation effects
            if (pointer instanceof CSVar csVar) {
                Context context = csVar.getContext();
                for (CSObj obj : diffSet) {
                    csVar.getVar().getStoreArrays().forEach(store -> {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        CSVar valueVar = csManager.getCSVar(context, store.getRValue());
                        addPFGEdge(valueVar, arrayIndex);
                    });
                    csVar.getVar().getLoadArrays().forEach(store -> {
                        CSVar lValue = csManager.getCSVar(context, store.getLValue());
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, lValue);
                    });
                    csVar.getVar().getLoadFields().forEach(load -> {
                        CSVar lValue = csManager.getCSVar(context, load.getLValue());
                        JField field = load.getRValue().getFieldRef().resolve();
                        InstanceField instanceField = csManager.getInstanceField(obj, field);
                        addPFGEdge(instanceField, lValue);
                    });
                    csVar.getVar().getStoreFields().forEach(store -> {
                        CSVar rValue = csManager.getCSVar(context, store.getRValue());
                        JField field = store.getLValue().getFieldRef().resolve();
                        InstanceField instanceField = csManager.getInstanceField(obj, field);
                        addPFGEdge(rValue, instanceField);
                    });
                    if (!taintAnalysis.isTaint(obj)) processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet result = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj)) {
                result.addObject(obj);
            }
        }
        if (!result.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, result);
            }
            taintAnalysis.propagate(pointer, result);
        }
        return result;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        recv.getVar().getInvokes().forEach(invoke -> {
            JMethod method = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context newContext = contextSelector.selectContext(csCallSite, recvObj, method);
            CSMethod csMethod = csManager.getCSMethod(newContext, method);
            Edge<CSCallSite, CSMethod> edge = null;
            if (invoke.isDynamic()) {
                edge = new Edge<>(CallKind.DYNAMIC, csCallSite, csMethod);
            } else if (invoke.isInterface()) {
                edge = new Edge<>(CallKind.INTERFACE, csCallSite, csMethod);
            } else if (invoke.isSpecial()) {
                edge = new Edge<>(CallKind.SPECIAL, csCallSite, csMethod);
            } else if (invoke.isVirtual()) {
                edge = new Edge<>(CallKind.VIRTUAL, csCallSite, csMethod);
            }
            CSVar csThis = csManager.getCSVar(newContext, method.getIR().getThis());
            workList.addEntry(csThis, PointsToSetFactory.make(recvObj));

            assert edge != null;
            if (callGraph.addEdge(edge)) {
                for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                    Var argVar = invoke.getInvokeExp().getArg(i);
                    Var param = method.getIR().getParam(i);
                    CSVar csVar = csManager.getCSVar(recv.getContext(), argVar);
                    CSVar csRVar = csManager.getCSVar(newContext, param);
                    addPFGEdge(csVar, csRVar);
                }
                Var lValue = invoke.getLValue();
                if (lValue != null) {
                    CSVar retVar = csManager.getCSVar(recv.getContext(), invoke.getLValue());
                    for (Var var : method.getIR().getReturnVars()) {
                        CSVar csRetVar = csManager.getCSVar(newContext, var);
                        addPFGEdge(csRetVar, retVar);
                    }
                }
                taintAnalysis.handleCall(recv.getVar(), recvObj.getObject(), csCallSite, method);

                addReachable(csMethod);
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
