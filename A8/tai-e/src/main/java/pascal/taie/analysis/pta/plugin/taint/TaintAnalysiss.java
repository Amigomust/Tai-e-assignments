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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.*;
import java.util.List;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final InfoFlowGraph infoFlowGraph;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        infoFlowGraph = new InfoFlowGraph();
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public void addIFGEdge(Pointer src, Pointer target) {
        if (infoFlowGraph.addEdge(src, target)) {
            PointsToSet newSet = PointsToSetFactory.make();
            for (CSObj obj : src.getPointsToSet()) {
                if (manager.isTaint(obj.getObject())) {
                    newSet.addObject(obj);
                }
            }
            if (!newSet.isEmpty()) {
                solver.addToWorkList(target, newSet);
            }
        }
    }

    public void propagate(Pointer pointer, PointsToSet incrementalSet) {
        PointsToSet result = PointsToSetFactory.make();
        for (CSObj obj : incrementalSet) {
            if (manager.isTaint(obj.getObject())) {
                result.addObject(obj);
            }
        }
        if (!result.isEmpty()) {
            for (Pointer succ: infoFlowGraph.getSuccsOf(pointer)) {
                solver.addToWorkList(succ, result);
            }
        }
    }

    public void handleCall(Var base, Obj recvObj, CSCallSite csCallSite, JMethod method) {
        Invoke invoke = csCallSite.getCallSite();
        Set<TaintTransfer> transfers = resolveTransferEdges(method);
        for (TaintTransfer t : transfers) {
            int from = t.from();
            int to = t.to();
            Pointer fromVar = null;
            Pointer toVar = null;
            if (from == TaintTransfer.BASE) {
                if (base != null) {
                    fromVar = csManager.getCSVar(csCallSite.getContext(), base);
                }
            } else {
                Var var = invoke.getInvokeExp().getArg(from);
                fromVar = csManager.getCSVar(csCallSite.getContext(), var);
            }

            if (to == TaintTransfer.BASE && base != null) {
                toVar = csManager.getCSVar(csCallSite.getContext(), base);
            } else if (to == TaintTransfer.RESULT && invoke.getLValue() != null){
                toVar = csManager.getCSVar(csCallSite.getContext(), invoke.getLValue());
            }
            if (fromVar != null && toVar != null) addIFGEdge(fromVar, toVar);
        }

        Set<Source> sources = resolveSources(method);
        if (invoke.getLValue() != null && !sources.isEmpty()) {
            PointsToSet pointsToSet = PointsToSetFactory.make();
            for (Source source : sources) {
                pointsToSet.addObject(csManager.getCSObj(emptyContext, manager.makeTaint(invoke, source.type())));
            }
            CSVar csVar = csManager.getCSVar(csCallSite.getContext(), invoke.getLValue());
            solver.addToWorkList(csVar, pointsToSet);
        }
    }

    public boolean isTaint(CSObj obj)  {
        return manager.isTaint(obj.getObject());
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintTransfer> resolveTransferEdges(JMethod method) {
        Set<TaintTransfer> transfers = config.getTransfers();
        Set<TaintTransfer> result = new HashSet<>();
        transfers.stream().filter(t -> t.method() == method).forEach(result::add);
        return result;
    }

    private Set<Source> resolveSources(JMethod method) {
        Set<Source> sources = config.getSources();
        Set<Source> result = new HashSet<>();
        sources.stream().filter(s -> s.method() == method).forEach(result::add);
        return result;
    }

    private Set<Sink> resolveSinks(JMethod method) {
        Set<Sink> sinks = config.getSinks();
        Set<Sink> result = new HashSet<>();
        sinks.stream().filter(s -> s.method() == method).forEach(result::add);
        return result;
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();

        Map<JMethod, Set<Sink>> sinksMap = new HashMap<>();
        PointerAnalysisResult result = solver.getResult();
        result.getCSCallGraph().edges().forEach(edge -> {
            CSCallSite invoke = edge.getCallSite();
            CSMethod csMethod = edge.getCallee();
            JMethod jMethod = csMethod.getMethod();
            if (!sinksMap.containsKey(jMethod)) {
                sinksMap.put(jMethod, resolveSinks(jMethod));
            }
            Set<Sink> sinks = sinksMap.get(jMethod);
            for (Sink sink : sinks) {
                Var argVar = invoke.getCallSite().getInvokeExp().getArg(sink.index());
                CSVar csVar = csManager.getCSVar(invoke.getContext(), argVar);
                csVar.getPointsToSet().forEach(csObj -> {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        taintFlows.add(new TaintFlow(manager.getSourceCall(obj), invoke.getCallSite(), sink.index()));
                    }
                });
            }
        });
        // You could query pointer analysis results you need via variable result.
        return taintFlows;
    }

    class InfoFlowGraph {

        /**
         * Map from a pointer (node) to its successors in PFG.
         */
        private final MultiMap<Pointer, Pointer> successors = Maps.newMultiMap();

        /**
         * Adds an edge (source -> target) to this PFG.
         *
         * @return true if this PFG changed as a result of the call,
         * otherwise false.
         */
        boolean addEdge(Pointer source, Pointer target) {
            return successors.put(source, target);
        }

        /**
         * @return successors of given pointer in the PFG.
         */
        Set<Pointer> getSuccsOf(Pointer pointer) {
            return successors.get(pointer);
        }
    }
}
