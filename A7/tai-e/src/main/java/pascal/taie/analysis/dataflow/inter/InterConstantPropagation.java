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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public PointerAnalysisResult pta;

    public Map<Obj, Set<Var>> aliasMap = new HashMap<>();
    public Map<Pair<Obj, FieldRef>, Value> instanceFieldValue = new HashMap<>();
    public Map<JField, Value> staticFieldValue = new HashMap<>();
    public Map<Pair<Obj, Value>, Value> arrayIndexValue = new HashMap<>();
    public Map<JField, Set<Stmt>> staticFieldLoadStmts = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        pta.getVars().forEach(var -> pta.getPointsToSet(var).forEach(obj -> {
            Set<Var> alias = aliasMap.getOrDefault(obj, new HashSet<>());
            alias.add(var);
            aliasMap.put(obj, alias);
        }));
        icfg.getNodes().forEach(node -> {
            if (node instanceof LoadField loadField) {
                if (loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                    JField jField = staticFieldAccess.getFieldRef().resolve();
                    Set<Stmt> stmts = staticFieldLoadStmts.getOrDefault(jField, new HashSet<>());
                    stmts.add(node);
                    staticFieldLoadStmts.put(jField, stmts);
                }
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed;
        if (stmt instanceof StoreField storeField) {
            changed = out.copyFrom(in);
            Value rValue = in.get(storeField.getRValue());
            if (storeField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                JField staticField = staticFieldAccess.getFieldRef().resolve();
                Value old = staticFieldValue.getOrDefault(staticField, Value.getUndef());
                Value newValue = cp.meetValue(old, rValue);
                if (!old.equals(newValue)) {
                    staticFieldValue.put(staticField, newValue);
                    solver.addAllToWorkList(staticFieldLoadStmts.getOrDefault(staticField,  new HashSet<>()));
                }
            } else if (storeField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                Var var = instanceFieldAccess.getBase();
                FieldRef fieldRef = instanceFieldAccess.getFieldRef();
                pta.getPointsToSet(var).forEach(obj -> {
                     Value old = instanceFieldValue.getOrDefault(new Pair<>(obj, fieldRef), Value.getUndef());
                     Value newValue = cp.meetValue(old, rValue);
                     if (!newValue.equals(old)) {
                         // Puts all load x Instruments of o's alias into the workList if o.x is updated.
                         instanceFieldValue.put(new Pair<>(obj, fieldRef), newValue);
                         propagateFieldAlias(obj);
                     }
                });
            }
        } else if (stmt instanceof StoreArray storeArray) {
            changed = out.copyFrom(in);
            Value rValue = in.get(storeArray.getRValue());
            ArrayAccess arrayAccess = storeArray.getArrayAccess();
            Value indexValue = in.get(arrayAccess.getIndex());
            pta.getPointsToSet(arrayAccess.getBase()).forEach(obj -> {
                Value old = arrayIndexValue.getOrDefault(new Pair<>(obj, indexValue), Value.getUndef());
                Value newValue = cp.meetValue(old, rValue);
                if (!newValue.equals(old) && !indexValue.isUndef()) {
                    // Puts all load Array Instruments of o's alias into the workList
                    arrayIndexValue.put(new Pair<>(obj, indexValue), newValue);
                    propagateArrayAccessAlias(obj);
                }
            });
        } else if (stmt instanceof LoadField loadField) {
            changed = out.copyFrom(in);
            Var var = loadField.getLValue();
            Value rValue;
            if (loadField.getFieldAccess() instanceof StaticFieldAccess staticFieldAccess) {
                rValue = staticFieldValue.getOrDefault(staticFieldAccess.getFieldRef().resolve(), Value.getUndef());
            } else if (loadField.getFieldAccess() instanceof InstanceFieldAccess instanceFieldAccess) {
                rValue = Value.getUndef();
                Var base = instanceFieldAccess.getBase();
                for (Obj obj : pta.getPointsToSet(base)) {
                     Value value = instanceFieldValue.getOrDefault(new Pair<>(obj, loadField.getFieldRef()), Value.getUndef());
                     rValue = cp.meetValue(rValue, value);
                }
            } else {
                assert false;
                rValue = Value.getNAC();
            }
            changed |= out.update(var, rValue);
        } else if (stmt instanceof LoadArray loadArray) {
            changed = out.copyFrom(in);
            Var lValue = loadArray.getLValue();
            Value indexValue = in.get(loadArray.getArrayAccess().getIndex());
            Value resValue = Value.getUndef();
            if (!indexValue.isUndef()) {
                for (Obj obj : pta.getPointsToSet(loadArray.getArrayAccess().getBase())) {
                    for (var entry : arrayIndexValue.entrySet()) {
                        var pair = entry.getKey();
                        var keyIndexValue = pair.second();
                        var arrayAccessValue = entry.getValue();
                        if (obj.equals(pair.first())) {
                            if (indexValue.isNAC()) {
                                resValue = cp.meetValue(resValue, arrayAccessValue);
                            } else if (indexValue.isConstant() && (keyIndexValue.isNAC() || keyIndexValue.equals(indexValue))) {
                                resValue = cp.meetValue(resValue, arrayAccessValue);
                            }
                        }
                    }
                }
                changed |= out.update(lValue, resValue);
            }
        } else {
            changed = cp.transferNode(stmt, in, out);
        }
        return changed;
    }

    private void propagateFieldAlias(Obj obj) {
        aliasMap.getOrDefault(obj, new HashSet<>()).forEach(
                alias -> alias.getLoadFields().forEach(loadField -> solver.addToWorkList(loadField)));
    }

    private void propagateArrayAccessAlias(Obj array) {
        aliasMap.getOrDefault(array, new HashSet<>()).forEach(
                alias -> alias.getLoadArrays().forEach(loadArray -> solver.addToWorkList(loadArray)));
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact result = out.copy();
        Optional<LValue> def = edge.getSource().getDef();
        if (def.isPresent()) {
            LValue lValue = def.get();
            if (lValue instanceof Var var) {
                result.remove(var);
            }
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact result = cp.newInitialFact();
        JMethod callee = edge.getCallee();
        Stmt caller = edge.getSource();
        if (caller instanceof Invoke invoke) {
            InvokeExp invokeExp = invoke.getInvokeExp();
            for (int i = 0; i < invokeExp.getArgCount(); i ++) {
                Var arg = invokeExp.getArg(i);
                Var param = callee.getIR().getParam(i);
                Value v = callSiteOut.get(arg);
                result.update(param, v);
            }
        }
        return result;

    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact result = cp.newInitialFact();
        Optional<LValue> def = edge.getCallSite().getDef();
        if (def.isPresent()) {
            LValue lValue = def.get();
            if (lValue instanceof Var var) {
                for (Var retVar : edge.getReturnVars()) {
                    Value oldValue = result.get(var);
                    Value newValue = cp.meetValue(oldValue, returnOut.get(retVar));
                    result.update(var, newValue);
                }
                if (ConstantPropagation.canHoldInt(var) && !result.get(var).isConstant()) result.update(var, Value.getNAC());
            }
        }

        return result;
    }
}
