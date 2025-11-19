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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.IR;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> queue = new LinkedList<>();
        queue.add(entry);
        while (!queue.isEmpty()) {
            JMethod method = queue.poll();
            if (callGraph.addReachableMethod(method)) {
                callGraph.getCallSitesIn(method).forEach(invoke -> {
                    CallKind callKind = CallGraphs.getCallKind(invoke);
                    for (JMethod callee : resolve(invoke)) {
                        callGraph.addEdge(new Edge<>(callKind, invoke, callee));
                        queue.add(callee);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        MethodRef methodRef = callSite.getMethodRef();
        JClass receiverClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        Set<JMethod> methods = new HashSet<>();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        switch (callKind) {
            case VIRTUAL, INTERFACE -> {
                Queue<JClass> klassQueue = new LinkedList<>();
                Set<JClass> visited = new HashSet<>();
                klassQueue.add(receiverClass);
                visited.add(receiverClass);
                while (!klassQueue.isEmpty()) {
                    JClass klass = klassQueue.poll();
                    if (klass.isInterface()) {
                        for (JClass nextKlass : hierarchy.getDirectSubinterfacesOf(klass)) {
                            if (visited.add(nextKlass)) {
                                klassQueue.add(nextKlass);
                            }
                        }

                        for (JClass nextKlass : hierarchy.getDirectImplementorsOf(klass)) {
                            if (visited.add(nextKlass)) {
                                klassQueue.add(nextKlass);
                            }
                        }
                } else {
                    JMethod targetMethod = dispatch(klass, subsignature);
                    if (targetMethod != null) {
                        methods.add(targetMethod);
                    }
                    for (JClass subClass : hierarchy.getDirectSubclassesOf(klass)) {
                        if (subClass != null && visited.add(subClass)) {
                            klassQueue.add(subClass);
                        }
                    }
                }
                }
            }
            case SPECIAL -> {
                JMethod target = dispatch(receiverClass, subsignature);
                if (target != null) {
                    methods.add(target);
                }
            }
            case STATIC -> {
                JMethod target = receiverClass.getDeclaredMethod(subsignature);
                if (target != null) {
                    methods.add(target);
                }
            }
        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()) {
            return method;
        }
        JClass superClass = jclass.getSuperClass();
        if (superClass != null) {
            return dispatch(superClass, subsignature);
        }
        return null;
    }
}
