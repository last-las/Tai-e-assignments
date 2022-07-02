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
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
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
        // TODO - finish me
        Vector<JMethod> workList = new Vector<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod curMethod = workList.remove(0);
            if (!callGraph.contains(curMethod)) {
                callGraph.addReachableMethod(curMethod);
                callGraph.callSitesIn(curMethod).forEach(callSite -> {
                    for (JMethod jMethod : resolve(callSite)) {
                        Edge<Invoke, JMethod> edge
                                = new Edge<>(CallGraphs.getCallKind(callSite), callSite, jMethod);
                        callGraph.addEdge(edge);
                        workList.add(jMethod);
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
        // TODO - finish me
        Set<JMethod> targetMethods = new HashSet<JMethod>();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> {
                targetMethods.add(declaringClass.getDeclaredMethod(subsignature));
            }
            case SPECIAL -> {
                JMethod targetMethod = dispatch(declaringClass, subsignature);
                if (targetMethod != null) {
                    targetMethods.add(targetMethod);
                }
            }
            case VIRTUAL -> {
                for (JClass subClass : getSubClassesOfClass(declaringClass)) {
                    JMethod targetMethod = dispatch(subClass, subsignature);
                    if (targetMethod != null) {
                        targetMethods.add(targetMethod);
                    }
                }
            }
            case INTERFACE -> {
                for (JClass subClass : getSubClassesOfInterface(declaringClass)) {
                    JMethod targetMethod = dispatch(subClass, subsignature);
                    if (targetMethod != null) {
                        targetMethods.add(targetMethod);
                    }
                }
            }
        }
        return targetMethods;
    }

    private Set<JClass> getSubClassesOfClass(JClass declaringClass) {
        Set<JClass> subClasses = new HashSet<>();
        Vector<JClass> dfsQueue = new Vector<>();
        dfsQueue.add(declaringClass);
        while (!dfsQueue.isEmpty()) {
            JClass curClass = dfsQueue.remove(0);
            if (!subClasses.contains(curClass)) {
                subClasses.add(curClass);
                dfsQueue.addAll(hierarchy.getDirectSubclassesOf(curClass));
            }
        }

        return subClasses;
    }

    private Set<JClass> getSubClassesOfInterface(JClass declaringClass) {
        // search all sub-interfaces and get the implementors of them
        Set<JClass> subInterfaces = new HashSet<>();
        Set<JClass> subClasses = new HashSet<>();
        Vector<JClass> dfsQueue = new Vector<>();
        dfsQueue.add(declaringClass);
        while (!dfsQueue.isEmpty()) {
            JClass curInterface = dfsQueue.remove(0);
            if (!subInterfaces.contains(curInterface)) {
                subInterfaces.add(curInterface);
                subClasses.addAll(hierarchy.getDirectImplementorsOf(curInterface));
                dfsQueue.addAll(hierarchy.getDirectSubinterfacesOf(curInterface));
            }
        }

        // get all subclasses of the implementors
        dfsQueue.addAll(subClasses);
        subClasses.clear();
        while (!dfsQueue.isEmpty()) {
            JClass curClass = dfsQueue.remove(0);
            if (!subClasses.contains(curClass)) {
                subClasses.add(curClass);
                dfsQueue.addAll(hierarchy.getDirectSubclassesOf(curClass));
            }
        }

        return subClasses;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        do {
            for (JMethod declaredMethod : jclass.getDeclaredMethods()) {
                if (!declaredMethod.isAbstract() &&
                        Objects.equals(declaredMethod.getSubsignature().toString(), subsignature.toString())) {
                    return declaredMethod;
                }
            }

            jclass = jclass.getSuperClass();
        } while (jclass != null);

        return null;
    }
}
