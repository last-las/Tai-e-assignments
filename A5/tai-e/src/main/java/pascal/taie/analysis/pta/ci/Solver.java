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
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

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
        // TODO - finish me
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod jMethod = stmt.getMethodRef().resolve();
                Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(stmt), stmt, jMethod);
                if (callGraph.addEdge(edge)) {// 1. add the edge to call graph
                    // 2. add reachable
                    addReachable(jMethod);
                    // 3. add parameter edges to PFG
                    List<Var> args = stmt.getInvokeExp().getArgs();
                    IR ir = jMethod.getIR();
                    List<Var> params = ir.getParams();
                    for (int i = 0; i < params.size(); i++) {
                        VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
                        VarPtr paramPtr = pointerFlowGraph.getVarPtr(params.get(i));
                        addPFGEdge(argPtr, paramPtr);
                    }
                    // 4. add return edges to PFG
                    Var result = stmt.getLValue();
                    if (result == null) {
                        return null;
                    }
                    VarPtr resultPtr = pointerFlowGraph.getVarPtr(result);
                    List<Var> returnVars = ir.getReturnVars();
                    for (Var returnVar : returnVars) {
                        VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                        addPFGEdge(returnVarPtr, resultPtr);
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(New stmt) {
            Var x = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            VarPtr xPtr = pointerFlowGraph.getVarPtr(x);
            PointsToSet pointsToSet = new PointsToSet(obj);

            workList.addEntry(xPtr, pointsToSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lVar = stmt.getLValue();
            Var rVar = stmt.getRValue();
            VarPtr lVarPtr = pointerFlowGraph.getVarPtr(lVar);
            VarPtr rVarPtr = pointerFlowGraph.getVarPtr(rVar);
            addPFGEdge(rVarPtr, lVarPtr);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField lField = stmt.getFieldRef().resolve();
                Var rVar = stmt.getRValue();
                StaticField lFieldPtr = pointerFlowGraph.getStaticField(lField);
                VarPtr rVarPtr = pointerFlowGraph.getVarPtr(rVar);
                addPFGEdge(rVarPtr, lFieldPtr);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Var lVar = stmt.getLValue();
                JField rField = stmt.getFieldRef().resolve();
                VarPtr lVarPtr = pointerFlowGraph.getVarPtr(lVar);
                StaticField rFieldPtr = pointerFlowGraph.getStaticField(rField);
                addPFGEdge(rFieldPtr, lVarPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet sourcePSet = source.getPointsToSet();
            if (!sourcePSet.isEmpty()) {
                workList.addEntry(target, sourcePSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            // remove <n, pts> from WL
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet delta = propagate(n, pts);

            if (n instanceof VarPtr varPtr) {
                Var x = varPtr.getVar();
                for (Obj obj : delta) {
                    for (StoreField storeField : x.getStoreFields()) { // x.f = y
                        JField jField = storeField.getFieldRef().resolve();
                        InstanceField fieldPointer = pointerFlowGraph.getInstanceField(obj, jField);
                        Var y = storeField.getRValue();
                        VarPtr yPointer = pointerFlowGraph.getVarPtr(y);


                        addPFGEdge(yPointer, fieldPointer);
                    }

                    for (LoadField loadField : x.getLoadFields()) { // y = x.f
                        JField jField = loadField.getFieldRef().resolve();
                        InstanceField fieldPointer = pointerFlowGraph.getInstanceField(obj, jField);
                        Var y = loadField.getLValue();
                        VarPtr yPointer = pointerFlowGraph.getVarPtr(y);

                        addPFGEdge(fieldPointer, yPointer);
                    }

                    /*
                    * The ld/sd Array situation may seem a little wierd, here is some explanation:
                    * According to slide "6 PTA.pdf p86", the Array element, such as "array[0] = x", will
                    * be convert to "array.arr = x". So when variable x receives a new object, the behavior
                    * of Store/LoadArray is almost the same as Store/LoadField, but because the field is always
                    * "arr", pointerFlowGraph.getArrayIndex doesn't need the second argument any more.
                    * */
                    for (StoreArray storeArray : x.getStoreArrays()) { // x[i] = y
                        Var y = storeArray.getRValue();
                        ArrayIndex arrayPointer = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr yPointer = pointerFlowGraph.getVarPtr(y);

                        addPFGEdge(yPointer, arrayPointer);
                    }

                    for (LoadArray loadArray : x.getLoadArrays()) { // y = x[i]
                        Var y = loadArray.getLValue();
                        ArrayIndex arrayPointer = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr yPointer = pointerFlowGraph.getVarPtr(y);

                        addPFGEdge(arrayPointer, yPointer);
                    }
                    processCall(x, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet oldPointsToSet = pointer.getPointsToSet();
        PointsToSet deltaPointsToSet = new PointsToSet();

        for (Obj obj : pointsToSet) {
            if (!oldPointsToSet.contains(obj)) {
                oldPointsToSet.addObject(obj);
                deltaPointsToSet.addObject(obj);
            }
        }

        if (!deltaPointsToSet.isEmpty()) {
            for (Pointer succsPointer : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succsPointer, deltaPointsToSet);
            }
        }
        return deltaPointsToSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke callSite: var.getInvokes()) {
            // dispatch
            JMethod jMethod = resolveCallee(recv, callSite);

            // add to workList
            IR ir = jMethod.getIR();
            Var methodThisVar = ir.getThis();
            VarPtr methodThisPtr = pointerFlowGraph.getVarPtr(methodThisVar);
            PointsToSet pointsToSet = new PointsToSet(recv);
            workList.addEntry(methodThisPtr, pointsToSet);

            // update call graph if needed
            Edge<Invoke, JMethod> newEdge = new Edge<>(CallGraphs.getCallKind(callSite), callSite, jMethod);
            if (callGraph.addEdge(newEdge)) {
                addReachable(jMethod);

                List<Var> args = callSite.getInvokeExp().getArgs();
                List<Var> params = ir.getParams();
                for (int i = 0; i < params.size(); i++) {
                    VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
                    VarPtr paramPtr = pointerFlowGraph.getVarPtr(params.get(i));
                    addPFGEdge(argPtr, paramPtr);
                }

                Var result = callSite.getLValue();
                if (result == null) {
                    continue;
                }
                VarPtr resultPtr = pointerFlowGraph.getVarPtr(result);
                List<Var> returnVars = ir.getReturnVars();
                for (Var returnVar : returnVars) {
                    VarPtr returnVarPtr = pointerFlowGraph.getVarPtr(returnVar);
                    addPFGEdge(returnVarPtr, resultPtr);
                }
            }
        }
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
