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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Var;
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
import pascal.taie.util.collection.Pair;

import java.util.*;

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

    private final Map<JMethod, Set<CSCallSite>> sinkMethod2CallSites = new HashMap<>();

    private final Set<CSCallSite> staticTransferCallSite = new HashSet<>();
    private final Set<Pair<CSCallSite, CSVar>> instanceTransferCallSite = new HashSet<>();

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

    public void addEntryToWorkList(CSVar csVar, CSObj csObj) {
        workList.addEntry(csVar, PointsToSetFactory.make(csObj));
    }

    public Set<CSCallSite> getCallSitesForSinkMethod(JMethod sink) {
        return sinkMethod2CallSites.computeIfAbsent(sink, set -> new HashSet<>());
    }

    private void recordSinkMethodCallSite(JMethod method, CSCallSite csCallSite) {
        if (taintAnalysis.isSinkMethod(method)) {
            sinkMethod2CallSites.computeIfAbsent(method, set -> new HashSet<>()).add(csCallSite);
        }
    }

    public void addStaticTransferCallSite(CSCallSite csCallSite) {
        staticTransferCallSite.add(csCallSite);
    }

    public void addDynamicTransferCallSite(CSCallSite csCallSite, CSVar base) {
        instanceTransferCallSite.add(new Pair<>(csCallSite, base));
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
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            StmtVisitor<Void> stmtProcessor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().stmts().forEach(
                    stmt -> stmt.accept(stmtProcessor)
            );
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

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) { // x = new T();
            Obj newObj = heapModel.getObj(stmt);
            Context newContext = contextSelector.selectHeapContext(csMethod, newObj);
            CSObj newCsObj = csManager.getCSObj(newContext, newObj);

            Var x = stmt.getLValue();
            CSVar csX = csManager.getCSVar(newContext, x);

            workList.addEntry(csX, PointsToSetFactory.make(newCsObj));

            return null;
        }

        @Override
        public Void visit(LoadField stmt) { // y = T.f;
            if (stmt.isStatic()) {
                Var y = stmt.getLValue();
                CSVar csY = csManager.getCSVar(context, y);

                JField tField = stmt.getFieldRef().resolve();
                StaticField csTField = csManager.getStaticField(tField);

                addPFGEdge(csTField, csY);
            }

            return null;
        }

        @Override
        public Void visit(StoreField stmt) { // T.f = y;
            if (stmt.isStatic()) {
                JField tField = stmt.getFieldRef().resolve();
                StaticField csTField = csManager.getStaticField(tField);

                Var y = stmt.getRValue();
                CSVar csY = csManager.getCSVar(context, y);

                addPFGEdge(csY, csTField);
            }

            return null;
        }

        @Override
        public Void visit(Copy stmt) { // x = y;
            Var y = stmt.getRValue();
            CSVar csY = csManager.getCSVar(context, y);

            Var x = stmt.getLValue();
            CSVar csX = csManager.getCSVar(context, x);

            addPFGEdge(csY, csX);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) { // r = T.m(a1,...,an);
            if (!stmt.isStatic()) {
                return null;
            }
            // for static method we don't need to dispatch it

            // select context
            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            JMethod jMethod = stmt.getMethodRef().resolve();
            Context newContext = contextSelector.selectContext(csCallSite, jMethod);

            // Neither there is no need to add anything to workList

            IR ir = jMethod.getIR();
            CSMethod csMethod = csManager.getCSMethod(newContext, jMethod);
            Edge<CSCallSite, CSMethod> newEdge = new Edge<>(CallGraphs.getCallKind(stmt), csCallSite, csMethod);
            if (callGraph.addEdge(newEdge)) {
                addReachable(csMethod);

                // add edges from arguments to parameters
                List<Var> args = stmt.getInvokeExp().getArgs();
                List<Var> params = ir.getParams();
                for (int i = 0; i < args.size(); i++) {
                    CSVar csArg = csManager.getCSVar(context, args.get(i));
                    CSVar csParam = csManager.getCSVar(newContext, params.get(i));

                    addPFGEdge(csArg, csParam);
                }

                Var callerVar = stmt.getLValue();
                if (callerVar != null) {
                    // add edges for return vars from callee to caller
                    CSVar csCallerVar = csManager.getCSVar(context, callerVar);
                    for (Var calleeVar : ir.getReturnVars()) {
                        CSVar csCalleeVar = csManager.getCSVar(newContext, calleeVar);
                        addPFGEdge(csCalleeVar, csCallerVar);
                    }

                    // if invoke stmt is source, add a taintObj to csCallerVar's pointer set
                    Optional<CSObj> result = taintAnalysis.createTaintObjFromSource(stmt);
                    result.ifPresent(csObj -> addEntryToWorkList(csCallerVar, csObj));
                }


                taintAnalysis.propTaintOnStatic(csCallSite);
                recordSinkMethodCallSite(jMethod, csCallSite);
            }

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet srcPSet = source.getPointsToSet();
            if (!srcPSet.isEmpty()) {
                workList.addEntry(target, srcPSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet delta = propagate(n, pts);

            if (n instanceof CSVar csVar) {
                for (CSObj csObj : delta) {
                    Var var = csVar.getVar();
                    processCall(csVar, csObj);
                    if (taintAnalysis.isTaintObj(csObj)) {
                        instanceTransferCallSite.stream()
                                .filter(pair -> {
                                    CSCallSite csCallSite =  pair.first();
                                    CSVar base = pair.second();
                                    return  base.getContext() == csObj.getContext() &&
                                            (base.getVar() == var || csCallSite.getCallSite().getInvokeExp().getArgs().stream().anyMatch(arg -> arg == var));
                                })
                                .forEach(pair -> {
                                    taintAnalysis.propTaintOnDynamic(pair.first(), pair.second());
                                });

                        staticTransferCallSite.stream()
                                .filter(csCallSite ->
                                        csCallSite.getContext() == csObj.getContext() &&
                                        csCallSite.getCallSite().getInvokeExp().getArgs().stream().anyMatch(arg -> arg == var))
                                .forEach(csCallSite -> taintAnalysis.propTaintOnStatic(csCallSite));
                        // skip taint object then
                        continue;
                    }

                    for (StoreField storeField : var.getStoreFields()) { // x.f = y;
                        JField field = storeField.getFieldRef().resolve();
                        InstanceField fieldPtr = csManager.getInstanceField(csObj, field);
                        Var y = storeField.getRValue();
                        CSVar csY = csManager.getCSVar(csVar.getContext(), y);

                        addPFGEdge(csY, fieldPtr);
                    }

                    for (LoadField loadField : var.getLoadFields()) { // y = x.f;
                        JField field = loadField.getFieldRef().resolve();
                        InstanceField fieldPtr = csManager.getInstanceField(csObj, field);
                        Var y = loadField.getLValue();
                        CSVar csY = csManager.getCSVar(csVar.getContext(), y);

                        addPFGEdge(fieldPtr, csY);
                    }

                    for (StoreArray storeArray : var.getStoreArrays()) { // x[i] = y;
                        ArrayIndex arrayPtr = csManager.getArrayIndex(csObj);
                        Var y = storeArray.getRValue();
                        CSVar csY = csManager.getCSVar(csVar.getContext(), y);

                        addPFGEdge(csY, arrayPtr);
                    }

                    for (LoadArray loadArray : var.getLoadArrays()) { // y = x[i];
                        ArrayIndex arrayPtr = csManager.getArrayIndex(csObj);
                        Var y = loadArray.getLValue();
                        CSVar csY = csManager.getCSVar(csVar.getContext(), y);

                        addPFGEdge(arrayPtr, csY);
                    }
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
        PointsToSet delta = PointsToSetFactory.make();

        for (CSObj csObj : pointsToSet) {
            if (oldPointsToSet.addObject(csObj)) {
                delta.addObject(csObj);
            }
        }

        if (!delta.isEmpty()) {
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var x = recv.getVar();
        for (Invoke invoke : x.getInvokes()) { // r = x.k(a1,...,an);
            // dispatch method
            JMethod jMethod = resolveCallee(recvObj, invoke);

            // select context
            Context curContext = recv.getContext();
            CSCallSite csCallSite = csManager.getCSCallSite(curContext, invoke);
            Context newContext = contextSelector.selectContext(csCallSite, recvObj, jMethod);

            // add <Method's this, recvObj> to workList
            IR ir = jMethod.getIR();
            Var methodThis = ir.getThis();
            CSVar csMethodThis = csManager.getCSVar(newContext, methodThis);
            workList.addEntry(csMethodThis, PointsToSetFactory.make(recvObj));

            CSMethod csMethod = csManager.getCSMethod(newContext, jMethod);
            Edge<CSCallSite, CSMethod> newEdge = new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod);
            if (callGraph.addEdge(newEdge)) {
                addReachable(csMethod);

                // add edges from arguments to parameters
                List<Var> args = invoke.getInvokeExp().getArgs();
                List<Var> params = ir.getParams();
                for (int i = 0; i < args.size(); i++) {
                    CSVar csArg = csManager.getCSVar(curContext, args.get(i));
                    CSVar csParam = csManager.getCSVar(newContext, params.get(i));

                    addPFGEdge(csArg, csParam);
                }

                Var callerVar = invoke.getResult();
                if (callerVar != null) {
                    // add edges for return vars from callee to caller
                    CSVar csCallerVar = csManager.getCSVar(curContext, callerVar);
                    for (Var calleeVar : ir.getReturnVars()) {
                        CSVar csCalleeVar = csManager.getCSVar(newContext, calleeVar);
                        addPFGEdge(csCalleeVar, csCallerVar);
                    }

                    // if invoke is source, create a taintObj and add it to csCallerVar
                    Optional<CSObj> result = taintAnalysis.createTaintObjFromSource(invoke);
                    result.ifPresent(taintObj -> addEntryToWorkList(csCallerVar, taintObj));
                }

                taintAnalysis.propTaintOnDynamic(csCallSite, recv);
                recordSinkMethodCallSite(jMethod, csCallSite);
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
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
