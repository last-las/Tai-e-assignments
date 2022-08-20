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
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.HybridArrayHashMap;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final Map<JField, Set<StoreField>> field2StaticStoreFields = new HybridArrayHashMap<>();
    private  final Map<JField, Set<LoadField>> field2StaticLoadFields = new HybridArrayHashMap<>();
    private final Map<Var, Set<StoreField>> var2InstanceStoreFields = new HybridArrayHashMap<>();
    private final Map<Var, Set<LoadField>> var2InstanceLoadFields = new HybridArrayHashMap<>();
    private final Map<Var, Set<StoreArray>> var2StoreArrays = new HybridArrayHashMap<>();
    private final Map<Var, Set<LoadArray>> var2LoadArrays = new HybridArrayHashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // instance fields and arrays
        for (Var var1 : pta.getVars()) {
            for (Var var2 : pta.getVars()) {
                Set<Obj> pts1 = pta.getPointsToSet(var1);
                Set<Obj> pts2 = pta.getPointsToSet(var2);

                if (pts1.stream().anyMatch(pts2::contains)) { // has intersection
                    var2InstanceStoreFields.computeIfAbsent(var1, k -> new HashSet<>()).addAll(var2.getStoreFields());
                    var2InstanceLoadFields.computeIfAbsent(var1, k-> new HashSet<>()).addAll(var2.getLoadFields());
                    var2StoreArrays.computeIfAbsent(var1, k -> new HashSet<>()).addAll(var2.getStoreArrays());
                    var2LoadArrays.computeIfAbsent(var1, k -> new HashSet<>()).addAll(var2.getLoadArrays());
                }
            }
        }
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
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof LoadArray loadArray) {
            return transferLoadArrayNode(loadArray, in, out);
        } else if (stmt instanceof StoreArray storeArray) {
            return transferStoreArrayNode(storeArray, in, out);
        } else if (stmt instanceof LoadField loadField) {
            return transferLoadFieldNode(loadField, in, out);
        } else if (stmt instanceof StoreField storeField) {
            return transferStoreFieldNode(storeField, in, out);
        }

        return cp.transferNode(stmt, in, out);
    }

    private boolean transferLoadArrayNode(LoadArray loadArray, CPFact in, CPFact out) { // y = x[i];
        Var y = loadArray.getLValue();
        Var index = loadArray.getArrayAccess().getIndex();
        if (ConstantPropagation.canHoldInt(y) && ConstantPropagation.canHoldInt(index)) {
            CPFact newOut = in.copy();

            Var x = loadArray.getArrayAccess().getBase();
            Value curIndexVal = in.get(index);

            newOut.update(y, var2StoreArrays.get(x).stream()
                    .filter(storeArray -> isAliasArrayIndex(curIndexVal, solver.getInFact(storeArray).get(storeArray.getArrayAccess().getIndex())))
                    .map(storeArray -> solver.getInFact(storeArray).get(storeArray.getRValue()))
                    .reduce(cp::meetValue).orElse(Value.getUndef())
            );

            return out.copyFrom(newOut);
        }

        return out.copyFrom(in);
    }

    private boolean transferStoreArrayNode(StoreArray storeArray, CPFact in, CPFact out) { // x[i] = y;
        Var y = storeArray.getRValue();
        Value yInVal = in.get(y);
        Value yOutVal = out.get(y);
        if (!yInVal.equals(yOutVal)) {
            Var index = storeArray.getArrayAccess().getIndex();
            if (ConstantPropagation.canHoldInt(y) && ConstantPropagation.canHoldInt(index)) {
                Var x = storeArray.getArrayAccess().getBase();
                solver.addToWorkList(var2LoadArrays.get(x));
            }
        }

        return out.copyFrom(in);
    }

    private boolean isAliasArrayIndex(Value i1, Value i2) {
        if (i1.isUndef() || i2.isUndef()) {
            return false;
        } else if (i1.isConstant() && i2.isConstant()) {
            return i1.getConstant() == i2.getConstant();
        } else {
            return true;
        }
    }

    private boolean transferLoadFieldNode(LoadField loadField, CPFact in, CPFact out) { // y = x.f | y = F.f
        Var y = loadField.getLValue();
        if (ConstantPropagation.canHoldInt(y)) {
            CPFact newOut = in.copy();
            FieldAccess fieldAccess = loadField.getFieldAccess();
            if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                newOut.update(y, var2InstanceStoreFields.get(instanceFieldAccess.getBase())
                        .stream().map(storeField -> solver.getInFact(storeField).get(storeField.getRValue()))
                        .reduce(cp::meetValue).orElse(Value.getUndef())
                );
            } else {
                StaticFieldAccess staticFieldAccess = (StaticFieldAccess) fieldAccess;
                JField jField = staticFieldAccess.getFieldRef().resolve();
                field2StaticLoadFields.computeIfAbsent(jField, k -> new HashSet<>()).add(loadField);
                newOut.update(y, field2StaticStoreFields.computeIfAbsent(jField, k -> new HashSet<>())
                        .stream().map(storeField -> solver.getInFact(storeField).get(storeField.getRValue()))
                        .reduce(cp::meetValue).orElse(Value.getUndef())
                );
            }

            return out.copyFrom(newOut);
        }

        return out.copyFrom(in);
    }

    private boolean transferStoreFieldNode(StoreField storeField, CPFact in, CPFact out) { // x.f = y;
        FieldAccess fieldAccess = storeField.getFieldAccess();
        Var y = storeField.getRValue();
        Value yInVal = in.get(y);
        Value yOutVal = out.get(y);
        if (ConstantPropagation.canHoldInt(y) && !yInVal.equals(yOutVal)) {
            if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                solver.addToWorkList(var2InstanceLoadFields.get(instanceFieldAccess.getBase()));
            } else {
                StaticFieldAccess staticFieldAccess = (StaticFieldAccess) fieldAccess;
                JField jField = staticFieldAccess.getFieldRef().resolve();
                field2StaticStoreFields.computeIfAbsent(jField, k -> new HashSet<>()).add(storeField);

                solver.addToWorkList(field2StaticLoadFields.computeIfAbsent(jField, k -> new HashSet<>()));
            }
        }

        return out.copyFrom(in);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact newOut = out.copy();
        Stmt sourceStmt = edge.getSource();
        if (sourceStmt instanceof DefinitionStmt<?,?>) {
            LValue lValue = ((DefinitionStmt<?, ?>) sourceStmt).getLValue();
            if (lValue instanceof Var lVar) {
                newOut.update(lVar, Value.getUndef());
            }
        }
        return newOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact newOut = new CPFact();

        Stmt sourceStmt = edge.getSource();
        assert sourceStmt instanceof Invoke;
        List<Var> arguments = ((Invoke) sourceStmt).getInvokeExp().getArgs();
        JMethod callee = edge.getCallee();
        List<Var> parameters = callee.getIR().getParams();

        for (int i = 0; i < parameters.size(); i++) {
            newOut.update(parameters.get(i), callSiteOut.get(arguments.get(i)));
        }

        return newOut;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact newOut = new CPFact();

        Collection<Var> returnVars = edge.getReturnVars();
        Value returnValue = returnVars.stream().map(returnOut::get).reduce(cp::meetValue).orElse(Value.getUndef());
        Stmt callSite = edge.getCallSite();
        Optional<LValue> def = callSite.getDef();
        if (def.isPresent()) {
            LValue lValue = def.get();
            if (lValue instanceof Var lVar) {
                newOut.update(lVar, returnValue);
            }
        }
        return newOut;
    }
}
