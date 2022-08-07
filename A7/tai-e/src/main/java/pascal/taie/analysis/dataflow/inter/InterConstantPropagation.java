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
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Pair;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private final ExtralFact extralFact = new ExtralFact();
    private final AliasSearcher aliasSearcher = new AliasSearcher();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // calculate alias information
        Collection<Var> vars = pta.getVars();
        for (Var var1 : vars) {
            for (Var var2 : vars) {
                if (var1.equals(var2)) {
                    continue;
                }

                Set<Obj> pts1 = pta.getPointsToSet(var1);
                Set<Obj> pts2 = pta.getPointsToSet(var2);
                boolean isAlias = false;
                for (Obj obj : pts1) {
                    if (pts2.contains(obj)) {
                        isAlias = true;
                        break;
                    }
                }

                if (isAlias) {
                    aliasSearcher.merge(var1, var2);
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
        if (out.equals(in)) {
            return false;
        } else {
            out.clear();
            out.copyFrom(in);
            return true;
        }
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();
        StmtProcessor stmtProcessor = new StmtProcessor(this.extralFact, this.aliasSearcher, this.cp, newOut);
        stmt.accept(stmtProcessor);

        if (out.equals(newOut)) {
            if (stmtProcessor.isExtraFactChanged()) {
                return true;
            } else {
                return false;
            }
        } else {
            out.clear();
            out.copyFrom(newOut);
            return true;
        }
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
        if (sourceStmt instanceof DefinitionStmt<?,?> definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
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
        Value returnValue = mergeReturnVars(returnVars, returnOut);
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

    private Value mergeReturnVars(Collection<Var> returnVars, CPFact returnOut) {
        Value returnValue = Value.getUndef();
        for (Var returnVar : returnVars) {
            returnValue = cp.meetValue(returnValue, returnOut.get(returnVar));
            if (returnValue.isNAC()) {
                return returnValue;
            }
        }

        return returnValue;
    }
}

class ExtralFact {

    public Map<JField, Value> staticFieldsValue = Maps.newMap();

    public Map<Pair<Var, JField>, Value> instanceFieldsValue = Maps.newMap();

    public Map<Pair<Var, Value>, Value> arraysValue = Maps.newMap();

    public void printArraysValue() {
        for (Pair<Var, Value> varValuePair : arraysValue.keySet()) {
            Var first = varValuePair.first();
            System.out.println(first.getMethod().getName() + ":" + first + "[" + varValuePair.second() + "]=" + arraysValue.get(varValuePair));
        }
    }

    public Value getStaticFieldValue(JField jField) {
        Value value = staticFieldsValue.get(jField);
        return parseValue(value);
    }

    public void setStaticFieldValue(JField jField, Value value) {
        if (!value.isUndef()) {
            staticFieldsValue.put(jField, value);
        }
    }

    public Value getInstanceFieldValue(Var base, JField jField) {
        Value value = instanceFieldsValue.get(new Pair<>(base, jField));
        return parseValue(value);
    }

    public void setInstanceFieldValue(Var base, JField jField, Value value) {
        if (!value.isUndef()) {
            instanceFieldsValue.put(new Pair<>(base, jField), value);
        }
    }

    public Value getArrayValue(Var base, Value indexVal) {
        if (indexVal.isConstant()) {
            return meetValue(
                    _getArrayValue(base, indexVal),
                    _getArrayValue(base, Value.getNAC())
            );
        } else if (indexVal.isNAC()) {
            Value baseNacVal = _getArrayValue(base, Value.getNAC());
            if (!baseNacVal.isUndef()) {
                return baseNacVal;
            }

            Value baseConstantVal = Value.getUndef();
            for (Pair<Var, Value> varValuePair : arraysValue.keySet()) {
                if (varValuePair.first() == base) {
                    baseConstantVal = meetValue(baseConstantVal, arraysValue.get(varValuePair));
                }
            }
            return baseConstantVal;
        } else { // Undef
            return Value.getUndef();
        }
    }

    public Value _getArrayValue(Var base, Value indexVal) {
        Value value = arraysValue.get(new Pair<>(base, indexVal));
        return parseValue(value);
    }

    public void setArrayValue(Var base, Value indexVal, Value arrayValue) {
        if (!indexVal.isUndef()) {
            _setArrayValue(base, indexVal, arrayValue);
        }
    }

    private void _setArrayValue(Var base, Value indexVal, Value arrayValue) {
        if (!arrayValue.isUndef()) {
            arraysValue.put(new Pair<>(base, indexVal), arrayValue);
        }
    }

    private Value parseValue(Value value) {
        if (value == null) {
            return Value.getUndef();
        } else {
            return value;
        }
    }

    private Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.getConstant() == v2.getConstant()) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }
}

// a very stupid implementation... space for time :(
class AliasSearcher {
    private final Map<Var, Set<Var>> aliasMap;

    public AliasSearcher() {
        aliasMap = new HashMap<>();
    }

    public Collection<Var>  getAliasOf(Var var) {
        Set<Var> aliasSet = aliasMap.get(var);
        if (aliasSet == null) {
            aliasSet = new HashSet<>();
            aliasSet.add(var);
            aliasMap.put(var, aliasSet);
        }
        return aliasSet;
    }

    public void merge(Var var1, Var var2) {
        if (aliasMap.containsKey(var1)) {
            Set<Var> var1AliasSet = aliasMap.get(var1);
            var1AliasSet.add(var2);
        } else {
            HashSet<Var> var1AliasSet = new HashSet<>();
            var1AliasSet.add(var1);
            var1AliasSet.add(var2);

            aliasMap.put(var1, var1AliasSet);
        }

        if (aliasMap.containsKey(var2)) {
            Set<Var> var2AliasSet = aliasMap.get(var2);
            var2AliasSet.add(var1);
        } else {
            HashSet<Var> var2AliasSet = new HashSet<>();
            var2AliasSet.add(var1);
            var2AliasSet.add(var2);

            aliasMap.put(var2, var2AliasSet);
        }
    }
}

// todo: might need to change Void into Boolean here?
class StmtProcessor implements StmtVisitor<Void> {
    private final ExtralFact extralFact;
    private final AliasSearcher aliasSearcher;
    private final ConstantPropagation cp;
    private final CPFact newOut;

    private boolean isExtraFactChanged = false;

    public StmtProcessor(ExtralFact extralFact, AliasSearcher aliasSearcher, ConstantPropagation cp, CPFact newOut) {
        this.extralFact = extralFact;
        this.aliasSearcher = aliasSearcher;
        this.cp = cp;
        this.newOut = newOut;
    }

    public boolean isExtraFactChanged() {
        return isExtraFactChanged;
    }

    @Override
    public Void visit(Copy copy) {
        Var lVar = copy.getLValue();
        if (ConstantPropagation.canHoldInt(lVar)) {
/*            Var rVar = copy.getRValue();
            Value rValue = newOut.get(rVar);*/
            Value lVarNewValue = ConstantPropagation.evaluate(copy.getRValue(), this.newOut);
            newOut.update(lVar, lVarNewValue);
        }
        return null;
    }

    // todo: should we handle FloatLiteral or DoubleLiteral here(I suppose not)
    @Override
    public Void visit(AssignLiteral assignLiteral) {
        Var lVar = assignLiteral.getLValue();
        if (ConstantPropagation.canHoldInt(lVar)){
            Literal rLiteral = assignLiteral.getRValue();
            /*if (rLiteral instanceof  IntLiteral intLiteral) {
                int intVal = intLiteral.getValue();
                newOut.update(lVar, Value.makeConstant(intVal));
            } else { // If rLiteral is an instance of FloatLiteral / DoubleLiteral, we make it NAC to make sure soundness.
                newOut.update(lVar, Value.getNAC());
            }*/
            Value lVarNewValue = ConstantPropagation.evaluate(rLiteral, this.newOut);
            newOut.update(lVar, lVarNewValue);
        }
        return null;
    }

    @Override
    public Void visit(Binary binary) {
        Var lVar = binary.getLValue();
        if (ConstantPropagation.canHoldInt(lVar)) {
            BinaryExp rBinaryExp = binary.getRValue();
            Value lVarNewValue = ConstantPropagation.evaluate(rBinaryExp, this.newOut);
            newOut.update(lVar, lVarNewValue);
        }
        return null;
    }

    @Override
    public Void visit(Unary unary) {
        Var lVar = unary.getLValue();
        if (ConstantPropagation.canHoldInt(lVar)) {
            UnaryExp unaryExp = unary.getRValue();
            Value lVarNewValue = ConstantPropagation.evaluate(unaryExp, this.newOut);
            newOut.update(lVar, lVarNewValue);
        }
        return null;
    }

    @Override
    public Void visit(LoadField loadField) {
        Var lVar = loadField.getLValue();
        if (!ConstantPropagation.canHoldInt(lVar)) {
            return null;
        }

        FieldAccess fieldAccess = loadField.getFieldAccess();
        JField jField = fieldAccess.getFieldRef().resolve();
        Value newValue = Value.getUndef();
        if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) { // load instance field
            Var base = instanceFieldAccess.getBase();
            for (Var var : aliasSearcher.getAliasOf(base)) { // meet all alias value into `newValue`
                Value aliasValue = extralFact.getInstanceFieldValue(var, jField);
                newValue = cp.meetValue(newValue, aliasValue);
            }

        } else { // load static field
            newValue = extralFact.getStaticFieldValue(jField);
        }

        newOut.update(lVar, newValue);
        return null;
    }

    @Override
    public Void visit(StoreField storeField) {
        Var rVar = storeField.getRValue();
        Value rVarValue = newOut.get(rVar);

        FieldAccess fieldAccess = storeField.getFieldAccess();
        JField jField = fieldAccess.getFieldRef().resolve();
        Value oldValue, newValue;
        if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) { // store instance field
            Var base = instanceFieldAccess.getBase();
            oldValue = extralFact.getInstanceFieldValue(base, jField);
            newValue = cp.meetValue(oldValue, rVarValue);
            extralFact.setInstanceFieldValue(base, jField, newValue);
        } else { // store static field
            oldValue = extralFact.getStaticFieldValue(jField);
            newValue = cp.meetValue(oldValue, rVarValue);
            extralFact.setStaticFieldValue(jField, newValue);
        }

        if (!oldValue.equals(newValue)) {
            isExtraFactChanged = true;
        }

        return null;
    }

    @Override
    public Void visit(LoadArray loadArray) {
        Var lVar = loadArray.getLValue();
        if (!ConstantPropagation.canHoldInt(lVar)) {
            return null;
        }

        ArrayAccess arrayAccess = loadArray.getArrayAccess();
        Var base = arrayAccess.getBase();
        Var index = arrayAccess.getIndex();
        Value indexValue = newOut.get(index);
        Value lVarNewValue = Value.getUndef();

        for (Var var : aliasSearcher.getAliasOf(base)) { // meet all alias value
            Value aliasValue = extralFact.getArrayValue(var, indexValue);
            lVarNewValue = cp.meetValue(lVarNewValue, aliasValue);
        }

        newOut.update(lVar, lVarNewValue);

        return null;
    }


    /*
    *
    * i = 5;
    * a[i] = 20;
    * x = a[i];      i = 7;
    *       [merged]
    *       a[i] = 1;
    *       y = a[i];
    * */
    @Override
    public Void visit(StoreArray storeArray) {
        Var rVar = storeArray.getRValue();
        Value rVarValue = newOut.get(rVar);
        ArrayAccess arrayAccess = storeArray.getArrayAccess();
        Var base = arrayAccess.getBase();
        Var index = arrayAccess.getIndex();
        Value indexValue = newOut.get(index);
        if (indexValue.isUndef()) {
            return null;
        }

        Value oldValue = extralFact._getArrayValue(base,indexValue);
        Value newValue = cp.meetValue(rVarValue, oldValue);
        extralFact.setArrayValue(base, indexValue, newValue);

        if (!oldValue.equals(newValue)) {
            isExtraFactChanged = true;
        }

        return null;
    }
}