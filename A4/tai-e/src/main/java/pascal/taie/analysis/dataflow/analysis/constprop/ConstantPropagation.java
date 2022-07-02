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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Map;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact boundaryFact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            boundaryFact.update(param, Value.getNAC());
        }

        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()) {
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            target.update(var, meetValue(v1, v2));
        }

    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
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

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();
        if (stmt instanceof DefinitionStmt<?,?>) {
            LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (lValue instanceof Var lVar) {
                if (canHoldInt(lVar)) {
                    RValue rValue = ((DefinitionStmt<?, ?>) stmt).getRValue();
                    Value newValueOfLVar = evaluate(rValue,in);
                    newOut.update(lVar, newValueOfLVar);
                }
            }
        }

        if (out.equals(newOut)) {
            return false;
        } else {
            out.clear();
            out.copyFrom(newOut);
            return true;
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            int value = ((IntLiteral) exp).getValue();
            return Value.makeConstant(value);
        } else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            Value val1 = in.get(operand1);
            Value val2 = in.get(operand2);

            if (val1.isConstant() && val2.isConstant()) {
                int value1 = val1.getConstant();
                int value2 = val2.getConstant();

                Value result;
                if (exp instanceof ArithmeticExp) {
                    result = arithmeticResult(value1, value2, ((ArithmeticExp) exp).getOperator());
                } else if (exp instanceof ConditionExp) {
                    result = conditionResult(value1, value2, ((ConditionExp) exp).getOperator());
                } else if (exp instanceof ShiftExp) {
                    result = shiftResult(value1, value2, ((ShiftExp) exp).getOperator());
                } else { // BitwiseExp
                    result = bitwiseResult(value1, value2, ((BitwiseExp) exp).getOperator());
                }

                return result;
            } else if (val1.isNAC() || val2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        } else {
            return Value.getNAC();
        }
    }

    private static Value arithmeticResult(int value1, int value2, ArithmeticExp.Op op) {
        return switch (op) {
            case ADD -> Value.makeConstant(value1 + value2);
            case DIV -> {
                if (value2 == 0) {
                    yield  Value.getUndef();
                } else {
                    yield Value.makeConstant(value1 / value2);
                }
            }
            case MUL -> Value.makeConstant(value1 * value2);
            case REM -> {
                if (value2 == 0) {
                    yield Value.getUndef();
                } else {
                    yield Value.makeConstant(value1 % value2);
                }
            }
            case SUB -> Value.makeConstant(value1 - value2);
        };
    }

    private static Value conditionResult(int value1, int value2, ConditionExp.Op op) {
        boolean flag = switch (op) {
            case EQ -> value1 == value2;
            case NE -> value1 != value2;
            case LT -> value1 < value2;
            case GT -> value1 > value2;
            case LE -> value1 <= value2;
            case GE -> value1 >= value2;
        };
        if (flag) {
            return Value.makeConstant(1);
        } else {
            return Value.makeConstant(0);
        }
    }

    private static Value shiftResult(int value1, int value2, ShiftExp.Op op) {
        int v = switch (op) {
            case SHL -> value1 << value2;
            case SHR -> value1 >> value2;
            case USHR -> value1 >>> value2;
        };

        return Value.makeConstant(v);
    }

    private static Value bitwiseResult(int value1, int value2, BitwiseExp.Op op) {
        int v = switch (op) {
            case OR -> value1 | value2;
            case AND -> value1 & value2;
            case XOR -> value1 ^ value2;
        };

        return Value.makeConstant(v);
    }
}
