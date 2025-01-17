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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        deadCode.addAll(ir.getStmts());
        HashSet<Stmt> visitedSet = new HashSet<>(); // record visited Stmt
        Vector<Stmt> visitList = new Vector<>(); // BFS list
        visitList.add(cfg.getEntry());

        while (!visitList.isEmpty()) { // bfs
            Stmt curStmt = visitList.remove(0);
            visitedSet.add(curStmt);
            Set<Stmt> curStmtSuccessors;
            if (curStmt instanceof AssignStmt<?, ?> assignStmt) {
                SetFact<Var> curLiveVars = liveVars.getOutFact(curStmt);
                if (!isUseLessAssignment(assignStmt,curLiveVars)) {
                    deadCode.remove(curStmt);
                }
                curStmtSuccessors = cfg.getSuccsOf(curStmt);
            } else if (curStmt instanceof If ifStmt) {
                deadCode.remove(curStmt);

                CPFact curCPFact = constants.getInFact(curStmt);
                curStmtSuccessors = getSuccessorsOfIfStmt(ifStmt, curCPFact, cfg);
            } else if (curStmt instanceof SwitchStmt switchStmt) {
                deadCode.remove(curStmt);

                CPFact curCPFact = constants.getInFact(curStmt);
                curStmtSuccessors = getSuccessorsOfSwitchStmt(switchStmt, curCPFact, cfg);
            } else { // DefinitionStmt and other stmt.class
                deadCode.remove(curStmt);
                curStmtSuccessors = cfg.getSuccsOf(curStmt);
            }

            for (Stmt succes: curStmtSuccessors) {
                if (!visitedSet.contains(succes)) {
                    visitedSet.add(succes);
                    visitList.add(succes);
                }
            }
        }
        return deadCode;
    }

    private static boolean isUseLessAssignment(AssignStmt<?,?> assignStmt, SetFact<Var> curLiveVars) {
        LValue lValue = assignStmt.getLValue();
        if (lValue instanceof Var lVar) {
            return !curLiveVars.contains(lVar) && hasNoSideEffect(assignStmt.getRValue());
        }

        return false;
    }

    private static Set<Stmt> getSuccessorsOfIfStmt(If ifStmt, CPFact curCPFact, CFG<Stmt> cfg) {
        Set<Stmt> successor = new HashSet<>();

        ConditionExp conditionExp = ifStmt.getCondition();
        Value value = ConstantPropagation.evaluate(conditionExp, curCPFact);
        if (value.isConstant()) {
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(ifStmt);
            for (Edge<Stmt> outEdge: outEdges) {
                boolean condition;
                if (value.getConstant() == 1) {
                    condition = true;
                } else {
                    assert value.getConstant() == 0;
                    condition = false;
                }
                Edge.Kind kind = outEdge.getKind();
                if (condition && kind == Edge.Kind.IF_TRUE) {
                    successor.add(outEdge.getTarget());
                    break;
                } else if (!condition && kind == Edge.Kind.IF_FALSE){
                    successor.add(outEdge.getTarget());
                    break;
                }
            }
            assert successor.size() == 1;
        } else {
            successor.addAll(cfg.getSuccsOf(ifStmt));
        }

        return successor;
    }

    private static Set<Stmt> getSuccessorsOfSwitchStmt(SwitchStmt switchStmt, CPFact curCPFact, CFG<Stmt> cfg) {
        Set<Stmt> successor = new HashSet<>();

        Var var = switchStmt.getVar();
        Value value = ConstantPropagation.evaluate(var, curCPFact);
        if (value.isConstant()) {
            int constant = value.getConstant();
            for (Pair<Integer, Stmt> caseTarget : switchStmt.getCaseTargets()) {
                if (caseTarget.first() == constant) {
                    successor.add(caseTarget.second());
                    break;
                }
            }
            if (successor.isEmpty()) {
                successor.add(switchStmt.getDefaultTarget());
            }
        } else {
            successor.addAll(cfg.getSuccsOf(switchStmt));
        }

        return successor;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
