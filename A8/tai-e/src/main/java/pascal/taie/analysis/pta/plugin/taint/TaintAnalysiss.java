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
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public Optional<CSObj> getTaintObjOf(Invoke stmt) {
        JMethod method = stmt.getMethodRef().resolve();
        if(config.getSources().stream().anyMatch(source -> source.method() == method)){
            // assume the source's type is equal to method's return type, fix here if not
            CSObj csObj = makeTaint(stmt, method.getReturnType());
            return Optional.of(csObj);
        } else {
            return Optional.empty();
        }
    }

    public void taintTransferStatic(CSCallSite csCallSite) {
        JMethod method = csCallSite.getCallSite().getMethodRef().resolve();

        config.getTransfers().stream().filter(transfer ->method.equals(transfer.method()) && isArgToResult(transfer)).forEach(
                transfer -> transferTaintArgToResult(transfer, csCallSite)
        );
    }

    public void taintTransferDynamic(CSCallSite csCallSite, CSVar base) {
        JMethod method = csCallSite.getCallSite().getMethodRef().resolve();

        config.getTransfers().stream().filter(transfer -> transfer.method() == method).forEach(transfer -> {
            if (isArgToResult(transfer)) {
                transferTaintArgToResult(transfer, csCallSite);
            } else if (isArgToBase(transfer)) {
                transferTaintArgToBase(transfer, csCallSite, base);
            } else if (isBaseToResult(transfer)) {
                transferTaintBaseToResult(transfer, csCallSite, base);
            }
        });
    }

    public boolean isTaintObj(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

    private CSObj makeTaint(Invoke stmt, Type type) {
        Obj taintObj = manager.makeTaint(stmt, type);
        return csManager.getCSObj(emptyContext, taintObj);
    }

    private boolean isArgToResult(TaintTransfer transfer) {
        return  transfer.from() >= 0 &&
                transfer.to() == TaintTransfer.RESULT;
    }

    private void transferTaintArgToResult(TaintTransfer transfer, CSCallSite csCallSite) {
        Invoke callSite = csCallSite.getCallSite();
        List<Var> args = callSite.getInvokeExp().getArgs();

        int index = transfer.from();
        if (index >= args.size()) {
            return;
        }

        Context context = csCallSite.getContext();
        Var arg = args.get(index);
        CSVar csArg = csManager.getCSVar(context, arg);
        Var result = callSite.getResult();
        if (result == null) {
            return;
        }
        CSVar csResult = csManager.getCSVar(context, result);

        csArg.getPointsToSet().objects().forEach(csObj -> {
            Obj obj = csObj.getObject();
            if (manager.isTaint(obj)) {
                Invoke sourceCall = manager.getSourceCall(obj);
                CSObj taintCsObj = makeTaint(sourceCall, transfer.type());

                solver.addEntryToWorkList(csResult, taintCsObj);
            }
        });
    }

    private boolean isArgToBase(TaintTransfer transfer) {
        return transfer.from() >= 0 &&
                transfer.to() == TaintTransfer.BASE;
    }

    private void transferTaintArgToBase(TaintTransfer transfer, CSCallSite csCallSite, CSVar base) {
        Invoke callSite = csCallSite.getCallSite();
        List<Var> args = callSite.getInvokeExp().getArgs();
        int index = transfer.from();

        if (index >= args.size()) {
            return;
        }

        Context context = csCallSite.getContext();
        Var arg = args.get(index);
        CSVar csArg = csManager.getCSVar(context, arg);

        csArg.getPointsToSet().objects().forEach(csObj -> {
            Obj obj = csObj.getObject();
            if (manager.isTaint(obj)) {
                Invoke sourceCall = manager.getSourceCall(obj);
                CSObj taintCsObj = makeTaint(sourceCall, transfer.type());

                solver.addEntryToWorkList(base, taintCsObj);
            }
        });
    }

    private boolean isBaseToResult(TaintTransfer transfer) {
        return transfer.from() == TaintTransfer.BASE &&
                transfer.to() == TaintTransfer.RESULT;
    }

    private void transferTaintBaseToResult(TaintTransfer transfer, CSCallSite csCallSite, CSVar base){
        Invoke callSite = csCallSite.getCallSite();
        Context context = csCallSite.getContext();
        Var result = callSite.getResult();
        if (result == null) {
            return;
        }
        CSVar csResult = csManager.getCSVar(context, result);

        base.getPointsToSet().objects().forEach(csObj -> {
            Obj obj = csObj.getObject();
            if (manager.isTaint(obj)) {
                Invoke sourceCall = manager.getSourceCall(obj);
                CSObj taintCsObj = makeTaint(sourceCall, transfer.type());

                solver.addEntryToWorkList(csResult, taintCsObj);
            }
        });
    }

    private void propagateTaintObj(CSVar csVar, CSObj csObj) {
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        config.getSinks().forEach(sink -> {
            JMethod method = sink.method();
            solver.getCsCallSiteOfMethod(method).forEach(csCallSite -> {
                Invoke sinkCall = csCallSite.getCallSite();
                List<Var> args = sinkCall.getInvokeExp().getArgs();
                int index = sink.index();

                if (index >= args.size()) {
                    return;
                }
                Var arg = args.get(index);
                Context context = csCallSite.getContext();
                CSVar csVar = csManager.getCSVar(context, arg);

                result.getPointsToSet(csVar).forEach(csObj -> {
                    if (isTaintObj(csObj)) {
                        Invoke sourceCall = manager.getSourceCall(csObj.getObject());
                        taintFlows.add(new TaintFlow(sourceCall, sinkCall, index));
                    }
                });
            });
        });
        return taintFlows;
    }
}
