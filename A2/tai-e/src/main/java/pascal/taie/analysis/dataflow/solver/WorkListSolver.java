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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.Vector;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        // TODO - How about using Set? Why or Why not?
        Vector<Node> workList = new Vector<Node>();
        // add all basic blocks to workList, except Entry block!
        for (Node node: cfg) {
            if (!cfg.isEntry(node)) {
                workList.add(node);
            }
        }

        while (!workList.isEmpty()) {
            Node curBlock = workList.remove(0);
            // calculate IN[B] and update the result
            Fact inB = result.getInFact(curBlock);
            for (Node predsNode: cfg.getPredsOf(curBlock)) {
                Fact outP = result.getOutFact(predsNode);
                analysis.meetInto(outP, inB);
            }

            // calculate OUT[B]
            Fact outB = result.getOutFact(curBlock);
            if (analysis.transferNode(curBlock, inB, outB)) {
                workList.addAll(cfg.getSuccsOf(curBlock));
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
