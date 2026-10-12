/*
 * This file is part of the OpenJML project.
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.ArrayList;
import java.util.List;

import org.smtlib.ICommand;
import org.smtlib.IResponse;
import org.smtlib.ISolver;

/** Executes an SMT script, sending each run of declarations, definitions and assertions
 * ({@link ISolver#isBlockCommand(ICommand)}) to the solver with {@link ISolver#sendCommands(List)},
 * which a solver adapter may send as one block that the solver acknowledges once, instead of one
 * command (and one 'success' round trip) at a time. All other commands are executed one at a
 * time, as {@link ICommand.IScript#execute(ISolver)} does.
 */
public class SolverBatch {

    /** A run shorter than this is sent command by command, as there is nothing to gain */
    static public int minimumBlockSize = 2;

    /** Executes the script: like script.execute(solver), stops at the first error and returns it,
     * and otherwise returns the response to the last command. */
    static public IResponse execute(ICommand.IScript script, ISolver solver) {
        IResponse response = solver.smt().responseFactory.success();
        List<ICommand> block = new ArrayList<>();
        for (ICommand c: script.commands()) {
            if (ISolver.isBlockCommand(c)) {
                block.add(c);
                continue;
            }
            if (!block.isEmpty()) {
                IResponse r = sendBlock(block, solver);
                block.clear();
                if (r.isError()) return r;
            }
            response = c.execute(solver);
            if (response.isError()) return response;
        }
        // A trailing block (unusual: scripts normally end with check-sat) replaces the last response
        if (!block.isEmpty()) response = sendBlock(block, solver);
        return response;
    }

    static private IResponse sendBlock(List<ICommand> block, ISolver solver) {
        if (block.size() >= minimumBlockSize) return solver.sendCommands(block);
        IResponse r = solver.smt().responseFactory.success();
        for (ICommand c: block) {
            r = c.execute(solver);
            if (r.isError()) break;
        }
        return r;
    }
}
