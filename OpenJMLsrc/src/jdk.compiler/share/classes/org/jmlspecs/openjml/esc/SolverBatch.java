/*
 * This file is part of the OpenJML project.
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;

import org.smtlib.ICommand;
import org.smtlib.INode;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.SMT;
import org.smtlib.SolverProcess;

/** Executes an SMT script, sending each run of declarations, definitions and assertions to the
 * solver as a single block instead of one command (and one 'success' round trip) at a time.
 * A block is written as
 * <pre>
 *   (set-option :print-success false)
 *   ...commands...
 *   (set-option :print-success true)
 * </pre>
 * so that a successful block produces exactly one 'success' from the solver, while any command
 * that fails still produces its (error ...) response. All other commands (set-logic,
 * set-option, push, pop, check-sat, get-value, ...) are executed through the solver adapter as
 * usual, since adapters may keep state for them (e.g. Solver_z3_4_3 tracks the logic and the
 * push depth). This is the same set of commands, in the same order and with the same adapter
 * translation, as {@link ICommand.IScript#execute(ISolver)} sends; only the acknowledgments
 * differ.
 * <p>
 * jSMTLIB answers :print-success on the client side and does not expose raw sending, so the
 * adapter's translation and its solver process are reached by reflection:
 * {@code AbstractSolver.translate(INode)} and the {@code AbstractSolver.solverProcess} field,
 * both protected. If either is unavailable, the script is executed the ordinary way. The
 * adapter's whole-run time-limit handling (jSMTLIB 0.14.0: {@code endedByTimeLimit},
 * {@code timeLimitResponse}, {@code timeLimitResponseAfterExit}) is reached the same way, so that
 * a block cut short by --timeout-method gets the timeout response, as a single command would. A public
 * jSMTLIB entry point (e.g. {@code ISolver.sendBatch(List<ICommand>)}) would replace this.
 */
public class SolverBatch {

    /** A block smaller than this is sent command by command, as there is nothing to gain */
    static public int minimumBlockSize = 2;

    /** Commands that are sent as part of a block */
    static public boolean isBatchable(ICommand c) {
        return c instanceof ICommand.Iassert
            || c instanceof ICommand.Ideclare_fun
            || c instanceof ICommand.Ideclare_const
            || c instanceof ICommand.Idefine_fun // includes define-const
            || c instanceof ICommand.Idefine_fun_rec
            || c instanceof ICommand.Idefine_funs_rec
            || c instanceof ICommand.Ideclare_sort
            || c instanceof ICommand.Idefine_sort
            || c instanceof ICommand.Ideclare_datatype
            || c instanceof ICommand.Ideclare_datatypes;
    }

    /** Executes the script: like script.execute(solver), stops at the first error and returns it,
     * and otherwise returns the response to the last command. */
    static public IResponse execute(ICommand.IScript script, ISolver solver) {
        SMT.Configuration smtConfig = solver.smt();
        Access access = Access.of(solver);
        if (access == null) return script.execute(solver);
        IResponse response = smtConfig.responseFactory.success();
        List<ICommand> block = new ArrayList<>();
        for (ICommand c: script.commands()) {
            if (isBatchable(c)) {
                block.add(c);
                continue;
            }
            if (!block.isEmpty()) {
                IResponse r = sendBlock(block, solver, access);
                block.clear();
                if (r.isError()) return r;
            }
            response = c.execute(solver);
            if (response.isError()) return response;
        }
        // A trailing block (unusual: scripts normally end with check-sat) replaces the last response
        if (!block.isEmpty()) response = sendBlock(block, solver, access);
        return response;
    }

    /** Sends the given commands as one block, returning success or the error(s) the solver reported. */
    static protected IResponse sendBlock(List<ICommand> block, ISolver solver, Access access) {
        SMT.Configuration smtConfig = solver.smt();
        if (block.isEmpty()) return smtConfig.responseFactory.success();
        if (access.endedByTimeLimit()) return smtConfig.responseFactory.timeout();
        if (block.size() < minimumBlockSize) {
            IResponse r = smtConfig.responseFactory.success();
            for (ICommand c: block) {
                r = c.execute(solver);
                if (r.isError()) break;
            }
            return r;
        }
        StringBuilder sb = new StringBuilder();
        sb.append("(set-option :print-success false)\n");
        try {
            for (ICommand c: block) sb.append(access.translate(c)).append('\n');
        } catch (Exception e) {
            return smtConfig.responseFactory.error("Failed to translate a command for the solver: " + e);
        }
        sb.append("(set-option :print-success true)\n");
        try {
            SolverProcess process = access.process();
            // The only output of a successful block is the 'success' acknowledging the last command.
            // A failing command produces an (error ...) response. z3 then continues with the rest of
            // the block and still sends the final 'success'; cvc5 stays alive but ignores all further
            // input, so after an error the final 'success' is waited for only for a bounded time.
            StringBuilder out = new StringBuilder(process.sendAndListen(sb.toString()));
            while (!endsWithSuccess(out)) {
                if (!process.isRunning(true)) break;
                String more = out.indexOf("(error") >= 0 ? listen(process, errorWaitMillis) : process.listen();
                if (more == null || more.isEmpty()) break;
                out.append(more);
            }
            IResponse timedOut = access.timeLimitResponse(out.toString());
            if (timedOut != null) return timedOut;
            boolean completed = endsWithSuccess(out);
            String text = out.toString().trim();
            if (completed) text = text.substring(0, text.length() - "success".length()).trim();
            if (completed && text.isEmpty()) return smtConfig.responseFactory.success();
            if (!completed) {
                // The solver did not finish the block (e.g. cvc5 ignores all input after an error),
                // so it cannot be used further. Its OS process is stopped, leaving the adapter as it
                // is: a later exit() then finds the process dead and cleans up, rather than waiting
                // for a reply that will never come.
                process.stopIfRunning();
                text = text + " [the solver did not complete the block and was stopped]";
            }
            return smtConfig.responseFactory.error("Error in a block of commands sent to the solver: " + text);
        } catch (Exception e) {
            // e.g. the whole-run time limit ended the solver before or during the block
            IResponse timedOut = access.timeLimitResponseAfterExit();
            if (timedOut != null) return timedOut;
            return smtConfig.responseFactory.error("Error writing a block of commands to the solver: " + e);
        }
    }

    /** How long to wait for the rest of a block's output once the solver has reported an error */
    static public long errorWaitMillis = 2000;

    /** Listens for the next output, waiting at most the given time; returns null on a timeout */
    static private String listen(SolverProcess process, long millis) throws Exception {
        java.util.concurrent.ExecutorService ex = java.util.concurrent.Executors.newSingleThreadExecutor(r -> {
            Thread t = new Thread(r, "SolverBatch listen"); t.setDaemon(true); return t; });
        try {
            java.util.concurrent.Future<String> f = ex.submit(process::listen);
            try {
                return f.get(millis, java.util.concurrent.TimeUnit.MILLISECONDS);
            } catch (java.util.concurrent.TimeoutException e) {
                f.cancel(true);
                return null;
            }
        } finally {
            ex.shutdownNow();
        }
    }

    static private boolean endsWithSuccess(StringBuilder out) {
        String s = out.toString().trim();
        return s.equals("success") || s.endsWith("\nsuccess");
    }

    /** Reflective access to the adapter's translation and solver process */
    static protected class Access {
        final ISolver solver;
        final Method translate;
        final Field process;
        // The adapter's time-limit handling; null if this jSMTLIB does not have it
        final /*@Nullable*/ Field endedByTimeLimit;
        final /*@Nullable*/ Method timeLimitResponse;
        final /*@Nullable*/ Method timeLimitResponseAfterExit;

        private Access(ISolver solver, Method translate, Field process,
                Field endedByTimeLimit, Method timeLimitResponse, Method timeLimitResponseAfterExit) {
            this.solver = solver; this.translate = translate; this.process = process;
            this.endedByTimeLimit = endedByTimeLimit;
            this.timeLimitResponse = timeLimitResponse;
            this.timeLimitResponseAfterExit = timeLimitResponseAfterExit;
        }

        /** Returns the accessors for this solver adapter, or null if it does not have them */
        static Access of(ISolver solver) {
            Method m = null, tl = null, tla = null;
            Field f = null, ended = null;
            for (Class<?> c = solver.getClass(); c != null; c = c.getSuperclass()) {
                try { if (m == null) m = c.getDeclaredMethod("translate", INode.class); } catch (NoSuchMethodException e) {}
                try { if (f == null) f = c.getDeclaredField("solverProcess"); } catch (NoSuchFieldException e) {}
                try { if (ended == null) ended = c.getDeclaredField("endedByTimeLimit"); } catch (NoSuchFieldException e) {}
                try { if (tl == null) tl = c.getDeclaredMethod("timeLimitResponse", String.class); } catch (NoSuchMethodException e) {}
                try { if (tla == null) tla = c.getDeclaredMethod("timeLimitResponseAfterExit"); } catch (NoSuchMethodException e) {}
            }
            if (m == null || f == null || !SolverProcess.class.isAssignableFrom(f.getType())) return null;
            try {
                m.setAccessible(true);
                f.setAccessible(true);
                if (ended != null) ended.setAccessible(true);
                if (tl != null) tl.setAccessible(true);
                if (tla != null) tla.setAccessible(true);
            } catch (RuntimeException e) {
                return null;
            }
            return new Access(solver, m, f, ended, tl, tla);
        }

        String translate(ICommand c) throws Exception {
            return (String)translate.invoke(solver, c);
        }

        SolverProcess process() throws Exception {
            return (SolverProcess)process.get(solver);
        }

        boolean endedByTimeLimit() {
            try {
                return endedByTimeLimit != null && endedByTimeLimit.getBoolean(solver);
            } catch (Exception e) {
                return false;
            }
        }

        /** The timeout response if the given output is the solver's report that its whole-run limit ended it, else null */
        /*@Nullable*/ IResponse timeLimitResponse(String output) {
            try {
                return timeLimitResponse == null ? null : (IResponse)timeLimitResponse.invoke(solver, output);
            } catch (Exception e) {
                return null;
            }
        }

        /*@Nullable*/ IResponse timeLimitResponseAfterExit() {
            try {
                return timeLimitResponseAfterExit == null ? null : (IResponse)timeLimitResponseAfterExit.invoke(solver);
            } catch (Exception e) {
                return null;
            }
        }
    }
}
