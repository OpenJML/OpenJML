/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;

import org.jmlspecs.openjml.proverinterface.ProverException;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

public class ExternalProcessNoThread implements IExternalProcess {

    /** A debugging flag - 0 = show nothing; 1 = show errors; 2 = show something; 3 = show everything */
    // Value should be 1 for ordinary operation
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("MS_SHOULD_BE_FINAL")
    static public int showCommunication = 1;
    
    public Context context;
    public Log log;
    public String[] app;
    public /*@nullable*/ String prompt;
    
    public ExternalProcessNoThread(Context context, /*@nullable*/ String prompt, String[] app) {
        this.context = context;
        this.log = Log.instance(context);
        this.app = app;
        this.prompt = prompt;
    }
        

    public void restartProver() throws ProverException {
        kill();
        start();
    }

    
    /** The stream connection to send information to the prover process. */
    //@ invariant process != null ==> toProver != null;
    protected Writer toProver;
    
    /** The stream connection to read information from the prover process. */
    //@ invariant process != null ==> fromProver != null;
    protected Reader fromProver;
    
    /** The error stream connection to read information from the prover process. */
    //@ invariant process != null ==> errors != null;
    protected Reader errors;
    
    protected Process process;

    public String[] app() { return app; }
    
    /** Does the startup work */
    public void start() throws ProverException {
        String[] app = app();
        if (app == null) {
            // FIXME - fix this error message
            throw new ProverException("No path to the executable found; specify it using -Dopenjml.prover.cvc3");
        } else {
            java.io.File f = new java.io.File(app[0]);
            if (!f.exists()) log.getWriter(WriterKind.NOTICE).println("Does not appear to exist: " + app()[0]);
            //if (!f.exists()) throw new ProverException("The specified executable does not appear to exist: " + app[0]);
        }
        try {
            process = Runtime.getRuntime().exec(app);
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch prover process: " + app()[0] + " " + e);
        }
        // TODO: assess performance of using buffered readers/writers
        toProver = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
        fromProver = new BufferedReader(new InputStreamReader(process.getInputStream()));
        errors = new InputStreamReader(process.getErrorStream());
        //eatPrompt(false);
    }    
    
    public void kill() {
        process.destroy();
        process = null;
    }
    
    /** Does the actual work of sending information to the prover process.  You 
     * need to call eatPrompt for each newline you send.  This method does not 
     * add any newlines to the supplied String. 
     * @param s the String to send
     * @throws ProverException if something goes wrong
     */
    public void send(String s) throws ProverException {
        if (showCommunication >= 2) {
            log.getWriter(WriterKind.NOTICE).print("SENDING ["+s.length()+ "]" + s); // ss has a newline so we only use print here
            log.getWriter(WriterKind.NOTICE).flush();
        }
        try {
            // The number 2000 here is arbitrary - it is just a significant
            // amount to send at once, breaking up long inputs so that the
            // prover process has a chance to catch up.  Not sure it is or
            // should be needed, but it seemed to help avoid deadlocks at one
            // time.
            final int gulp = 2000;
            if (s.length() > gulp) {
                int i = 0;
                for (; i< s.length()-gulp; i+= gulp) {
                    toProver.append(s.substring(i,i+gulp));
                    try { Thread.sleep(1); } catch (Exception e) {}
                }
                toProver.append(s.substring(i));
            } else {
                toProver.append(s);
            }
            toProver.flush();
        } catch (IOException e) {
            throw new ProverException("Failed to write to prover: (" + s.length() + " chars) " + e);
        }
    }

    public String eatPrompt() throws ProverException {
        return eatPrompt(true);
    }

    /** A buffer to hold input */
    /*@ non_null */
    protected char[] cbuf = new char[3000000];

    /** Returns the prover-specific prompt string that the eatPrompt method
     * should look for.  The string may not contain any CR/NL characters.
     * @return the prompt string
     */
    public /*@non_null*/ String prompt() { return prompt; }
    
    @Override
    public int readToCompletion() throws ProverException {
        // We read characters until the process terminates
        // FIXME - need a better way to read both inputs
        // FIXME - this probably can be made a lot more efficient
//        boolean interactive = true;
//        char[] prompt = prompt().toCharArray();
        try {
//            if (interactive) {
//                int offset = 0;
//                String s = "";
//                while (errors.ready()) {
//                    int n = errors.read(cbuf,offset,cbuf.length-offset);
//                    if (n < 0) throw new ProverException("Prover died");
//                    if (n == 0) break;
//                    offset += n;
//                }
//                if (offset > 0) {
//                    log.getWriter(WriterKind.NOTICE).println("ERROR: " + String.valueOf(cbuf,0,offset));
//                }
//                int truncated = 0;
//                while (true) { // There is always a prompt to read, so it is OK to block
//                        // until it is read.  That gives the prover process time to
//                        // do its processing.
//                    //log.getWriter(WriterKind.NOTICE).println(" ... LISTENING");
//                    int n = fromProver.read(cbuf,offset,cbuf.length-offset);
//                    if (n < 0) {
//                        int off = 0;
//                        while (errors.ready()) {
//                            int nn = errors.read(cbuf,off,cbuf.length-off);
//                            if (nn < 0) throw new ProverException("Prover died-eStream");
//                            if (nn == 0) break;
//                            off += nn;
//                        }
//                        String serr = String.valueOf(cbuf,0,off);
//                        if (!serr.startsWith("searching")) log.getWriter(WriterKind.NOTICE).println("ERROR STREAM ON DEATH: " + serr);
//                        throw new ProverException("Prover died");
//                    }
//                    offset += n;
//                    
//                    if (endsWith(offset,prompt)) break;
//                    if (offset > cbuf.length-1000) {
//                        if (s.length() > 280000) {
//                            // excessive length
//                            truncated += offset;
//                        } else {
//                            s = s + String.valueOf(cbuf,0,offset);
//                            log.getWriter(WriterKind.NOTICE).println("BUFFER FULL " + s.length());
//                        }
//                        offset = 0;
//                    }
//                }
//                if (truncated > 0) {
//                    log.getWriter(WriterKind.NOTICE).println("OUTPUT LENGTH " + s.length() + truncated);
//                    throw new ProverException("Excessive output: " + s.length() + truncated);
//                }
//                s = s + String.valueOf(cbuf,0,offset);
//                offset = 0;
//                if (errors.ready()) {
//                    while (errors.ready()) {
//                        int n = errors.read(cbuf,offset,cbuf.length-offset);
//                        if (n < 0) throw new ProverException("Prover died");
//                        if (n == 0) break;
//                        offset += n;
//                    }
//                    if (offset > 0) {
//                        String errorString = new String(cbuf,0,offset);
//                        if (!errorString.startsWith("\nWARNING") &&
//                                !errorString.startsWith("CVC3 (version") &&
//                                !errorString.startsWith("searching")) {
//                            if (showCommunication >= 1) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
//                            throw new ProverException("Prover error message: " + errorString);
//                        } else {
//                            if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
//                        }
//                    }
//                }
//                if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD: " + s);
//                return s;
//            } else {
                // In non-interactive mode, there may be no input at all
                // We sleep briefly, hoping that the target process will have time to put out any output
                try { Thread.sleep(1); } catch (Exception e) { /* No action needed */ }
                int offset = 0;
                if (true) { // FIXME - true or false?
                    // TODO: Problem: When the prover produces a counterexample, it does not always do so promptly.
                    // So the loop below tends to exit before all (or any) counterexample information is retrieved.
                    do {
                        int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) {
                            return process.exitValue();
                        }
                        offset += n;
                    } while (fromProver.ready());
                } else {
                    while (fromProver.ready()) {
                        int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) {
                            throw new ProverException("Prover died");
                        }
                        offset += n;
                    }
                }
                String s = new String(cbuf,0,offset);
                offset = 0;
                if (errors.ready()) {
                    while (errors.ready()) {
                        int n = errors.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) throw new ProverException("Prover died");
                        if (n == 0) break;
                        offset += n;
                    }
                    if (offset > 0) {
                        String errorString = new String(cbuf,0,offset);
                        if (!errorString.startsWith("\nWARNING") &&
                                !errorString.startsWith("CVC3 (version") &&
                                !errorString.startsWith("searching")) {
                            if (showCommunication >= 1) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
                        }
                    }
                }
                if (showCommunication >= 3) Log.instance(context).getWriter(WriterKind.NOTICE).println("HEARD: " + s);
//            }
        } catch (IOException e) {
            throw new ProverException("IO Error on reading from prover: " + e);
        }
        return -2;
    }
    
    protected String eatPrompt(boolean wait) throws ProverException {
        // We read characters until we get to the prompt sequence "> "
        // that marks the end of the input.  Be careful 
        // that sequence is not elsewhere in the input as well.
        // FIXME - need a better way to read both inputs
        // FIXME - this probably can be made a lot more efficient
        boolean interactive = true;
        char[] prompt = prompt().toCharArray();
        try {
            if (interactive) {
                int offset = 0;
                String s = "";
                while (errors.ready()) {
                    int n = errors.read(cbuf,offset,cbuf.length-offset);
                    if (n < 0) throw new ProverException("Prover died");
                    if (n == 0) break;
                    offset += n;
                }
                if (offset > 0) {
                    log.getWriter(WriterKind.NOTICE).println("ERROR: " + String.valueOf(cbuf,0,offset));
                }
                int truncated = 0;
                while (true) { // There is always a prompt to read, so it is OK to block
                        // until it is read.  That gives the prover process time to
                        // do its processing.
                    //log.getWriter(WriterKind.NOTICE).println(" ... LISTENING");
                    int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                    if (n < 0) {
                        int off = 0;
                        while (errors.ready()) {
                            int nn = errors.read(cbuf,off,cbuf.length-off);
                            if (nn < 0) throw new ProverException("Prover died-eStream");
                            if (nn == 0) break;
                            off += nn;
                        }
                        String serr = String.valueOf(cbuf,0,off);
                        if (!serr.startsWith("searching")) log.getWriter(WriterKind.NOTICE).println("ERROR STREAM ON DEATH: " + serr);
                        throw new ProverException("Prover died");
                    }
                    offset += n;
                    
                    if (endsWith(offset,prompt)) break;
                    if (offset > cbuf.length-1000) {
                        if (s.length() > 280000) {
                            // excessive length
                            truncated += offset;
                        } else {
                            s = s + String.valueOf(cbuf,0,offset);
                            log.getWriter(WriterKind.NOTICE).println("BUFFER FULL " + s.length());
                        }
                        offset = 0;
                    }
                }
                if (truncated > 0) {
                    log.getWriter(WriterKind.NOTICE).println("OUTPUT LENGTH " + s.length() + truncated);
                    throw new ProverException("Excessive output: " + s.length() + truncated);
                }
                s = s + String.valueOf(cbuf,0,offset);
                offset = 0;
                if (errors.ready()) {
                    while (errors.ready()) {
                        int n = errors.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) throw new ProverException("Prover died");
                        if (n == 0) break;
                        offset += n;
                    }
                    if (offset > 0) {
                        String errorString = new String(cbuf,0,offset);
                        if (!errorString.startsWith("\nWARNING") &&
                                !errorString.startsWith("CVC3 (version") &&
                                !errorString.startsWith("searching")) {
                            if (showCommunication >= 1) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
                        }
                    }
                }
                if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD: " + s);
                return s;
            } else {
                // In non-interactive mode, there may be no input at all
                // We sleep briefly, hoping that the target process will have time to put out any output
                try { Thread.sleep(1); } catch (Exception e) { /* No action needed */ }
                int offset = 0;
                if (wait) {
                    // TODO: Problem: When the prover produces a counterexample, it does not always do so promptly.
                    // So the loop below tends to exit before all (or any) counterexample information is retrieved.
                    do {
                        int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) {
                            throw new ProverException("Prover died");
                        }
                        offset += n;
                    } while (fromProver.ready());
                } else {
                    while (fromProver.ready()) {
                        int n = fromProver.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) {
                            throw new ProverException("Prover died");
                        }
                        offset += n;
                    }
                }
                String s = new String(cbuf,0,offset);
                offset = 0;
                if (errors.ready()) {
                    while (errors.ready()) {
                        int n = errors.read(cbuf,offset,cbuf.length-offset);
                        if (n < 0) throw new ProverException("Prover died");
                        if (n == 0) break;
                        offset += n;
                    }
                    if (offset > 0) {
                        String errorString = new String(cbuf,0,offset);
                        if (!errorString.startsWith("\nWARNING") &&
                                !errorString.startsWith("CVC3 (version") &&
                                !errorString.startsWith("searching")) {
                            if (showCommunication >= 1) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + errorString);
                        }
                    }
                }
                if (showCommunication >= 3) Log.instance(context).getWriter(WriterKind.NOTICE).println("HEARD: " + s);
                return s;
            }
        } catch (IOException e) {
            throw new ProverException("IO Error on reading from prover: " + e);
        }
    }
    
    protected boolean endsWith(int offset, char[] prompt) {
        int k = offset - prompt.length;
        if (k < 0) return false;
        for (int i=0; i < prompt.length; i++) {
            if (cbuf[k+i] != prompt[i]) return false;
        }
        return true;
    }
    
 
}
