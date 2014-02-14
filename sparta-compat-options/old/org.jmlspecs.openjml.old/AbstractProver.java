package org.jmlspecs.openjml.provers;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.lang.reflect.Constructor;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.proverinterface.IProver;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.ProverException;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Options;

public abstract class AbstractProver implements IProver {

    /** A debugging flag - 0 = show nothing; 1 = show errors; 2 = show something; 3 = show everything */
    // Value should be 1 for ordinary operation
    // @edu.umd.cs.findbugs.annotations.SuppressWarnings("MS_SHOULD_BE_FINAL")
    static public int showCommunication = 1;
    
    public Context context;
    public Log log;
    
    public AbstractProver(Context context) {
        this.context = context;
        this.log = Log.instance(context);
    }
        
    abstract public int assume(JCExpression tree) throws ProverException;

    static public Map<String,Class<? extends IProver>> map = new HashMap<String,Class<? extends IProver>>();
    static {
        map.put(YicesProver.NAME,org.jmlspecs.openjml.provers.YicesProver.class);
        map.put(CVC3Prover.NAME,org.jmlspecs.openjml.provers.CVC3Prover.class);
        map.put(SimplifyProver.NAME,org.jmlspecs.openjml.provers.SimplifyProver.class);
        map.put("smt",org.jmlspecs.openjml.provers.SMTProver.class);
    }
    
    @Nullable
    public String getProverPath(String proverKey) {
        String app = Options.instance(context).get("-exec");
        if (app == null) app = Options.instance(context).get(getProverPathKey(proverKey));
        return app;
    }
    
    @NonNull
    public String getProverPathKey(String proverKey) {
        return Strings.proverPropertyPrefix + proverKey;
    }
    
    static public IProver getProver(Context context, String prover) throws ProverException {
        try {
            Class<? extends IProver> c;
            c = map.get(prover);
            if (c == null) {
                Log.instance(context).error("esc.no.prover",prover);
        		throw new ProverException("Failed to find a prover named " + prover);
            }
            Constructor<? extends IProver> cn = c.getConstructor(Context.class);
            return cn.newInstance(context);
        } catch (java.lang.reflect.InvocationTargetException e) {
        	if (e.getCause() instanceof ProverException) {
        		throw (ProverException)e.getCause();
        	} else {
        		Log.instance(context).error("esc.create.prover.exception",prover,e.getCause().toString());
        		throw new ProverException(e.getCause().toString());
        	}
        } catch (Exception e) {
            Log.instance(context).error("esc.create.prover.exception",prover,e.toString());
    		throw new ProverException(e.toString());
        }
    }
    // Override if the prover can support weights
    public int assume(JCExpression tree, int weight) throws ProverException {
        return assume(tree);
    }

    public IProverResult check() throws ProverException {
        return check(true);
    }
    
    abstract public int rawassume(String s) throws ProverException;
    
    abstract public IProverResult check(boolean details) throws ProverException;

    abstract public void define(String id, Type type) throws ProverException;

    public void kill() throws ProverException {
        if (process != null) process.destroy();
        process = null;
    }
    
    abstract public void pop() throws ProverException;

    abstract public void push() throws ProverException;

    public void reassertCounterexample(ICounterexample ce) {
        throw new UnsupportedOperationException();
    }

    public void restartProver() throws ProverException {
        kill();
        start();
    }

    public void retract() throws ProverException {
        throw new UnsupportedOperationException();
    }

    public void retract(int i) throws ProverException {
        throw new UnsupportedOperationException();
    }
    
    /** The process that is the actual prover */
    protected Process process = null;
    
    /** The stream connection to send information to the prover process. */
    //@ invariant process != null ==> toProver != null;
    protected Writer toProver;
    
    /** The stream connection to read information from the prover process. */
    //@ invariant process != null ==> fromProver != null;
    protected Reader fromProver;
    
    /** The error stream connection to read information from the prover process. */
    //@ invariant process != null ==> errors != null;
    protected Reader errors;
    

    abstract protected String[] app();
    
    /** Does the startup work */
    protected void start() throws ProverException {
        String[] app = app();
        if (app == null || app[0] == null) {
            throw new ProverException("No path to the executable found; specify it using -exec or the property openjml.prover." + name());
        } else {
            java.io.File f = new java.io.File(app[0]);
            if (!f.exists()) log.noticeWriter.println("Does not appear to exist: " + app[0]);
            //if (!f.exists()) throw new ProverException("The specified executable does not appear to exist: " + app[0]);
        }
        try {
            process = Runtime.getRuntime().exec(app);
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch prover process: " + app + " " + e);
        }
        // TODO: assess performance of using buffered readers/writers
        toProver = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
        fromProver = new BufferedReader(new InputStreamReader(process.getInputStream()));
        errors = new InputStreamReader(process.getErrorStream());
        eatPrompt(false);
    }    
    
    /** Returns a version of the input with newlines and indents in order to
     * format long VCs more readably.
     * @param s The input string
     * @return a prettified version of the input
     */
    protected @NonNull String pretty(@NonNull String s) {
        return s;
    }

    /** Does the actual work of sending information to the prover process.  You 
     * need to call eatPrompt for each newline you send.  This method does not 
     * add any newlines to the supplied String. 
     * @param s the String to send
     * @throws ProverException if something goes wrong
     */
    protected void send(String s) throws ProverException {
        if (showCommunication >= 2) {
            String ss = pretty(s);
            log.noticeWriter.print("SENDING ["+s.length()+ "]" + ss); // ss has a newline so we only use print here
            log.noticeWriter.flush();
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

    protected String eatPrompt() throws ProverException {
        return eatPrompt(true);
    }

    /** A buffer to hold input */
    /*@ non_null */
    protected char[] cbuf = new char[3000000];

    /** Returns the prover-specific prompt string that the eatPrompt method
     * should look for.  The string may not contain any CR/NL characters.
     * @return the prompt string
     */
    abstract protected @NonNull String prompt();
    
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
                    log.noticeWriter.println("ERROR: " + String.valueOf(cbuf,0,offset));
                }
                int truncated = 0;
                while (true) { // There is always a prompt to read, so it is OK to block
                        // until it is read.  That gives the prover process time to
                        // do its processing.
                    //log.noticeWriter.println(" ... LISTENING");
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
                        if (!serr.startsWith("searching")) log.noticeWriter.println("ERROR STREAM ON DEATH: " + serr);
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
                            log.noticeWriter.println("BUFFER FULL " + s.length());
                        }
                        offset = 0;
                    }
                }
                if (truncated > 0) {
                    log.noticeWriter.println("OUTPUT LENGTH " + s.length() + truncated);
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
                            if (showCommunication >= 1) log.noticeWriter.println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) log.noticeWriter.println("HEARD ERROR: " + errorString);
                        }
                    }
                }
                if (showCommunication >= 3) log.noticeWriter.println("HEARD: " + s);
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
                            if (showCommunication >= 1) log.noticeWriter.println("HEARD ERROR: " + errorString);
                            throw new ProverException("Prover error message: " + errorString);
                        } else {
                            if (showCommunication >= 3) log.noticeWriter.println("HEARD ERROR: " + errorString);
                        }
                    }
                }
                if (showCommunication >= 3) Log.instance(context).noticeWriter.println("HEARD: " + s);
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
    
    public Supports supports() {
        return new Supports();
    }


}
