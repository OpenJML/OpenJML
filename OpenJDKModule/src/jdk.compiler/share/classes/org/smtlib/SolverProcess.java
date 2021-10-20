/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/** This class implements launching, writing to, and reading responses from a 
 * launched process (in particular, solver processes).
 * @author David Cok
 */
public class SolverProcess {
    
    static public int sleepTime = 1;
    static public boolean useNotifyWait = false; // TOOD: Not sure that true works
    static public boolean useShutdownHooks = true;
    static public boolean useMultiThreading = true;
	
	final static protected String eol = System.getProperty("line.separator");
	
	protected StreamGobbler standardOut;
	protected StreamGobbler errorOut;
	
	/** Wraps an exception thrown because of a failure in the prover */
	public static class ProverException extends RuntimeException {
		private static final long serialVersionUID = 1L;

		public ProverException(String s) { super(s); }
	}
	
	/** The command-line arguments that launch a new process */
	protected String[] app;

	/** The text that marks the end of the text returned from the process */
	protected String endMarker;

	/** The Java process object (initialized by start() )*/
	protected Process process;
	
	/** The Writer object that writes to the spawned process (initialized by start() )*/
	protected Writer toProcess;
	
	/** The Reader process that reads from the standard output of the spawned process (initialized by start() )*/
	protected Reader fromProcess;
	
	/** The Reader process that reads from the standard error stream of the spawned process (initialized by start() )*/
	protected Reader errors;
	
	/** A place (e.g., log file), if non-null, to write all outbound communications for diagnostic purposes */
	public /*@Nullable*/Writer log;
	
	/** Constructs a SolverProcess object, without actually starting the process as yet.
	 * @param cmd the command-line that will launch the desired process
	 * @param endMarker text that marks the end of text returned from the process, e.g. the end of the 
	 * prompt for new input
	 * @param logfile if not null, the name of a file to log communications to, for diagnostic purposes
	 */
	static java.io.PrintWriter pw = null;
	public SolverProcess(String[] cmd, String endMarker, /*@Nullable*/String logfile) {
		this.endMarker = endMarker;
		try {
			if (logfile != null) {
				log = new FileWriter(logfile);
			} else {
//			    log = pw == null ? (pw = new java.io.PrintWriter(System.out)) : pw;
			}
		} catch (IOException e) {
			System.out.println("Failed to create solver log file " + logfile + ": " + e); // FIXME - wwrite to somewhere better
		}
		setCmd(cmd);
	}
	
	/** Enables changing the command-line; must be called prior to start() */
	public void setCmd(String[] cmd) {
		this.app = cmd;
		try {
			if (log != null && cmd != null) {
				// TODO: Might be nicer to escape any backslashes and enclose strings in quotes, in case arguments contain spaces or special characters
				log.write(";; ");
				for (String s: cmd) { log.write(s); log.write(" "); }
				log.write(eol);
			}
		} catch (IOException e) {
			System.out.println("Failed to write to solver log file : " + e); // FIXME - wwrite to somewhere better
		}
	}
	
	protected Thread shutdownThread = null;
	
	/** Starts the process; if the argument is true, then also listens to its output until a prompt is read. */
    public void start(boolean listen) throws ProverException {
    	try {
    	    String path = System.getenv("PATH");
    	    if (false && path != null) {
    	        String[] envp = new String[] { "PATH=" + path };
    	        process = Runtime.getRuntime().exec(app,envp);
    	    } else {
                process = Runtime.getRuntime().exec(app);
    	    }
//    		if (useShutdownHooks) {
//    		    shutdownThread = new Thread() { public void run() { process.destroyForcibly(); }};
//    		    Runtime.getRuntime().addShutdownHook( shutdownThread );
//    		}
    		toProcess = new OutputStreamWriter(process.getOutputStream());
    		if (useMultiThreading) {
                errorOut = new StreamGobbler(process.getErrorStream(), null);
                standardOut = new StreamGobbler(process.getInputStream(), s->endsWith(s,endMarker));
                errorOut.start();
                standardOut.start();
    		} else {
    		    fromProcess = new BufferedReader(new InputStreamReader(process.getInputStream()));
    		    errors = new InputStreamReader(process.getErrorStream());
    		}
    		Thread.sleep(1000);
    		if (listen) listen();
    	} catch (IOException e) {
    		throw new ProverException(e.getMessage());
    	} catch (RuntimeException|InterruptedException e) {
    		throw new ProverException(e.getMessage());
    	}
    }
    
    boolean endsWith(StringBuilder sb, String endMarker) {
        int sblen = sb.length();
        int len = endMarker.length();
        int i = len;
        while (i > 0 && endMarker.charAt(len-i) == sb.charAt(sblen-i)) --i;
        if (i != 0) return false;
        // In some cases, the endMarker is just an eol, but the ojutput can be a long
        // S-expression broken up with eols. SO we must recognize an end of input only
        // if the parentheses are balanced.
        i = sb.indexOf("(");
        if (i < 0) return true;
        int count = 1;
        i++;
        for (; i < sblen; ++i) {
            char c = sb.charAt(i);
            if (c == '(') count++;
            else if (c == ')') count--;
        }
        return count == 0;
    }

    /** Listens to the process's standard output until the designated endMarker is read 
     * and to the error output. If there is error output, it is returned;
     * otherwise the standard output is returned.
     */
	public String listen() throws IOException {
		// FIXME - need to put the two reads in parallel, otherwise one might block on a full buffer, preventing the other from completing
		if (!useMultiThreading) {
		    String err = listenThru(errors,null);
	        String out = listenThru(fromProcess,endMarker);
	        err = err + listenThru(errors,null);
	        if (log != null) {
	            if (!out.isEmpty()) { log.write(";OUT: "); log.write(out); log.write(eol); log.flush(); } // input usually ends with a prompt and no line terminator
	            if (!err.isEmpty()) { log.write(";ERR: "); log.write(err); } // input usually ends with a line terminator, we think
	        }
//	      System.out.println("OUT: " + out.replace('\r', '@').replace('\n', '@'));
//	      System.out.println("ERR: " + err.replace('\r', '@').replace('\n', '@'));
	        // In some cases (yices2) the prompt is on the error stream. Our heuristic is that then there is no line-termination
	        if (err.endsWith("\n") || out.isEmpty()) {
	            return err.isEmpty() || err.charAt(0) == ';' ? out : err; // Note: the guard against comments (starting with ;) is for Z3
	        } else {
                if (out.endsWith(endMarker)) out = out.substring(0,out.length()-endMarker.length());
	            return out;
	        }
		} else {
		    // FIXME - should not have to busy wait with sleep command and the watsch on a field in another thread
            String out;
            if (useNotifyWait) {
                out = standardOut.getString();  // may block until output is available
            } else {
                try { do { Thread.sleep(sleepTime); } while (standardOut.output == null && process.isAlive()); } catch (InterruptedException e) {}
                out = standardOut.getString();
            }
		    String err = errorOut.getString(); // errorOut is set up to not block -- presuming error output is ready if standard out has completed, since there is no indication when the error output is completed
            if (err.endsWith("\n") || out.isEmpty()) {
                return err.isEmpty() || err.charAt(0) == ';' ? out : err; // Note: the guard against comments (starting with ;) is for Z3
            } else {
                if (out.endsWith(endMarker)) out = out.substring(0,out.length()-endMarker.length());
                return out;
            }
		}
	}
	
	/** Returns true if the process is still running; this relies on exceptions
	 * for control flow and may be a bit expensive.
	 */
	public boolean isRunning(boolean expectStopped) {
		if (process == null) return false;
		try {
			process.exitValue();
			if (!expectStopped) {
				if (log != null) { 
					try {
						log.write("Solver has unexpectedly terminated"); log.write(eol); log.flush();
					} catch (IOException e) {
						// ignore
					}
				}	
			}
			return false;
		} catch (IllegalThreadStateException e) {
			return true;
		}
	}
	
	/** Aborts the process; returns immediately if already stopped */
	public void exit() {
		if (process == null) return;
		if (shutdownThread != null) Runtime.getRuntime().removeShutdownHook(shutdownThread);
		shutdownThread = null;
		process.destroy();
		process = null;
		toProcess = null;
		if (log != null) {
			try {
				log.write(";;Exiting solver"); 
				log.write(eol);
				log.flush();
				log.close();
			} catch (IOException e) {
				// Ignore
			}
		}
	}
	
	/** Sends all the given text arguments, then (if listen is true) listens for the designated end marker text */
	public /*@Nullable*/ String send(boolean listen, String ... args) throws IOException {
		if (toProcess == null) throw new ProverException("The solver has not been started");
		for (String arg: args) {
			if (log != null) log.write(arg);
			toProcess.write(arg);
		}
		if (log != null) log.flush();
		toProcess.flush();
		if (listen) return listen();
		return null;
	}

	/** Sends all the given text arguments, then listens for the designated end marker text */
	public /*@Nullable*/ String sendAndListen(String ... args) throws IOException {
		return send(true,args);
	}

	/** Sends all the given text arguments, but does not wait for a response */
	public void sendNoListen(String ... args) throws IOException {
		send(false,args);
	}

// TODO - combine listen and noListen versions of send?
	
	/** A pool of buffers used by listenThru. The listenThru method needs a buffer, which may need to be big.
	 *  However, the method is called often and we do not want to be continually allocating big buffers that
	 *  have to wait around to be garbage collected.  Especially since, unless there are multiple SMT processes
	 *  working simultaneously, we will never need more than one of these.  But in order to be thread-safe we 
	 *  cannot simply declare a static buffer.
	 */
	static private List<char[]> bufferCollection = Collections.synchronizedList(new LinkedList<char[]>());
	
	/** Gets a buffer out of the shared free-list of buffers 
	 * @return a free buffer available to be used
	 */
	synchronized private static char[] getBuffer() {
		char[] buf;
		if (bufferCollection.isEmpty()) {
			// There is nothing magic about the size of the buffers - just meant to be generally enough to
			// hold the output of a read, but not so large as to unnecessarily use memory. 
			// If it is not large enough, it will be expanded.
			buf = new char[10000];
		} else {
			buf = bufferCollection.remove(0);
		}
		return buf;
	}
	
	/** Puts a buffer back into the shared free-list.
	 * @param buf the buffer being released
	 */
	synchronized private static void putBuffer(char[] buf) {
		bufferCollection.add(buf);
	}
	
	/** Reads the given Reader until the given String is read (or end of input is reached);
	 * may block until input is available; the stopping string must occur at the end of the
	 * input.  This is typically used to read through a prompt on standard output; when the stopping
	 * string (the prompt) is read, one knows that the output from the program is complete and not
	 * to wait for any more.
	 * 
	 * @param r the Reader to read characters from
	 * @param end a stopping String
	 * @return the String read
	 * @throws IOException if an IO failure occurs
	 */
	static public /*@NonNull*/String listenThru(/*@NonNull*/Reader r, /*@Nullable*/ String end) throws IOException {
	    if (!useMultiThreading) {
	        char[] buf = getBuffer();
	        try {
	            int len = end != null ? end.length() : 0;
	            int p = 0; // Number of characters read
	            int parens = 0;
	            while (end != null || r.ready()) {
	                //System.out.println("ABOUT TO READ " + p);
	                int i = r.read(buf,p,buf.length-p);
	                if (i == -1) break; // End of Input
	                for (int ii=0; ii<i; ++ii) {
	                    if (buf[p+ii] == '(') ++parens; 
	                    else if (buf[p+ii] == ')') --parens;
	                }
	                p += i;
	                //System.out.println("HEARD: " + new String(buf,0,p));
	                if (p>100 && len == 1) {
	                    len = len;
	                }
	                if (end != null && p >= len) {
	                    // Need to compare a String to a part of a char array - we iterate by
	                    // hand to avoid creating a new String or CharBuffer object
	                    boolean match = true;
	                    int k = p-len;
	                    for (int j=0; j<len; j++) {
	                        if (end.charAt(j) != buf[k++]) { match = false; break; }
	                    }
	                    if (match && (badFormat || parens == 0)) break; // stopping string matched
	                }
	                if (p == buf.length) { // expand the buffer
	                    char[] nbuf = new char[2*buf.length];
	                    System.arraycopy(buf,0,nbuf,0,p);
	                    buf = nbuf;
	                }
	            }
	            return new String(buf,0,p);
	        } finally {
	            putBuffer(buf);
	        }
	    } else {
	        return null;
	    }
	}
	
	public static boolean badFormat = false;
	
	public static class StreamGobbler extends Thread {
	    
	    /*@ non_null */java.io.InputStream is;
        /*@ non_null */StringBuilder accumulator;
        /*@ nullable */String output;
	    /*@ nullable */ java.util.function.Function<StringBuilder,Boolean> endRecognizer;
	    
	    char[] buf = new char[10000];
	    
	    public StreamGobbler(/*@ non_null */java.io.InputStream is, 
	                            /*@ nullable */ java.util.function.Function<StringBuilder,Boolean> endRecognizer) {
	        this.is = is;
	        this.endRecognizer = endRecognizer;
	        accumulator = new StringBuilder();
	    }
	    
	    public void run()
	    {
	        try (
	            InputStreamReader isr = new InputStreamReader(is);
	            BufferedReader br = new BufferedReader(isr); ){
	            int n;
	            while ((n = br.read(buf)) > 0) {
	                accumulator.append(buf,0,n);
	                //System.out.println("OUT/ERR: " + accumulator.toString());
	                if (endRecognizer != null && endRecognizer.apply(accumulator)) {
	                    putString();
	                }
	            }
	            // if n == -1 then end of stream has been reached and the StreamGobbler exits
	        } catch (IOException ioe) {
	            throw new RuntimeException(ioe);
	        }
	    }
	    
	    public synchronized void putString() {
	        output = accumulator.toString();
	        accumulator.setLength(0);
            if (useNotifyWait) notifyAll();
	    }
	    
	    public synchronized /*@ nullable */ String getString() {
	        if (useNotifyWait) {
	            if (endRecognizer == null) {
                    String s = accumulator.toString();
                    accumulator.setLength(0);
                    return s;
	            } else {
	                while (output == null) {
	                    try {
	                        wait();
	                    } catch (InterruptedException e) {}
	                }
	                String out = output;
	                output = null;
	                return out;
	            }
	            
	        } else {
	            if (output == null) {
	                synchronized(accumulator) {
	                    String s = accumulator.toString();
	                    accumulator.setLength(0);
	                    return s;
	                }
	            } else {
	                String s = output;
	                output = null;
	                return s;
	            }
	        }
	    }
	}
	
	public static void main(String ... args) {
        java.util.Scanner in = new java.util.Scanner(System.in); 
        SolverProcess.useMultiThreading = true;
	    SolverProcess sp = new SolverProcess(args, "\n", null);
	    sp.start(false);
	    while (true) {
            String s = in.nextLine(); 
            System.out.println("READ " + s);
            try {
                System.out.println("WRITING " + s);
//                sp.toProcess.write(s);
//                sp.toProcess.write("\n");
//                sp.toProcess.flush();
                String out = sp.sendAndListen(s + "\n");
                System.out.println("HEARD: " + out);
            } catch (java.io.IOException e) {
                System.out.println("FAILED TO WRITE INPUT " + e);
            }
            try { Thread.sleep(100); } catch (Exception e) {}
//            if (SolverProcess.useMultiThreading) { 
//                System.out.println("OUT: " + sp.standardOut.getString());
//                System.out.println("ERR: " + sp.errorOut.getString());
//            } else {
//                try {
//                    System.out.println("OUT: " + ((BufferedReader)sp.fromProcess).readLine());
//                    System.out.println("ERR: " + ((InputStreamReader)sp.errors).read());
//                } catch (java.io.IOException e) {
//                    System.out.println("FAILED TO READ FROM PROCESS " + e);
//                }
//            }
	    }
	}
}
