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

import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.proverinterface.ProverException;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;

public class ExternalProcess implements IExternalProcess  {

    /** This class reads an input Reader into a StringBuilder on a separate
     * thread. If prompt is null, the thread will read to end of file; if prompt 
     * is non-empty, the thread will read until that string is at the end of the
     * text read; if prompt is an empty string, text is read until halt() is
     * called or end-of-file is reached. Threads are used to read the
     * regular and error output because otherwise the process can deadlock,
     * with reading or writing methods blocked because buffers are full but
     * not being read; also, both the regular and error output need to be read
     * simultaneously.
     */
    static class ThreadedReader extends Thread {
        /** The input to be read. */
        protected Reader is;

        /** The StringBuilder that accumulates the text that was read. */
        protected StringBuilder output;
        
        /** The string that will terminate reading the output, 
         * or null to read to end-of-file */
        protected /*@nullable*/ String prompt;

        /** Creates a class instance (but does not start it) for reading
         * the given input into the specified StringBuilder.
         */
        public ThreadedReader(/*@non_null*/ Reader is, /*@nullable*/ String prompt, /*@non_null*/ StringBuilder output) {
            this.is = is;
            this.prompt = prompt;
            this.output = output;
        }
        
        /** A buffer used simply to receive characters read, trying to do as
         * little copying and conversion as possible, within run().
         */
        // There is no magic about the size of this buffer - enough for a gulp
        // of reading, but not huge.
        private char[] cbuf = new char[4096];

        /** The method that is run in the new thread, when start is called;
         * don't call it directly. */
        public void run() {
            try {
                int numRead = 0;
                while (!stop && numRead != -1) {
                    if (!is.ready()) Thread.sleep(1);
                    while ((prompt == null || is.ready()) && (numRead = is.read(cbuf)) != -1) {
                        output.append(cbuf,0,numRead);
                    }
                    if (prompt != null && !prompt.isEmpty() && output.length() >= prompt.length()) {
                        if (output.indexOf(prompt,output.length()-prompt.length()) != -1) return;
                    }
                }
            } catch (Exception x) {
                output.append("Exception in thread: ");
                output.append(x.getMessage());
                output.append(System.getProperty("line.separator"));
                throw new RuntimeException("Exception in executable process reader",x);
                // FIXME - what error reporting mechanism should be used here and elsewhere (ProverException)
            }
            stop = false;
        }
        
        /** Flag that will halt the read loop */
        private boolean stop = false;
        
        /** Call this to cause the thread to cleanly exit without yet having 
         * seen an end-of-file.
         */ // FIXME - do we have concurrency/memory-model issues if this is written from a different thread?
        public void halt() {
            stop = true;
        }
    }

      
    /** If non-zero then log communication:
     * <UL>
     * <LI> =0 : no communication written
     * <LI> =1 : log errors (default)
     * <LI> =2 : log errors and strings sent
     * <LI> =3 " log errors, strings sent, and output heard
     * </UL>
     * This behavior can be overridden by showCommunication().
     */ 
    public int showCommunication = 1;

    /** The OpenJML log, for notification and warning and error messages */
    protected Log log;
    
    /** The executable and its options. */
    protected String[] app;
    
    /** The string that terminates reading the output. */
    protected /*@nullable*/ String prompt;

    /** Creates an instance of the class, but does not start execution;
     *   The prompt string may be null (non-interactive) but
     *   may not contain any CR/NL characters. */
    public ExternalProcess(Context context, String prompt, String... app) {
        this.log = Log.instance(context);
        this.prompt = prompt;
        this.app = app;
    }


    /** The process being managed */
    protected Process process = null;

    /** The stream connection to send information to the process. */
    //@ invariant process != null ==> toProver != null;
    protected Writer toProver;
    
    /** The stream connection to read information from the process. */
    //@ invariant process != null ==> fromProver != null;
    protected Reader fromProver;
    
    /** The error stream connection to read information from the process. */
    //@ invariant process != null ==> errors != null;
    protected Reader errors;
    
    /** The StringBuilder that collects output text */
    public StringBuilder outputString = new StringBuilder();
    
    /** The StringBuilder that collects error text */
    public StringBuilder errorString = new StringBuilder();
    
    /** The thread used for the error output. */
    private ThreadedReader errorReader;
    
    /** The thread used for the usual output. */
    private ThreadedReader outputReader;

    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#app()
     */
    @Override
    public String[] app() { return app; }
    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#prompt()
     */
    @Override
    public /*@nullable*/ String prompt() { return prompt; }
    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#start()
     */
    @Override
    public void start() throws ProverException {
        outputString.setLength(0);
        errorString.setLength(0);
        if (app() == null) {
            throw new ProverException("No path to the executable found");
        }
        try {
            process = new ProcessBuilder(app()).start();
        } catch (IOException e) {
            process = null;
            throw new ProverException("Failed to launch process: " + app()[0] + Strings.space + e);
        }
        // TODO: assess performance of using buffered readers/writers
        toProver = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
        fromProver = new BufferedReader(new InputStreamReader(process.getInputStream()));
        errors = new InputStreamReader(process.getErrorStream());
        
        errorReader = new ThreadedReader(errors, prompt==null? null : "", errorString);
        outputReader = new ThreadedReader(fromProver, prompt, outputString);
     
        errorReader.start();
        outputReader.start();
    }  
    
//    @Override
//    public String output() {
//        return outputString.toString();
//    }
//    
//    @Override
//    public String errorOutput() {
//        return errorString.toString();
//    }
    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#kill()
     */
    @Override
    public void kill() {
        process.destroy();
        process = null;
    }
    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#send(java.lang.String)
     */
    @Override
    public void send(String s) throws ProverException {
        outputString.setLength(0);
        errorString.setLength(0);
        if (showCommunication >= 2) {
            log.getWriter(WriterKind.NOTICE).println("SENDING ["+s.length()+ "]" + s);
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
    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#readToCompletion()
     */
    @Override
    public int readToCompletion() throws ProverException {
        if (prompt() != null) log.error("jml.internal","ExternalProcess.runToCompletion shouldnot be called when prompt has been set");
        int exitVal = -1;
        try {
            exitVal = process.waitFor();
            errorReader.join();   // Handle condition where the
            outputReader.join();  // process ends before the threads finish
        } catch (InterruptedException e) {
            throw new ProverException("readToCompletion was interrupted",e);
        }
        return exitVal;
    }
    
    
    /* (non-Javadoc)
     * @see org.jmlspecs.openjml.utils.IExternalProcess#eatPrompt()
     */
    @Override
    public String eatPrompt() throws ProverException {
        try {
            outputReader.join();
            errorReader.halt();
            errorReader.join();
            String err = errorString.toString();
            String out = outputString.toString();
            showCommunication(out,err);
            errorReader = new ThreadedReader(errors, prompt==null? null : "", errorString);
            outputReader = new ThreadedReader(fromProver, prompt, outputString);
            errorReader.start();
            outputReader.start();
            return out;
        } catch (InterruptedException e) {
            return null;
        }
    }
    
    /** A method meant to be overridden by other classes to control what
     * communication information is printed out.
     * @throws ProverException
     */
    protected void showCommunication(String out, String err) throws ProverException {
        if (showCommunication >= 3) {
            log.getWriter(WriterKind.NOTICE).println("HEARD: " + out);
        }
        if (showCommunication >= 1) {
            if (!err.isEmpty()  &&
                    !err.startsWith("\nWARNING") &&
                    !err.startsWith("CVC3 (version") &&
                    !err.startsWith("Yices (version") &&
                    !err.contains("searching") &&
                    !err.trim().isEmpty()) {
                if (showCommunication >= 1) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + err);
                //throw new ProverException("Prover error message: " + errorString);
            } else {
                if (showCommunication >= 3) log.getWriter(WriterKind.NOTICE).println("HEARD ERROR: " + err);
            }
        }
    }
    
}
