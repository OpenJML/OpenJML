package org.jmlspecs.openjml.utils;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.proverinterface.ProverException;

/** This is an interface to the Java functionality to spawn external processes, 
 * reading the external process's output and error
 * streams. There are two ways to use this class.
 * <P>
 * <B>Execute to completion (non-interactive):</B> 
 * <UL>
 * <LI>Create an ExecProcess with the 'prompt' argument set to null. 
 * <LI>Call start()
 * <LI>Send any input, using send(). Skip this step if the executable is not
 * expecting any input.
 * <LI>Call readToCompletion(). It will block until the process is finished.
 * The return value is the exit value of the external process.
 * <LI>Use outputString.toString() and errorString.toString() to get the 
 * outputs from the external process.
 * </UL>
 * <B>Execute interactively:</B> The model is that the external process accepts
 * input and responds with output, ending in a prompt. So the output reader
 * accumulates the output and terminates with the prompt sequence is seen.
 * The error reader is then terminated as well, given a bit of an opportunity
 * to read anything in its stream.
 * The reader expects the prompt to be at the end of the output; if the prompt
 * sequence is within the output, the reader may or may not terminate. 
 * <UL>
 * <LI>Create an ExecProcess with the desired prompt string
 * <LI>Call start()
 * <LI>Call eatPrompt() to consume the first prompt after starting the process.
 * Use outputString.toString() and errorString.toString() to get the 
 * outputs from the external process.
 * <LI>Repeat:
 * <UL>
 * <LI> Call send() to send input to the external process
 * <LI> Call eatPrompt() to get output and consume the prompt. 
 * Use outputString.toString() and errorString.toString() to get the 
 * outputs from the external process.
 * </UL>
 * <LI> To terminate: Either send input (using send()) that terminates the 
 * process, or call kill().
 * </UL>
 * 
 * 
 * @author David Cok
 *
 */
public interface IExternalProcess {

    /** Returns the stored executable command line */
    public abstract String[] app();

    /** Returns the prover-specific prompt string that the eatPrompt method
     * should look for.
     * @return the prompt string
     */
    public @Nullable
    abstract String prompt();

    /** Starts the executable and the threads that read the executable's output;
     * the StringBuilders are reset to empty to start with. */
    public abstract void start() throws ProverException;

    /** Ends the external process */
    public abstract void kill();

    /** Does the actual work of sending information to the prover process.  You 
     * need to call eatPrompt for each newline you send.  This method does not 
     * add any newlines to the supplied String. 
     * @param s the String to send
     * @throws ProverException if something goes wrong
     */
    public abstract void send(String s) throws ProverException;

    /** Waits for the external process to complete, reading the output along
     * the way; expects 'prompt' to be null.
     * @return
     */
    public abstract int readToCompletion() throws ProverException;

    /** Reads output from the external process until the regular output is 
     * waiting for more input, but sees the prompt sequence at the end of the
     * output already seen. Returns the regular output; error output is 
     * available using errorString.toString()
     * @throws ProverException
     */
    public abstract String eatPrompt() throws ProverException;
    
//    /** Returns the regular output from the most recent eatPrompt or
//     * readToCompletion call
//     */
//    public abstract String output();
//    
//    /** Returns the error output from the most recent eatPrompt or
//     * readToCompletion call
//     */
//    public abstract String errorOutput();

}