package org.jmlspecs.openjmltest;

import static org.junit.Assert.fail;

import org.junit.Assert;


/** This is a base class for all tests that run external scripts.
 * The external script is responsible for checking output and comparing
 * against expected output; the test is successful if the script returns a 0 exit code
 * and a failure otherwise.
 * 
 * The test name must be a file-system folder under the 'OpenJML/test' directory.
 * The script that is run is the 'run' script within that folder;
 * the current working directory is also that same folder.
 * 
 * @author David R. Cok
 *
 */
public abstract class RunBase extends JmlTestSuite {
    
    /** Timeout to apply to the test, in milliseconds; <=0 means no timeout */
    public int timeoutMS = 0;

    /** Convenient holder for the array needed by the ProcessBuilder */
    protected static final String[] args = new String[] { "./run" };
    
    /** Runs the 'run' executable within the 'workingDir' folder, reporting a test success if 
     * the exit code is 0 and failure for any other result.
     */
    public void run(String workingDir) {
        Process process = null;
        try {
            var pb = new ProcessBuilder(args);
            pb.inheritIO();
            pb.directory(new java.io.File(workingDir));
            process = pb.start();
            if (timeoutMS > 0 && timeout(process,timeoutMS)) {
                throw new AssertionError("Test " + getTestName() + ": did not complete within the timeout period");
            }
            int exitCode = process.waitFor();
            Assert.assertEquals("Test " + getTestName() + ": emitted a failure exit code:", 0, exitCode);
        } catch (AssertionError e) {
            throw e;
        } catch (Throwable e) {
            throw new AssertionError("Test " + getTestName() + ": failed to launch or to execute: " + e);
        }
    }
    
    /** A helper method that runs a test in the folder 'test/testname' where testname is both
     * the name of the test method and the name of the test folder.
     */
    public void doTest() {
        run("test/" + getTestName());
    }

}

