package org.jmlspecs.openjmltest;

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
public abstract class RunBase extends JmlTestCase {

    public static final String[] args = new String[] { "./run" };
    
    /** Runs the 'run' executable within the 'workingDir' folder, reporting a test success if 
     * the exit code is 0 and fialure for any other result.
     */
    public void run(String workingDir) {
        try {
            Process process = Runtime.getRuntime().exec(args, null, new java.io.File(workingDir));
            int exitCode = process.waitFor();
            //System.out.println("EXIT: " + exitCode);
            if (exitCode != 0) Assert.fail("Test case emitted a failure exit code: " + exitCode);
        } catch (Throwable e) {
            //System.out.println("FAILED " + e);
            Assert.fail("Test " + workingDir + " failed to launch: " + e);
        }
    }
    
    /** A helper method that runs a test in the folder 'test/testname' where testname is the both
     * the name of the test method and the name of the test folder.
     */
    public void help() {
        run("test/" + getTestName());
    }

}

