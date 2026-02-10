package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedIgnorable;
import org.openjml.runners.ParameterizedWithNames;

/** These tests check running ESC on files in the file system, comparing the
 * output against expected files. These tests are a bit easier to create, since 
 * the file and output do not have to be converted into Strings; however, they
 * are not as easily read, since the content is tucked away in files, rather 
 * than immediately there in the test class.
 * <P>
 * To add a new test:
 * <UL>
 * <LI> create a directory containing the test files as a subdirectory of 
 * 'test'
 * <LI> add a test to this class - typically named similarly to the folder
 * containing the source data
 * </UL>
 */


@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escnonpublic extends EscBaseFiles {
    
    String dir = "../../OpenJMLDemo/";

    boolean enableSubexpressions = false;
    
    public java.util.List<String> collectArgs(String sourceDirname, String outDir, String ... opts) {
        Assume.assumeTrue( new File(dir).exists() );
        new File(outDir).mkdirs();
        java.util.List<String> args = new LinkedList<String>();
        File source = new File(sourceDirname);
        args.add("-cp");
        if (source.isDirectory()) args.add(sourceDirname);
        else args.add(source.getParent());
        args.add("--esc"); // FIXME - merge this with what is in EscBase
        args.add("-jmltesting");
        args.add("--code-math=java");
        args.add("--check-feasibility=basic");
        args.add("--no-warn=implicit-everything");
        if (new File(sourceDirname).isDirectory()) args.add("--dir");
        args.add(sourceDirname);
        if (solver != null) args.add("-prover="+solver);
        //addOptionsToArgs(options,args);        
        args.addAll(Arrays.asList(opts));
        return args;
    }

    public void helpTCF(String sourceDirname, String outDir, String ... opts) {
    	escOnFiles(sourceDirname,outDir,opts);
    }

    @Test
    public void escStaticModel() {
        expectedExit = 0;
        helpTCF(dir + "src/escStaticModel",dir + "src/escStaticModel","--progress");
    }

    @Test @Ignore // Sometimes times out
    public void dmz() {
        expectedExit = 0;
        helpTCF(dir + "src/dmz",dir + "src/dmz","--progress");
    }

    @Test
    public void dmz2() {
        expectedExit = 0;
        helpTCF(dir + "src/dmz2",dir + "src/dmz2","--progress");
    }

    @Test
    public void dmz3() {
        expectedExit = 0;
        helpTCF(dir + "src/dmz3",dir + "src/dmz3","--progress");
    }
    
    @Test @Ignore // not working yet
    public void escSokoban() { // FIXME
        //helpTCF("../../OpenJMLDemo/src/sokoban/Game.java","test/sokoban","-classpath","test/sokoban","--progress","-escMaxWarnings=10","-method=main","-show");
        helpTCF(dir + "src/sokoban/src",dir + "src/sokoban/src","--progress","--timeout=120");
    }

    @Test @Ignore // not working yet
    public void escSokoban2() {
        helpTCF(dir + "src/sokoban2/src",dir + "src/sokoban2/src","--progress","--timeout=120");//,"-escMaxWarnings=1","-method=Game.Game(Board,Player)","-subexpressions","-show");
    }

    @Test @Ignore // not working yet
    public void escSokoban3() {
        helpTCF(dir + "src/sokoban3/src",dir + "src/sokoban3/src","--progress","--timeout=120"); //,"-subexpressions","-show");
    }

}
