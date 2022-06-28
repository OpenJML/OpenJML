package org.jmlspecs.openjmltest.testcases;

import org.jmlspecs.openjmltest.LoopInvBase;
import org.junit.Test;

public class loopInv extends LoopInvBase {

    public loopInv() {
    }

    public void helper(String sourceDirname, String outDir, String... opts) {
        loopInvOnFiles(sourceDirname, outDir, opts);
    }

    @Test
    public void testLoopExcercises2() {
        expectedExit = 0;
        helper(LoopExercisesPath + "LoopExercises2.java", "test/loopInv");
    }

    @Test
    public void testLoop1() {
        expectedExit = 0;
        helper(LoopExercisesPath + "Loop1.java", "test/loop1");
    }

    @Test
    public void testLoop2() {
        helper(LoopExercisesPath + "Loop2.java", "test/loop2");
    }
}
