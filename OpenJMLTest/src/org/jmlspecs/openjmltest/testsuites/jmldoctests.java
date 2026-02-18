package org.jmlspecs.openjmltest.testsuites;

import static org.junit.Assert.fail;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjmltest.EscBase;
import org.jmlspecs.openjmltest.EscBaseFiles;
import org.junit.Assume;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

/** These tests run jmldoc
 */
// FIXME - nothing implemented as yet

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class jmldoctests extends EscBaseFiles {

    @Test @Ignore
    public void jmldoc1() {
        helpEscSimple();
    }

    @Test @Ignore
    public void jmldoc2() {
        helpEscSimple();
    }

    @Test @Ignore
    public void jmldoc3() {
        helpEscSimple();
    }

    @Test @Ignore
    public void jmldoc4() {
        helpEscSimple();
    }

    @Test @Ignore
    public void jmldoc5() {
        helpEscSimple();
    }

    @Test @Ignore
    public void jmldoc6() {
        helpEscSimple();
    }

    @Test @Ignore
    public void jmldoc7() {
        helpEscSimple();
    }
}
