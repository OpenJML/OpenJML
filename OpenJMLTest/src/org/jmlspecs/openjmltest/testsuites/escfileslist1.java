package org.jmlspecs.openjmltest.testsuites;

import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfileslist1 extends escfileslist {

    @Parameters
    public static java.util.Collection<String[]> data() { 
        var data = escfileslist.alldata();
        var n = data.size();
        java.util.Collection<String[]> ndata = new java.util.LinkedList<>();
        for (int i=0; i<(int)(.4*n); i++) ndata.add(data.get(i));
        return ndata;
    }

    public escfileslist1(String testName) {
        super(testName);
    }

    @Test
    public void test() {
        helpTF(testName, addVE(getOptions()));
    }
}
