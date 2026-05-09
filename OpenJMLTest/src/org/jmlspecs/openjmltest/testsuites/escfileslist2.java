package org.jmlspecs.openjmltest.testsuites;

import org.junit.FixMethodOrder;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.openjml.runners.ParameterizedWithNames;

@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfileslist2 extends escfileslist {

    @Parameters
    public static java.util.Collection<String[]> data() { 
        var data = escfileslist.alldata();
        var n = data.size();
        java.util.Collection<String[]> ndata = new java.util.LinkedList<>();
        for (int i=(int)(split1*n); i<(int)(split2*n); i++)  ndata.add(data.get(i));
        System.out.println("escfileslist2: Running " + ndata.size() + " of " + n + " tests");
        return ndata;
    }

    public escfileslist2(String testName) {
        super(testName);
    }
    
    
    @Test
    public void test() {
        helpEscName(testName, getOptions());
    }

    

}
