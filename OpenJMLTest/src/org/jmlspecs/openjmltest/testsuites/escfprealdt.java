package org.jmlspecs.openjmltest.testsuites;

import org.junit.runner.RunWith;
import org.openjml.runners.ParameterizedWithNames;

/** The escfpreal tests with the datatype encoding of the --fpreal sort (--fpreal-encoding=datatype) */
@org.junit.FixMethodOrder(org.junit.runners.MethodSorters.NAME_ASCENDING)
@RunWith(ParameterizedWithNames.class)
public class escfprealdt extends escfpreal {

    @Override
    public void setUp() throws Exception {
        super.setUp();
        addOptions("--fpreal-encoding=datatype");
    }
}
