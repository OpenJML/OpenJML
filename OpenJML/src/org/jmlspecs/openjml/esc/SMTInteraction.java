package org.jmlspecs.openjml.esc;

import com.sun.tools.javac.util.Context;

public interface SMTInteraction {

    public Context getContext();
    public boolean isVerbose();
    
}
