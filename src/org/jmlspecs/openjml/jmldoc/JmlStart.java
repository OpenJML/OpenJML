package org.jmlspecs.openjml.jmldoc;

import java.io.PrintWriter;

import com.sun.tools.javac.util.Context;
import com.sun.tools.javadoc.Start;

public class JmlStart extends Start {

    public JmlStart(String name, String doclet) {
        super(name,doclet);
    }
    
    protected void moreRegister(Context context) {
        org.jmlspecs.openjml.jmldoc.Main.registerTools(context,new PrintWriter(System.out,true));
    }
}
