package org.jmlspecs.openjml.strongarm;

import java.io.StringWriter;
import java.io.Writer;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;

import com.sun.tools.javac.tree.JCTree;


public class SpecPretty extends JmlPretty {

    public SpecPretty(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
       
    }
    
    /** we need to remove the bodies **/
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        that.body = null;
        super.visitJmlMethodDecl(that);
    }
    
    static public @NonNull String write(@NonNull JCTree tree, boolean source) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new SpecPretty(sw,source);
        p.width = 2;
        tree.accept(p);
        return sw.toString();
    }

  
}
