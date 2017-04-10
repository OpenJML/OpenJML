package org.jmlspecs.openjml.strongarm;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import javax.lang.model.element.ElementKind;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;


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
    
    static public @NonNull String write(@NonNull JmlClassDecl tree, boolean source) {
        StringWriter sw = new StringWriter();
        JmlPretty p = new SpecPretty(sw,source);
        p.width = 2;
        p.specOnly = true;

        // we don't want this
        /* tree.accept(p); */
        
        // we want to preserve the imports and package statements that already exist
        // (this requires we start at the toplevel)
        p.visitTopLevel(tree.toplevel);
        
        return sw.toString();
    }
    
    @Override
    public void visitVarDef(JCVariableDecl that) {
        
        if(that instanceof JmlVariableDecl){
            
            JmlVariableDecl vd = (JmlVariableDecl)that;
        
            // ignore fields.
            if (vd.sym.getKind() == ElementKind.FIELD){
                return;
            }
        }
          
        
        super.visitVarDef(that);
        
    }


  
}
