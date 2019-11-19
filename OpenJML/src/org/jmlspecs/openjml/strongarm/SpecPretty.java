package org.jmlspecs.openjml.strongarm;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import javax.lang.model.element.ElementKind;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;


public class SpecPretty extends JmlPretty {

    private boolean writeKey;
    private String  key;
    
    public SpecPretty(Writer out, boolean sourceOutput) {
        super(out, sourceOutput);
    }

    public SpecPretty(Writer out, boolean sourceOutput, boolean writeKey, String key) {        
        super(out, sourceOutput);
        
        this.writeKey = writeKey;
        this.key      = key;
    }

    
    /** we need to remove the bodies **/
    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        that.body = null;
        super.visitJmlMethodDecl(that);
    }
    
    @Override 
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        if (that.cases.isEmpty()) return;
        try {
            if (useJMLComments) { 
                align(); 
                if(writeKey){
                    print("/*+" + key +  "@");
                }else{
                    print("/*@");
                }
                println(); 
            }
            boolean first = true;
            for (JmlSpecificationCase c: that.cases) {
                if (first) first = false;
                else {
                    print("also"); //$NON-NLS-1$
                    println();
                }
                indent();
                align();
                c.accept(this);  // presumes already aligned; does not end with println
                println();
                undent();
            }
            if (that.feasible != null) {
                print("also feasible"); println();
                indent();
                for (JmlMethodClause cl: that.feasible) {
                    cl.accept(this);
                }
                undent();
            }
            if (useJMLComments) { align(); print(" */"); println(); }
        } catch (Exception e) { 
            perr(that,e);
        }
    }

    
    static public @NonNull String write(@NonNull JmlMethodSpecs tree, boolean source, boolean writeKey, String key) {
        StringWriter sw = new StringWriter();
        JmlPretty p = null;
        if(writeKey){
            p = new SpecPretty(sw,source, writeKey, key);
        }else{
            p = new SpecPretty(sw,source);            
        }
        p.width = 2;
        p.specOnly = true;

        tree.accept(p); 
        
        
        return sw.toString();
    }
    static public @NonNull String write(@NonNull JmlMethodSpecs tree, boolean source) {
        return write(tree, source, false, null);
    }
    
    
    static public @NonNull String write(@NonNull JmlClassDecl tree, boolean source, boolean writeKey, String key) {
        StringWriter sw = new StringWriter();
        JmlPretty p = null;
        if(writeKey){
            p = new SpecPretty(sw,source, writeKey, key);
        }else{
            p = new SpecPretty(sw,source);            
        }
        p.width = 2;
        p.specOnly = true;

        // we don't want this
        /* tree.accept(p); */
        
        // we want to preserve the imports and package statements that already exist
        // (this requires we start at the toplevel)
        p.visitTopLevel(tree.toplevel);
        
        return sw.toString();
    }
    static public @NonNull String write(@NonNull JmlClassDecl tree, boolean source) {
        return write(tree, source, false, null);
    }
    
    @Override
    public void visitVarDef(JCVariableDecl that) {
        
        if(that instanceof JmlVariableDecl){
            
            JmlVariableDecl vd = (JmlVariableDecl)that;
        
            // ignore fields.
            if (vd.sym.getKind() == ElementKind.FIELD && vd.fieldSpecsCombined==null){
                return;
            }
            
            that.init = null;
        }
          
        
        super.visitVarDef(that);
        
    }


  
}
