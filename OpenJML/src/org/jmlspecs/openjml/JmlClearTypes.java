package org.jmlspecs.openjml;

import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Check;
import com.sun.tools.javac.comp.CompileStates;
import com.sun.tools.javac.comp.CompileStates.CompileState;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;

import static com.sun.tools.javac.code.Flags.UNATTRIBUTED;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

public class JmlClearTypes extends JmlTreeScanner {

    public JmlClearTypes(Context context) {
        this.context = context;
    }
    
    @Override
    public void scan(JCTree node) {
//        if (!(node == null || node instanceof JmlClassDecl || node instanceof JmlMethodDecl 
//                || node instanceof JCPrimitiveTypeTree
//                || node instanceof JCTypeIntersection
//                || node instanceof JCTypeParameter)) {
        if (node != null) {
            if (node instanceof JmlClassDecl) {
                JmlClassDecl decl = ((JmlClassDecl)node);
                ClassSymbol c = decl.sym;
                if (c != null) c.flags_field |= UNATTRIBUTED;
                if (node.type != null && node.type.tsym != null) {
                    Name n = node.type.tsym.flatName();
                    if (decl.toplevel.mode != JmlCompilationUnit.SPEC_FOR_BINARY
                            || decl.isJML()
                            ) ClassReader.instance(context).removeClass(n);
                    Check.instance(context).compiled.remove(n);
                }
                JmlSpecs.instance(context).removeSpecs(((JmlClassDecl)node).sym);
                ((JmlClassDecl)node).typeSpecs = null;
                ((JmlClassDecl)node).specsDecl = null;
//                ((JmlClassDecl)node).sym = null;
            }
            if (node instanceof JmlMethodDecl) {
//                ((JmlMethodDecl)node).sym = null;
                ((JmlMethodDecl)node).specsDecl = null;
            }
            if (node instanceof JCIdent) ((JCIdent)node).sym = null;
//            node.type = null;
        }
        
        super.scan(node);
    }
    
    Context context;
    
    public static void clear(Context context, List<Env<AttrContext>> envs) {
        for (Env<AttrContext> env: envs) {
            new JmlClearTypes(context).scan(env.toplevel);
            CompileStates.instance(context).put(env, CompileState.PARSE);
        }
    }
    
}
