package org.jmlspecs.openjml.utils.ui.aspects;

import java.util.Queue;

import org.jmlspecs.openjml.utils.ui.ASTViewer;
import org.jmlspecs.openjml.utils.ui.ASTViewerConfigurationUtil;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.util.Pair;

public aspect ASTTransformAspect {
    
    pointcut callJmlCompilerRAC(Env<AttrContext> env): 
        call(* org.jmlspecs.openjml.JmlCompiler.rac(Env<AttrContext>)) 
            && args(env) && if(ASTViewerConfigurationUtil.viewASTEnabled());
    
    before(Env<AttrContext> env) : callJmlCompilerRAC(env) {
        ASTViewer.addView("PRE JmlCompiler.rac", env.tree, ASTViewer.ViewType.DIALOG);
    }
 
    after(Env<AttrContext> env) returning(Env<AttrContext> e) : callJmlCompilerRAC(env)  {
        ASTViewer.addView("POST JmlCompiler.rac", e.tree, ASTViewer.ViewType.DIALOG);
    }
    
    
    pointcut callDesugar(final Env<AttrContext> env, Queue<Pair<Env<AttrContext>, JCClassDecl>> results): 
        call(* com.sun.tools.javac.main.JavaCompiler.desugar(Env<AttrContext>, Queue<Pair<Env<AttrContext>, JCClassDecl>>)) 
            && args(env, results) && if(ASTViewerConfigurationUtil.viewASTEnabled());

    
    before(final Env<AttrContext> env, Queue<Pair<Env<AttrContext>, JCClassDecl>> results) : callDesugar(env, results) {
        ASTViewer.addView("PRE JavaCompiler.desugar", env.tree, ASTViewer.ViewType.DIALOG);
    }

    after(final Env<AttrContext> env, Queue<Pair<Env<AttrContext>, JCClassDecl>> results) : callDesugar(env, results) {
        ASTViewer.addView("POST JavaCompiler.desugar", env.tree, ASTViewer.ViewType.DIALOG);
    }

}
