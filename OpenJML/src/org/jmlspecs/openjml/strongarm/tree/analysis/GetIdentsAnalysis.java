package org.jmlspecs.openjml.strongarm.tree.analysis;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.strongarm.Strongarm;

import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log.WriterKind;

public class GetIdentsAnalysis extends JmlTreeAnalysis {

    private Set<JCIdent> idents = new HashSet<JCIdent>();
    
    public GetIdentsAnalysis(Context context) {
        super(context);
    }
    
    @Override
    public void scan(JCTree node) {
        super.scan(node);
    }

    
    @Override
    public void visitIdent(JCIdent tree){
        if(tree==null) return;
        idents.add(tree);
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        
        handleField(tree);
        
        scan(tree.selected);
    }
    
    
    private void handleField(JCFieldAccess access){

        if(access.selected instanceof JCIdent){
            JCIdent selected = (JCIdent)access.selected;
            
        }
        
        if(access.selected instanceof JCFieldAccess){
            handleField((JCFieldAccess)access.selected);
        }
    }
    
    public static Set<JCIdent> analyze(List<JCExpression> list){
        
        Set<JCIdent> idents = new HashSet<JCIdent>();
        
        for(JCExpression e : list){

            GetIdentsAnalysis analysis = new GetIdentsAnalysis(Strongarm._context);
            
            analysis.scan(list);
            
            idents.addAll(analysis.idents);
        }
        
        return idents;
    }
    
    public static Set<JCIdent> analyze(JCTree e){
        
        GetIdentsAnalysis analysis = new GetIdentsAnalysis(Strongarm._context);
        
        
        analysis.scan(e);
        
        return analysis.idents;
        
    }


    public static Set<JCIdent> analyze(JCTree tree, Context ctx){
        
        GetIdentsAnalysis analysis = new GetIdentsAnalysis(ctx);
        
        
        analysis.scan(tree);
        
        return analysis.idents;
        
    }
}