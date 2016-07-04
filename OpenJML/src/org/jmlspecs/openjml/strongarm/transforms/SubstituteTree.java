package org.jmlspecs.openjml.strongarm.transforms;

import java.io.StringWriter;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.source.tree.ExpressionStatementTree;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class SubstituteTree extends JmlTreeScanner{

    public JCTree currentReplacement;
    public static SubstituteTree instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab syms;
    public static boolean inferdebug = false; 
    public static boolean verbose = false; 
    


    
    public SubstituteTree(Context context){
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        
        this.inferdebug = JmlOption.isOption(context, JmlOption.INFER_DEBUG);           


        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;

    }

    public static void cache(Context context){
        if(instance==null){
            instance = new SubstituteTree(context);
        }
    }
    
    @Override
    public void scan(JCTree node) {
        //if (node != null) System.out.println("Node: "+ node.toString() + "<CLZ>" + node.getClass());
        super.scan(node);
    }
    
    @Override
    public void visitIdent(JCIdent tree){
        //if (tree != null) 
//            if(tree.toString().contains("ar_80")){            
//                System.out.println(">>IDENT: " + tree.toString());
//            }
//        
        
        if(tree==null) return;
        
        if(replace().toString().equals(tree.getName().toString()) && with() instanceof JCIdent){
            JCIdent with = (JCIdent)with();
            tree.name = with.name;
        }
            
            
            
    }
    //JCParens
    
    @Override
    public void visitUnary(JCUnary tree){
        if(tree.arg instanceof JCIdent){
            JCIdent arg = (JCIdent)tree.arg;
            
            if(replace().toString().equals(arg.getName().toString())){

                if (verbose) {
                    log.noticeWriter.println("Replacing ARG: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                }
                
                tree.arg = with();
            }
            
        }
        super.visitUnary(tree);
    }

    @Override
    public void visitParens(JCParens tree){
        
        
        if(tree.expr instanceof JCIdent){
            JCIdent expr = (JCIdent)tree.expr;
            
            if(replace().toString().equals(expr.getName().toString())){

                if (verbose) {
                    log.noticeWriter.println("Replacing PARENS: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                }
                tree.expr = with();
            }
            
        }
        
        //if(tree.expr instanceof )
        super.visitParens(tree);
        }
    private boolean isRedundant(JCBinary tree){
        if(currentReplacement instanceof JCBinary)
            return tree == currentReplacement;
        
        return false;
    }
    
    @Override 
    public void visitIndexed(JCArrayAccess tree){
        
        if(tree.toString().equals(with().toString())==false){
        
            if(tree instanceof JmlBBArrayAccess){
                JmlBBArrayAccess access = (JmlBBArrayAccess)tree;
                
                if(access.indexed instanceof JCFieldAccess){
                    handleField((JCFieldAccess)access.indexed);
                }
                
                if(access.index instanceof JCFieldAccess){
                    handleField((JCFieldAccess)access.index);
                }
                
                
                if(access.indexed instanceof JCIdent && access.indexed.toString().equals(replace().toString())){
                    access.indexed = with();
                }
                
                if(access.index instanceof JCIdent && access.index.toString().equals(replace().toString())){
                    access.index = with();
                }
            }
            
        }
        
        
        super.visitIndexed(tree);
    }
    
    @Override
    public void visitBinary(JCBinary tree) {
        
        if(isRedundant(tree)) return;
        
        if(tree.lhs instanceof JCIdent){ 
            JCIdent lhs = (JCIdent)tree.lhs;
            
            //log.noticeWriter.println("ReplacingLHS " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());

            
            if(replace().toString().equals(lhs.getName().toString())){

                if (verbose) {
                    log.noticeWriter.println("Replacing LHS: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                }
                
                tree.lhs = with();
                
               
            } 
            
        }
        
        if(tree.rhs instanceof JCIdent){ 
            JCIdent rhs = (JCIdent)tree.rhs;
            
            //log.noticeWriter.println("ReplacingRHS " + replace().toString() + " -> " + with().toString() + "in: " + tree.toString());

            
            if(replace().toString().equals(rhs.getName().toString())){

                if (verbose) {
                    log.noticeWriter.println("Replacing RHS: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                }

                tree.rhs = with();
                
            }
            
        }
        
        if(tree.lhs instanceof JCFieldAccess){
            handleField((JCFieldAccess)tree.lhs);
        }
        if(tree.rhs instanceof JCFieldAccess){
            handleField((JCFieldAccess)tree.rhs);
        }
//        if(//tree.)
        
        // we are always replacing IDENTS with EXPRESSIONS
        super.visitBinary(tree);
    }
    
    private void handleField(JCFieldAccess access){
        
        
    
        if(access.selected instanceof JCIdent){
            JCIdent selected = (JCIdent)access.selected;
            
            if(replace().toString().equals(selected.getName().toString())){

                if (verbose) {
                    log.noticeWriter.println("Replacing SELECTED: " + replace().toString() + " -> " + with().toString() + " in: " + access.toString());
                }

                access.selected = with();
                
            }
        }
        
        
        if(access.name.toString().equals(replace().toString())){
            
            if (verbose) {
                log.noticeWriter.println("Replacing TARGET: " + replace().toString() + " -> " + with().toString() + " in: " + access.toString());
            }

            if(with() instanceof JCIdent){
                JCIdent with = (JCIdent)with();
                access.name = with.name;
            }
            //access.name = with();
        }
    
        
        if(access.selected instanceof JCFieldAccess){
            handleField((JCFieldAccess)access.selected);
        }
        
        
    }
    
    public Name replace(){
        JCTree p = currentReplacement;
        
        if(p instanceof JCExpression){
            
            if(p instanceof JCBinary){
                JCBinary bProp = (JCBinary)p;
                if(bProp.lhs instanceof JCIdent){
                    return ((JCIdent)bProp.lhs).getName();
                }else{
                    return null; //((JCLiteral)bProp.lhs).getValue();
                }
                
            }else{
                //log.error("jml.internal", "Unexpected node: " + p.getClass() + " found during replacement.");
            }
            
        }else if(p instanceof JCVariableDecl){
            JCVariableDecl pVarDecl = (JCVariableDecl)p;
            return pVarDecl.getName();
        }
        
        //log.error("jml.internal", "LHS Missing in Replacement");

        
        return null;
    }
    
    public JCExpression with(){
        JCTree p = currentReplacement;

        
        if(p instanceof JCExpression){
            
            if(p instanceof JCBinary){
                JCBinary bProp = (JCBinary)p;
                return bProp.rhs;
            }else{
                log.error("jml.internal", "Unexpected node: " + p.getClass() + " found during replacement.");
            }
            
        }else if(p instanceof JCVariableDecl){
            JCVariableDecl pVarDecl = (JCVariableDecl)p;
            return pVarDecl.init;
        }
        
        log.error("jml.internal", "RHS Missing in Replacement");

        
        return null;
    }

    public static JCExpression replace(JCTree replace, JCTree in){

        instance.currentReplacement = replace;
        
        if(instance.replace()==null) return null;
        if(instance.replace().toString().startsWith("ASSERT")) return null;
        
        if(instance.replace()!=null && instance.with()!=null){
        
            //it's of course possible this is a direct substitution 
            if(in instanceof JCIdent){
                if(((JCIdent) in).getName().equals(instance.replace())){    
                    
                    if(instance.with().toString().equals("true")){
                        ((JCIdent) in).name = instance.treeutils.makeIdent(0, instance.with().toString(), in.type).name;
                    }
                   
                    return instance.with();
                }
            }else{
                instance.scan(in);
            }           
        }
        return null;
    }
    

}
