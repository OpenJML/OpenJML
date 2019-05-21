package org.jmlspecs.openjml.strongarm.transforms;

import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.annotation.NonNull;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlBBArrayAccess;
import org.jmlspecs.openjml.JmlTree.JmlBBFieldAssignment;
import org.jmlspecs.openjml.JmlTree.JmlStatementExpr;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.ext.OptionsInfer;
import org.jmlspecs.openjml.strongarm.Strongarm;
import org.jmlspecs.openjml.strongarm.SubstitutionCache;
import org.jmlspecs.openjml.vistors.IJmlVisitor;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.source.tree.ExpressionStatementTree;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCArrayAccess;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCTypeCast;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Log.WriterKind;
import com.sun.tools.javac.util.Name;

public class SubstituteTree2 extends JmlTreeScanner{

    public JCTree                          currentReplacement;
    public static SubstituteTree2           instance;
    
    final protected Log                    log;
    final protected Utils                  utils;
    final protected JmlTreeUtils           treeutils;
    final protected JmlTree.Maker          M;
    final protected Context                context;
    final Symtab                           syms;
    public static boolean                  inferdebug; 
    public static boolean                  verbose; 
        
    public SubstituteTree2(Context context){
        this.context    = context;
        this.log        = Log.instance(context);
        this.utils      = Utils.instance(context);
        this.treeutils  = JmlTreeUtils.instance(context);
        this.M          = JmlTree.Maker.instance(context);
        this.syms       = Symtab.instance(context);
        this.inferdebug = JmlOption.isOption(context, OptionsInfer.INFER_DEBUG);           
        
        this.verbose = inferdebug || JmlOption.isOption(context,"-verbose") // The Java verbose option
            || utils.jmlverbose >= Utils.JMLVERBOSE;
    }

    public static void cache(Context context){
        if(instance==null){
            instance = new SubstituteTree2(context);
        }
    }
    
    @Override
    public void scan(JCTree node) {
        //if (node != null) System.out.println("Node: "+ node.toString() + "<CLZ>" + node.getClass());
        super.scan(node);
    }
    
    @Override
    public void visitSelect(JCFieldAccess tree) {
        
        handleField(tree);
        
        scan(tree.selected);
    }
    
    @Override
    public void visitIdent(JCIdent tree){
        if(tree==null) return;
        
        if(canReplace(tree) && with() instanceof JCIdent && with()!=null && replace()!=null && tree.getName()!=null && with() instanceof JCIdent){
            try {
                if(verbose){
                    log.getWriter(WriterKind.NOTICE).println("\t\tReplacing IDENT: " + tree.getName().toString() + " -> " + with().toString() + " in: " + tree.toString());
                }
                
                JCIdent with = (JCIdent)with();
                if(with==null || with.name==null){
                    return;
                }
                tree.name = with.name;
                // also the symbol
                tree.sym  = with.sym;
            }catch(NullPointerException e){}
        }
    }

    @Override
    public void visitUnary(JCUnary tree){
        if(tree.arg instanceof JCIdent){
            JCIdent arg = (JCIdent)tree.arg;
            
            if(canReplace(arg)){
                try {
                    if (verbose) {
                        log.getWriter(WriterKind.NOTICE).println("\t\tReplacing ARG: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                    }                
                    tree.arg = with();
                }catch(NullPointerException e){}
            }            
        }
        super.visitUnary(tree);
    }

    private String replacementSummary(JCTree tree){
           
        if(isTmpVar){
            return String.format("%s -> %s in: %s", replace().toString(), with().toString(), tree.toString());            
        }else{
            return String.format("%s -> %s in: %s", replace().toString(), with().toString(), tree.toString());
        }
    }
    @Override
    public void visitParens(JCParens tree){
        
        if(tree.expr instanceof JCIdent){
            JCIdent expr = (JCIdent)tree.expr;
            
            if(canReplace(expr)){
                try {
                    if (verbose) {
                        log.getWriter(WriterKind.NOTICE).println("\t\tReplacing PARENS: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                    }
                    tree.expr = with();
                }catch(NullPointerException e){}
            }    
        }
        super.visitParens(tree);
    }
    
    private boolean isRedundant(JCBinary tree){
        return currentReplacement!=null && currentReplacement.toString().equals(tree.toString());
    }
    
    @Override 
    public void visitIndexed(JCArrayAccess tree){
        
               
        
            
        JCArrayAccess access = tree;
        
        if(access.indexed instanceof JCFieldAccess){
            handleField((JCFieldAccess)access.indexed);
        }
        
        if(access.index instanceof JCFieldAccess){
            handleField((JCFieldAccess)access.index);
        }
        
        if(access.indexed instanceof JCIdent && canReplace((JCIdent)access.indexed)){
           
            try {
                log.getWriter(WriterKind.NOTICE).println("\t\tReplacing INDEXED: " + access.indexed.toString() + " -> " + with().toString() + " in: " + tree.toString());

                access.indexed = with();
            }catch(NullPointerException e){}
        }
        
        if(access.index instanceof JCIdent && canReplace((JCIdent)access.index)){

            try {
                log.getWriter(WriterKind.NOTICE).println("\t\tReplacing INDEXED: " + access.indexed.toString() + " -> " + with().toString() + " in: " + tree.toString());

                access.index = with();
            }catch(NullPointerException e){}
        }
    
        
    
      super.visitIndexed(tree);
    }
    
    @Override
    public void visitBinary(JCBinary tree) {
        
        
        if(tree.lhs instanceof JCIdent){ 
            // 
            // tree.operator.toString().startsWith("==")==false){
            //
            JCIdent lhs = (JCIdent)tree.lhs;

            if(canReplace(lhs) && isRedundant(tree)==false && replace()!=null && with()!=null){
                
                try {
                    if (verbose) {
                        log.getWriter(WriterKind.NOTICE).println("\t\tReplacing LHS: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                    }
                    
                    tree.lhs = with();
                }catch(NullPointerException e){}
            }
        }
        
        if(tree.rhs instanceof JCIdent && isRedundant(tree)==false){ 

            JCIdent rhs = (JCIdent)tree.rhs;

            if(canReplace(rhs)){

                try {
                    if (verbose) {
                        log.getWriter(WriterKind.NOTICE).println("\t\tReplacing RHS: " + replace().toString() + " -> " + with().toString() + " in: " + tree.toString());
                    }
    
                    tree.rhs = with();
                }catch(NullPointerException e){}
            }
        }
        
        if(tree.lhs instanceof JCFieldAccess){
            handleField((JCFieldAccess)tree.lhs);
        }
        if(tree.rhs instanceof JCFieldAccess){
            handleField((JCFieldAccess)tree.rhs);
        }

        super.visitBinary(tree);        
    }
    
    private void handleField(JCFieldAccess access){

        if(access.selected instanceof JCIdent){
            JCIdent selected = (JCIdent)access.selected;
            
            if(canReplace(selected) && with()!=null && replace()!=null){

                try {
                    if (verbose) {
                        log.getWriter(WriterKind.NOTICE).println("\t\tReplacing SELECTED: " + replace().toString() + " -> " + with().toString() + " in: " + access.toString());
                    }
    
                    access.selected = with();
                }catch(NullPointerException e){}
            }
        }
        
        
        
        if(access.sym instanceof VarSymbol && canReplace((VarSymbol)access.sym, access.name)){
           
            try {
                if (verbose) {
                    log.getWriter(WriterKind.NOTICE).println("\t\tReplacing TARGET: " + replace().toString() + " -> " + with().toString() + " in: " + access.toString());
                }
                
                if(Strongarm.identCache.contains(access.toString())){
                    Strongarm.oldCache.add(access);
                }
    
                if(with() instanceof JCIdent){
                    JCIdent with = (JCIdent)with();
                    access.name = with.name;
                    access.sym  = with.sym;
                }
            }catch(NullPointerException e){}
        }
        
        if(access.selected instanceof JCFieldAccess){
            handleField((JCFieldAccess)access.selected);
        }
    }
    
    public JCIdent handleTypeCast(JCTypeCast tree){
        
        if(tree.expr instanceof JCIdent){
            return (JCIdent)tree.expr;
        }
        
        if(tree.expr instanceof JCTypeCast){
            return handleTypeCast((JCTypeCast)tree.expr);
        }
        
        return null;
    }
    
        
    public Name replace(){
        JCTree p = currentReplacement;
        Name n = null;
        
        if(isTmpVar){
            return tmpVar;
        }
        
        if(p instanceof JCExpression){
            
            if(p instanceof JCBinary){
                JCBinary bProp = (JCBinary)p;
                if(bProp.lhs instanceof JCIdent){
                    n = ((JCIdent)bProp.lhs).getName();
                }else if(bProp.lhs instanceof JCTypeCast){
                    n =  handleTypeCast((JCTypeCast)bProp.lhs).getName();
                }else{
                    return null; //((JCLiteral)bProp.lhs).getValue();
                }
                
            }else{
                //log.error("jml.internal", "Unexpected node: " + p.getClass() + " found during replacement.");
            }
            
        }else if(p instanceof JCVariableDecl){
            JCVariableDecl pVarDecl = (JCVariableDecl)p;
            n =  pVarDecl.getName();
        }
        
        if(n==null){
            return null;
        }
        
        // it's possible it was a pre-state assignment
//        if(n.toString().startsWith("PRE_")){
//            // fix it up
//            n = n.subName(4, n.length());
//        }
//        
        return n;
        
    }
    
    public JCExpression with(){
        JCTree p = currentReplacement;
        
        if(isTmpVar){
            return (JCExpression)currentReplacement;
        }
        
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
        
        // this isn't supposed to happen. 
        log.error("jml.internal", "RHS Missing in Replacement");
        
        return null;
    }
    
    private ArrayList<JCTree> _subs; 
    private boolean isTmpVar = false;
    private Name tmpVar   = null;
    
    private boolean canReplace(JCIdent ident){
        try {
            boolean can =  canReplace((VarSymbol)ident.sym, ident.name);
            
            if(can && with()!=null && replace()!=null){
                return true;
            }
            
            return false;
            
        }catch(ClassCastException e){
            return false;
        }catch(Exception e){
            return false;
        }
    }
    
    
    private boolean nameAssignmentIsntRedundant(Name name, JCTree sub){
        
        if(sub instanceof JCBinary){
            JCBinary e = (JCBinary)sub;
            
            if(e.lhs.toString().equals(name.toString())){
                return false;
            }
            
        }   
        
        return true;
    }
    
    private boolean isCircular(Name name, JCTree sub){
        
        if(sub instanceof JCBinary){
            JCBinary e = (JCBinary)sub;
            
            if(e.rhs.toString().equals(name.toString())){
                return true;
            }
            
        }   
        
        return false;
    }
    
    
    
    // IF IT is an EQUALITY
    private boolean canReplace(VarSymbol sym, Name name){

        _subs = substitutionCache.getSubstitutionsAlongPath(sym, path);
        instance.currentReplacement = null;
        
        Collections.reverse(_subs);
        
        if(name.toString().startsWith("_JML__tmp")){
            isTmpVar = true;
            tmpVar = name;
        }else{
            isTmpVar = false;
            tmpVar = null;
        }
        
        for(JCTree sub : _subs){
            // tmp vars always match replacement (because they are synthetic)
            if(isTmpVar && nameAssignmentIsntRedundant(name, sub)){
                instance.currentReplacement = sub;
            }
            // if it's a JCExpression, make sure the LHS says something about the current ident.
            else{
                
                if(sub instanceof JCBinary){
                    JCBinary e = (JCBinary)sub;
                    
                    if(e.lhs.toString().equals(name.toString())){
                        instance.currentReplacement = sub;
                    }
                    
                }else if(sub instanceof JmlBBFieldAssignment){
                    JmlBBFieldAssignment fa = (JmlBBFieldAssignment)sub;
                    
                        JCExpression newField = fa.args.get(0);
                        JCExpression oldField = fa.args.get(1);
                        
                        if(name.toString().equals(newField.toString())){
                            
                            JCExpression ass = treeutils.makeBinary(
                                    0, 
                                    JCTree.Tag.EQ, 
                                    newField, 
                                    oldField
                                    );
            
                            
                            instance.currentReplacement = ass;                        
                    }
                    
                }
            }
            
        }
        
        if(_subs.size() > 0 && instance.currentReplacement !=null){
            
            
            if(isTmpVar){
                if(nameAssignmentIsntRedundant(name,instance.currentReplacement)==false){
                    isTmpVar = false;
                    tmpVar = null;
                }
                
                if(isCircular(name, instance.currentReplacement)){
                    return false;
                }
            }
            
            if(removeVersions==false){
                
                // if it's the case we are replacing 
                // a version of a variable only, don't do it.
                if(replace()!=null && with()!=null){
                    if(replace().toString().startsWith(with().toString())){
                        return false;
                    }
                }
                
            }
            
            return true;
        }
        
        return false;
    }
    
    
    
    private SubstitutionCache substitutionCache;
    private ArrayList<BasicBlock> path;
    private boolean removeVersions;

    public static JCExpression replace(SubstitutionCache substitutionCache, ArrayList<BasicBlock> path, JCTree in){
        return replace(substitutionCache, path, in, true);
    }
    public static JCExpression replace(SubstitutionCache substitutionCache, ArrayList<BasicBlock> path, JCTree in, boolean removeVersions){

        instance.substitutionCache = substitutionCache;
        instance.removeVersions    = removeVersions;
        instance.path              = path;
        /**
         * If "in" is a JCIdent, we probably have to directly
         * make a substitution
         */
        if(in instanceof JCIdent){

            if(instance.canReplace((JCIdent)in)){    
                return instance.with();
            }
            
        }else{
            instance.scan(in);
        }           
        
        
        return null; // this means we didn't change the underlying proposition (but we may have internally substituted some things)
    }
   
    /**
     * TODO: 
     * 
     * We need to make a case for expressions that get subed, eg:
     * 
     * 
     * _JMLtmp4  -> a > b
     * 
     * There is no equality that manages that. Maybe the functions we've written already take care 
     * of this detail but not totally sure. 
     */
    
    
    
    
}
