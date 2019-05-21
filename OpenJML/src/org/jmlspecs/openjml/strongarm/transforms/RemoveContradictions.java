package org.jmlspecs.openjml.strongarm.transforms;

import java.util.HashSet;
import java.util.Set;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.translators.FeasibilityCheckerSMT;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCParens;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class RemoveContradictions extends JmlTreeScanner {

    public JCTree                      currentReplacement;

    public static RemoveContradictions instance;

    final protected Log                log;

    final protected Utils              utils;

    final protected JmlTreeUtils       treeutils;

    final protected JmlTree.Maker      M;

    final protected Context            context;

    final Symtab                       syms;

    public static boolean              inferdebug = false;

    public static boolean              verbose    = false;

    public RemoveContradictions(Context context) {

        this.context = context;
        this.log = Log.instance(context);
        this.utils = Utils.instance(context);
        this.treeutils = JmlTreeUtils.instance(context);
        this.M = JmlTree.Maker.instance(context);
        this.syms = Symtab.instance(context);

        this.inferdebug = JmlOption.isOption(context, org.jmlspecs.openjml.ext.OptionsInfer.INFER_DEBUG);

        this.verbose = inferdebug || JmlOption.isOption(context, "-verbose") // The
                                                                             // Java
                                                                             // verbose
                                                                             // option
                || utils.jmlverbose >= Utils.JMLVERBOSE;

    }

    public static void cache(Context context) {
        if (instance == null) {
            instance = new RemoveContradictions(context);
        }
    }

    protected boolean isFeasible(List<JmlMethodClause> clauses) {

        Set<String> maybeUnaryNot = new HashSet<String>();
        Set<String> maybeUnary = new HashSet<String>();
        
        Set<String> maybeNE = new HashSet<String>();
        Set<String> maybeEQ = new HashSet<String>();
        
        for (JmlMethodClause c : clauses) {
            
            if(c instanceof JmlMethodClauseGroup){
                visitJmlMethodClauseGroup((JmlMethodClauseGroup)c);
            }
            
            if (c instanceof JmlMethodClauseExpr) {
                JmlMethodClauseExpr expr = (JmlMethodClauseExpr) c;
                if (expr.expression.toString().equals("!true")
                        || expr.expression.toString().equals("!(true)")) {
                    return false;
                }
                
                JCExpression e = expr.expression;

                // put it in the right bucket
                if(e.toString().startsWith("!")){
                    String s = e.toString();
                    maybeUnaryNot.add(s);
                }else{
                    String s = e.toString();
                    maybeUnary.add(s);
                }
                
                // check the OTHER list.
                if(e.toString().startsWith("!")){
                    String s = e.toString();
                    s = s.substring(2).substring(0, s.length()-4) + ";";
                    
                    if(maybeUnary.contains(s)){
                        return false;
                    }
                }else{
                    String s = e.toString();
                    
                    s = "!(" + s.substring(0, s.length()-1) + ");";

                    if(maybeUnaryNot.contains(s)){
                        return false;
                    }
                    
                }
                
                
                String s = expr.toString();
                              
                
                if(s.contains("!=") && maybeEQ.contains(s.replaceAll("!=", "=="))){
                    return false;
                }else{
                    maybeNE.add(s);
                }
                
                if(s.contains("==") && maybeNE.contains(s.replaceAll("==", "!="))){
                    return false;
                }else{
                    maybeEQ.add(s);
                }                
            }
        }

        return true;

    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {

        Set<JmlMethodClauseExpr> props = null;

        List<JmlSpecificationCase> replacedCases = null;

        if(tree!=null && tree.cases!=null && tree.cases.head!=null && tree.cases.head.clauses!=null && tree.cases.head.clauses.head!=null){
        if (tree.cases.head.clauses.head instanceof JmlMethodClauseExpr) {

            for (List<JmlSpecificationCase> cases = tree.cases; cases.nonEmpty(); cases = cases.tail) {

                if (isFeasible(cases.head.clauses)) {
                    
                    if (replacedCases == null) {
                        replacedCases = List.of(cases.head);
                    } else {
                        replacedCases = replacedCases.append(cases.head);
                    }
                }

            }
            if (replacedCases == null) {
                replacedCases = List.nil();
            }
            tree.cases = replacedCases;
        } else {
            super.visitJmlMethodClauseGroup(tree);
        }
        }else{
            super.visitJmlMethodClauseGroup(tree);            
        }
    }

    /**
     * Here we translate down to SMT conditions to check if the preconditions in
     * parent blocks imply the conditions in lower blocks.
     * 
     * We need to do this sort of thing in the case that simple rewriting isn't
     * enough to dispatch duplicate precondtions.
     */
    public void filterBlock(JmlSpecificationCase block) {

        // we keep repeating this
        /*
         * List<JmlMethodClause> replacedClauses = null;
         * Set<JmlMethodClauseExpr> filterSet = getFilters();
         * 
         * for(List<JmlMethodClause> clauses = block.clauses;
         * clauses.nonEmpty(); clauses = clauses.tail){
         * 
         * // Only include the preconditions not implied by previous
         * preconditions // note that this is a path sensitive analysis -- the
         * entire context of the current method's smt translation // will be
         * taken into account. For example, while a > 0 => a == 3 mahy not be
         * generally true, it may be true // for the given method. A human would
         * see this and not write it in the preconditions, thus we aim to //
         * filter this sort of thing out. if(!(clauses.head instanceof
         * JmlMethodClauseExpr) || clauses.head.token != JmlToken.REQUIRES ||
         * new SubstitutionEQProverSMT(context).checkImplies(filterSet,
         * (JmlMethodClauseExpr)clauses.head, currentMethod)==false){
         * if(replacedClauses == null){ replacedClauses = List.of(clauses.head);
         * }else{ replacedClauses = replacedClauses.append(clauses.head); }
         * 
         * if (verbose) { log.noticeWriter.println("Kept EXPR: " +
         * clauses.head); }
         * 
         * }else{ if (verbose) { log.noticeWriter.println("Filtering EXPR: " +
         * clauses.head); } } }
         * 
         * block.clauses = replacedClauses;
         */
    }

    public static void simplify(JCTree node) {
        instance.scan(node);
    }
}