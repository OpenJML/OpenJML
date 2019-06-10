package org.jmlspecs.openjml.strongarm.transforms;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.strongarm.AnalysisTypes;
import org.jmlspecs.openjml.strongarm.AnalysisTypes.AnalysisType;
import org.jmlspecs.openjml.vistors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.Utils;
import static org.jmlspecs.openjml.ext.MethodExprClauseExtensions.*;
import static org.jmlspecs.openjml.ext.RecommendsClause.*;
import static org.jmlspecs.openjml.ext.AssignableClauseExtension.*;


import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

public class CleanupPrestateAssignable extends JmlTreeScanner {

    final protected Log                     log;

    final protected Utils                   utils;

    final protected JmlTreeUtils            treeutils;

    final protected JmlTree.Maker           M;

    final protected Context                 context;

    final Symtab                            syms;

    public static boolean                   inferdebug = false;

    public static boolean                   verbose    = false;

    public static CleanupPrestateAssignable instance;

    public CleanupPrestateAssignable(Context context) {

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
            instance = new CleanupPrestateAssignable(context);
        }
    }

    /**
     * Locals removed if they are a formal and primative OR if they are just
     * local. Fields stay.
     */
    private boolean isAnAcceptableOperator(Symbol s) {
        String str = s.toString();

        if (str.contains(">") || str.contains("<") || str.contains("==")) {
            return true;
        }

        return false;

    }

    public boolean shouldRemove(JmlMethodClause clause) {

        if (clause.toString().contains(Strings.prePrefix)) {
            return true;
        }

//        if(clause.toString().contains("__")) {
//            return true;
//        }
        
        if (clause instanceof JmlMethodClauseExpr) {

            JmlMethodClauseExpr mExpr = (JmlMethodClauseExpr) clause;

            if (mExpr.clauseKind == ensuresClauseKind
                    && mExpr.expression instanceof JCBinary) {
                JCBinary b = (JCBinary) mExpr.expression;

                if (b.lhs.toString().equals("\\result")
                        && isAnAcceptableOperator(b.operator) == false) {
                    return true;
                }
            }
            
//            if (mExpr.token == JmlTokenKind.REQUIRES) {
//                if (mExpr.toString().contains("\\old")) {
//                    return true;
//                }
//            }

        }

        if (clause instanceof JmlMethodClauseStoreRef) {
            JmlMethodClauseStoreRef mExpr = (JmlMethodClauseStoreRef) clause;

            if (mExpr.clauseKind == assignableClauseKind
                    && mExpr.toString().startsWith("assignable \\result.")) {
                return true;
            }

            if (mExpr.clauseKind == assignableClauseKind
                    && mExpr.toString().startsWith("assignable \\result")) {
                return true;
            }
            if (AnalysisTypes.enabled(context, AnalysisType.TAUTOLOGIES)) {
                if (mExpr.clauseKind == assignableClauseKind
                        && mExpr.toString().startsWith("assignable true")) {
                    return true;
                }
            }

            if (mExpr.clauseKind == assignableClauseKind && mExpr.toString()
                    .startsWith("assignable " + Strings.newArrayVarString)) {
                return true;
            }

            if (mExpr.clauseKind == assignableClauseKind && mExpr.toString()
                    .startsWith("assignable " + Strings.newObjectVarString)) {
                return true;
            }

        }
        if (clause instanceof JmlMethodClauseExpr
                || clause instanceof JmlMethodClauseStoreRef) {
            // filter any junk here
            if ((clause instanceof JmlMethodClauseExpr
                    || clause instanceof JmlMethodClauseStoreRef)
                    && (clause.toString().contains(Strings.allocName) || clause
                            .toString().contains(Strings.isAllocName))) {
                return true;
            }

            if (AnalysisTypes.enabled(context, AnalysisType.TAUTOLOGIES)) {
                if (clause instanceof JmlMethodClauseExpr
                        && (((JmlMethodClauseExpr) clause).expression.toString()
                                .equals("true"))) {
                    return true;
                }
            }

            if (AnalysisTypes.enabled(context, AnalysisType.UNSAT)) {
                if (clause instanceof JmlMethodClauseExpr
                        && (((JmlMethodClauseExpr) clause).expression.toString()
                                .contains("!true"))) {
                    return true;
                }
            }

            if (AnalysisTypes.enabled(context, AnalysisType.TAUTOLOGIES)) {
                if (clause instanceof JmlMethodClauseExpr
                        && (((JmlMethodClauseExpr) clause).expression.toString()
                                .equals("true == true"))) {
                    return true;
                }

                if (clause instanceof JmlMethodClauseExpr
                        && (((JmlMethodClauseExpr) clause).expression.toString()
                                .contains("null == null"))) {
                    return true;
                }

                if (clause instanceof JmlMethodClauseExpr
                        && (((JmlMethodClauseExpr) clause).expression.toString()
                                .contains("0 == 0"))) {
                    return true;
                }
            }
            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("java_lang_CharSequence"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("/*mising*/"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("_heap__"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("java_lang_reflect"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("_JML_iterator"))) {
                return true;
            }
            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("T[]"))) {
                return true;
            }
            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("<captured wildcard>"))) {
                return true;
            }

            if (AnalysisTypes.enabled(context, AnalysisType.TAUTOLOGIES)) {
                if (clause instanceof JmlMethodClauseExpr
                        && (((JmlMethodClauseExpr) clause).expression.toString()
                                .contains("0 <= 0"))) {
                    return true;
                }
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("null."))) {
                return true;
            }

            // if(clause instanceof JmlMethodClauseExpr &&
            // (((JmlMethodClauseExpr)clause).expression.toString().contains("0
            // >= 0"))){
            // return true;
            // }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("\\type"))) {
                return true;
            }

            if (clause.toString().contains(Strings.tmpVarString)) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains(Strings.newArrayVarString))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("_switchExpression"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("> (0 > 0)"))) {
                return true;
            }

            // weird edge case
            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains(
                                    "result - (context.pos - context.readPos)"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("null[0]"))) {
                return true;
            }
            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("colSize == this.values"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .startsWith("this != null"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("(E)"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("result >"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("colSize =="))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("bigint)this.in.availableBytes;"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("bigint)"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("data == availableBytes"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && clause.clauseKind == requiresClauseKind
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("\\result"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && clause.clauseKind == ensuresClauseKind
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("this.overallStart == time"))) {
                return true;
            }

            if (clause instanceof JmlMethodClauseExpr
                    && clause.clauseKind == ensuresClauseKind
                    && (((JmlMethodClauseExpr) clause).expression.toString()
                            .contains("colSize == children.content.theSize"))) {
                return true;
            }

            if (clause.toString().contains(Strings.newObjectVarString)) {
                return true;
            }

            if (clause.toString().contains("\"null\" != null;")
                    || clause.toString().contains("\"\" != null;")) {
                return true;
            }
        }

        return false;
    }

    public void filterBlock(JmlSpecificationCase block) {

        List<JmlMethodClause> replacedClauses = null;

        if (block.clauses == null) {
            return;
        }

        for (List<JmlMethodClause> clauses = block.clauses; clauses
                .nonEmpty(); clauses = clauses.tail) {

            if (shouldRemove(clauses.head) == false) {
                if (replacedClauses == null) {
                    replacedClauses = List.of(clauses.head);
                } else {
                    replacedClauses = replacedClauses.append(clauses.head);
                }
            }
        }

        block.clauses = replacedClauses;
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {

        filterBlock(tree);

        super.visitJmlSpecificationCase(tree);
    }

    public void scan(JCTree node) {
        super.scan(node);
    }

    public static void simplify(JCTree node) {
        instance.scan(node);
    }

}
