package org.jmlspecs.openjml.strongarm.tree.analysis;

import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseStoreRef;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.strongarm.tree.And;
import org.jmlspecs.openjml.strongarm.tree.Or;
import org.jmlspecs.openjml.strongarm.tree.Prop;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.List;

public class SpecToExpression {

    public static JCExpression convertTree(JmlMethodSpecs spec,
            JmlTreeUtils treeutils) {

        Prop<JCExpression> tree = convert(spec.cases, treeutils);

        return tree.toTree(treeutils);
    }

    public static Prop<JCExpression> convert(List<JmlSpecificationCase> cases,
            JmlTreeUtils treeutils) {


        if(cases.tail==null || cases.tail.head==null){
            return convert(cases.head, treeutils);
        }
        
        return Or.of(convert(cases.head, treeutils),
                convert(cases.tail, treeutils));
    }

    public static Prop<JCExpression> convert(JmlSpecificationCase theCase,
            JmlTreeUtils treeutils) {

        if (!(theCase.clauses.head instanceof JmlMethodClauseGroup)
                && theCase.clauses.size() == 0) {
            return convert(theCase.clauses.head, treeutils);
        }

        Prop<JCExpression> p = null;

        for (List<JmlMethodClause> clauses = theCase.clauses; clauses
                .nonEmpty(); clauses = clauses.tail) {
            // TODO -- here we should skip clauses that don't produce logical
            // conditions.
            if (p == null) {
                p = convert(clauses.head, treeutils);
            } else {
                p = And.of(p, convert(clauses.head, treeutils));
            }
        }

        return p;
    }

    public static Prop<JCExpression> convertExprs(List<JCExpression> exprs, JmlTreeUtils treeutils) {

        Prop<JCExpression> p = null;

        for (List<JCExpression> clauses = exprs; exprs.nonEmpty()
                ; clauses = clauses.tail) {
            if (p == null) {
                p = new Prop<JCExpression>(clauses.head, null);
            } else {
                p = And.of(p, new Prop<JCExpression>(clauses.head, null));
            }
        }

        return p;
    }

    public static Prop<JCExpression> convert(JmlMethodClause expr,
            JmlTreeUtils treeutils) {

        if (1 == 1) {
            System.out.println("test");
        }

        if (expr instanceof JmlMethodClauseExpr) {
            JmlMethodClauseExpr e = (JmlMethodClauseExpr) expr;
            return new Prop<JCExpression>(e.expression, null);
        }

        else if (expr instanceof JmlMethodClauseGroup) {
            JmlMethodClauseGroup group = (JmlMethodClauseGroup) expr;
            return convert(group.cases, treeutils);
        }

        else if (expr instanceof JmlMethodClauseStoreRef) {
            JmlMethodClauseStoreRef ref = (JmlMethodClauseStoreRef) expr;

            return convertExprs(ref.list, treeutils);
        }

        else {
            throw new IllegalArgumentException(
                    "Not implemented for :" + expr.getClass());
        }
    }

}
