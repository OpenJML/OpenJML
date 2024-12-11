package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.ext.FunctionLikeExpressions.*;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;

public class LocsetExtensions extends JmlExtension {

    public static final String unionID = "\\set_union";
    public static final IJmlClauseKind unionKind = new AnyArgExpression(unionID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            var t = (JmlMethodInvocation)tree;
            super.typecheck(attr, tree, localEnv);
            //System.out.println("UNION " + t);
            Type locsetType = JmlPrimitiveTypes.locsetTypeKind.getType(attr.context);
            for (JCExpression e: ((JmlMethodInvocation)tree).args) {
                //System.out.println("  UNION ARG " + e + " " + e.type);
                if (!(attr.jmltypes.isSameType(e.type, locsetType))) {
                    utils.error(e.pos, "jml.message", "The arguments of \\set_union must have type locset, not " + e.type);
                }
            }
            return locsetType;
        }
    };

    public static final String subsetID = "\\subset";
    public static final IJmlClauseKind subsetKind = new AnyArgBooleanExpression(subsetID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            var t = ((JmlMethodInvocation)tree);
            super.typecheck(attr, tree, localEnv);
            Type locsetType = JmlPrimitiveTypes.locsetTypeKind.getType(attr.context);
            for (JCExpression e: t.args) {
                if (!(attr.jmltypes.isSameType(e.type, locsetType))) {
                    utils.error(e.pos, "jml.message", "The arguments of \\subset must have type locset, not " + e.type);
                }
            }
            checkNumberArgs(parser, t, n->(n==2), "jml.message", "A \\subset expression must have two arguments, not " + t.args.size());
            return attr.syms.booleanType;
        }
    };

    public static final String disjointID = "\\disjoint";
    public static final IJmlClauseKind disjointKind = new AnyArgBooleanExpression(disjointID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> localEnv) {
            super.typecheck(attr, tree, localEnv);
            Type locsetType = JmlPrimitiveTypes.locsetTypeKind.getType(attr.context);
            var t = ((JmlMethodInvocation)tree);
            for (JCExpression e: t.args) {
                if (!(attr.jmltypes.isSameType(e.type, locsetType))) {
                    utils.error(e.pos, "jml.message", "The arguments of \\disjoint must have type locset, not " + e.type);
                }
            }
            checkNumberArgs(parser, t, n->(n==2), "jml.message", "A \\disjoint expression must have two arguments, not " + t.args.size());
            return attr.syms.booleanType;
        }
    };

}
