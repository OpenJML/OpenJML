package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseInvariants;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Kinds.KindSelector;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.comp.Attr.ResultInfo;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class MethodExprListClauseExtensions extends JmlExtension {
    
    public static final String invariantsID = "invariants";
        
    public static final IJmlClauseKind invariantsClauseKind = new IJmlClauseKind.MethodSpecClauseKind(invariantsID) {
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public 
        JmlMethodClauseInvariants parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            if (mods != null) {
                error(mods.pos(), "jml.message", "a " + keyword + " clause may not have modifiers");
                return null;
            }
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            parser.nextToken();
            var n = parser.parseOptionalName();
            var exprs = parser.parseExpressionList();
            JmlMethodClauseInvariants cl = parser.maker().at(pp).JmlMethodClauseInvariants(exprs);
            if (cl != null) cl.name = n;
            wrapup(cl, clauseType, true, true);
            return cl;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree tree, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            JmlMethodClauseInvariants cl = (JmlMethodClauseInvariants)tree;
            for (var e: cl.expressions) attr.attribTree(e, env, attr.new ResultInfo(KindSelector.VAL_TYP, Type.noType));
            return null;
        }
        
};
    
}
