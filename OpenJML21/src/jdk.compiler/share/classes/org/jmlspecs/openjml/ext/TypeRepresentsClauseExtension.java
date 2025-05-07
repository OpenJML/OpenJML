package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.EQ;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class TypeRepresentsClauseExtension extends JmlExtension {

    public static final String representsID = "represents";
    //public static final String capturedID = "captured";
        
    public static final IJmlClauseKind representsClause = new IJmlClauseKind.TypeClause(representsID) {
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseRepresents parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            parser.nextToken();
            var n = parser.parseOptionalName();
            boolean strict = JmlOption.langJML.equals(JmlOption.value(parser.context, JmlOption.LANG));
            JCExpression id = parser.parseStoreRef(strict);
            boolean suchThat;
            JCExpression e;
            if (parser.token().kind == EQ) {
                suchThat = false;
                parser.nextToken();
                e = parser.parseExpression();
            } else if (parser.jmlTokenClauseKind() == org.jmlspecs.openjml.ext.Operators.leftarrowKind) {
                if (utils.isDeprecationSet() && ! strict) {
                    utils.warning(parser.pos(), "jml.deprecated.left.arrow.in.represents");
                }
                suchThat = false;
                parser.nextToken();
                e = parser.parseExpression();
            } else if (parser.jmlTokenClauseKind() == MiscExtensions.suchthatKind) {
                suchThat = true;
                parser.nextToken();
                e = parser.parseExpression();
            } else {
                if (id != null) error(parser.pos(), parser.endPos(), "jml.bad.represents.token");
                e = null;
                parser.skipToSemi();
                suchThat = false;
            }
            Maker M = parser.maker().at(pp);
            if (e == null) { // skip
                e = parser.maker().Erroneous();
            }
            if (mods == null) mods = M.Modifiers(0);
            JmlTypeClauseRepresents tcl = parser.to(M.JmlTypeClauseRepresents(
                    mods, id, suchThat, e));
            wrapup(tcl, clauseType, true, true);
            tcl.name = n;
            return tcl;
            }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    
    
//    public static final IJmlClauseKind capturedClause = new IJmlClauseKind.TypeClause(capturedID) {
//        public boolean oldNoLabelAllowed() { return false; }
//        public boolean preOrOldWithLabelAllowed() { return false; }
//        
//        public 
//        JmlVariableDecl parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
//            init(parser);
//            int pp = parser.pos();
//            parser.nextToken();
//            Name className = Names.instance(context).fromString("");
//            List<JCTree> decls = parser.classOrInterfaceBodyDeclaration(className,false);
//            if (decls.size() != 1) {
//                log.error(pp,"jml.message", "Expected exactly one declaration");
//                if (decls.size() == 0) return null;
//            }
//            JCTree t = decls.get(0);
//            if (!(t instanceof JmlVariableDecl)) {
//                log.error(pp, "jml.message", "Expected a field declaration");
//                return null;
//            }
//            JmlVariableDecl vd = (JmlVariableDecl)t;
//            JCAnnotation a = parser.tokenToAnnotationAST("Ghost", pp, pp);
//            vd.mods.annotations = vd.mods.annotations.append(a);
//            a = parser.tokenToAnnotationAST("Captured", pp, pp);
//            vd.mods.annotations = vd.mods.annotations.append(a);
//            return vd;
//        }
//        
//        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
//            // TODO Auto-generated method stub
//            return null;
//        }
//    };
   
}
