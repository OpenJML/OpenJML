package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.EQ;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IF;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeRepresentsClauseExtension extends JmlExtension.TypeClause {

    public static final String representsID = "represents";
    

    @Override
    public IJmlClauseKind[]  clauseTypesA() { return clauseTypes(); }
    public static IJmlClauseKind[] clauseTypes() { return new IJmlClauseKind[]{
            representsClause}; }
    
    public static final IJmlClauseKind representsClause = new IJmlClauseKind.TypeClause() {
        public String name() { return representsID; }
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseRepresents parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            scanner.setJmlKeyword(false);
            parser.nextToken();
            JCExpression id = parser.parseStoreRef(true);
            boolean suchThat;
            JCExpression e;
            if (parser.token().kind == EQ) {
                suchThat = false;
                parser.nextToken();
                e = parser.parseExpression();
            } else if (parser.jmlTokenKind() == JmlTokenKind.LEFT_ARROW) {
                if (parser.isDeprecationSet() || JmlOption.langJML.equals(JmlOption.value(context, JmlOption.LANG))) {
                    log.warning(parser.pos(), "jml.deprecated.left.arrow.in.represents");
                }
                suchThat = false;
                parser.nextToken();
                e = parser.parseExpression();
            } else if (parser.jmlTokenKind() == JmlTokenKind.BSSUCHTHAT) {
                suchThat = true;
                parser.nextToken();
                e = parser.parseExpression();
            } else {
                if (id != null) error(parser.pos(), parser.endPos(), "jml.bad.represents.token");
                e = null;
                parser.skipToSemi();
                suchThat = false;
            }
            scanner.setJmlKeyword(true);
            if (e == null) { // skip
                e = jmlF.Erroneous();
            } else if (parser.token().kind != SEMI) {
                parser.jmlerror(parser.pos(), parser.endPos(),
                        "jml.invalid.expression.or.missing.semi");
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
            }
//            if (id == null) return null;
            if (mods == null) mods = jmlF.at(pp).Modifiers(0);
            JmlTypeClauseRepresents tcl = parser.to(jmlF.at(pp).JmlTypeClauseRepresents(
                    mods, id, suchThat, e));
            tcl.source = log.currentSourceFile();
            return tcl;
            }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
