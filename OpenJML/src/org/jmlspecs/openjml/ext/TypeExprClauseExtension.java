package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;
import static com.sun.tools.javac.parser.Tokens.TokenKind.STAR;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SUPER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.THIS;
import static com.sun.tools.javac.parser.Tokens.TokenKind.BANG;
import static com.sun.tools.javac.parser.Tokens.TokenKind.COMMA;
import static com.sun.tools.javac.parser.Tokens.TokenKind.DOT;
import static com.sun.tools.javac.parser.Tokens.TokenKind.FOR;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LPAREN;
import static com.sun.tools.javac.parser.Tokens.TokenKind.NEW;
import static com.sun.tools.javac.parser.Tokens.TokenKind.RPAREN;
import static org.jmlspecs.openjml.ext.MiscExtensions.everythingID;
import static org.jmlspecs.openjml.ext.MiscExtensions.nothingID;
import static org.jmlspecs.openjml.ext.MiscExtensions.notspecifiedID;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodSig;
import org.jmlspecs.openjml.JmlTree.JmlTypeClause;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeExprClauseExtension extends JmlExtension {

    public static final String invariantID = "invariant";
    public static final String constraintID = "constraint";
    public static final String axiomID = "axiom";
    public static final String initiallyID = "initially";
    
    public static final IJmlClauseKind invariantClause = new TypeClause(invariantID);
    
    public static final IJmlClauseKind constraintClause = new TypeClause(constraintID);
    
    public static final IJmlClauseKind axiomClause = new TypeClause(axiomID);
    
    public static final IJmlClauseKind initiallyClause = new TypeClause(initiallyID);
    
    public static class TypeClause extends IJmlClauseKind.TypeClause {
        public TypeClause(String keyword) { super(keyword); }

        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClause parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            
            if (clauseType == constraintClause) {
                JmlTree.JmlTypeClauseConstraint tcl = parseConstraint(mods);
                tcl.source = log.currentSourceFile();
                return tcl;
            } else {
                parser.nextToken();
                JCExpression e = parser.parseExpression();
                if (parser.token().kind != SEMI) {
                    parser.jmlerror(parser.pos(), parser.endPos(), "jml.bad.construct",
                            keyword + " declaration");
                    parser.skipThroughSemi();
                } else {
                    parser.nextToken();
                }
                Maker M = parser.maker().at(pp);
                if (mods == null) mods = M.Modifiers(0);
                JmlTypeClauseExpr tcl = parser.to(M.JmlTypeClauseExpr(mods, keyword, clauseType, e));
                tcl.source = log.currentSourceFile();
                return tcl;
            }
        }
        
        /** Parses a constraint clause */
        public JmlTypeClauseConstraint parseConstraint(JCModifiers mods) {
            int pos = parser.pos();
            parser.nextToken();
            JCExpression e = parser.parseExpression();
            List<JmlMethodSig> sigs = null;
            boolean notlist = false;
            if (parser.token().kind == FOR) {
                parser.nextToken();
                if (parser.token().kind == BANG) {
                    notlist = true;
                    parser.nextToken();
                }
                if (parser.tokenIsId(everythingID,notspecifiedID)) {
                    parser.nextToken();
                    // This is the default, so we just leave sigs null
                    if (notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                    notlist = false;
                } else if (parser.tokenIsId(nothingID)) {
                    parser.nextToken();
                    if (!notlist) sigs = new ListBuffer<JmlMethodSig>().toList();
                    notlist = false;
                    // Here we just have an empty list
                } else {
                    sigs = parseMethodNameList();
                }
            }
            if (mods == null) mods = parser.jmlF.at(pos).Modifiers(0);
            JmlTypeClauseConstraint tcl = parser.to(parser.jmlF.at(pos).JmlTypeClauseConstraint(
                    mods, e, sigs));
            tcl.notlist = notlist;
            tcl.source = log.currentSourceFile();
            if (parser.token().kind != SEMI) {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.bad.construct",
                        "constraint declaration");
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
            }
            return tcl;
        }

        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
