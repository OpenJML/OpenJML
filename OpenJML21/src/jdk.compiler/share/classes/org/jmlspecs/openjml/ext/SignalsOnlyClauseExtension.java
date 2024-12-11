package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.COMMA;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import static org.jmlspecs.openjml.ext.MiscExtensions.*;
import static org.jmlspecs.openjml.ext.JmlPrimitiveTypes.*;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseSignalsOnly;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCErroneous;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

public class SignalsOnlyClauseExtension extends JmlExtension {

    public static final String signalsOnlyID = "signals_only";
    
    public static final IJmlClauseKind signalsOnlyClauseKind = new IJmlClauseKind.MethodSpecClauseKind(signalsOnlyID) {
        @Override
        public boolean oldNoLabelAllowed() { return false; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        @Override
        public JmlMethodClauseSignalsOnly parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            parser.nextToken();

            IJmlClauseKind jt = this;
            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();

            if (parser.jmlTokenClauseKind() == nothingKind) {
                parser.nextToken();
                if (parser.token().kind != SEMI) {
                    parser.syntaxError(parser.pos(), null, "jml.expected.semi.after.nothing");
                    parser.skipThroughSemi();
                } else {
                    parser.nextToken();
                }
            } else if (parser.token().kind == SEMI) {
                parser.syntaxError(parser.pos(), null, "jml.use.nothing", keyword);
                parser.nextToken();
            } else {
                while (true) {
                	// parseType allows trailing [] and type annotations, which is overly general
                	// and confuses error reporting and recovery
                	JCExpression typ = parser.parseType(false);
                    list.append(typ);
                    TokenKind tk = parser.token().kind;
                    if (tk == SEMI) {
                        parser.nextToken();
                        break;
                    } else if (tk == COMMA) {
                        parser.nextToken();
                        continue;
                    } else if (!parser.getScanner().jml() || parser.isEndJml()) {  // FIXME - change to get JML status from parser
                        parser.syntaxError(parser.pos(), null, "jml.missing.semi");
                        parser.skipThroughEndOfJML();
                        break;
                    } else if (typ instanceof JCErroneous) {
                        parser.skipThroughSemi();
                        break;
                    } else {
                        parser.syntaxError(parser.pos(), null, "jml.missing.comma");
                        continue;
                    }
                }
            }
            // FIXME - use wrapup
            return toP(parser.maker().at(pp).JmlMethodClauseSignalsOnly(keyword, clauseType, list.toList()));
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    
    static {
        synonym("throws_only", signalsOnlyClauseKind);
    }
}
