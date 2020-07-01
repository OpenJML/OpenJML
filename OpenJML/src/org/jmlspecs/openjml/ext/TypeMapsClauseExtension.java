package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.DOT;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LBRACKET;
import static com.sun.tools.javac.parser.Tokens.TokenKind.STAR;
import static org.jmlspecs.openjml.ext.MiscExtensions.intoKind;
import static org.jmlspecs.openjml.ext.TypeMapsClauseExtension.mapsClause;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeMapsClauseExtension extends JmlExtension {
    
    public static final String mapsID = "maps";
    
    public static final IJmlClauseKind mapsClause = new IJmlClauseKind.TypeClause(mapsID) {

        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseMaps parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            JmlTypeClauseMaps mapsClause = parseMaps(pp, mods, null);
            return mapsClause;
        }
        
        /** Parses a maps clause */
        public JmlTypeClauseMaps parseMaps(int pos, JCModifiers mods,
                ListBuffer<JCTree> list) {
            if (!parser.isNone(mods))
                parser.jmlerror(mods.getStartPosition(), mods.getPreferredPosition(),
                        parser.getEndPos(mods), "jml.no.mods.allowed",
                        mapsClause.name());
            parser.nextToken(); // skip over the maps token
            JCExpression e = parseMapsTarget();
            ListBuffer<JmlGroupName> glist;
            if (parser.jmlTokenClauseKind() != intoKind) {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.expected",
                        "an \\into token here, or the maps target is ill-formed");
                glist = new ListBuffer<JmlGroupName>();
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
                glist = parser.parseGroupNameList();
                if (parser.token().kind != TokenKind.SEMI) {
                    parser.jmlerror(parser.pos(), parser.endPos(), "jml.bad.construct",
                            "maps clause");
                    parser.skipThroughSemi();
                } else {
                    parser.nextToken();
                }
            }
            return toP(parser.jmlF.at(pos).JmlTypeClauseMaps(e, glist.toList()));
        }

        /** Parses the target portion (before the \\into) of a maps clause */
        public JCExpression parseMapsTarget() {
            int p = parser.pos();
            if (parser.token().kind != IDENTIFIER) {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.expected", "an identifier");
                parser.skipThroughSemi();
                return toP(parser.jmlF.at(p).Erroneous());
            }
            Name n = parser.ident();
            JCExpression result = parser.to(parser.jmlF.at(p).Ident(n));
            if (parser.token().kind == LBRACKET) {
                result = parser.parseArrayRangeExpr(result, false);
            }
            if (parser.token().kind == DOT) {
                parser.nextToken();
                if (parser.token().kind == STAR) {
                    parser.nextToken();
                    n = null;
                } else if (parser.token().kind == IDENTIFIER) {
                    n = parser.ident();
                } else {
                    parser.jmlerror(parser.pos(), parser.endPos(), "jml.ident.or.star.after.dot");
                    parser.skipThroughSemi();
                    return toP(parser.jmlF.at(p).Erroneous());
                }
                // Caution: Java will not expect n to be null
                // It is null to denote a wildcard selector
                result = parser.to(parser.jmlF.at(p).Select(result, n));
            } else if (!(result instanceof JmlStoreRefArrayRange)) {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.expected",
                        "a . to select a field");
                parser.skipThroughSemi();
                return parser.to(parser.jmlF.at(p).Erroneous());
            }
            return result;
        }

        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
