package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.COMMA;
import static com.sun.tools.javac.parser.Tokens.TokenKind.DOT;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.LBRACKET;
import static com.sun.tools.javac.parser.Tokens.TokenKind.STAR;
import static org.jmlspecs.openjml.ext.MiscExtensions.intoKind;

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
                utils.error(mods.getStartPosition(), mods.getPreferredPosition(),
                        parser.getEndPos(mods), "jml.no.mods.allowed",
                        mapsClause.keyword());
            parser.nextToken(); // skip over the maps token
            ListBuffer<JCExpression> exprs = new ListBuffer<>();
            JCExpression e = parser.parseStoreRef(false);
            if (e != null) exprs.add(e);
            while (parser.token().kind == COMMA) {
                parser.nextToken();
                e = parser.parseStoreRef(false);
                if (e != null) exprs.add(e);
            }
            ListBuffer<JmlGroupName> glist;
            if (parser.jmlTokenClauseKind() != intoKind) {
                utils.error(parser.pos(), parser.endPos(), "jml.expected",
                        "an \\into token here, or the maps target is ill-formed");
                glist = new ListBuffer<JmlGroupName>();
                parser.skipToSemi();
            } else {
                parser.nextToken();
                glist = parser.parseGroupNameList();
            }
            var t = toP(parser.jmlF.at(pos).JmlTypeClauseMaps(exprs.toList(), glist.toList()));
            wrapup(t, TypeInClauseExtension.inClause, true, true); // FIXME - make a proper mapsClauseKind
            return t;
        }

//        /** Parses the target portion (before the \\into) of a maps clause */
//        public JCExpression parseMapsTarget() {
//            int p = parser.pos();
//        	JCExpression target = parser.parseExpression();
//        	if (target instanceof JCTree.JCIdent) return target;
//        	if (target instanceof JCTree.JCArrayAccess) return target;
//        	if (target instanceof JCTree.JCFieldAccess) return target;
//            utils.error(parser.pos(), parser.endPos(), "jml.expected", "an identifier, field access or array access");
//            parser.skipThroughSemi();
//            return toP(parser.jmlF.at(p).Erroneous());
//        }

        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
