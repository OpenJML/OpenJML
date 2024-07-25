package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.ListBuffer;

public class StatementLocationsExtension extends JmlExtension {
    
    public static final String havocID = "havoc";
    public static final String loopwritesID = "loop_writes";
    
    public static final IJmlClauseKind havocStatement = new LocationSetStatementType(havocID);
    
    public static final IJmlClauseKind loopwritesStatement = new LocationSetStatementType(loopwritesID);
    
    static {
        synonym("loop_assignable",loopwritesStatement);
        synonym("loop_assigns",loopwritesStatement);
        synonym("loop_modifies",loopwritesStatement);
    }
    
    public static class LocationSetStatementType extends IJmlClauseKind.Statement {
        public LocationSetStatementType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            parser.nextToken(); // skipping keyword
            var n = parser.parseOptionalName();

            ListBuffer<JCExpression> list = new ListBuffer<JCExpression>();
            if (parser.token().kind == SEMI) {
                parser.syntaxError(parser.pos(), null, "jml.use.nothing.assignable"); // FIXME - fix to use keyword
//                parser.nextToken(); // skip over the SEMI
            } else {
                list = parser.parseStoreRefListOrKeyword(false);
//                if (parser.token().kind == SEMI) {
//                    // OK, go on
//                } else if (parser.jmlTokenKind() == ENDJMLCOMMENT) {
//                    parser.syntaxError(parser.pos(), null, "jml.missing.semi");
//                }
                if (list.isEmpty()) {
                    parser.syntaxError(parser.pos(), null, "jml.use.nothing.assignable");
                }
//                if (parser.token().kind != SEMI) {
//                    // error already reported
//                    parser.skipThroughSemi();
//                } else {
//                    parser.nextToken();
//                }
            }
            // FIXME - refactor to use wrapup
            var st = keyword.equals(havocID) ? (parser.maker().at(pp).JmlHavocStatement(list.toList()))
            					: parser.maker().at(pp).JmlStatementLoopModifies(clauseType, list.toList());
            wrapup(st, clauseType, true, false);
            return st;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
