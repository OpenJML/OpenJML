package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;

public class AssignableClauseExtension extends JmlExtension {
    
    public static final String assignableID = "assignable";
    public static final String assignsID = "assigns";
    public static final String writesID = "writes";
    public static final String accessibleID = "accessible";
    public static final String readsID = "reads";
    public static final String capturesID = "captures";
    
    public static final IJmlClauseKind assignableClauseKind = new LocationSetClauseType(assignableID) {
        public String keyword() { return assignableID; }
    };
    
    public static final IJmlClauseKind accessibleClauseKind = new LocationSetClauseType(accessibleID) {
        public String keyword() { return accessibleID; }
    };
    
    public static final IJmlClauseKind capturesClauseKind = new LocationSetClauseType(capturesID) {
        public String keyword() { return capturesID; }
    };
    
    static {
        synonym(writesID,assignableClauseKind);
        synonym("modifies",assignableClauseKind);
        synonym(assignsID,assignableClauseKind);
        synonym("modifiable",assignableClauseKind);
        synonym(readsID,accessibleClauseKind);
    }
    
    public static class LocationSetClauseType extends IJmlClauseKind.MethodSpecClauseKind {
        public LocationSetClauseType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        @Override
        public JmlMethodClause parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            init(parser);
            this.keyword = keyword;
            
            int pp = parser.pos();
            
            parser.nextToken();
            var n = parser.parseOptionalName();

            List<JCExpression> list = List.<JCExpression>nil();
            if (parser.token().kind == SEMI) {
                parser.syntaxError(parser.pos(), null, "jml.use.nothing.assignable"); // FIXME - fix to use keyword
                parser.nextToken(); // skip over the SEMI
            } else {
                try { list = parser.parseLocationList(); } catch (Exception e) { System.out.println("EXC " + e); e.printStackTrace(System.out); }
                if (parser.token().kind == SEMI) {
                    // OK, go on
                } else if (parser.isEndJml()) {
                    parser.syntaxError(parser.pos(), null, "jml.missing.semi");
                }
                if (parser.token().kind != SEMI) {
                    // error already reported
                    parser.skipThroughSemi();
                } else {
                    if (list.isEmpty()) {
                        parser.syntaxError(parser.pos(), null, "jml.use.nothing.assignable");
                    }
                    parser.nextToken();
                }
            }  // FIXME - fix the above; cf loop_writes
            var cl = parser.maker().at(pp).JmlMethodClauseStoreRef(keyword, clauseType, list);
            cl.name = n;
            wrapup(cl, clauseType, false, false);
            return cl;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
