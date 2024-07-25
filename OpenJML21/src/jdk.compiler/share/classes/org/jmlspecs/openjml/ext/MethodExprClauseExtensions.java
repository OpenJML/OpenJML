package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseBehaviors;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;

import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class MethodExprClauseExtensions extends JmlExtension {
    
    public static final String requiresID = "requires";
    public static final String recommendsID = "recommends";
    public static final String ensuresID = "ensures";
    public static final String divergesID = "diverges";
    public static final String whenID = "when";
    public static final String continuesID = "continues";
    public static final String breaksID = "breaks";
    public static final String returnsID = "returns";
    public static final String behaviorsID = "behaviors";
    
    public static final IJmlClauseKind requiresClauseKind = new MethodClauseExprType(requiresID) {
        public boolean isPreconditionClause() { return true; }
    };
    
    public static final IJmlClauseKind ensuresClauseKind = new MethodClauseExprType(ensuresID) {
        public boolean oldNoLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind divergesClauseKind = new MethodClauseExprType(divergesID);
    
    public static final IJmlClauseKind whenClauseKind = new MethodClauseExprType(whenID);
    
    public static final IJmlClauseKind continuesClauseKind = new MethodClauseExprType(continuesID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind breaksClauseKind = new MethodClauseExprType(breaksID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseKind returnsClauseKind = new MethodClauseExprType(returnsID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final String[] behaviorsCommands = { "complete", "disjoint", "local_complete", "local_disjoint", "implementable" }; // MUST BE SORTED
    static { java.util.Arrays.sort(behaviorsCommands); }

    
    public static final IJmlClauseKind behaviorsClauseKind = new MethodClauseExprType(behaviorsID) {
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
        
        @Override
        public 
        JmlMethodClauseBehaviors parse(JCModifiers mods, String keyword, IJmlClauseKind clauseKind, JmlParser parser) {
            init(parser);
            if (mods != null && mods.flags != 0) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers : " + mods);
            }
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            parser.nextToken();
            var n = parser.parseOptionalName();
            JmlMethodClauseBehaviors cl = null;
            JCExpression e = parser.parseExpression();
            if (e instanceof JCIdent id) {
                var s = id.getName().toString();
                if (!java.util.Arrays.stream(behaviorsCommands).filter(x->x.equals(s)).findFirst().isPresent()) {
                    error(e, "jml.message", "this word is not a recognized 'behaviors' option: " + s);
                } else {
                    cl = parser.maker().at(pp).JmlMethodClauseBehaviors(s);
                    cl.name = n;
                }
            } else {
                error(e, "jml.message", "the content of a behaviors clause must be a simple identifier");
            }
            wrapup(cl, clauseKind, true, true);
            return cl;           
        }

    };

    // FIXME -- allow this
//    static {
//        synonym("behaviours",behaviorsClauseKind);
//    }
    

}
