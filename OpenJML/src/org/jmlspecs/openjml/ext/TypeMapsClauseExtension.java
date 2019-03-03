package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class TypeMapsClauseExtension extends JmlExtension.TypeClause {

    @Override
    public IJmlClauseKind[] clauseTypes() { return new IJmlClauseKind[]{
            mapsClause}; }
    
    public static final String mapsID = "maps";
    
    public static final IJmlClauseKind mapsClause = new IJmlClauseKind.TypeClause() {
        public String name(){
            return mapsID;
        }

        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseMaps parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            JmlTypeClauseMaps mapsClause = parser.parseMaps(pp, mods, null);
            return mapsClause;
        }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
