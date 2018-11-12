package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseMaps;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class TypeMapsClauseExtension implements JmlExtension.TypeClause {

    @Override
    public IJmlClauseType[] clauseTypes() { return new IJmlClauseType[]{
            mapsClause}; }
    
    public static final String mapsID = "maps";
    
    public static final IJmlClauseType mapsClause = new IJmlClauseType.TypeClause() {
        public String name(){
            return mapsID;
        }

        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseMaps parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            int pp = parser.pos();
            init(parser);
            return null;
// FIXME
            
//            JmlTypeClauseMaps mapsClause = parseMaps(pp, mods, list);
//            if (mostRecentVarDecl == null) {
//                log.error(mapsClause.pos(), "jml.misplaced.var.spec",
//                        mapsClause.keyword);
//            } else {
//                if (mostRecentVarDecl.fieldSpecs == null) {
//                    mostRecentVarDecl.fieldSpecs = new JmlSpecs.FieldSpecs(
//                            mostRecentVarDecl);
//                }
//                mostRecentVarDecl.fieldSpecs.list.append(mapsClause);
//                currentVariableDecl = mostRecentVarDecl;
//            }
        }
        
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
