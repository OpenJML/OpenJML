package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.ListBuffer;

public class TypeInClauseExtension extends JmlExtension {
    
    public static final String inID = "in";
    
    public static final IJmlClauseKind inClause = new IJmlClauseKind.TypeClause(inID) {

        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseIn parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            int pp = parser.pos();
            if (!parser.isNone(mods))
                error(mods, "jml.no.mods.allowed", inClause.keyword());
            init(parser);
            parser.nextToken(); // skip over the in token
            ListBuffer<JmlGroupName> list = parser.parseGroupNameList();
            var t = parser.toP(parser.maker().at(pp).JmlTypeClauseIn(list.toList()));
            wrapup(t, clauseType, true, true);
            return t;
        }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
