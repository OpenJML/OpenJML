package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

public class TypeInClauseExtension implements JmlExtension.TypeClause {

    @Override
    public IJmlClauseType[] clauseTypes() { return new IJmlClauseType[]{
            inClause}; }
    
    public static final String inID = "in";
    
    public static final IJmlClauseType inClause = new IJmlClauseType.TypeClause() {
        public String name(){
            return inID;
        }

        public boolean oldNoLabelAllowed() { return false; }
        public boolean preOrOldWithLabelAllowed() { return false; }
        
        public 
        JmlTypeClauseIn parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            int pp = parser.pos();
            if (!parser.isNone(mods))
                error(mods, "jml.no.mods.allowed", inClause.name());
            init(parser);
            scanner.setJmlKeyword(false);
            parser.nextToken(); // skip over the in token
            ListBuffer<JmlGroupName> list = parser.parseGroupNameList();
            scanner.setJmlKeyword(true);
            parser.accept(SEMI);
            return parser.toP(jmlF.at(pp).JmlTypeClauseIn(list.toList()));
        }
        
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
