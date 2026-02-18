package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlExtension;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.ListBuffer;

public class MethodDeclClauseExtension extends JmlExtension  {

    public static final String oldID = "old";
    
    public static final IJmlClauseKind oldClause = new MethodClauseDeclType(oldID) {
        public boolean isPreconditionClause() { return true; }
    };
    
    public static class MethodClauseDeclType extends IJmlClauseKind.MethodSpecClauseKind {
        public MethodClauseDeclType(String keyword) { super(keyword); }
 
        @Override
        public 
        JmlMethodClauseDecl parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            // TODO: Warning if mods is not null or empty
            if (!utils.hasNone(mods)) utils.warning(mods, "jml.no.mods.allowed");
            int pp = parser.pos();
            int pe = parser.endPos();
            
            parser.nextToken();

            mods = parser.modifiersOpt();

            Utils.instance(parser.context).setJML(mods);
            Utils.instance(parser.context).setJMLTop(mods);
            JCExpression t = parser.parseType(true);
            boolean prev = parser.setInJmlDeclaration(true); // allows non-ghost declarations
            ListBuffer<JCTree.JCVariableDecl> decls = parser.variableDeclarators(mods, t,
                    new ListBuffer<JCVariableDecl>(), true);
            parser.setInJmlDeclaration(prev);
            JmlMethodClauseDecl res = parser.to(parser.maker().at(pp)
                    .JmlMethodClauseDecl(keyword, clauseType, decls.toList()));
            wrapup(res, clauseType, true, true);
            return res;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
