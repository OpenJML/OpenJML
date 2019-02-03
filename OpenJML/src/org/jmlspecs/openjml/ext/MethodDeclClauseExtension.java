package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;
import org.jmlspecs.openjml.JmlExtension;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

public class MethodDeclClauseExtension extends JmlExtension.MethodClause  {

    public static final String oldID = "old";
    public static final String forallID = "forall";
    
    public static final IJmlClauseType oldClause = new MethodClauseDeclType() {
        public String name() { return oldID; }
        public boolean isPreconditionClause() { return true; }
    };
    
    public static final IJmlClauseType forallClause = new MethodClauseDeclType() {
        public String name() { return forallID; }
        public boolean isPreconditionClause() { return true; }
    };
    
    @Override
    public IJmlClauseType[] clauseTypes() { return new IJmlClauseType[]{
            oldClause, forallClause }; }
    
    public static class MethodClauseDeclType extends IJmlClauseType.MethodClause {

        @Override
        public 
        JmlMethodClauseDecl parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            init(parser);
            // TODO: Warning if mods is not null or empty
            mods = parser.maker().Modifiers(0L);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            scanner.setJmlKeyword(false);
            parser.nextToken();

            // non_null and nullable and perhaps other type modifiers in the
            // future are allowed
            JCModifiers mods2 = parser.modifiersOpt();
            JCExpression t = parser.parseType();
            boolean prev = parser.setInJmlDeclaration(true); // allows non-ghost declarations
            ListBuffer<JCTree.JCVariableDecl> decls = parser.variableDeclarators(mods2, t,
                    new ListBuffer<JCVariableDecl>());
            parser.setInJmlDeclaration(prev);
            JmlMethodClauseDecl res = parser.to(jmlF.at(pp)
                    .JmlMethodClauseDecl(keyword, clauseType, decls.toList()));
            scanner.setJmlKeyword(true);
            if (parser.token().kind == SEMI) {
                parser.nextToken();
            } else {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.bad.construct",
                        keyword + " specification");
                parser.skipThroughSemi();
            }
            return res;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
