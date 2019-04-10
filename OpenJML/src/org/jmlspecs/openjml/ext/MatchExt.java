package org.jmlspecs.openjml.ext;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.source.tree.TreeVisitor;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

public class MatchExt extends ExpressionExtension {

    public MatchExt(Context context) {
        super(context);
    }

    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.MATCH }; }
    
    @Override
    public IJmlClauseKind[] clauseTypes() {
        return null;
    }
    
    @Override
    public JCExpression parse(String keyword, IJmlClauseKind clauseType, JmlParser parser) {
        parser.nextToken();
        parser.parseExpression();
        parser.accept(TokenKind.LBRACE);
        System.out.println("Parsing match expression");
        parser.skipThroughRightBrace();
        return null;
    }
    
    @Override
    public JCExpression parse(JmlParser parser,
            @Nullable List<JCExpression> typeArgs) {
        return parse(null,null,parser);
    }

    
    static public class MatchExpr extends JmlExpression {

        @Override
        public Kind getKind() {
            return null;
        }

        @Override
        public Tag getTag() {
            return null;
        }

        @Override
        public void accept(Visitor v) {
            // TODO Auto-generated method stub
            
        }

        @Override
        public <R, D> R accept(TreeVisitor<R, D> v, D d) {
            // TODO Auto-generated method stub
            return null;
        }
        
    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr,
            Env<AttrContext> env) {
        // TODO Auto-generated method stub
        return null;
    }

}
