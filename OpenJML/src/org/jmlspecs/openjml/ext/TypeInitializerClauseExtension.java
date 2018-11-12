package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.EQ;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IDENTIFIER;
import static com.sun.tools.javac.parser.Tokens.TokenKind.IF;
import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlGroupName;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseIn;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseInitializer;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.ITokenKind;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Name;

public class TypeInitializerClauseExtension implements JmlExtension.TypeClause {

    public static final String initializerID = "initializer";
    public static final String staticinitializerID = "static_initializer";

    @Override
    public IJmlClauseType[] clauseTypes() { return new IJmlClauseType[]{
            initializerClause, staticinitializerClause}; }
    
    public static final IJmlClauseType initializerClause = new InitializerBlock() {
        public String name() { return initializerID; }
    };
    
    public static final IJmlClauseType staticinitializerClause = new InitializerBlock() {
        public String name() { return staticinitializerID; }
    };
    
    private static class InitializerBlock extends IJmlClauseType.TypeClause {
        
        public 
        JmlTypeClauseInitializer parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            init(parser);
            int pp = parser.pos();
            JmlTypeClauseInitializer initializer = jmlF.at(pp).JmlTypeClauseInitializer(clauseType,mods);
            //@ FIXME - parse failure?
            initializer.specs = parser.currentMethodSpecs;
            parser.currentMethodSpecs = null;
            initializer = parser.to(initializer);
            // FIXME parser.list.append(initializer);
            wrapup(initializer, clauseType, false);
            return initializer;
        }
        
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
}
