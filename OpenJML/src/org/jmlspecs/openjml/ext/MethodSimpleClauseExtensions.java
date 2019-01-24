package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseDecl;

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

public class MethodSimpleClauseExtensions extends JmlExtension.MethodClause {
    
    public static final String specGroupStartID = "{|";
    public static final String specGroupEndID = "|}";
    public static final String alsoID = "also";
    public static final String modelprogramID = "model_program";
    
    public static final IJmlClauseType specGroupStartClause = new MethodClauseType() {
        @Override public String name() { return specGroupStartID; }
    };
    
    public static final IJmlClauseType specGroupEndClause = new MethodClauseType() {
        @Override public String name() { return specGroupEndID; }
    };
    
    public static final IJmlClauseType modelprogramClause = new MethodClauseType() {
        @Override public String name() { return modelprogramID; }
    };
    
    public static final IJmlClauseType alsoClause = new MethodClauseType() {
        @Override public String name() { return alsoID; }
    };
    
    public static final IJmlClauseType declClause = new MethodClauseType() {
        @Override public String name() { return "jml declaration"; }
    };
    
    @Override
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            specGroupStartClause, specGroupEndClause, modelprogramClause, alsoClause,}; }
    
    public static class MethodClauseType extends IJmlClauseType.MethodClause {

        @Override
        public 
        JmlMethodClauseDecl parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            parser.nextToken();
            return null;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
    
}
