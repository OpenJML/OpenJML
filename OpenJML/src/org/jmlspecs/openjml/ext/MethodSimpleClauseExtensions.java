package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
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
    
    public static final IJmlClauseKind specGroupStartClause = new MethodClauseType() {
        @Override public String name() { return specGroupStartID; }
    };
    
    public static final IJmlClauseKind specGroupEndClause = new MethodClauseType() {
        @Override public String name() { return specGroupEndID; }
    };
    
    public static final IJmlClauseKind modelprogramClause = new MethodClauseType() {
        @Override public String name() { return modelprogramID; }
    };
    
    public static final IJmlClauseKind alsoClause = new MethodClauseType() {
        @Override public String name() { return alsoID; }
    };
    
    public static final IJmlClauseKind declClause = new MethodClauseType() {
        @Override public String name() { return "jml declaration"; }
    };
    
    @Override
    public IJmlClauseKind[]  clauseTypes() { return new IJmlClauseKind[]{
            specGroupStartClause, specGroupEndClause, modelprogramClause, alsoClause,}; }
    
    public static class MethodClauseType extends IJmlClauseKind.MethodClause {

        @Override
        public 
        JmlMethodClauseDecl parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            parser.nextToken();
            return null;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
    
}
