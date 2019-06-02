package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlDefinitions;
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

public class MethodSimpleClauseExtensions {
    
//    public static final String specGroupStartID = "{|";
//    public static final String specGroupEndID = "|}";
    public static final String alsoID = "also";
    public static final String codeID = "code";
    public static final String impliesthatID = "implies_that";
    public static final String forexampleID = "for_example";
    public static final String behaviorID = "behavior";
    public static final String normalbehaviorID = "normal_behavior";
    public static final String exceptionalbehaviorID = "exceptional_behavior";
    public static final String abruptbehaviorID = "abrupt_behavior";
    public static final String exampleID = "example";
    public static final String normalexampleID = "normal_example";
    public static final String exceptionalexampleID = "exceptional_example";
    public static final String modelprogramID = "model_program";
    
//    public static final IJmlClauseKind specGroupStartClause = new MethodClauseType(specGroupStartID);
    
//    public static final IJmlClauseKind specGroupEndClause = new MethodClauseType(specGroupEndID);
    
    public static final IJmlClauseKind modelprogramClause = new MethodClauseType(modelprogramID);
    
    public static final IJmlClauseKind alsoClause = new MethodClauseType(alsoID);
    
    public static final IJmlClauseKind codeClause = new MethodClauseType(codeID);
    
    public static final IJmlClauseKind impliesthatClause = new MethodClauseType(impliesthatID);
    
    public static final IJmlClauseKind forexampleClause = new MethodClauseType(forexampleID);
    
    public static final IJmlClauseKind behaviorClause = new MethodClauseType(behaviorID);
    
    public static final IJmlClauseKind normalbehaviorClause = new MethodClauseType(normalbehaviorID);
    
    public static final IJmlClauseKind exceptionalbehaviorClause = new MethodClauseType(exceptionalbehaviorID);
    
    public static final IJmlClauseKind abruptbehaviorClause = new MethodClauseType(abruptbehaviorID);
    
    public static final IJmlClauseKind exampleClause = new MethodClauseType(exampleID);
    
    public static final IJmlClauseKind normalexampleClause = new MethodClauseType(normalexampleID);
    
    public static final IJmlClauseKind exceptionalexampleClause = new MethodClauseType(exceptionalexampleID);
    
    public static final IJmlClauseKind declClause = new MethodClauseType("jml declaration") {
        @Override public String name() { return "jml declaration"; }
    };
    
    
    public static class MethodClauseType extends IJmlClauseKind.MethodClause {
        public MethodClauseType(String keyword) { super(keyword); }
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
