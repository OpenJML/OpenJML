package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.Extensions;
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
    
    public static final String normalBehaviorID = "normal_behavior";
    public static final String exceptionalBehaviorID = "exceptional_behavior";
    public static final String behaviorID = "behavior";
    public static final String feasibleBehaviorID = "feasible_behavior";
    public static final String abruptBehaviorID = "abrupt_behavior";
    public static final String normalExampleID = "normal_example";
    public static final String exceptionalExampleID = "exceptional_example";
    public static final String forExampleID = "for_example";
    public static final String exampleID = "example";
    public static final String impliesThatID = "implies_that";
    public static final String specGroupStartID = "{|";
    public static final String specGroupEndID = "|}";
    public static final String alsoID = "also";
    public static final String elseID = "also";
    public static final String codeID = "code";
    public static final String modelprogramID = "model_program";
    
    public static final IJmlClauseKind specGroupStartClause = new MethodKeywordClauseType(specGroupStartID);
    
    public static final IJmlClauseKind specGroupEndClause = new MethodKeywordClauseType(specGroupEndID);
    
    public static final IJmlClauseKind modelprogramClause = new MethodKeywordClauseType(modelprogramID);
    public static final IJmlClauseKind normalBehaviorClause = new MethodKeywordClauseType(normalBehaviorID);
    public static final IJmlClauseKind exceptionalBehaviorClause = new MethodKeywordClauseType(exceptionalBehaviorID);
    public static final IJmlClauseKind behaviorClause = new MethodKeywordClauseType(behaviorID);
    public static final IJmlClauseKind feasibleBehaviorClause = new MethodKeywordClauseType(feasibleBehaviorID);
    public static final IJmlClauseKind abruptBehaviorClause = new MethodKeywordClauseType(abruptBehaviorID);
    public static final IJmlClauseKind normalExampleClause = new MethodKeywordClauseType(normalExampleID);
    public static final IJmlClauseKind exceptionalExampleClause = new MethodKeywordClauseType(exceptionalExampleID);
    public static final IJmlClauseKind forExampleClause = new MethodKeywordClauseType(forExampleID);
    public static final IJmlClauseKind exampleClause = new MethodKeywordClauseType(exampleID);
    public static final IJmlClauseKind impliesThatClause = new MethodKeywordClauseType(impliesThatID);
    
    public static final IJmlClauseKind alsoClause = new MethodKeywordClauseType(alsoID);
    public static final IJmlClauseKind elseClause = new MethodKeywordClauseType(elseID);
    public static final IJmlClauseKind codeClause = new MethodKeywordClauseType(codeID);
    
    public static final IJmlClauseKind declClause = new MethodKeywordClauseType("jml declaration") {
        @Override public String name() { return "jml declaration"; }
    };
    
    public void register() {
        synonym("normal_behaviour",normalBehaviorClause);
        synonym("exceptional_behaviour",exceptionalBehaviorClause);
        synonym("behaviour",behaviorClause);
    }
    
    public static class MethodKeywordClauseType extends IJmlClauseKind.MethodClauseKind {
        public MethodKeywordClauseType(String keyword) { super(keyword); }
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
