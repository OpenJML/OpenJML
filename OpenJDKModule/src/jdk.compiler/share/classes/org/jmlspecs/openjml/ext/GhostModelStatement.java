/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;
import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatement;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

/** This class handles expression extensions that take an argument list of JCExpressions.
 * Even if there are constraints on the number of arguments, it
 * is more robust to accept all of them and then issue an error in the typechecker
 * if the number of arguments is wrong.
 * 
 * @author David Cok
 *
 */// TODO: This extension is inappropriately named at present.  However, I expect that this 
// extension will be broken into individual extensions when type checking and
// RAC and ESC translation are added.
public class GhostModelStatement extends JmlExtension {

    public static final String ghostID = "ghost";
    public static final String modelID = "model";
    
   // public static final IJmlClauseKind ghostDeclaration = new JmlDeclarationType(ghostID);
   // public static final IJmlClauseKind modelDeclaration = new JmlDeclarationType(modelID);
    

    public static class JmlDeclarationType extends IJmlClauseKind.Statement {
        public JmlDeclarationType(String keyword) { super(keyword); }

        public JCStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            JCAnnotation a = null; // parser.tokenToAnnotationAST(clauseType == ghostDeclaration ? JmlTokenKind.GHOST :  JmlTokenKind.MODEL, pp, pe);
            parser.nextToken();
            boolean saved = parser.setInJmlDeclaration(true);
            try {
                mods = parser.modifiersOpt();
                mods.annotations = mods.annotations.prepend(a);
                parser.utils.setJML(mods);
                JCExpression t = parser.parseType();
                ListBuffer<JCStatement> stats =
                        parser.variableDeclarators(mods, t, new ListBuffer<JCStatement>());
                // A "LocalVariableDeclarationStatement" subsumes the terminating semicolon
                parser.storeEnd(stats.last(), parser.token().endPos);
                parser.accept(SEMI);

                JCStatement st = toP(stats.first());
                wrapup(st, clauseType, false);
                return st;
            } finally {
                parser.setInJmlDeclaration(saved);
            }
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
}
    
    
}
