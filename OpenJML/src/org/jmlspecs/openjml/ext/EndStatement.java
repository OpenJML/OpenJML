/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

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
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;

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
public class EndStatement extends JmlExtension.Statement {

    public static final String endID = "end";
    public static final String beginID = "begin";
    public static final String refactoringID = "refactoring";
    public static final String asID = "as";
    
    @Override
    public IJmlClauseKind[]  clauseTypesA() { return clauseTypes(); }
    public static IJmlClauseKind[]  clauseTypes() { return new IJmlClauseKind[]{
            beginClause, endClause, refactoringClause, asClause }; }

    public static final IJmlClauseKind beginClause = new SimpleStatement(beginID);
    public static final IJmlClauseKind endClause = new SimpleStatement(endID);
    public static final IJmlClauseKind refactoringClause = new SimpleStatement(refactoringID);
    public static final IJmlClauseKind asClause = new SimpleStatement(asID);

    public static class SimpleStatement extends IJmlClauseKind.Statement {
        public SimpleStatement(String id) { super(id); }
        
        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);

            int pp = parser.pos();
            int pe = parser.endPos();

            scanner.setJmlKeyword(false);
            parser.nextToken();

            JmlStatement st = toP(parser.maker().at(pp).JmlStatement(clauseType, null));
            wrapup(st,clauseType,true,false);
            return st;

        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    
//    public static final IJmlClauseType orClause = new IJmlClauseType.Statement() {
//        public String name() { return orID; }
//     
//        @Override
//        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
//            init(parser);
//
//            int pp = parser.pos();
//            int pe = parser.endPos();
//
//            scanner.setJmlKeyword(false);
//            parser.nextToken();
//
//            JmlStatement st = toP(jmlF.at(pp).JmlStatement(endClause, null));
//            wrapup(st,clauseType,true);
//            return st;
//
//        }
//
//        @Override
//        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
//            // TODO Auto-generated method stub
//            return null;
//        }
//    };
    
}
