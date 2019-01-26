/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.IJmlClauseType;
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
    
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            endClause }; }
    
    public static final IJmlClauseType endClause = new IJmlClauseType.Statement() {
        public String name() { return endID; }
     
        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseType clauseType, JmlParser parser) {
            init(parser);

            int pp = parser.pos();
            int pe = parser.endPos();

            scanner.setJmlKeyword(false);
            parser.nextToken();

//            Token tk = parser.token();
//            if (tk.kind == TokenKind.SEMI) {
//                // this is what we expect
//                parser.accept(TokenKind.SEMI);
//            } else if (tk.ikind == JmlTokenKind.ENDJMLCOMMENT) {
//                // show with no list and no semicolon
//                error(parser.pos()-1, parser.pos(), "jml.missing.semicolon.in.show");  // FIXME - fix error message
//            } else {
//                error(parser.pos(), parser.pos()+1, "jml.bad.expression.list.in.show"); // FIXME 
//                parser.skipThroughSemi();
//            }
            JmlStatement st = toP(jmlF.at(pp).JmlStatement(endClause, null));
            wrapup(st,clauseType,true);
            return st;

        }

        @Override
        public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
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
