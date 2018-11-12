/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.COLON;
import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.IJmlLoop;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.Token;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Log;

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
public class StatementExprType extends IJmlClauseType.Statement {
    
    public StatementExprType(String keyword) {
        this.keyword = keyword;
    }

    @Override
    public JmlAbstractStatement parse(JCModifiers mods, String id, IJmlClauseType clauseType, JmlParser parser) {
        init(parser);
        int pp = parser.pos();
        int pe = parser.endPos();

        parser.nextToken();
        Token tk = parser.token();

        JCExpression t = parser.parseExpression();
        String nm = clauseType.name();
        JmlTree.JmlStatementExpr ste = jmlF
                .at(pp)
                .JmlExpressionStatement(
                        nm,
                        clauseType,
                          nm.equals("assume") ? Label.EXPLICIT_ASSUME :
                                                Label.EXPLICIT_ASSERT,  // FIXME?
                            t);
        if (tk.kind == COLON) {
            parser.nextToken();
            ste.optionalExpression = parser.parseExpression();
        }
        wrapup(ste,clauseType,true);
        return ste;
    }
    
    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
        return null;
    }

    // FIXME
//    @Override
//    public List<JmlStatementLoop> loopSpecs() {
//        return null;
//    }
//
//    @Override
//    public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) {
//    }
}
