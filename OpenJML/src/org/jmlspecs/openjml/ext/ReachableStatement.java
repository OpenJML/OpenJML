/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.IJmlClauseType;
import org.jmlspecs.openjml.JmlTokenKind;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree.JCExpression;
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
public class ReachableStatement extends StatementExtension {

    public ReachableStatement(Context context) {
        super(context);
    }
    
    public static void register(Context context) {}
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.REACHABLE}; }

    public static final String reachableID = "reachable";
    public static final String unreachableID = "unreachable";
    
    public static final IJmlClauseType reachableClause = new IJmlClauseType() {
        public String name() { return reachableID; }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };

    public static final IJmlClauseType unreachableClause = new IJmlClauseType() {
        public String name() { return unreachableID; }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };

    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            reachableClause, unreachableClause }; }
    

    // allowed forms:
    //   reachable ;
    //   reachable <expr> ;
    //   reachable <expr> : <expr> ; // The first <epxr> is a String literal, used as a message or identifier
    // FIXME - string literal is not used
    public JCStatement parse(String keyword, JmlParser parser) {
        init(parser);
        int pp = parser.pos();
        int pe = parser.endPos();
        JmlTokenKind jt = parser.jmlTokenKind();
        int p = scanner.currentPos();
        parser.nextToken();
        if (parser.token().kind == TokenKind.SEMI) {
            return jmlF.at(p).JmlExpressionStatement(jt,null,jmlF.Literal(TypeTag.BOOLEAN,1));
        } else {
            JCExpression opt = null;
            JCExpression e = parser.parseExpression();
            if (e == null) return null;
            if (parser.token().kind == TokenKind.COLON) {
                opt = parser.parseExpression();
            }
            
            if (parser.token().ikind == JmlTokenKind.ENDJMLCOMMENT) {
                parser.jmlwarning(p-2, "jml.missing.semi", jt);
            } else if (parser.token().kind != TokenKind.SEMI) {
                parser.jmlerror(p, "jml.missing.semi", jt);
            }
            return jmlF.at(p).JmlExpressionStatement(jt,null,e);
        }

    }
    
    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
        // TODO Auto-generated method stub
        return null;
    }
    
}
