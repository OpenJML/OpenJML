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
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
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
public class SetStatement extends StatementExtension {

    public SetStatement(Context context) {
        super(context);
    }
    
    public static void register(Context context) {}
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            }; }
    
    public static final String setID = "set";
    public static final String debugID = "debug";
    
    public static final IJmlClauseType setClause = new IJmlClauseType() {
        public String name() { return setID; }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public static final IJmlClauseType debugClause = new IJmlClauseType() {
        public String name() { return debugID; }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }
    };
    
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            setClause, debugClause }; }
    
    public JCStatement parse(String keyword, JmlParser parser) {
        init(parser);
        
        int pp = parser.pos();
        int pe = parser.endPos();
        
        scanner.setJmlKeyword(false);
        parser.nextToken();
        // Only StatementExpressions are allowed - 
        // assignment statements and stand-alone method calls -
        // but JML constructs are allowed.
//        boolean prev = parser.setInJmlDeclaration(true);
        JCExpression e;
        try {
            e = parser.parseExpression(); // Was super.
        } finally {
//            parser.setInJmlDeclaration(prev);
        }
        JCStatement t = jmlF.Exec(e);
//        if (!(t instanceof JCExpressionStatement)) {
//            parser.jmlerror(t.getStartPosition(),
//                    parser.getEndPos(t),
//                    "jml.bad.statement.in.set.debug");
//            t = null;
//        }
        JCStatement st = toP(jmlF.at(pp).JmlStatement(keyword, (JCExpressionStatement)t));
        scanner.setJmlKeyword(true);
        parser.accept(TokenKind.SEMI);
//        parser.rescan();
//        parser.needSemi = false;
        return st;

//        JmlTokenKind jt = parser.jmlTokenKind();
//        int p = scanner.currentPos();
//        parser.nextToken();
//        if (parser.token().kind == TokenKind.SEMI) {
//            return jmlF.at(p).JmlExpressionStatement(jt,null,jmlF.Literal(TypeTag.BOOLEAN,1));
//        } else {
//            JCExpression opt = null;
//            JCExpression e = parser.parseExpression();
//            if (e == null) return null;
//            if (parser.token().kind == TokenKind.COLON) {
//                opt = parser.parseExpression();
//            }
//            
//            if (parser.token().ikind == JmlTokenKind.ENDJMLCOMMENT) {
//                parser.jmlwarning(p-2, "jml.missing.semi", jt);
//            } else if (parser.token().kind != TokenKind.SEMI) {
//                parser.jmlerror(p, "jml.missing.semi", jt);
//            }
//            return jmlF.at(p).JmlExpressionStatement(jt,null,e);
//        }

    }
    
    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
        // TODO Auto-generated method stub
        return null;
    }
    
}
