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
public class AssertAssumeStatement extends StatementExtension implements IJmlLoop {

    public AssertAssumeStatement(Context context) {
        super(context);
    }
    
    public static void register(Context context) {}
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.ASSERT, JmlTokenKind.ASSUME}; }
    
    public static final String assertID = "assert";
    public static final String assumeID = "assume";
    public static final String useID = "use";
    
    public static final IJmlClauseType assertClause = new IJmlClauseType() {
        public String name() { return assertID; }
    };
    
    public static final IJmlClauseType assumeClause = new IJmlClauseType() {
        public String name() { return assumeID; }
    };
    
    public static final IJmlClauseType useClause = new IJmlClauseType() {
        public String name() { return useID; }
    };
    
    
    public IJmlClauseType[]  clauseTypes() { return new IJmlClauseType[]{
            assertClause, assumeClause, useClause }; }
    
    public JCStatement parse(String id, JmlParser parser) {
        init(parser);
        int pp = parser.pos();
        int pe = parser.endPos();
        JmlTokenKind jt = parser.jmlTokenKind();
        int p = scanner.currentPos();
        parser.nextToken();
        Token tk = parser.token();

        JCExpression t = null;
        t = parser.parseExpression();
        JmlTree.JmlStatementExpr ste = jmlF
                .at(p)
                .JmlExpressionStatement(
                        jt,
                          jt == JmlTokenKind.ASSUME ? Label.EXPLICIT_ASSUME :
                          jt == JmlTokenKind.ASSERT ? Label.EXPLICIT_ASSERT :
                        null,
                            t);
        if (tk.kind == COLON) {
            parser.nextToken();
            ste.optionalExpression = parser.parseExpression();
        }
        toP(ste);
        ste.source = Log.instance(context).currentSourceFile();
        //ste.line = log.currentSource().getLineNumber(pos);
        return ste;
    }
    
    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
        return null;
    }

    @Override
    public List<JmlStatementLoop> loopSpecs() {
        return null;
    }

    @Override
    public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) {
    }
}
