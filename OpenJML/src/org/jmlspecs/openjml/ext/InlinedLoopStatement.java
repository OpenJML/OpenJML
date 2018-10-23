/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.JmlTokenKind.ENDJMLCOMMENT;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.IJmlLoop;
import org.jmlspecs.openjml.JmlTree.JmlStatementLoop;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.StatementExtension;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;

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
public class InlinedLoopStatement extends StatementExtension implements IJmlLoop {

    public InlinedLoopStatement(Context context) {
        super(context);
    }
    
    public static void register(Context context) {}
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.INLINED_LOOP}; }
    
    public List<JmlStatementLoop> loopSpecs;
    
    // allowed forms:
    //   reachable ;
    //   reachable <expr> ;
    //   reachable <expr> : <expr> ; // The first <epxr> is a String literal, used as a message or identifier
    // FIXME - string literal is not used
    public JCStatement parse(JmlParser parser) {
        init(parser);
        int pp = parser.pos();
        int pe = parser.endPos();
        JmlTokenKind jt = parser.jmlTokenKind();
        int p = scanner.currentPos();
        parser.nextToken();
        if (parser.token().kind == TokenKind.SEMI) {
            return jmlF.at(p).JmlExpressionStatement(jt,null,null);
        } else {
            
            if (parser.token().ikind == JmlTokenKind.ENDJMLCOMMENT) {
                parser.jmlwarning(p-2, "jml.missing.semi", jt);
            } else if (parser.token().kind != TokenKind.SEMI) {
                parser.jmlerror(p, "jml.missing.semi", jt);
            }
            return jmlF.at(p).JmlExpressionStatement(jt,null,null);
        }

    }
    
    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> env) {
        return null;
    }

    @Override
    public List<JmlStatementLoop> loopSpecs() {
        return loopSpecs;
    }

    @Override
    public void setLoopSpecs(List<JmlStatementLoop> loopSpecs) {
        this.loopSpecs = loopSpecs;
    }
    
}
