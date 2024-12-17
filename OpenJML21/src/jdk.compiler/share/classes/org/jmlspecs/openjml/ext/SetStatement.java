/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlAnnotation;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.JmlToken;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
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
public class SetStatement extends JmlExtension {

    public static final String setID = "set";
   
    public static final IJmlClauseKind setClause = new JmlStatementType(setID);
    

    public static class JmlStatementType extends IJmlClauseKind.Statement {
        public JmlStatementType(String keyword) { super(keyword); }
        public boolean oldNoLabelAllowed() { return true; }
        public boolean preOrOldWithLabelAllowed() { return true; }

        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            var token = parser.token();
            parser.nextToken();
            boolean saved = parser.setInJmlDeclaration(true);
            try {
                JCStatement t = parser.parseJavaStatement();
                JmlAbstractStatement st = toP(parser.maker().at(pp).JmlStatement(clauseType, t));
                if (t instanceof JmlVariableDecl jmlstat) {
                	JmlToken jt = new JmlToken(Modifiers.GHOST, pp, pe);
                	jt.source = Log.instance(parser.context).currentSourceFile();
                	//jmlstat.mods.add(jt);
                	JmlTreeUtils.instance(parser.context).addAnnotation(jmlstat.mods, jt, parser);
                }
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
