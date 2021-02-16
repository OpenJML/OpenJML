package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.Maker;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCExpressionStatement;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.Context;

public class TypeDeclClauseExtension extends JmlExtension {

    public static final String typedeclID = "type declaration";
    //public static final String capturedID = "captured";
    
    public static final IJmlClauseKind typedeclClause = new TypeClause(typedeclID);
    //public static final IJmlClauseKind capturedClause = new TypeClause(capturedID);
    
    public static class TypeClause extends IJmlClauseKind.TypeClause {
        public TypeClause(String keyword) { super(keyword); }
        
        public 
        JmlTypeClauseExpr parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            
            int pp = parser.pos();
            int pe = parser.endPos();
            
            parser.nextToken();

            JCExpression e = parser.parseExpression();
            if (parser.token().kind != SEMI) {
                parser.jmlerror(parser.pos(), parser.endPos(), "jml.bad.construct",
                        keyword + " declaration");
                parser.skipThroughSemi();
            } else {
                parser.nextToken();
            }
            Maker M = parser.maker().at(pp);
            if (mods == null) mods = M.Modifiers(0);
            JmlTypeClauseExpr tcl = parser.to(M.JmlTypeClauseExpr(mods, keyword, clauseType, e));
            tcl.source = log.currentSourceFile();
            return tcl;
        }
        
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    }
}
