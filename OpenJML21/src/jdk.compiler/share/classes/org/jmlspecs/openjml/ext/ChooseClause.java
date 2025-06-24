package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.ELSE;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.ListBuffer;

public class ChooseClause extends JmlExtension {
    
    public static final String chooseID = "choose";
    public static final String repeatID = "repeat";
    
    public static final IJmlClauseKind chooseStatement = new IJmlClauseKind.Statement(chooseID) {
        @Override
        public boolean oldNoLabelAllowed() { return true; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            int pp = parser.pos();
            int pe = parser.endPos();
            init(parser);
            parser.nextToken(); // skip over choose token
            ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
            JCBlock elseBlock = null;
            boolean saved = parser.inModelProgram;
            parser.inModelProgram = true;
            try {
                orBlocks.append(parser.block()); // FIXME - here and below - what if block()
                // returns null.
                while (parser.tokenIsId("or")) {
                    parser.nextToken();
                    orBlocks.append(parseGuardedBlock());
                }
                // FIXME - if there are some literally true guards, there is no point to an else block
                if (parser.token().kind == ELSE) {
                    parser.nextToken();
                    elseBlock = parser.block();
                }
            } finally {
                parser.inModelProgram = saved;
            }
            return toP(parser.maker().at(pp).JmlChoose(keyword, clauseType, orBlocks.toList(), elseBlock));
        }
        
        JCBlock parseGuardedBlock() {
            JCTree.JCExpression ex;
            if (parser.token().kind != Tokens.TokenKind.LBRACE) {
                ex = parser.parseExpression();
                parser.accept(Tokens.TokenKind.ARROW);            
            } else {
                ex = parser.jmlF.at(parser.token().pos).Literal(TypeTag.BOOLEAN,1); // true
            }
            JCBlock bl = parser.block();
            return bl;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };

    public static final IJmlClauseKind repeatStatement = new IJmlClauseKind.Statement(repeatID) {
        @Override
        public boolean oldNoLabelAllowed() { return true; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            int pp = parser.pos();
            int pe = parser.endPos();
            init(parser);
            parser.nextToken(); // skip over choose token
            ListBuffer<JCBlock> orBlocks = new ListBuffer<JCBlock>();
            JCBlock elseBlock = null;
            boolean saved = parser.inModelProgram;
            parser.inModelProgram = true;
            try {
                var ex = parser.parseExpression();
                parser.accept(Tokens.TokenKind.ARROW);
                orBlocks.append(parseGuardedBlock());
                // returns null.
                while (parser.tokenIsId("or")) {
                    parser.nextToken();
                    ex = parser.parseExpression();
                    parser.accept(Tokens.TokenKind.ARROW);
                    orBlocks.append(parser.block());
                }
                // FIXME Check that there are no literally true gurads (or won't terminate)
                if (parser.token().kind == ELSE) {
                    // FIXME - error(parser.token(), "jml.message", "A repeat statement may not have an else block");
                    parser.nextToken();
                    parser.block(); // skip any block
                }
            } finally {
                parser.inModelProgram = saved;
            }
            return toP(parser.maker().at(pp).JmlChoose(keyword, clauseType, orBlocks.toList(), elseBlock));
        }
        
        JCBlock parseGuardedBlock() {
            JCTree.JCExpression ex;
            if (parser.token().kind == Tokens.TokenKind.LBRACE) {
                // FIXME _ ERROR _ requires a guard
                // FIXME - error(parser.token(), "jml.message", "In a repeat statement, all blocks must have guards");
                ex = null;
            } else {
            ex = parser.parseExpression();
            }
            parser.accept(Tokens.TokenKind.ARROW);
            JCBlock bl = parser.block();
            return bl;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    

    static {
    }
}
