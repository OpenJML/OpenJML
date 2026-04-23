package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.ELSE;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlChoose;
import org.jmlspecs.openjml.JmlTreeUtils;

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
import com.sun.tools.javac.tree.JCTree.JCStatement;
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
                error(parser.context, mods, "jml.message", "A " + keyword + " statement may not have modifiers");
                return null;
            }
            int pp = parser.pos();
            int pe = parser.endPos();
            parser.nextToken(); // skip over choose token
            parser.accept(Tokens.TokenKind.LBRACE);
            ListBuffer<JmlChoose.Item> oritems = new ListBuffer<>();
            JCStatement elseBlock = null;
            boolean saved = parser.inModelProgram;
            parser.inModelProgram = true;
            try {
                oritems.append(parseGuardedBlock(parser));
                // returns null.
                while (parser.tokenIsId("or")) {
                    parser.nextToken();
                    oritems.append(parseGuardedBlock(parser));
                }
                // FIXME - if there are some literally true guards, there is no point to an else block
                if (parser.token().kind == ELSE) {
                    var tutils = JmlTreeUtils.instance(parser.context);
                    for (var orb: oritems) {
                        if (tutils.isTrueLit(orb.guard)) {
                            Utils.instance(parser.context).warning(parser.token().pos, "jml.message", "An else block is dead code if any guard is true");
                        }
                    }
                    parser.nextToken(); // skip else
                    elseBlock = parser.parseStatement();
                }
                parser.accept(Tokens.TokenKind.RBRACE);
            } finally {
                parser.inModelProgram = saved;
            }
            return parser.toP(parser.maker().at(pp).JmlChoose(keyword, clauseType, oritems.toList(), elseBlock));
        }

        JmlChoose.Item parseGuardedBlock(JmlParser parser) {
            JCTree.JCExpression ex;
            if (parser.token().kind != Tokens.TokenKind.ARROW) {
                ex = parser.parseExpression();
            } else {
                ex = parser.jmlF.at(parser.token().pos).Literal(TypeTag.BOOLEAN,1); // true
            }
            parser.accept(Tokens.TokenKind.ARROW);
            JCStatement stat = parser.parseStatement();
            return new JmlChoose.Item(ex,stat);
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
                error(parser.context, mods, "jml.message", "A " + keyword + " repeat statement may not have modifiers");
                return null;
            }
            int pp = parser.pos();
            int pe = parser.endPos();
            parser.nextToken(); // skip over repeat token
            parser.accept(Tokens.TokenKind.LBRACE);
            ListBuffer<JmlChoose.Item> oritems = new ListBuffer<>();
            JCStatement elseBlock = null;
            boolean saved = parser.inModelProgram;
            parser.inModelProgram = true;
            try {
                oritems.append(parseRepeatGuardedBlock(parser));
                while (parser.tokenIsId("or")) {
                    parser.nextToken();
                    oritems.append(parseRepeatGuardedBlock(parser));
                }
                if (parser.token().kind == ELSE) {
                    parser.log.error(parser.token().pos, "jml.message", "A repeat statement may not have an else block");
                    parser.nextToken();
                    parser.parseStatement(); // skip any block
                }
                parser.accept(Tokens.TokenKind.RBRACE);
            } finally {
                parser.inModelProgram = saved;
            }
            return parser.toP(parser.maker().at(pp).JmlChoose(keyword, clauseType, oritems.toList(), elseBlock));
        }

        JmlChoose.Item parseRepeatGuardedBlock(JmlParser parser) {
            JCTree.JCExpression ex;
            if (parser.token().kind == Tokens.TokenKind.ARROW) {
                parser.log.error(parser.token().pos, "jml.message", "In a repeat statement, all blocks must have guards");
                ex = null;
            } else {
                ex = parser.parseExpression();
                
                var tutils = JmlTreeUtils.instance(parser.context);
                if (tutils.isTrueLit(ex)) {
                    // FIXME - what if the action is a return
                   parser.log.error(parser.token().pos, "jml.message", "An repeat statement never completes if some guard is always true");
                }

//                if (parser.treeutils.isTrueLit(ex)) {
//                    
//                }
            }
            parser.accept(Tokens.TokenKind.ARROW);
            return new JmlChoose.Item(ex, parser.parseStatement());
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
