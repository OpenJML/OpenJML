/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import static org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.alsoClause;
import static org.jmlspecs.openjml.ext.MethodSimpleClauseExtensions.elseClause;

import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlAbstractStatement;
import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.JmlTree.JmlSpecificationCase;
import org.jmlspecs.openjml.JmlTree.JmlStatement;
import org.jmlspecs.openjml.JmlTree.JmlStatementSpec;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.parser.Tokens.TokenKind;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;

// FIXME - combine this with other statements
public class Refining extends JmlExtension {
	public Refining() {}

    public static final String endID = "end";
    public static final String beginID = "begin";
    public static final String refiningID = "refining";
    
    public static final IJmlClauseKind beginClause = new SimpleStatement(beginID);
    public static final IJmlClauseKind endClause = new SimpleStatement(endID);
    public static final IJmlClauseKind refiningClause = new RefiningStatement(refiningID);

    public static class SimpleStatement extends IJmlClauseKind.Statement {
        public SimpleStatement(String id) { super(id); }
        
        @Override
        public JmlAbstractStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);

            int pp = parser.pos();
            int pe = parser.endPos();

            parser.nextToken();

            JmlStatement st = toP(parser.maker().at(pp).JmlStatement(clauseType, null));
            wrapup(st,clauseType,false,false);
            return st;

        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };

    // FIXME - this goes somewhere else?
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
    
    public static class RefiningStatement extends IJmlClauseKind.Statement {
        public RefiningStatement(String id) { super(id); }
        
        public JCStatement parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
            int pos = parser.pos();
            JmlStatementSpec ste;
            ListBuffer<JCIdent> exports = new ListBuffer<>();
            if (clauseType == Refining.refiningClause) {
                parser.nextToken();
                IJmlClauseKind ext = parser.methodSpecKeywordS();
                if (ext == alsoClause) { // jmlTokenKind() == JmlTokenKind.ALSO) {
                    utils.error(parser.pos(), parser.endPos(), "jml.invalid.also");
                    parser.nextToken();
                }
                if (ext == elseClause) { //token.ikind == TokenKind.ELSE) {
                    utils.error(parser.pos(), parser.endPos(), "jml.invalid.also"); // FIXME - should warn about else
                    parser.nextToken();
                }
                if (parser.token().kind == TokenKind.COLON) { 
                    parser.nextToken();
                    exports.add(parser.jmlF.at(parser.pos()).Ident(parser.ident()));
                    while (parser.token().kind == TokenKind.COMMA) {
                        parser.nextToken();
                        exports.add(parser.jmlF.at(pos).Ident(parser.ident()));
                    }
                    if (parser.token().kind != TokenKind.SEMI) {
                        utils.error(pos,parser.endPos(), "jml.message", "Expected a comma or semicolon here");
                    }
                    parser.nextToken();
                }
            } else {
                warning(pos,parser.endPos(),"jml.refining.required");
            }
            if (!parser.isNone(mods)) {
                utils.error(mods.getStartPosition(),
                        parser.getEndPos(mods),
                        "jml.no.mods.in.refining");
            }
            mods = parser.modifiersOpt();
            JmlMethodSpecs specs = parser.parseMethodSpecs(mods);
            for (JmlSpecificationCase c : specs.cases) {
                if (!parser.isNone(c.modifiers)) {
                    utils.error(c.modifiers.getStartPosition(),
                            parser.getEndPos(c.modifiers),
                            "jml.no.mods.in.refining");
                    c.modifiers = parser.jmlF.Modifiers(0);
                }
            }
            ste = parser.jmlF.at(pos).JmlStatementSpec(specs);
            ste.exports = exports.toList();
 //           ste.label = parser.names.fromString("`SSL"+pos); 
            parser.storeEnd(ste, parser.getEndPos(specs));

            JCStatement begin = null;
            if (parser.jmlTokenClauseKind() == Refining.beginClause) {
                begin = (JCStatement)Extensions.findSM(beginID).parse(mods, beginID, beginClause, parser);
            }
            ListBuffer<JCStatement> stats = new ListBuffer<>();
            List<JCStatement> stat;
            if (begin != null) {
                // Has a begin statement, so we read statement until an end
                while (true) {
                	if (parser.jmlTokenClauseKind() == Operators.startjmlcommentKind &&
                			parser.jmlTokenClauseKind(parser.getScanner().token(1)) == Refining.endClause) {
                		parser.nextToken();
                	}
                    if (parser.jmlTokenClauseKind() == Refining.endClause) {
                        Extensions.findSM(endID).parse(mods, endID, endClause, parser);
                        break;
                    }
                    stat = parser.blockStatement();
                    if (stat.isEmpty()) {
                        error(begin, "jml.message", "Expected an 'end' statement to match the begin statement before the end of block");
                        break;
                    } else {
                        stats.addAll(stat);
                    }
                }
            } else {
                stat = parser.blockStatement();
                if (stat == null || stat.isEmpty()) {
                    error(ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
                    return null;
                } else if (stat.head instanceof JmlAbstractStatement && stat.head.toString() == Refining.beginID) {
                    error(stat.head, "jml.message", "Statement specs may not precede a JML statement clause");
                    return stat.head;
                }
                stats.addAll(stat);
            }
            //ste.statements = parser.collectLoopSpecs(stats.toList());
            ste.statements = stats.toList();
            return ste;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }

    }
}
