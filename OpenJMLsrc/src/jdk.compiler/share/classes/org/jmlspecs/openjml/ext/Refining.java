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
import org.jmlspecs.openjml.Utils;
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
import com.sun.tools.javac.util.Context;
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
            int pp = parser.pos();
            int pe = parser.endPos();

            parser.nextToken();

            JmlStatement st = parser.toP(parser.maker().at(pp).JmlStatement(clauseType, null));
            wrapup(parser,st,clauseType,false,false);
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
            int pos = parser.pos();
            JmlStatementSpec ste;
            ListBuffer<JCIdent> exports = new ListBuffer<>();
            JmlMethodSpecs specs;
            try {
                parser.inRefinementSpec = true;
                if (clauseType == Refining.refiningClause) {
                    parser.nextToken();
                    IJmlClauseKind ext = parser.methodSpecKeywordS();
                    if (ext == alsoClause) { // jmlTokenKind() == JmlTokenKind.ALSO) {
                        Utils.instance(parser.context).error(parser.pos(), parser.endPos(), "jml.invalid.also");
                        parser.nextToken();
                    }
                    if (ext == elseClause) {
                        Utils.instance(parser.context).error(parser.pos(), parser.endPos(), "jml.invalid.also"); // FIXME - should warn about else
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
                            Utils.instance(parser.context).error(pos,parser.endPos(), "jml.message", "Expected a comma or semicolon here");
                        }
                        parser.nextToken();
                    }
                } else {
                    warning(parser.context,pos,parser.endPos(),"jml.refining.required");
                }
                if (!parser.isNone(mods)) {
                    Utils.instance(parser.context).error(mods.getStartPosition(),
                            parser.getEndPos(mods),
                            "jml.no.mods.in.refining");
                }
                mods = parser.modifiersOpt();
                specs = parser.parseMethodSpecs(mods);
                for (JmlSpecificationCase c : specs.cases) {
                    if (!parser.isNone(c.modifiers)) {
                        Utils.instance(parser.context).error(c.modifiers.getStartPosition(),
                                parser.getEndPos(c.modifiers),
                                "jml.no.mods.in.refining");
                        c.modifiers = parser.jmlF.Modifiers(0);
                    }
                }
            } finally {
                parser.inRefinementSpec = false;
            }
            ste = parser.jmlF.at(pos).JmlStatementSpec(specs);
            ste.exports = exports.toList();
 //           ste.label = parser.names.fromString("`SSL"+pos); 
            parser.storeEnd(ste, parser.getEndPos(specs));

            JCStatement begin = null;
            if (parser.jmlTokenClauseKind() == Refining.beginClause) {
                begin = (JCStatement)Extensions.instance(parser.context).findSM(beginID).parse(mods, beginID, beginClause, parser);
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
                        Extensions.instance(parser.context).findSM(endID).parse(mods, endID, endClause, parser);
                        break;
                    }
                    stat = parser.blockStatement();
                    if (stat.isEmpty()) {
                        error(parser.context, begin, "jml.message", "Expected an 'end' statement to match the begin statement before the end of block");
                        break;
                    } else {
                        stats.addAll(stat);
                    }
                }
            } else {
                stat = parser.blockStatement();
                if (stat == null || stat.isEmpty()) {
                    error(parser.context, ste, "jml.message", "Statement specs found at the end of a block (or before an erroneous statement)");
                    return null;
                } else if (stat.head instanceof JmlAbstractStatement && stat.head.toString() == Refining.beginID) {
                    error(parser.context, stat.head, "jml.message", "Statement specs may not precede a JML statement clause");
                    return stat.head;
                }
                stats.addAll(stat);
            }
            if (ste.statementSpecs.cases.size() == 0) {
                Utils.instance(parser.context).warning(pos, "jml.message", "There are no refining specifications");
            }
            //ste.statements = parser.collectLoopSpecs(stats.toList()); // FIXME - does everything work before a loop spec + statement?
            ste.statements = stats.toList();
            checkStats(parser.context, ste.statements);
            return ste;
        }
        
        // FIXME - review this test -- an empty block might be OK, but end of block is not
        protected void checkStats(Context context, List<JCStatement> stats) {
            JCStatement st = firstStat(stats);
            if (st instanceof JCTree.JCBreak || st instanceof JCTree.JCContinue || st instanceof JCTree.JCThrow || st instanceof JCTree.JCReturn) {
                error(context, st, "jml.message", "A statement specification cannot be applied to this statement: " + st);
            }
        }
        
        protected JCStatement firstStat(List<JCStatement> stats) {
            if (stats.head == null) return null;
            for (JCStatement st: stats) {
                if (st instanceof JCTree.JCBlock bl) {
                    var stt = firstStat(bl.stats);
                    if (stt != null) return stt;
                }
                return st;
            }
            return null;
        }

        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }

    }
}
