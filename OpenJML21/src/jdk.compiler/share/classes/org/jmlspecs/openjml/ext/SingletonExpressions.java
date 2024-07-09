/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;


import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.Utils;
import static org.jmlspecs.openjml.IJmlClauseKind.SingletonExpressionKind;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Log;

/** This class handles expression extensions that take an argument list of JCExpressions.
 * Even if there are constraints on the number of arguments, it
 * is more robust to accept all of them and then issue an error in the typechecker
 * if the number of arguments is wrong.
 * 
 * @author David Cok
 *
 */
public class SingletonExpressions extends JmlExtension {
	
    public static final String resultID ="\\result";
    public static final IJmlClauseKind resultKind = new SingletonExpressionKind(resultID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            JCTree.JCMethodDecl md = attr.jmlenv.enclosingMethodDecl;
            JCTree res = md.getReturnType();
            Type t;
            if (res == null || (!res.type.isErroneous() && JmlTypes.instance(attr.context).isSameType(res.type,attr.syms.voidType))) {
                Utils.instance(attr.context).error(that.pos+1, "jml.void.result");
                t = attr.syms.errType;
            } else {
                t = res.type;
            }
            if (attr.jmlenv.currentLabel != null) {
                Utils.instance(attr.context).error(that.pos, "jml.no.result.in.old");
            }
            if (!attr.resultClauses.contains(attr.jmlenv.currentClauseKind)) {
                // The +1 is to fool the error reporting mechanism into 
                // allowing other error reports about the same token
                Utils.instance(attr.context).error(that.pos+1, "jml.misplaced.result", attr.jmlenv.currentClauseKind.keyword());
                t = attr.syms.errType;
            }
            that.type = t;
            return t;
        }
    };

    
    public static final String elseID = "\\else";
    public static final IJmlClauseKind elseKind = new SingletonExpressionKind(elseID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return attr.syms.booleanType;
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            if (this == elseKind) strictCheck(parser, e);
        }
    };
    
    public static final String countID = "\\count";
    public static final IJmlClauseKind countKind = new SingletonExpressionKind(countID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {

            Type t = attr.syms.intType;
            if (attr.loopStack.isEmpty()) {
                Utils.instance(attr.context).error(that.pos,"jml.outofscope", keyword());
            } else {
                ((JmlSingleton)that).info = attr.loopStack.get(0).sym;
            }
            return t;
        }
    };
    
    public static final IJmlClauseKind indexKind = countKind;
    static {
        Extensions.allKinds.put("\\index", countKind);
    }
    
    
    public static final String valuesID = "\\values";
    public static final IJmlClauseKind valuesKind = new SingletonExpressionKind(valuesID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            Type t = attr.JMLValuesType;
            if (attr.foreachLoopStack.isEmpty()) {
                Utils.instance(attr.context).error(that.pos,"jml.outofscope", keyword());
            } else {
                JCVariableDecl d = attr.foreachLoopStack.get(0).valuesDecl;
                if (d == null) {
                    Log.instance(attr.context).error(that.pos,"jml.notforthisloop", keyword());
                } else {
                    ((JmlSingleton)that).info = d.sym;
                }
            }
            return t;
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            strictCheck(parser, e);
        }
    };
    
    public static final String informalCommentID = "(*...*)";
    public static final IJmlClauseKind informalCommentKind = new SingletonExpressionKind(informalCommentID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return Symtab.instance(attr.context).booleanType;
        }

        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            e.info = rep; // FIXME - probably a token too late
        }
    };
    
    public static final String exceptionID = "\\exception";
    public static final IJmlClauseKind exceptionKind = new SingletonExpressionKind(exceptionID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            Type t;
            if (!attr.exceptionClauses.contains(attr.jmlenv.currentClauseKind)) {
                // The +1 is to fool the error reporting mechanism into 
                // allowing other error reports about the same token
                Utils.instance(attr.context).error(that.pos+1, "jml.misplaced.exception", attr.jmlenv.currentClauseKind.keyword());
                t = attr.syms.errType;
            } else {
                t = attr.jmlenv.currentExceptionType;
            }
            return t;
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            strictCheck(parser, e);
        }
    };
    
    public static final String locksetID = "\\lockset";
    public static final IJmlClauseKind locksetKind = new SingletonExpressionKind(locksetID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return attr.JMLSetType;
        }
    };
    
    public static class LabelKind extends SingletonExpressionKind {
    	public LabelKind(String name) { super(name); }
        @Override
        public JCTree.JCExpression parse(JCTree.JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            init(parser);
//            IJmlClauseKind jt = parser.jmlTokenClauseKind();
            int p = parser.pos();
//            String stringRep = parser.getScanner().chars();
//            parser.nextToken();
//            if (parser.token().kind == TokenKind.LPAREN) {
//                return parser.syntaxError(p, null, "jml.no.args.allowed", jt.name());
//            } else {
//                JmlSingleton e = toP(parser.maker().at(p).JmlSingleton(jt));
//                e.kind = this;
//                checkParse(parser,e,stringRep);
//                return e;
//            }
            return parser.maker().at(p).Ident(parser.ident());
        }
       @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return null;
        }
    };
    public static final String preLabelID = "\\Pre";
    public static final LabelKind preLabelKind = new LabelKind(preLabelID);
    public static final String oldLabelID = "\\Old";
    public static final LabelKind oldLabelKind = new LabelKind(oldLabelID);
    public static final String hereLabelID = "\\Here";
    public static final LabelKind hereLabelKind = new LabelKind(hereLabelID);
}

