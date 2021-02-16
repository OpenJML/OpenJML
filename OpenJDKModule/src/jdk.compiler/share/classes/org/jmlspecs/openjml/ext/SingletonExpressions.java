/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;


import org.jmlspecs.openjml.Extensions;
import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
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
public class SingletonExpressions extends ExpressionExtension {

    protected JmlTypes jmltypes;

    public SingletonExpressions(Context context) {
        super(context);
        this.jmltypes = JmlTypes.instance(context);
    }

    public static final String resultID ="\\result";
    public static final IJmlClauseKind resultKind = new IJmlClauseKind.SingletonExpressionKind(resultID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            JCTree.JCMethodDecl md = attr.enclosingMethodEnv.enclMethod;
            JCTree res = md.getReturnType();
            Type t;
            if (res == null || (!res.type.isErroneous() && JmlTypes.instance(context).isSameType(res.type,syms.voidType))) {
                Log.instance(context).error(that.pos+1, "jml.void.result");
                t = syms.errType;
            } else {
                t = res.type;
            }
            if (attr.currentEnvLabel != null) {
                Log.instance(context).error(that.pos, "jml.no.result.in.old");
            }
            if (!attr.resultClauses.contains(attr.currentClauseType)) {
                // The +1 is to fool the error reporting mechanism into 
                // allowing other error reports about the same token
                Log.instance(context).error(that.pos+1, "jml.misplaced.result", attr.currentClauseType.name());
                t = syms.errType;
            }
            return t;
        }
    };

    
    public static final String elseID = "\\else";
    public static final IJmlClauseKind elseKind = new IJmlClauseKind.SingletonExpressionKind(elseID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            return syms.booleanType;
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            if (this == elseKind) strictCheck(parser, e);
        }
    };
    
    public static final String countID = "\\count";
    public static final IJmlClauseKind countKind = new IJmlClauseKind.SingletonExpressionKind(countID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            Type t = syms.intType;
            if (attr.loopStack.isEmpty()) {
                Log.instance(context).error(that.pos,"jml.outofscope", name());
            } else {
                ((JmlSingleton)that).info = attr.loopStack.get(0).sym;
            }
            return t;
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            if (this == countKind) strictCheck(parser, e);
        }
    };
    
    public static final IJmlClauseKind indexKind = countKind;
    
    public static final String valuesID = "\\values";
    public static final IJmlClauseKind valuesKind = new IJmlClauseKind.SingletonExpressionKind(valuesID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            Type t = attr.JMLValuesType;
            if (attr.foreachLoopStack.isEmpty()) {
                Log.instance(context).error(that.pos,"jml.outofscope", name());
            } else {
                JCVariableDecl d = attr.foreachLoopStack.get(0).valuesDecl;
                if (d == null) {
                    Log.instance(context).error(that.pos,"jml.notforthisloop", name());
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
    public static final IJmlClauseKind informalCommentKind = new IJmlClauseKind.SingletonExpressionKind(informalCommentID) {
        
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
    public static final IJmlClauseKind exceptionKind = new IJmlClauseKind.SingletonExpressionKind(exceptionID) {
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            syms = Symtab.instance(context);
            Type t;
            if (!attr.exceptionClauses.contains(attr.currentClauseType)) {
                // The +1 is to fool the error reporting mechanism into 
                // allowing other error reports about the same token
                Log.instance(context).error(that.pos+1, "jml.misplaced.exception", attr.currentClauseType.name());
                t = syms.errType;
            } else {
                t = attr.currentExceptionType;
            }
            return t;
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlSingleton e, String rep) {
            strictCheck(parser, e);
        }
    };
    
    public static final String locksetID = "\\lockset";
    public static final IJmlClauseKind locksetKind = new IJmlClauseKind.SingletonExpressionKind(locksetID) {
        @Override
        public Type typecheck(JmlAttr attr, JCTree that, Env<AttrContext> localEnv) {
            return attr.JMLSetType;
        }
    };
    
    static {
        Extensions.allKinds.put("\\index", countKind);
    }

    // FIXME - eventually remove these
    
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> localEnv) {
        return null;
    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        // TODO Auto-generated method stub
        
    }
    
    public void register(Context context) {
        Extensions.allKinds.put("\\index", countKind);
        //Extensions.expressionKinds.put("\\index", countKind);
    }
}

