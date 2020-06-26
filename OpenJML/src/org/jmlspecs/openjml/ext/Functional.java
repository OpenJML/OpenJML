/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import java.util.Iterator;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeVariableSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Names;

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
public class Functional extends ExpressionExtension {

    public Functional(Context context) {
        super(context);
    }
    
    static public class FunctionalKinds extends IJmlClauseKind.FunctionLikeExpressionKind {
        public FunctionalKinds(String keyword) {
            super(keyword);
        }
        
        @Override
        public void checkParse(JmlParser parser, JmlMethodInvocation e) {
            checkNumberArgs(parser, e, (n)->(n>0), "jml.message", "A " + keyword + " expression must have at least one argument");
        }

        // Returns null if 0 or more than one methods are abstract and not default,
        // otherwise returns the one abstract, non-default method
        protected MethodSymbol findFunctional(Type cl) {
            MethodSymbol result = null;
            for (Symbol s: cl.tsym.getEnclosedElements()) {
                if (!(s instanceof MethodSymbol)) continue;
                if ((s.flags() & Flags.ABSTRACT) == 0) continue;
                if ((s.flags() & Flags.DEFAULT) != 0) continue;
                // Also not static or final, but then the method can't be abstract
                if (result != null) {
                    return null;
                }
                result = (MethodSymbol)s;
            }
            return result;
        }
        
        protected Type resolve(Type t, Type cl) {
            if (t instanceof TypeVar) {
                Iterator<TypeVariableSymbol> tp = cl.tsym.getTypeParameters().iterator();
                Iterator<Type> tptypes = cl.getTypeArguments().iterator();
                while (tp.hasNext()) {
                    TypeVariableSymbol tsym = tp.next();
                    Type tt = tptypes.next();
                    if (t.tsym == tsym) {
                        return tt;
                    }
                }
                
            }
            return t;
        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> localEnv) {
            JmlMethodInvocation tree = (JmlMethodInvocation)expr;
            IJmlClauseKind kind = tree.kind;
            JmlTypes jmltypes = JmlTypes.instance(context);
            {
                    // Arbitrary number of arguments. The first argument
                    // is a Functional interface; the rest have to agree
                    // with its formal arguments.
                    if (tree.args.size() == 0) {
                        error(tree, kind.name() + " must have at least one argument");
                    }
                    ListBuffer<Type> argtypesBuf = new ListBuffer<>();
                    attr.attribArgs(tree.args, localEnv, argtypesBuf);
                    Type func = argtypesBuf.first();
                    MethodSymbol msym = findFunctional(func);
                    if (msym == null) {
                        error(tree.args.head, "Argument is not a functional");
                    } else {
                        int nn = msym.params().size() + 1;
                        if (kind == ensuresExprKind) ++nn;
                        if (nn != tree.args.size()) {
                            error(tree, "jml.message", "Expected " + nn + " arguments, not " + tree.args.size());
                        }
                        Iterator<Type> iter = argtypesBuf.iterator(); iter.next();
                        Iterator<VarSymbol> viter = msym.params().iterator();
                        int n = 1;
                        if (kind == ensuresExprKind) {
                            // Must match the return type
                            Type t = iter.next();
                            Type returnType = resolve(msym.getReturnType(), func);
                            if (!jmltypes.isSameType(t, returnType)) {
                                error(tree.args.get(n), "jml.message", "Second argument must match return type: " + t + " vs. " + returnType);
                            }
                            ++n;
                        }
                        while (iter.hasNext()) {
                            Type t = iter.next();
                            VarSymbol vs = viter.next();
                            Type paramType = resolve(vs.type, func);
                            if (!jmltypes.isSameType(t, paramType)) {
                                error(tree.args.get(n), "jml.message", "Argument types do not match: " + t + " vs. " + paramType);
                            }
                            ++n;
                        }
                    }
                    if (kind == requiresExprKind || kind == ensuresExprKind) return Symtab.instance(context).booleanType;
                    else return locset().type;
            }
        }
        
        private ClassSymbol _locset = null;
        
        private ClassSymbol locset() {
            if (_locset == null) _locset = ClassReader.instance(context).loadClass(Names.instance(context).fromString("org.jmlspecs.openjml.locset"));
            return _locset;
        }

    };
    static public final String bsrequiresID = "\\requires";
    static public final String bsensuresID = "\\ensures";
    static public final String bsreadsID = "\\reads";
    static public final String bswritesID = "\\writes";
    static public final IJmlClauseKind requiresExprKind = new FunctionalKinds(bsrequiresID);
    static public final IJmlClauseKind ensuresExprKind = new FunctionalKinds(bsensuresID);
    static public final IJmlClauseKind readsExprKind = new FunctionalKinds(bsreadsID);
    static public final IJmlClauseKind writesExprKind = new FunctionalKinds(bswritesID);
    

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr,
            Env<AttrContext> env) {
        // TODO Auto-generated method stub
        return null;
    }
    
    public void register() {
        synonym("\\assigns",writesExprKind);
    }

}
