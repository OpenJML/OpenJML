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
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.TypeVar;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
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

    protected JmlTypes jmltypes;
    
    public Functional(Context context) {
        super(context);
        this.jmltypes = JmlTypes.instance(context);
        
    }
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.BSREQUIRES, JmlTokenKind.BSENSURES,
            JmlTokenKind.BSREADS, JmlTokenKind.BSWRITES,
            }; }
    
    @Override
    public IJmlClauseKind[] clauseTypes() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
//        checkOneArg(parser,e);
    }
    
    private ClassSymbol _locset = null;
    
    private ClassSymbol locset() {
        if (_locset == null) _locset = ClassReader.instance(context).loadClass(Names.instance(context).fromString("org.jmlspecs.openjml.locset"));
        return _locset;
    }
    
    // Returns null if 0 or more than one methods are abstract and not default,
    // otherwise returns the one abstract, non-default method
    private MethodSymbol findFunctional(Type cl) {
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
    
    private Type resolve(Type t, Type cl) {
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
    
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> localEnv) {
        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        JmlTokenKind token = tree.token;
        
        switch (token) {
            case BSREQUIRES:
            case BSENSURES:
            case BSWRITES:
            case BSREADS:
                // Arbitrary number of arguments. The first argument
                // is a Functional interface; the rest have to agree
                // with its formal arguments.
                if (tree.args.size() == 0) {
                    error(tree, token.toString() + " must have at least one argument");
                }
                ListBuffer<Type> argtypesBuf = new ListBuffer<>();
                attr.attribArgs(tree.args, localEnv, argtypesBuf);
                Type func = argtypesBuf.first();
                MethodSymbol msym = findFunctional(func);
                if (msym == null) {
                    error(tree.args.head, "Argument is not a functional");
                } else {
                    int nn = msym.params().size() + 1;
                    if (token == JmlTokenKind.BSENSURES) ++nn;
                    if (nn != tree.args.size()) {
                        error(tree, "jml.message", "Expected " + nn + " arguments, not " + tree.args.size());
                    }
                    Iterator<Type> iter = argtypesBuf.iterator(); iter.next();
                    Iterator<VarSymbol> viter = msym.params().iterator();
                    int n = 1;
                    if (token == JmlTokenKind.BSENSURES) {
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
                if (token == JmlTokenKind.BSREQUIRES || token == JmlTokenKind.BSENSURES) return syms.booleanType;
                else return locset().type;
//                // Expect one argument of any array type, result type is \TYPE
//                // The argument expression may contain JML constructs
//                ListBuffer<Type> argtypesBuf = new ListBuffer<>();
//                attr.attribArgs(tree.args, localEnv, argtypesBuf);
//                //attr.attribTypes(tree.typeargs, localEnv);
//                int n = tree.args.size();
//                if (n != 1) {  // FIXME _ incorrect for BSOLD
//                    error(tree.pos(),"jml.one.arg",token.internedName(),n);
//                }
//                Type t = syms.errType;
//                if (n > 0) {
//                    Type tt = tree.args.get(0).type;
//                    if (tt == jmltypes.TYPE) {
//                        t = jmltypes.TYPE;
//                    } else if (tree.args.get(0).type.tsym == syms.classType.tsym) {  // FIXME - syms.classType is a parameterized type which is not equal to the argumet (particularly coming from \\typeof - using tsym works, but we ought to figure this out
//                        t = syms.classType;
//                    } else {
//                        error(tree.args.get(0).pos(),"jml.elemtype.expects.classtype",tree.args.get(0).type.toString());
//                        t = jmltypes.TYPE;
//                    }
//                }
//                return t;
            default:
                error(tree.pos(), "jml.error", "Unimplemented backslash token type in Functional.typecheck: " + token);
                return null;
        }
    }

}
