/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.DefaultJmlTokenKind;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Kinds;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.ExpressionExtension;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

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
public class Elemtype extends ExpressionExtension {

    protected JmlTypes jmltypes;
    
    public Elemtype(Context context) {
        super(context);
        this.jmltypes = JmlTypes.instance(context);
        
    }
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            DefaultJmlTokenKind.BSELEMTYPE, DefaultJmlTokenKind.BSTYPEOF,
            DefaultJmlTokenKind.BSOLD, DefaultJmlTokenKind.BSPAST, DefaultJmlTokenKind.BSPRE, DefaultJmlTokenKind.BSNOWARN, DefaultJmlTokenKind.BSNOWARNOP,
            DefaultJmlTokenKind.BSPOST, DefaultJmlTokenKind.BSASSIGNS,
            DefaultJmlTokenKind.BSWARN, DefaultJmlTokenKind.BSWARNOP}; }
    
    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
//        checkOneArg(parser,e);
    }
    
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> localEnv) {
        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        JmlTokenKind token = tree.token;
        
        switch ((DefaultJmlTokenKind) token) {
            case BSELEMTYPE:
                // Expect one argument of any array type, result type is \TYPE
                // The argument expression may contain JML constructs
                ListBuffer<Type> argtypesBuf = new ListBuffer<>();
                attr.attribArgs(tree.args, localEnv, argtypesBuf);
                //attr.attribTypes(tree.typeargs, localEnv);
                int n = tree.args.size();
                if (n != 1) {  // FIXME _ incorrect for BSOLD
                    error(tree.pos(),"jml.one.arg",token.internedName(),n);
                }
                Type t = syms.errType;
                if (n > 0) {
                    Type tt = tree.args.get(0).type;
                    if (tt == jmltypes.TYPE) {
                        t = jmltypes.TYPE;
                    } else if (tree.args.get(0).type.tsym == syms.classType.tsym) {  // FIXME - syms.classType is a parameterized type which is not equal to the argumet (particularly coming from \\typeof - using tsym works, but we ought to figure this out
                        t = syms.classType;
                    } else {
                        error(tree.args.get(0).pos(),"jml.elemtype.expects.classtype",tree.args.get(0).type.toString());
                        t = jmltypes.TYPE;
                    }
                }
                return t;
            case BSPOST:
                // FIXME - need to check types
                return syms.booleanType;
            default:
                error(tree.pos(), "jml.error", "Unimplemented backslash token type in ElemType.typecheck: " + token);
                return null;
        }
    }

}
