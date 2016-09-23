/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;

import com.sun.tools.javac.code.JmlTypes;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.ExpressionExtension;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.util.Context;

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
public class Erasure extends ExpressionExtension {

    protected JmlTypes jmltypes;
    
    public Erasure(Context context) {
        super(context);
        this.jmltypes = JmlTypes.instance(context);
        
    }
    
    static public JmlToken[] tokens() { return new JmlToken[]{JmlToken.BSERASURE}; }
    
    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        checkOneArg(parser,e);
    }
    
    public Type typecheck(JmlAttr attr, JCExpression expr, Env<AttrContext> localEnv) {
        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        JmlToken token = tree.token;
        
        // Expect one argument of any array type, result type is \TYPE
        // The argument expression may contain JML constructs
        int n = tree.args.size();
        if (n != 1) {
            error(tree.pos(),"jml.wrong.number.args",token.internedName(),1,n);
        } else {
            JCExpression e = tree.args.get(0);
            if (e instanceof JmlMethodInvocation && ((JmlMethodInvocation)e).token == JmlToken.BSTYPELC) {
                ((JmlMethodInvocation)e).javaType = true;
            }
        }
        attr.attribArgs(tree.args, localEnv);
        attr.attribTypes(tree.typeargs, localEnv);
        Type t = syms.errType;
        if (n > 0) {
            Type tt = tree.args.get(0).type;
            if (tt == jmltypes.TYPE || tt == syms.classType) t = syms.classType; 
        }
        return t;
    }
    
}
