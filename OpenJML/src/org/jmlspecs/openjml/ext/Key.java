package org.jmlspecs.openjml.ext;

import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.JmlExpression;
import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.esc.JmlAssertionAdder;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

public class Key extends ExpressionExtension {
    
    public Key(Context context) {
        super(context);
    }
    
    static public JmlTokenKind[] tokens() { return new JmlTokenKind[]{
            JmlTokenKind.BSKEY}; }
    
    @Override
    public void checkParse(JmlParser parser, JmlMethodInvocation e) {
        checkOneArg(parser,e);
    }
    
    @Override
    public Type typecheck(JmlAttr attr, JCExpression expr,
            Env<AttrContext> localEnv) {
        JmlMethodInvocation tree = (JmlMethodInvocation)expr;
        JmlTokenKind token = tree.token;
        ListBuffer<Type> argtypesBuf = new ListBuffer<>();
        attr.attribArgs(tree.args, localEnv, argtypesBuf);
        // FIXME - check that argumentw are strings
        return syms.booleanType;
    }
    
    @Override
    public JCExpression assertion(JmlAssertionAdder adder, JCExpression that) {
        JmlMethodInvocation expr = (JmlMethodInvocation)that;
        boolean value = true;
        for (JCExpression arg: expr.args) {
            if (arg instanceof JCLiteral) {
                String key = ((JCLiteral)arg).getValue().toString();
                value = value && Utils.instance(context).commentKeys.contains(key);
            }
        }
        return adder.treeutils.makeBooleanLiteral(that.pos,value);
    }
    
}
