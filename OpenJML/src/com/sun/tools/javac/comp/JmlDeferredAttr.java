package com.sun.tools.javac.comp;

import com.sun.tools.javac.comp.DeferredAttr.ArgumentExpressionKind;
import com.sun.tools.javac.comp.DeferredAttr.DeferredChecker;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.util.Context;

public class JmlDeferredAttr extends DeferredAttr {

    public static void preRegister(final Context context) {
        context.put(deferredAttrKey, new Context.Factory<DeferredAttr>() {
            public DeferredAttr make(Context context) {
                return new JmlDeferredAttr(context); // Registers itself on construction
            }
        });
    }

    public static DeferredAttr instance(Context context) {
        DeferredAttr instance = context.get(deferredAttrKey);
        if (instance == null)
            instance = new JmlDeferredAttr(context);
        return instance;
    }

    private JmlDeferredAttr(Context context) {
        super(context);
    }
    
    @Override
    boolean isDeferred(Env<AttrContext> env, JCExpression expr) {
        DeferredChecker dc = new JmlDeferredChecker(env);
        dc.scan(expr);
        return dc.result.isPoly();
    }
    
    class JmlDeferredChecker extends DeferredChecker {

        public JmlDeferredChecker(Env<AttrContext> env) {
            super(env);
        }
        
        @Override
        public void visitApply(JCMethodInvocation tree) {
            if (tree.meth != null) super.visitApply(tree);
            result = ArgumentExpressionKind.NO_POLY;
            return;
        }


    }
}
