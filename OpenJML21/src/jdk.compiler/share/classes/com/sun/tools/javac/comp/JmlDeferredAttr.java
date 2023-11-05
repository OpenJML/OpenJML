/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 * Reviewed: 2018-03-17
 */
package com.sun.tools.javac.comp;

import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTree.JmlLambda;
import org.jmlspecs.openjml.JmlTree.JmlSingleton;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;
import org.jmlspecs.openjml.visitors.IJmlVisitor;

import com.sun.tools.javac.comp.DeferredAttr.TypeDeclVisitor;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeCopier;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.tree.TreeScanner;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.util.Context;

public class JmlDeferredAttr extends DeferredAttr implements IJmlVisitor {

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
    
    Context context;

    private JmlDeferredAttr(Context context) {
        super(context);
        this.context = context;
    }
   
    // FIXME
//    // Overridden to use a JmlDeferredChecker
//    @Override
//    boolean isDeferred(Env<AttrContext> env, JCExpression expr) {
//        DeferredChecker dc = new JmlDeferredChecker(env);
//        dc.scan(expr);
//        return dc.result.isPoly();
//    }
    
    protected boolean hasTypeDeclaration(JCTree tree) { // OPENJML - private to protected
        TypeDeclVisitor typeDeclVisitor = new JmlTypeDeclVisitor();
        typeDeclVisitor.scan(tree);
        return typeDeclVisitor.result;
    }
    
    protected static class JmlTypeDeclVisitor extends TypeDeclVisitor implements IJmlVisitor {
    	
    	
    }


    
    // Overridden to use a JML copier
    protected TreeCopier<Void> makeCopier(TreeMaker make) {
        return new JmlTreeCopier(context,JmlTree.Maker.instance(context));
    }
    
    public void scan(JCTree that) {
        that.accept(attr);
        //result = attr.result;
    }
    
    // FIXME - this is likely not needed
    public void visitJmlSingleton(JmlSingleton that) {
    	scan(that);
    }

    // FIXME?
//    class JmlDeferredChecker extends DeferredChecker {
//
//        public JmlDeferredChecker(Env<AttrContext> env) {
//            super(env);
//        }
//        
//        // Overridden to handle JML function-like operators
//        @Override
//        public void visitApply(JCMethodInvocation tree) {
//            if (tree.meth != null) super.visitApply(tree);
//            else result = ArgumentExpressionKind.NO_POLY;
//            return;
//        }
//
//        // FIXME - motivate this override
//        protected boolean isSimpleReceiver(JCTree rec) {
//            if (rec.getTag() == JCTree.Tag.NO_TAG) return true;
//            return super.isSimpleReceiver(rec);
//        }
//        
//    }
}
