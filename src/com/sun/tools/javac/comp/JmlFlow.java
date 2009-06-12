package com.sun.tools.javac.comp;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.IJmlVisitor;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.Utils;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;

/**
 * This extends Flow to add flow checks to specifications.  Flow checks for:<BR>
 * uninitialized statements<BR>
 * assignments to final variables<BR>
 * unreachable statements<BR>
 * forward references<BR>
 * fall-through in cases<BR>
 * improper use of checked exceptions<BR>
 * exception never thrown in try<BR>
 * The JML additions just make sure that ghost fields, model methods and model classes
 * are visited by the flow tree walker.
 *
 * @author David Cok
 */  // FIXME - I think we need to implement the JML visit methods in order to do checks within JML expressions?
public class JmlFlow extends Flow implements IJmlVisitor {

    /** Registers a singleton factory for JmlFlow against the flowKey, so that there is
     * just one instance per context.
     * @param context the context in which to register the instance
     */
    public static void preRegister(final Context context) {
        context.put(Flow.flowKey, new Context.Factory<Flow>() {
            public Flow make() { 
                return new JmlFlow(context);
            }
        });
    }
    
    /** Returns the instance for the given context
     * 
     * @param context the context in which we are working
     * @return the non-null instance of JmlAttr for this context
     */
    public static JmlFlow instance(Context context) {
        Flow instance = context.get(flowKey); 
        if (instance == null)
            instance = new JmlFlow(context); // Registers itself in the super constructor
        return (JmlFlow)instance; // If the registered instance is only a Flow, something is catastrophically wrong
    }
    
    /** The compilation context of this instance */
    protected Context context;
    
    /** A constructor, but use instance() to generate new instances of this class. */
    protected JmlFlow(Context context) {
        super(context);
        this.context = context;
    }
    
    /** Overridden to be sure that ghost/model declarations within the class are
     * visited by the flow checker.
     */
    @Override
    public void visitClassDef(JCClassDecl tree) {
        super.visitClassDef(tree);
    }
    
    @Override
    public void moreClassDef(JCClassDecl tree) {
        if (tree.sym == null) return;
        if (Utils.instance(context).isInstrumented(tree.mods.flags)) return;
        JmlSpecs.TypeSpecs tspecs = JmlSpecs.instance(context).get(tree.sym);
        if (tspecs == null) return;
        
        JavaFileObject prev = Log.instance(context).currentSourceFile();
        try {
            for (JmlTypeClause c : tspecs.clauses) {
                if (c instanceof JmlTypeClauseDecl) {
                    JCTree d = ((JmlTypeClauseDecl)c).decl;
                    Log.instance(context).useSource(c.source());
                    if (c.modifiers != null && (c.modifiers.flags & Flags.SYNTHETIC) != 0) {
                        continue;
                    }
                    d.accept(this);
                }
            }
        } finally {
            Log.instance(context).useSource(prev);
        }
    }
    
    // FIXME - document better why this is here
    // is tree.meth null for some JML constructs?
    @Override
    public void visitApply(JCMethodInvocation tree) {
        if (tree.meth == null) return;
        if (tree.meth.type == null) {
            // FIXME - need to do this just because we don't have full attribution in trEnhancedForLoop
            scanExpr(tree.meth);
            scanExprs(tree.args);
        } else {
            super.visitApply(tree);
        }
        // Ignore JML functions (FIXME - should we make this a JmlTreeScanner and do lots more checks?)
    }

    //JAVA16 @Override
    public void visitJmlBinary(JmlBinary that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // TODO Auto-generated method stub
        visitClassDef(that);
    }

    //JAVA16 @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        // TODO Auto-generated method stub
        visitTopLevel(that);
    }

    //JAVA16 @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        // TODO Auto-generated method stub
        visitDoLoop(that);
    }

    //JAVA16 @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        // TODO Auto-generated method stub
        visitForeachLoop(that);
    }

    //JAVA16 @Override
    public void visitJmlForLoop(JmlForLoop that) {
        // TODO Auto-generated method stub
        visitForLoop(that);
    }

    //JAVA16 @Override
    public void visitJmlGroupName(JmlGroupName that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlImport(JmlImport that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        // TODO Auto-generated method stub
        visitMethodDef(that);
    }

    //JAVA16 @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // TODO Auto-generated method stub
        visitApply(that);
    }

    //JAVA16 @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlRefines(JmlRefines that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlSingleton(JmlSingleton that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStatement(JmlStatement that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        // TODO Auto-generated method stub
        
    }

    //JAVA16 @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        // TODO Auto-generated method stub
        visitVarDef(that);
    }

    //JAVA16 @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        // TODO Auto-generated method stub
        visitWhileLoop(that);
    }
}