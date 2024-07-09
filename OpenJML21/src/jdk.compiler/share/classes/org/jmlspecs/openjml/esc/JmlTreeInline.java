/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.Map;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.ext.SingletonExpressions;
import org.jmlspecs.openjml.visitors.JmlTreeCopier;

import com.sun.source.tree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeCopier;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

import org.jmlspecs.openjml.*;


/** This class makes a copy of a tree, performing designated substitutions as
 * it copies; new copies of the expressions provided for substitution are made 
 * for each use; in addition all local variables (let, forall, ...) have new
 * declarations and new symbols declared and appropriately substituted in their
 * bodies. As in JmlTreeCopier, some kinds of nodes are not copied.
 * 
 * @author David Cok
 *
 */

// DESIGN NOTE: This class follows the design of TreeCopier, namely to create
// copies by using the factory and explicitly filling in the nodes that the
// factory methods do not initialize.  This is fragile against additions or
// removal of fields from AST nodes.
// Alternately we could have used clone methods, and let the AST classes themselves
// be responsible for copying themselves.  JCTree does define clone().  
// Using clone() would not have permitted using an alternate factory to create
// the copy of the tree (a piece of functionality we don't use), and it would be
// different from how TreeCopier is implemented.
// So we live with this design.

// FIXME - This class does not yet take care of the start and end position information;
// also links between declarations and symbols are not updated (e.g. the map from
// symbols to class declarations).  It may be the case that the AST will have to be 
// completely re-attributed and that it is not really possible to have copies
// of trees that really work

public class JmlTreeInline extends JmlTreeCopier {
    
    // inherits protected Context context;
    
    // inherits protected JmlTree.Maker M;
    
    protected Map<Object,JCExpression> replacements;
    
    protected JmlTreeUtils treeutils;
    
    protected JCIdent returnId;
    
    protected Name breakName;
    
    protected JmlLabeledStatement labelled;
    
    /** Creates a new copier, whose new nodes are generated from the given factory*/
    public JmlTreeInline(JmlTree.Maker maker, Map<Object,JCExpression> replacements, JCIdent returnId, Name breakName, JmlLabeledStatement labelled) {
        super(maker.context,maker);
        this.treeutils = JmlTreeUtils.instance(context);
        this.replacements = replacements;
        this.returnId = returnId;
        this.breakName = breakName;
        this.labelled = labelled;
    }
    
    
    public JCTree visitReturn(ReturnTree node, Void p) {
        ExpressionTree rv = node.getExpression();
        if (rv != null) {
            JCExpression e = (JCExpression)rv.accept(this, p);
            JCBreak br = M.Break(breakName);
            br.target = labelled;
            if (returnId != null) {
                JCStatement assign = M.Assignment(returnId.sym, e);
                return M.Block(0L, List.<JCStatement>of(assign,br));
            } else {
                return M.Block(0L, List.<JCStatement>nil());
            }
        } else {
            JCBreak br = M.Break(breakName);
            br.target = labelled;
            return M.Block(0L, List.<JCStatement>of(br));
        }
    }



    // Only a few expression nodes need changing
    
    @Override
    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        JCIdent oldid = (JCIdent)node;
        /*@nullable*/ JCExpression newexpr = replacements == null ? null : replacements.get(oldid.sym);
        if (newexpr == null) {
            JCIdent id = (JCIdent)super.visitIdentifier(node,p).setType(((JCTree)node).type);
            id.sym = ((JCIdent)node).sym;
            return id;
        } else {
            return copy(newexpr);
        } 
    }
    
    @Override
    public JCTree visitArrayAccess(ArrayAccessTree node, Void p) {
        if (node instanceof JmlBBArrayAccess) {
            JmlBBArrayAccess aa = (JmlBBArrayAccess)node;
            return new JmlBBArrayAccess(aa.arraysId, aa.indexed, aa.index, aa.pos, aa.type);
        } else {
            return super.visitArrayAccess(node,p).setType(((JCTree)node).type);
        }
    }
    
    // FIXME - do we need array assignment and field assignment ?
    @Override 
    public JCTree visitJmlRange(JmlRange that, Void p) {
    	throw new RuntimeException("JmlRange not implemented in TreeInline");
    }
    
    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        // for substitution \result
        if (that.kind == SingletonExpressions.resultKind) {
            /*@nullable*/ JCExpression newexpr = replacements.get(that.kind);
            if (newexpr != null) return copy(newexpr);
            else return super.visitJmlSingleton(that,  p);
        } else {
            return super.visitJmlSingleton(that, p);
        }
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        try {
            ListBuffer<JCVariableDecl> newdecls = new ListBuffer<JCVariableDecl>();
            for (JCVariableDecl decl: that.decls) {
                // Quantified expressions do not have initializers; if they did we would have to worry about
                // the order of copying the initializers and adding items to the replacements map
                JCVariableDecl newdecl = treeutils.makeVariableDecl(decl.name,  decl.type, null, decl.pos);
                JCIdent id = treeutils.makeIdent(that,newdecl.sym);
                replacements.put(decl.sym, id);
                newdecls.add(newdecl);
            }
            JmlQuantifiedExpr q =  M.at(that.pos).JmlQuantifiedExpr(
                    that.kind,
                    newdecls.toList(),
                    null,
                    null);
            q.range = copy(that.range,p);
            q.value = copy(that.value,p);
            q.triggers = copy(that.triggers);
            q.racexpr = copy(that.racexpr);
            q.setType(that.type);
            return q;
        } finally {
            for (JCVariableDecl decl: that.decls) {
                replacements.remove(decl.sym);
            }
        }
    }

    @Override
    public JCTree visitLetExpr(LetExpr that, Void p) {
    	return null; // FIXME
//        try {
//            ListBuffer<JCVariableDecl> newdecls = new ListBuffer<JCVariableDecl>();
//            ListBuffer<JCExpression> newinits = new ListBuffer<JCExpression>();
//
//            // The initializers are evaluated in the external scope,
//            // even if there are multiple declarations
//            for (JCVariableDecl decl: that.defs) {
//                JCExpression newinit = copy(decl.init,p);
//                newinits.add(newinit);
//            }
//            for (JCVariableDecl decl: that.defs) {
//                JCExpression newinit = newinits.next();
//                JCVariableDecl newdecl = treeutils.makeVariableDecl(decl.name,  decl.type, newinit, decl.pos);
//                JCIdent id = treeutils.makeIdent(that,newdecl.sym);
//                replacements.put(decl.sym, id);
//                newdecls.add(newdecl);
//            }
//            LetExpr q =  M.LetExpr(newdecls.toList(), null);
//            q.expr = copy(that.expr, p);
//            q.setType(that.type);
//            q.pos = that.pos;
//            return q;
//        } finally {
//            for (JCVariableDecl decl: that.defs) {
//                replacements.remove(decl.sym);
//            }
//        }
    }

    @Override
    public JCTree visitJmlSetComprehension(JmlSetComprehension that, Void p) {
        JCVariableDecl decl = that.variable;
        try {
            JCVariableDecl newdecl = treeutils.makeVariableDecl(decl.name,  decl.type, null, decl.pos);
            JCIdent id = treeutils.makeIdent(that,newdecl.sym);
            replacements.put(decl.sym,id);
            JmlSetComprehension set = 
                    M.JmlSetComprehension(
                            copy(that.newtype,p),
                            newdecl,
                            copy(that.predicate,p));
            set.setType(that.type);
            set.pos = that.pos; 
            return set;
        } finally {
            replacements.remove(decl.sym);
        }
    }


    
    
    // TODO - Only implemented for Expressions, so far not for statements
    // If we do whole programs, we also need to remap anything containing a
    // declaration (including loops), as well as statement labels.

    @Override
    public JCTree visitJmlVariableDecl(JmlVariableDecl that, Void p) {
        JmlVariableDecl copy = (JmlVariableDecl)super.visitVariable(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl; // FIXME - repoint to new reference?
        copy.fieldSpecs = (that.fieldSpecs);// FIXME - copy
//        copy.fieldSpecsCombined = (that.fieldSpecsCombined); // FIXME - need copy
        copy.sym = that.sym;
        copy.type = that.type;
        return copy;
    }


    @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        // Don't use visitMethodInvocation, since it is designed just to produce
        // JCMethodInvocation nodes.  Normal method calls are JCMethodInvocations;
        // only special JML functions (e.g. \\nonnullelements) are JmlMethodInvocation
        // nodes.
        // CAUTION: if JCMethodInvocation adds fields, they have to be added here
        JmlMethodInvocation copy = M.at(that.pos).JmlMethodInvocation(
                that.kind,
                copy(that.args,p));
        copy.name = that.name;
        copy.startpos = that.startpos;
        copy.labelProperties = that.labelProperties;
        copy.type = that.type;
        copy.meth = copy(that.meth,p);
        copy.typeargs = copy(that.typeargs,p);
        copy.varargsElement = that.varargsElement; // FIXME - copy?
        return copy;
    }


//
//    @Override
//    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
//        JmlSpecificationCase copy = M.at(that.pos).JmlSpecificationCase(
//                copy(that.modifiers,p),
//                that.code,
//                that.token,
//                that.also,
//                copy(that.clauses,p),
//                copy(that.block,p));
//        copy.sourcefile = that.sourcefile;
//        copy.type = that.type;
//        return copy;
//    }
//
////    @Override
//    public JCTree visitJmlStatement(JmlStatement that, Void p) {
//        JmlStatement copy = M.at(that.pos).JmlStatement(
//                that.token,
//                copy(that.statement,p));
//        copy.type = that.type;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlStatementDecls(JmlStatementDecls that, Void p) {
//        JmlStatementDecls copy = M.at(that.pos).JmlStatementDecls(
//                copy(that.list,p));
//        copy.token = that.token;
//        copy.type = that.type;
//        return copy;
//    }
//
//
//    @Override
//    public JCTree visitJmlStatementHavoc(JmlStatementHavoc that, Void p) {
//        JmlStatementHavoc copy = M.at(that.pos).JmlHavocStatement(
//                copy(that.storerefs,p));
//        copy.type = that.type;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlStatementLoop(JmlStatementLoop that, Void p) {
//        JmlStatementLoop copy = M.at(that.pos).JmlStatementLoop(
//                that.token,
//                copy(that.expression,p));
//        copy.type = that.type;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
//        return M.at(that.pos).JmlStatementSpec(
//                copy(that.statementSpecs,p)).setType(that.type);
//    }
//
//
//    @Override
//    public JCTree visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, Void p) {
//        JmlTypeClauseConstraint copy = M.at(that.pos).JmlTypeClauseConstraint(
//                copy(that.modifiers,p),
//                copy(that.expression,p),
//                copy(that.sigs,p));
//        copy.token = that.token;
//        copy.source = that.source;
//        copy.type = that.type;
//        copy.notlist = that.notlist;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlTypeClauseDecl(JmlTypeClauseDecl that, Void p) {
//        JmlTypeClauseDecl copy = M.at(that.pos).JmlTypeClauseDecl(
//                copy(that.decl,p));
//        copy.token = that.token;
//        copy.modifiers = copy(that.modifiers,p);
//        copy.source = that.source;
//        copy.type = that.type;
//        return copy;
//    }
//
//
//    @Override
//    public JCTree visitJmlTypeClauseIn(JmlTypeClauseIn that, Void p) {
//        JmlTypeClauseIn copy = M.at(that.pos).JmlTypeClauseIn(
//                copy(that.list,p));
//        copy.token = that.token;
//        copy.source = that.source;
//        copy.modifiers = copy(that.modifiers,p);
//        copy.parentVar = that.parentVar; // FIXME - does this need repointing to the new copy
//        copy.type = that.type;
//        return copy;
//    }
//

//    @Override
//    public JCTree visitJmlTypeClauseMaps(JmlTypeClauseMaps that, Void p) {
//        JmlTypeClauseMaps copy = M.at(that.pos).JmlTypeClauseMaps(
//                copy(that.expression,p),
//                copy(that.list,p));
//        copy.token = that.token;
//        copy.modifiers = copy(that.modifiers,p);
//        copy.source = that.source;
//        copy.type = that.type;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, Void p) {
//        JmlTypeClauseMonitorsFor copy = M.at(that.pos).JmlTypeClauseMonitorsFor(
//                copy(that.modifiers,p),
//                copy(that.identifier,p),
//                copy(that.list,p));
//        copy.token = that.token;
//        copy.source = that.source;
//        copy.type = that.type;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, Void p) {
//        JmlTypeClauseRepresents copy = M.at(that.pos).JmlTypeClauseRepresents(
//                copy(that.modifiers,p),
//                copy(that.ident,p),
//                that.suchThat,
//                copy(that.expression,p));
//        copy.token = that.token;
//        copy.source = that.source;
//        copy.type = that.type;
//        return copy;
//    }
//
//    @Override
//    public JCTree visitJmlWhileLoop(JmlWhileLoop that, Void p) {
//        JmlWhileLoop r = M.at(that.pos).JmlWhileLoop(
//                (JmlWhileLoop)this.visitWhileLoop(that,p),
//                copy(that.loopSpecs,p));
//        // already done: r.type = that.type;
//        return r;
//    }
    
//    // We have to reimplement all the JCTree nodes because we want the type
//    // information copied
//    
//    @Override
//    public JCTree visitAnnotation(AnnotationTree node, Void p) {
//        return super.visitAnnotation(node,p).setType(((JCAnnotation)node).type);
//    }
//
//    @Override
//    public JCTree visitAssert(AssertTree node, Void p) {
//        return super.visitAssert(node,p).setType(((JCAssert)node).type);
//    }
//
//
//    public JCTree visitDoWhileLoop(DoWhileLoopTree node, Void p) {
//        return super.visitDoWhileLoop(node,p).setType(((JCDoWhileLoop)node).type);
//    }
//
//
//    public JCTree visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
//        return super.visitEnhancedForLoop(node,p).setType(((JCEnhancedForLoop)node).type);
//    }
//
//    public JCTree visitForLoop(ForLoopTree node, Void p) {
//        return super.visitForLoop(node,p).setType(((JCForLoop)node).type);
//    }
//
//
//    public JCTree visitLabeledStatement(LabeledStatementTree node, Void p) {
//        return super.visitLabeledStatement(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitLiteral(LiteralTree node, Void p) {
//        return super.visitLiteral(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitMethod(MethodTree node, Void p) {
//        JCTree t = super.visitMethod(node,p).setType(((JCTree)node).type);
//        ((JCMethodDecl)t).sym = ((JCMethodDecl)node).sym;
//        return t;
//    }

    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        JCMethodInvocation copy = (JCMethodInvocation)super.visitMethodInvocation(node,p).setType(((JCTree)node).type);
        copy.varargsElement = ((JCMethodInvocation)node).varargsElement; // FIXME - copy? - should be in super class
        return copy;
    }

//    public JCTree visitModifiers(ModifiersTree node, Void p) {
//        return super.visitModifiers(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitNewArray(NewArrayTree node, Void p) {
//        return super.visitNewArray(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitNewClass(NewClassTree node, Void p) {
//        return super.visitNewClass(node,p).setType(((JCTree)node).type);
//        // FIXME - does not copy constructor, varargsElement, constructorType
//    }
//
//    public JCTree visitParenthesized(ParenthesizedTree node, Void p) {
//        return super.visitParenthesized(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitReturn(ReturnTree node, Void p) {
//        return super.visitReturn(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitMemberSelect(MemberSelectTree node, Void p) {
//        JCTree t = super.visitMemberSelect(node,p).setType(((JCTree)node).type);
//        ((JCFieldAccess)t).sym = ((JCFieldAccess)node).sym;
//        return t;
//    }
//
//    public JCTree visitEmptyStatement(EmptyStatementTree node, Void p) {
//        return super.visitEmptyStatement(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitSwitch(SwitchTree node, Void p) {
//        return super.visitSwitch(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitSynchronized(SynchronizedTree node, Void p) {
//        return super.visitSynchronized(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitThrow(ThrowTree node, Void p) {
//        return super.visitThrow(node,p).setType(((JCTree)node).type);
//    }
//
//
//    public JCTree visitParameterizedType(ParameterizedTypeTree node, Void p) {
//        return super.visitParameterizedType(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitArrayType(ArrayTypeTree node, Void p) {
//        return super.visitArrayType(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitTypeCast(TypeCastTree node, Void p) {
//        return super.visitTypeCast(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitPrimitiveType(PrimitiveTypeTree node, Void p) {
//        return super.visitPrimitiveType(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitTypeParameter(TypeParameterTree node, Void p) {
//        return super.visitTypeParameter(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitInstanceOf(InstanceOfTree node, Void p) {
//        return super.visitInstanceOf(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitVariable(VariableTree node, Void p) {
//        JCTree t = super.visitVariable(node,p).setType(((JCTree)node).type);
//        ((JCVariableDecl)t).sym = ((JCVariableDecl)node).sym;
//        return t;
//    }
//
//    public JCTree visitWhileLoop(WhileLoopTree node, Void p) {
//        return super.visitWhileLoop(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitWildcard(WildcardTree node, Void p) {
//        return super.visitWildcard(node,p).setType(((JCTree)node).type);
//    }
//
//    public JCTree visitOther(Tree node, Void p) {
//        return super.visitOther(node,p).setType(((JCTree)node).type);
//    }
}
