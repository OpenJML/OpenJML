/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.source.tree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeCopier;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

/** This class extends TreeCopier to JML nodes.  It simply makes a deep copy of
 * the tree, including JML nodes and specs, without changing it.  CAUTION: Any 
 * new AST nodes or change to the fields of an AST node will require changes to
 * this code.
 * <P>
 * This copier does not copy type information or sym information (it does copy
 * class and method syms, since these are assigned in class and member Enter).
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
// 

public class JmlTreeCopierNoTypes extends TreeCopier<Void> implements JmlTreeVisitor<JCTree,Void> {
    
    protected Context context;
    
    /** The factory to be used to make new nodes */
    protected JmlTree.Maker M;
    
    /** Creates a new copier, whose new nodes are generated from the given factory*/
    protected JmlTreeCopierNoTypes(Context context, JmlTree.Maker maker) {
        super(maker);
        this.M = maker;
        this.context = context;
    }
    
    /** Static method to create a copy of the given AST with the given factory */
    public static <T extends JCTree> T copy(Context context, JmlTree.Maker maker, @Nullable T that) {
        return new JmlTreeCopier(context,maker).copy(that,null);  // FIXME - should use a factory
    }
    
    /** Deep copy of a list of nodes */
    public <T extends JCTree> ListBuffer<T> copy(@Nullable ListBuffer<T> trees, Void p) {
        if (trees == null)
            return null;
        ListBuffer<T> lb = new ListBuffer<T>();
        for (T tree: trees)
            lb.append(copy(tree, p));
        return lb;
    }


    
    public void visitTree(JCTree that) {
        // FIXME - proper error message
        Log.instance(context).error("log.internal","A node type is not implemented in JmlTreeCopier: " + that.getClass());
    }
    

    public JCTree visitJmlCompilationUnit(JmlCompilationUnit that, Void p) {
        JmlCompilationUnit copy = (JmlCompilationUnit)super.visitCompilationUnit(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsCompilationUnit = that == that.specsCompilationUnit ? copy : copy(that.specsCompilationUnit);
        copy.mode = that.mode;
        copy.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes; // FIXME - copy
        copy.specsTopLevelModelTypes = that.specsTopLevelModelTypes;// FIXME - copy
        copy.type = that.type;
        return copy;
    }
    
    public JCTree visitJmlChoose(JmlChoose that, Void p) {
        // FIXME - needs implementation
        return null;
    }

    public JCTree visitJmlClassDecl(JmlClassDecl that, Void p) {
        JmlClassDecl copy = (JmlClassDecl)super.visitClass(that,p);
        copy.toplevel.sourcefile = that.source();
        copy.specsDecls = that.specsDecls;// FIXME - copy
        copy.typeSpecs = that.typeSpecs;// FIXME - copy
        copy.typeSpecsCombined = that.typeSpecsCombined;// FIXME - copy
        copy.type = that.type;
        return copy;
    }

    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)super.visitMethod(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;// FIXME - copy
        copy.cases = copy(that.cases,p);
        copy.methodSpecsCombined = new JmlSpecs.MethodSpecs( // FIXME - factory
                copy(that.methodSpecsCombined.mods,p),
                copy(that.methodSpecsCombined.cases,p));
        copy.type = that.type;
        return copy;
    }

    public JCTree visitJmlVariableDecl(JmlVariableDecl that, Void p) {
        JmlVariableDecl copy = (JmlVariableDecl)super.visitVariable(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl; // FIXME - repoint to new reference?
        copy.fieldSpecs = (that.fieldSpecs);// FIXME - copy
        copy.fieldSpecsCombined = (that.fieldSpecsCombined); // FIXME - need copy
        return copy;
    }

    @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        JCExpression lhs = copy(that.lhs,p);
        JCExpression rhs = copy(that.rhs,p);
        JmlBinary r = M.at(that.pos).JmlBinary(that.op,lhs,rhs);
        return r;
    }
    
    @Override
    public JCTree visitJmlConstraintMethodSig(JmlConstraintMethodSig that,
            Void p) {
        return M.at(that.pos).JmlConstraintMethodSig(
                copy(that.expression,p),
                copy(that.argtypes,p));
    }

    @Override
    public JCTree visitJmlDoWhileLoop(JmlDoWhileLoop that, Void p) {
        JmlDoWhileLoop r = M.at(that.pos).JmlDoWhileLoop(
                (JCDoWhileLoop)this.visitDoWhileLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        return r;
    }

    @Override
    public JCTree visitJmlEnhancedForLoop(JmlEnhancedForLoop that, Void p) {
        JmlEnhancedForLoop r = M.at(that.pos).JmlEnhancedForLoop(
                (JCEnhancedForLoop)this.visitEnhancedForLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        // FIXME - implementation, indexDecl, valuesDecl, iterDecl
        return r;
    }


    @Override
    public JCTree visitJmlForLoop(JmlForLoop that, Void p) {
        JmlForLoop r = M.at(that.pos).JmlForLoop(
                (JCForLoop)this.visitForLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        return r;
    }

    @Override
    public JCTree visitJmlGroupName(JmlGroupName that, Void p) {
        JmlGroupName r = M.at(that.pos).JmlGroupName(copy(that.selection,p));
        return r;
    }

    @Override
    public JCTree visitJmlImport(JmlImport that, Void p) {
        JmlImport copy = (JmlImport)visitImport(that,p);
        copy.isModel = that.isModel;
        // already done: copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlLblExpression(JmlLblExpression that, Void p) {
        return M.at(that.pos).JmlLblExpression(
                that.labelPosition,
                that.token,
                that.label,
                copy(that.expression,p));
    }
    
    // FIXME - missing copying end positions, here and probably elsewhere

    @Override
    public JCTree visitJmlMethodClauseCallable(JmlMethodClauseCallable that, Void p) {
        JmlMethodClauseCallable copy;
        if (that.keyword != null) {
            copy = M.at(that.pos).JmlMethodClauseCallable(that.keyword);
        } else {
            copy = M.at(that.pos).JmlMethodClauseCallable(copy(that.methodSignatures,p));
        }
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseConditional(JmlMethodClauseConditional that, Void p) {
        JmlMethodClauseConditional copy = M.at(that.pos).JmlMethodClauseConditional(
                that.token,
                copy(that.expression,p),
                copy(that.predicate,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseDecl(JmlMethodClauseDecl that, Void p) {
        JmlMethodClauseDecl copy = M.at(that.pos).JmlMethodClauseDecl(
                that.token,
                copy(that.decls,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        JmlMethodClauseExpr copy = M.at(that.pos).JmlMethodClauseExpr(
                that.token,
                copy(that.expression,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseGroup(JmlMethodClauseGroup that, Void p) {
        JmlMethodClauseGroup copy = M.at(that.pos).JmlMethodClauseGroup(
                copy(that.cases,p));
        copy.token = that.token;
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseSignals(JmlMethodClauseSignals that, Void p) {
        JmlMethodClauseSignals copy = M.at(that.pos).JmlMethodClauseSignals(
                that.token,
                copy(that.vardef,p),
                copy(that.expression,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that, Void p) {
        JmlMethodClauseSignalsOnly copy = M.at(that.pos).JmlMethodClauseSignalsOnly(
                that.token,
                copy(that.list,p));
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, Void p) {
        JmlMethodClauseStoreRef r = M.at(that.pos).JmlMethodClauseStoreRef(
                that.token,
                copy(that.list,p));
        r.sourcefile = that.sourcefile;
        return r;
    }

    @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        // Don't use visitMethodInvocation, since it is designed just to produce
        // JCMethodInvocation nodes.  Normal method calls are JCMethodInvocations;
        // only special JML functions (e.g. \\nonnullelements) are JmlMethodInvocation
        // nodes.
        // CAUTION: if JCMethodInvocation adds fields, they have to be added here
        JmlMethodInvocation copy = M.at(that.pos).JmlMethodInvocation(
                that.token,
                copy(that.args,p));
        copy.startpos = that.startpos;
        copy.label = that.label;
        copy.type = that.type;
        copy.meth = copy(that.meth,p);
        copy.typeargs = copy(that.typeargs,p);
        copy.varargsElement = that.varargsElement; // FIXME - copy?
        return copy;
    }

    @Override
    public JCTree visitJmlMethodSpecs(JmlMethodSpecs that, Void p) {
        JmlMethodSpecs copy = M.at(that.pos).JmlMethodSpecs(copy(that.cases,p));
        copy.impliesThatCases = copy(that.impliesThatCases,p);
        copy.forExampleCases = copy(that.forExampleCases,p);
        copy.type = that.type;
        // FIXME - decl desugared
        return copy;
    }

    @Override
    public JCTree visitJmlModelProgramStatement(JmlModelProgramStatement that,
            Void p) {
        return M.at(that.pos).JmlModelProgramStatement(copy(that.item,p));
    }

    @Override
    public JCTree visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, Void p) {
        return M.at(that.pos).JmlPrimitiveTypeTree(that.token);
    }

    @Override
    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        JmlQuantifiedExpr q =  M.at(that.pos).JmlQuantifiedExpr(
                that.op,
                copy(that.decls,p),
                copy(that.range,p),
                copy(that.value,p));
        q.racexpr = copy(that.racexpr);
        return q;
    }

    @Override
    public JCTree visitJmlSetComprehension(JmlSetComprehension that, Void p) {
        return M.at(that.pos).JmlSetComprehension(
                copy(that.newtype,p),
                copy(that.variable,p),
                copy(that.predicate,p));
    }

    @Override
    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        JmlSingleton r = M.at(that.pos).JmlSingleton(that.token);
        r.type = that.type;
        r.info = that.info;
        r.symbol = that.symbol;
        return r;
    }

    @Override
    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
        JmlSpecificationCase copy = M.at(that.pos).JmlSpecificationCase(
                copy(that.modifiers,p),
                that.code,
                that.token,
                that.also,
                copy(that.clauses,p));
        copy.block = copy(that.block,p);
        copy.sourcefile = that.sourcefile;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatement(JmlStatement that, Void p) {
        JmlStatement copy = M.at(that.pos).JmlStatement(
                that.token,
                copy(that.statement,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementDecls(JmlStatementDecls that, Void p) {
        JmlStatementDecls copy = M.at(that.pos).JmlStatementDecls(
                copy(that.list,p));
        copy.token = that.token;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementExpr(JmlStatementExpr that, Void p) {
        JmlStatementExpr copy = M.at(that.pos).JmlExpressionStatement(
                that.token,
                that.label,
                copy(that.expression,p));
        copy.optionalExpression = copy(that.optionalExpression,p);
        copy.associatedPos = that.associatedPos;
        //copy.line = that.line;
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementHavoc(JmlStatementHavoc that, Void p) {
        JmlStatementHavoc copy = M.at(that.pos).JmlHavocStatement(
                copy(that.storerefs,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementLoop(JmlStatementLoop that, Void p) {
        JmlStatementLoop copy = M.at(that.pos).JmlStatementLoop(
                that.token,
                copy(that.expression,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        return M.at(that.pos).JmlStatementSpec(
                copy(that.statementSpecs,p));
    }

    @Override
    public JCTree visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, Void p) {
        JmlStoreRefArrayRange copy = M.at(that.pos).JmlStoreRefArrayRange(
                copy(that.expression,p),
                copy(that.lo,p),
                copy(that.hi,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStoreRefKeyword(JmlStoreRefKeyword that, Void p) {
        JmlStoreRefKeyword copy = M.at(that.pos).JmlStoreRefKeyword(
                that.token);
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlStoreRefListExpression(JmlStoreRefListExpression that, Void p) {
        JmlStoreRefListExpression copy = M.at(that.pos).JmlStoreRefListExpression(
                that.token,
                copy(that.list,p));
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseConditional(JmlTypeClauseConditional that, Void p) {
        JmlTypeClauseConditional copy = M.at(that.pos).JmlTypeClauseConditional(
                copy(that.modifiers,p),
                that.token,
                copy(that.identifier,p),
                copy(that.expression,p));
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, Void p) {
        JmlTypeClauseConstraint copy = M.at(that.pos).JmlTypeClauseConstraint(
                copy(that.modifiers,p),
                copy(that.expression,p),
                copy(that.sigs,p));
        copy.token = that.token;
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseDecl(JmlTypeClauseDecl that, Void p) {
        JmlTypeClauseDecl copy = M.at(that.pos).JmlTypeClauseDecl(
                copy(that.decl,p));
        copy.token = that.token;
        copy.modifiers = copy(that.modifiers,p);
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseExpr(JmlTypeClauseExpr that, Void p) {
        JmlTypeClauseExpr copy = M.at(that.pos).JmlTypeClauseExpr(
                copy(that.modifiers,p),
                that.token,
                copy(that.expression,p));
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseIn(JmlTypeClauseIn that, Void p) {
        JmlTypeClauseIn copy = M.at(that.pos).JmlTypeClauseIn(
                copy(that.list,p));
        copy.token = that.token;
        copy.source = that.source;
        copy.modifiers = copy(that.modifiers,p);
        copy.parentVar = that.parentVar; // FIXME - does this need repointing to the new copy
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, Void p) {
        JmlTypeClauseInitializer copy = M.at(that.pos).JmlTypeClauseInitializer(
                that.token);
        copy.modifiers = copy(that.modifiers,p);
        copy.specs = copy(that.specs,p);
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseMaps(JmlTypeClauseMaps that, Void p) {
        JmlTypeClauseMaps copy = M.at(that.pos).JmlTypeClauseMaps(
                copy(that.expression,p),
                copy(that.list,p));
        copy.token = that.token;
        copy.modifiers = copy(that.modifiers,p);
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, Void p) {
        JmlTypeClauseMonitorsFor copy = M.at(that.pos).JmlTypeClauseMonitorsFor(
                copy(that.modifiers,p),
                copy(that.identifier,p),
                copy(that.list,p));
        copy.token = that.token;
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, Void p) {
        JmlTypeClauseRepresents copy = M.at(that.pos).JmlTypeClauseRepresents(
                copy(that.modifiers,p),
                copy(that.ident,p),
                that.suchThat,
                copy(that.expression,p));
        copy.token = that.token;
        copy.source = that.source;
        copy.type = that.type;
        return copy;
    }

    @Override
    public JCTree visitJmlWhileLoop(JmlWhileLoop that, Void p) {
        JmlWhileLoop r = M.at(that.pos).JmlWhileLoop(
                (JmlWhileLoop)this.visitWhileLoop(that,p),
                copy(that.loopSpecs,p));
        // already done: r.type = that.type;
        return r;
    }
    
    // We have to reimplement all the JCTree nodes because we want the type
    // information copied
    
    @Override
    public JCTree visitAnnotation(AnnotationTree node, Void p) {
        return super.visitAnnotation(node,p);
    }

    @Override
    public JCTree visitAssert(AssertTree node, Void p) {
        return super.visitAssert(node,p);
    }

    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        return super.visitAssignment(node,p);
    }

    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        JCTree t = super.visitCompoundAssignment(node,p);
        ((JCAssignOp)t).operator = ((JCAssignOp)node).operator;
        return t;
    }

    public JCTree visitBinary(BinaryTree node, Void p) {
        JCTree t = super.visitBinary(node,p);
        ((JCBinary)t).operator = ((JCBinary)node).operator;
        return t;
    }

    public JCTree visitBlock(BlockTree node, Void p) {
        JCTree t = super.visitBlock(node,p);
        ((JCBlock)t).endpos = ((JCBlock)node).endpos;
        return t;
    }

    public JCTree visitBreak(BreakTree node, Void p) {
        return super.visitBreak(node,p);
        // FIXME - need to repoint reference to target
    }

    public JCTree visitCase(CaseTree node, Void p) {
        return super.visitCase(node,p);
    }

    public JCTree visitCatch(CatchTree node, Void p) {
        return super.visitCatch(node,p);
    }

    public JCTree visitClass(ClassTree node, Void p) {
        JCTree t = super.visitClass(node,p);
        ((JCClassDecl)t).sym = ((JCClassDecl)node).sym;
        return t;
    }

    public JCTree visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        return super.visitConditionalExpression(node,p);
    }

    public JCTree visitContinue(ContinueTree node, Void p) {
        return super.visitContinue(node,p);
        // FIXME - need to repoint reference to target
    }

    public JCTree visitDoWhileLoop(DoWhileLoopTree node, Void p) {
        return super.visitDoWhileLoop(node,p);
    }

    public JCTree visitErroneous(ErroneousTree node, Void p) {
        return super.visitErroneous(node,p);
    }

    public JCTree visitExpressionStatement(ExpressionStatementTree node, Void p) {
        return super.visitExpressionStatement(node,p);
    }

    public JCTree visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
        return super.visitEnhancedForLoop(node,p);
    }

    public JCTree visitForLoop(ForLoopTree node, Void p) {
        return super.visitForLoop(node,p);
    }

    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        JCIdent id = (JCIdent)super.visitIdentifier(node,p);
        return id;
    }

    public JCTree visitIf(IfTree node, Void p) {
        return super.visitIf(node,p);
    }

    public JCTree visitImport(ImportTree node, Void p) {
        return super.visitImport(node,p);
    }

    public JCTree visitArrayAccess(ArrayAccessTree node, Void p) {
        return super.visitArrayAccess(node,p);
    }

    public JCTree visitLabeledStatement(LabeledStatementTree node, Void p) {
        return super.visitLabeledStatement(node,p);
    }

    public JCTree visitLiteral(LiteralTree node, Void p) {
        return super.visitLiteral(node,p);
    }

    public JCTree visitMethod(MethodTree node, Void p) {
        JCTree t = super.visitMethod(node,p);
        ((JCMethodDecl)t).sym = ((JCMethodDecl)node).sym;
        return t;
    }

    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        JCMethodInvocation copy = (JCMethodInvocation)super.visitMethodInvocation(node,p);
        copy.varargsElement = ((JCMethodInvocation)node).varargsElement; // FIXME - copy? - should be in super class
        return copy;
    }

    public JCTree visitModifiers(ModifiersTree node, Void p) {
        return super.visitModifiers(node,p);
    }

    public JCTree visitNewArray(NewArrayTree node, Void p) {
        return super.visitNewArray(node,p);
    }

    public JCTree visitNewClass(NewClassTree node, Void p) {
        return super.visitNewClass(node,p);
        // FIXME - does not copy constructor, varargsElement, constructorType
    }

    public JCTree visitParenthesized(ParenthesizedTree node, Void p) {
        return super.visitParenthesized(node,p);
    }

    public JCTree visitReturn(ReturnTree node, Void p) {
        return super.visitReturn(node,p);
    }

    public JCTree visitMemberSelect(MemberSelectTree node, Void p) {
        JCTree t = super.visitMemberSelect(node,p);
        return t;
    }

    public JCTree visitEmptyStatement(EmptyStatementTree node, Void p) {
        return super.visitEmptyStatement(node,p);
    }

    public JCTree visitSwitch(SwitchTree node, Void p) {
        return super.visitSwitch(node,p);
    }

    public JCTree visitSynchronized(SynchronizedTree node, Void p) {
        return super.visitSynchronized(node,p);
    }

    public JCTree visitThrow(ThrowTree node, Void p) {
        return super.visitThrow(node,p);
    }

    public JCTree visitCompilationUnit(CompilationUnitTree node, Void p) {
        return super.visitCompilationUnit(node,p);
        // FIXME - lots more stuff to copy: docCOmments, endPositions, flags, lineMap, namedImportScope, packge, sourcefile, starImportScope
    }

    public JCTree visitTry(TryTree node, Void p) {
        return super.visitTry(node,p);
    }

    public JCTree visitParameterizedType(ParameterizedTypeTree node, Void p) {
        return super.visitParameterizedType(node,p);
    }

    public JCTree visitArrayType(ArrayTypeTree node, Void p) {
        return super.visitArrayType(node,p);
    }

    public JCTree visitTypeCast(TypeCastTree node, Void p) {
        return super.visitTypeCast(node,p);
    }

    public JCTree visitPrimitiveType(PrimitiveTypeTree node, Void p) {
        return super.visitPrimitiveType(node,p);
    }

    public JCTree visitTypeParameter(TypeParameterTree node, Void p) {
        return super.visitTypeParameter(node,p);
    }

    public JCTree visitInstanceOf(InstanceOfTree node, Void p) {
        return super.visitInstanceOf(node,p);
    }

    public JCTree visitUnary(UnaryTree node, Void p) {
        JCTree t = super.visitUnary(node,p);
        ((JCUnary)t).operator = ((JCUnary)node).operator;
        return t;
    }

    public JCTree visitVariable(VariableTree node, Void p) {
        JCTree t = super.visitVariable(node,p);
        return t;
    }

    public JCTree visitWhileLoop(WhileLoopTree node, Void p) {
        return super.visitWhileLoop(node,p);
    }

    public JCTree visitWildcard(WildcardTree node, Void p) {
        return super.visitWildcard(node,p);
    }

    public JCTree visitOther(Tree node, Void p) {
        return super.visitOther(node,p);
    }
    
    @Override
    public JCTree visitJmlDeclassifyClause(JmlDeclassifyClause that, Void p) {
        JmlDeclassifyClause copy = M.at(that.pos).JmlDeclassifyClause(that.token, that.expression, that.policy);
        return copy;    
    }

    @Override
    public JCTree visitJmlLevelStatement(JmlLevelStatement that, Void p) {
        JmlLevelStatement copy = M.at(that.pos).JmlLevelStatement(that.token, that.level);
        return copy;
    }

    @Override
    public JCTree visitJmlChannelStatement(JmlChannelStatement that, Void p) {
        JmlChannelStatement copy = M.at(that.pos).JmlChannelStatement(that.token, that.level);
        return copy;
    }

}
