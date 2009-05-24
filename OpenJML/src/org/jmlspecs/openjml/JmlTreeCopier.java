package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.*;

import com.sun.source.tree.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeCopier;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.List;


public class JmlTreeCopier extends TreeCopier<Void> implements JmlTreeVisitor<JCTree,Void> {
    protected JmlTree.Maker M;
    
    JmlTreeCopier(JmlTree.Maker maker) {
        super(maker);
        this.M = maker;
    }
    
    public static <T extends JCTree> T copy(JmlTree.Maker maker, T that) {
        return new JmlTreeCopier(maker).copy(that,null);
    }
    
    public void visitTree(JCTree that) {
        System.out.println("NOT IMPLEMENTED IN TREE COPY " + that.getClass());
    }
    

    //JAVA16 @Override
    public JCTree visitJmlBinary(JmlBinary that, Void p) {
        JCExpression lhs = copy(that.lhs,p);
        JCExpression rhs = copy(that.rhs,p);
        JmlBinary r = M.at(that.pos).JmlBinary(that.op,lhs,rhs);
        r.type = that.type;
        return r;
    }
    
    //JAVA16 @Override
    public JCTree visitJmlMethodInvocation(JmlMethodInvocation that, Void p) {
        List<JCExpression> args = copy(that.args, p);
        return M.at(that.pos).JmlMethodInvocation(that.token, args).setType(that.type);
    }


    //JAVA16 @Override
    public JCTree visitJmlDoWhileLoop(JmlDoWhileLoop that, Void p) {
        JmlDoWhileLoop r = M.at(that.pos).JmlDoWhileLoop((JCDoWhileLoop)this.visitDoWhileLoop(that,p),copy(that.loopSpecs,p));
        r.type = that.type;
        return r;
    }

    //JAVA16 @Override
    public JCTree visitJmlEnhancedForLoop(JmlEnhancedForLoop that, Void p) {
        JmlEnhancedForLoop r = M.at(that.pos).JmlEnhancedForLoop((JCEnhancedForLoop)this.visitEnhancedForLoop(that,p),copy(that.loopSpecs,p));
        r.type = that.type;
        return r;
    }


    //JAVA16 @Override
    public JCTree visitJmlForLoop(JmlForLoop that, Void p) {
        JmlForLoop r = M.at(that.pos).JmlForLoop((JCForLoop)this.visitForLoop(that,p),copy(that.loopSpecs,p));
        r.type = that.type;
        return r;
    }

//    public JCTree visitJmlFunction(JmlFunction that, Void p) {
//        JmlFunction r = M.at(that.pos).JmlFunction(that.token);
//        r.type = that.type;
//        return r;
//    }

    //JAVA16 @Override
    public JCTree visitJmlGroupName(JmlGroupName that, Void p) {
        JmlGroupName r = M.at(that.pos).JmlGroupName(copy(that.selection,p));
        r.type = that.type;
        return r;
    }

    //JAVA16 @Override
    public JCTree visitJmlImport(JmlImport that, Void p) {
        JmlImport r = M.at(that.pos).JmlImport(copy(that.qualid,p),that.staticImport,that.isModel);
        r.type = that.type;
        return r;
    }

    //JAVA16 @Override
    public JCTree visitJmlLblExpression(JmlLblExpression that, Void p) {
        return M.at(that.pos).JmlLblExpression(that.token,that.label,copy(that.expression)).setType(that.type);
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseAssignable(JmlMethodClauseStoreRef that, Void p) {
        JmlMethodClauseStoreRef r = M.at(that.pos).JmlMethodClauseStoreRef(that.token,copy(that.list,p));
        r.setType(that.type);
        r.sourcefile = that.sourcefile;
        return r;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseConditional(JmlMethodClauseConditional that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseDecl(JmlMethodClauseDecl that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseExpr(JmlMethodClauseExpr that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseGroup(JmlMethodClauseGroup that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodClauseSignals(JmlMethodClauseSignals that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    //JAVA16 @Override
    public JCTree visitJmlMethodSpecs(JmlMethodSpecs that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, Void p) {
        return M.at(that.pos).JmlPrimitiveTypeTree(that.token).setType(that.type);
    }

    public JCTree visitJmlQuantifiedExpr(JmlQuantifiedExpr that, Void p) {
        return M.at(that.pos).JmlQuantifiedExpr(that.op,copy(that.decls),copy(that.range),copy(that.predicate)).setType(that.type);
    }

    public JCTree visitJmlRefines(JmlRefines that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlSetComprehension(JmlSetComprehension that, Void p) {
        return M.at(that.pos).JmlSetComprehension(copy(that.newtype),copy(that.variable),copy(that.predicate)).setType(that.type);
    }

    public JCTree visitJmlSingleton(JmlSingleton that, Void p) {
        JmlSingleton r = M.at(that.pos).JmlSingleton(that.token);
        r.type = that.type;
        r.symbol = that.symbol;
        return r;
    }

    public JCTree visitJmlSpecificationCase(JmlSpecificationCase that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStatement(JmlStatement that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStatementDecls(JmlStatementDecls that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStatementExpr(JmlStatementExpr that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStatementLoop(JmlStatementLoop that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStatementSpec(JmlStatementSpec that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStoreRefKeyword(JmlStoreRefKeyword that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlStoreRefListExpression(JmlStoreRefListExpression that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseConditional(JmlTypeClauseConditional that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseDecl(JmlTypeClauseDecl that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseExpr(JmlTypeClauseExpr that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseIn(JmlTypeClauseIn that, Void p) {
        JmlTypeClauseIn copy = M.at(that.pos).JmlTypeClauseIn(copy(that.list));
        copy.token = that.token;
        copy.source = that.source;
        copy.modifiers = copy(that.modifiers);
        copy.parentVar = that.parentVar;
        return copy;
    }

    public JCTree visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseMaps(JmlTypeClauseMaps that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }

    public JCTree visitJmlWhileLoop(JmlWhileLoop that, Void p) {
        visitTree(that); // FIXME - implement
        return null;
    }
    
    // We have to reimplement all the JCTree nodes because we want the type
    // information copied
    
    @Override
    public JCTree visitAnnotation(AnnotationTree node, Void p) {
        return super.visitAnnotation(node,p).setType(((JCAnnotation)node).type);
    }

    @Override
    public JCTree visitAssert(AssertTree node, Void p) {
        return super.visitAssert(node,p).setType(((JCAssert)node).type);
    }

    @Override
    public JCTree visitAssignment(AssignmentTree node, Void p) {
        return super.visitAssignment(node,p).setType(((JCAssign)node).type);
    }

    public JCTree visitCompoundAssignment(CompoundAssignmentTree node, Void p) {
        return super.visitCompoundAssignment(node,p).setType(((JCAssignOp)node).type);
    }

    public JCTree visitBinary(BinaryTree node, Void p) {
        JCTree t = super.visitBinary(node,p).setType(((JCBinary)node).type);
        ((JCBinary)t).operator = ((JCBinary)node).operator;
        return t;
    }

    public JCTree visitBlock(BlockTree node, Void p) {
        return super.visitBlock(node,p).setType(((JCBlock)node).type);
    }

    public JCTree visitBreak(BreakTree node, Void p) {
        return super.visitBreak(node,p).setType(((JCBreak)node).type);
    }

    public JCTree visitCase(CaseTree node, Void p) {
        return super.visitCase(node,p).setType(((JCCase)node).type);
    }

    public JCTree visitCatch(CatchTree node, Void p) {
        return super.visitCatch(node,p).setType(((JCCatch)node).type);
    }

    public JCTree visitClass(ClassTree node, Void p) {
        return super.visitClass(node,p).setType(((JCClassDecl)node).type);
    }

    public JCTree visitConditionalExpression(ConditionalExpressionTree node, Void p) {
        return super.visitConditionalExpression(node,p).setType(((JCConditional)node).type);
    }

    public JCTree visitContinue(ContinueTree node, Void p) {
        return super.visitContinue(node,p).setType(((JCContinue)node).type);
    }

    public JCTree visitDoWhileLoop(DoWhileLoopTree node, Void p) {
        return super.visitDoWhileLoop(node,p).setType(((JCDoWhileLoop)node).type);
    }

    public JCTree visitErroneous(ErroneousTree node, Void p) {
        return super.visitErroneous(node,p).setType(((JCErroneous)node).type);
    }

    public JCTree visitExpressionStatement(ExpressionStatementTree node, Void p) {
        return super.visitExpressionStatement(node,p).setType(((JCExpressionStatement)node).type);
    }

    public JCTree visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
        return super.visitEnhancedForLoop(node,p).setType(((JCEnhancedForLoop)node).type);
    }

    public JCTree visitForLoop(ForLoopTree node, Void p) {
        return super.visitForLoop(node,p).setType(((JCForLoop)node).type);
    }

    public JCTree visitIdentifier(IdentifierTree node, Void p) {
        JCIdent id = (JCIdent)super.visitIdentifier(node,p).setType(((JCTree)node).type);
        id.sym = ((JCIdent)node).sym;
        return id;
    }

    public JCTree visitIf(IfTree node, Void p) {
        return super.visitIf(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitImport(ImportTree node, Void p) {
        return super.visitImport(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitArrayAccess(ArrayAccessTree node, Void p) {
        return super.visitArrayAccess(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitLabeledStatement(LabeledStatementTree node, Void p) {
        return super.visitLabeledStatement(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitLiteral(LiteralTree node, Void p) {
        return super.visitLiteral(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitMethod(MethodTree node, Void p) {
        return super.visitMethod(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitMethodInvocation(MethodInvocationTree node, Void p) {
        return super.visitMethodInvocation(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitModifiers(ModifiersTree node, Void p) {
        return super.visitModifiers(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitNewArray(NewArrayTree node, Void p) {
        return super.visitNewArray(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitNewClass(NewClassTree node, Void p) {
        return super.visitNewClass(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitParenthesized(ParenthesizedTree node, Void p) {
        return super.visitParenthesized(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitReturn(ReturnTree node, Void p) {
        return super.visitReturn(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitMemberSelect(MemberSelectTree node, Void p) {
        JCTree t = super.visitMemberSelect(node,p).setType(((JCTree)node).type);
        ((JCFieldAccess)t).sym = ((JCFieldAccess)node).sym;
        return t;
    }

    public JCTree visitEmptyStatement(EmptyStatementTree node, Void p) {
        return super.visitEmptyStatement(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitSwitch(SwitchTree node, Void p) {
        return super.visitSwitch(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitSynchronized(SynchronizedTree node, Void p) {
        return super.visitSynchronized(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitThrow(ThrowTree node, Void p) {
        return super.visitThrow(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitCompilationUnit(CompilationUnitTree node, Void p) {
        return super.visitCompilationUnit(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitTry(TryTree node, Void p) {
        return super.visitTry(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitParameterizedType(ParameterizedTypeTree node, Void p) {
        return super.visitParameterizedType(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitArrayType(ArrayTypeTree node, Void p) {
        return super.visitArrayType(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitTypeCast(TypeCastTree node, Void p) {
        return super.visitTypeCast(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitPrimitiveType(PrimitiveTypeTree node, Void p) {
        return super.visitPrimitiveType(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitTypeParameter(TypeParameterTree node, Void p) {
        return super.visitTypeParameter(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitInstanceOf(InstanceOfTree node, Void p) {
        return super.visitInstanceOf(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitUnary(UnaryTree node, Void p) {
        JCTree t = super.visitUnary(node,p).setType(((JCTree)node).type);
        ((JCUnary)t).operator = ((JCUnary)node).operator;
        return t;
    }

    public JCTree visitVariable(VariableTree node, Void p) {
        return super.visitVariable(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitWhileLoop(WhileLoopTree node, Void p) {
        return super.visitWhileLoop(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitWildcard(WildcardTree node, Void p) {
        return super.visitWildcard(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitOther(Tree node, Void p) {
        return super.visitOther(node,p).setType(((JCTree)node).type);
    }

    public JCTree visitJmlClassDecl(JmlClassDecl that, Void p) {
        JmlClassDecl copy = (JmlClassDecl)super.visitClass(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        copy.typeSpecs = that.typeSpecs;
        copy.type = that.type;
        return copy;
    }

    public JCTree visitJmlCompilationUnit(JmlCompilationUnit that, Void p) {
        JmlCompilationUnit copy = (JmlCompilationUnit)super.visitCompilationUnit(that,p);
        copy.sourcefile = that.sourcefile;
        copy.refinesClause = that.refinesClause;
        copy.specsSequence = that.specsSequence;
        copy.mode = that.mode;
        copy.parsedTopLevelModelTypes = that.parsedTopLevelModelTypes;
        copy.specsTopLevelModelTypes = that.specsTopLevelModelTypes;
        copy.type = that.type;
        return copy;
    }

    public JCTree visitJmlMethodDecl(JmlMethodDecl that, Void p) {
        JmlMethodDecl copy = (JmlMethodDecl)super.visitMethod(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        copy.methodSpecs = that.methodSpecs;
        copy.type = that.type;
        return copy;
    }

    public JCTree visitJmlVariableDecl(JmlVariableDecl that, Void p) {
        JmlVariableDecl copy = (JmlVariableDecl)super.visitVariable(that,p);
        copy.sourcefile = that.sourcefile;
        copy.specsDecl = that.specsDecl;
        copy.fieldSpecs = that.fieldSpecs;
        copy.sym = that.sym;
        copy.type = that.type;
        return copy;
    }

//    public JCTree visitAuxVarDSA(AuxVarDSA that, Void p) {
//        return that.copy();
//    }
//
//    public JCTree visitProgVarDSA(ProgVarDSA that, Void p) {
//        return that.copy();
//    }

}
