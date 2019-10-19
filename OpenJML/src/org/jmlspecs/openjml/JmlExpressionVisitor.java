/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.vistors.JmlTreeVisitor;

import com.sun.source.tree.*;

/**
 * This is an interface for visitors for JML Expression ASTs, with parameters and return 
 * types, as described in TreeVisitor.
 * 
 * @author David Cok
 * 
 * @param <R>
 *            the return type from the visitor methods
 * @param <P>
 *            the type of additional parameters (or Void)
 */
// TODO - TreeVisitor takes arguments that are interfaces, not specific node
// classes.  JmlExpressionVisitor should be modified to that model as well.
public abstract class JmlExpressionVisitor<R,P> implements JmlTreeVisitor<R,P> {

    public R shouldNotBeCalled(Object that) {
        throw new RuntimeException("visit class in JmlExpressionVisitor should not be called for " + that.getClass());
    }

    abstract public R visitMethodInvocation(MethodInvocationTree node, P p);
    abstract public R visitBinary(BinaryTree node, P p);
    abstract public R visitClass(ClassTree node, P p);
    abstract public R visitConditionalExpression(ConditionalExpressionTree node, P p);
    abstract public R visitErroneous(ErroneousTree node, P p);
    abstract public R visitIdentifier(IdentifierTree node, P p);
    abstract public R visitArrayAccess(ArrayAccessTree node, P p);
    abstract public R visitLiteral(LiteralTree node, P p);
    abstract public R visitNewArray(NewArrayTree node, P p);
    abstract public R visitNewClass(NewClassTree node, P p);
    abstract public R visitParenthesized(ParenthesizedTree node, P p);
    abstract public R visitMemberSelect(MemberSelectTree node, P p);
    abstract public R visitTypeCast(TypeCastTree node, P p);
    abstract public R visitInstanceOf(InstanceOfTree node, P p);
    abstract public R visitUnary(UnaryTree node, P p);
    abstract public R visitVariable(VariableTree node, P p);
    abstract public R visitLambdaExpression(LambdaExpressionTree node, P p);

    public R visitAnnotation(AnnotationTree node, P p)                                  { return shouldNotBeCalled(node); }
    public R visitAssert(AssertTree node, P p)                                          { return shouldNotBeCalled(node); }
    public R visitAssignment(AssignmentTree node, P p)                                  { return shouldNotBeCalled(node); }
    public R visitCompoundAssignment(CompoundAssignmentTree node, P p)                  { return shouldNotBeCalled(node); }
    public R visitBlock(BlockTree node, P p)                                            { return shouldNotBeCalled(node); }
    public R visitJmlBlock(BlockTree node, P p)                                         { return shouldNotBeCalled(node); }
    public R visitBreak(BreakTree node, P p)                                            { return shouldNotBeCalled(node); }
    public R visitCase(CaseTree node, P p)                                              { return shouldNotBeCalled(node); }
    public R visitCatch(CatchTree node, P p)                                            { return shouldNotBeCalled(node); }
    public R visitContinue(ContinueTree node, P p)                                      { return shouldNotBeCalled(node); }
    public R visitDoWhileLoop(DoWhileLoopTree node, P p)                                { return shouldNotBeCalled(node); }
    public R visitExpressionStatement(ExpressionStatementTree node, P p)                { return shouldNotBeCalled(node); }
    public R visitEnhancedForLoop(EnhancedForLoopTree node, P p)                        { return shouldNotBeCalled(node); }
    public R visitForLoop(ForLoopTree node, P p)                                        { return shouldNotBeCalled(node); }
    public R visitIf(IfTree node, P p)                                                  { return shouldNotBeCalled(node); }
    public R visitImport(ImportTree node, P p)                                          { return shouldNotBeCalled(node); }
    public R visitLabeledStatement(LabeledStatementTree node, P p)                      { return shouldNotBeCalled(node); }
    public R visitMethod(MethodTree node, P p)                                          { return shouldNotBeCalled(node); }
    public R visitModifiers(ModifiersTree node, P p)                                    { return shouldNotBeCalled(node); }
    public R visitReturn(ReturnTree node, P p)                                          { return shouldNotBeCalled(node); }
    public R visitEmptyStatement(EmptyStatementTree node, P p)                          { return shouldNotBeCalled(node); }
    public R visitSwitch(SwitchTree node, P p)                                          { return shouldNotBeCalled(node); }
    public R visitSynchronized(SynchronizedTree node, P p)                              { return shouldNotBeCalled(node); }
    public R visitThrow(ThrowTree node, P p)                                            { return shouldNotBeCalled(node); }
    public R visitCompilationUnit(CompilationUnitTree node, P p)                        { return shouldNotBeCalled(node); }
    public R visitTry(TryTree node, P p)                                                { return shouldNotBeCalled(node); }
    public R visitParameterizedType(ParameterizedTypeTree node, P p)                    { return shouldNotBeCalled(node); }
    public R visitUnionType(UnionTypeTree node, P p)                                    { return shouldNotBeCalled(node); }
    public R visitArrayType(ArrayTypeTree node, P p)                                    { return shouldNotBeCalled(node); }
    public R visitPrimitiveType(PrimitiveTypeTree node, P p)                            { return shouldNotBeCalled(node); }
    public R visitTypeParameter(TypeParameterTree node, P p)                            { return shouldNotBeCalled(node); }
    public R visitWhileLoop(WhileLoopTree node, P p)                                    { return shouldNotBeCalled(node); }
    public R visitWildcard(WildcardTree node, P p)                                      { return shouldNotBeCalled(node); }
    public R visitAnnotatedType(AnnotatedTypeTree node, P p)                            { return shouldNotBeCalled(node); }
    public R visitMemberReference(MemberReferenceTree node, P p)                        { return shouldNotBeCalled(node); }
    public R visitIntersectionType(IntersectionTypeTree node, P p)                      { return shouldNotBeCalled(node); }

    public R visitOther(Tree node, P p) { return shouldNotBeCalled(node); }
    
    abstract public R visitJmlBinary(JmlBinary that, P p)                     ;
    abstract public R visitJmlLblExpression(JmlLblExpression that, P p)       ;
    abstract public R visitJmlMethodInvocation(JmlMethodInvocation that, P p) ;
    abstract public R visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that, P p);
    abstract public R visitJmlQuantifiedExpr(JmlQuantifiedExpr that, P p)     ;
    abstract public R visitJmlSetComprehension(JmlSetComprehension that, P p) ;
    abstract public R visitJmlSingleton(JmlSingleton that, P p)               ;
    abstract public R visitJmlNewClass(JmlNewClass that, P p)                 ;

    public R visitJmlChoose(JmlChoose that, P p)                                        { return shouldNotBeCalled(that); }
    public R visitJmlClassDecl(JmlClassDecl that, P p)                                  { return shouldNotBeCalled(that); }
    public R visitJmlCompilationUnit(JmlCompilationUnit that, P p)                      { return shouldNotBeCalled(that); }
    public R visitJmlConstraintMethodSig(JmlMethodSig that, P p)                        { return shouldNotBeCalled(that); }  
    public R visitJmlDoWhileLoop(JmlDoWhileLoop that, P p)                              { return shouldNotBeCalled(that); }
    public R visitJmlEnhancedForLoop(JmlEnhancedForLoop that, P p)                      { return shouldNotBeCalled(that); }
    public R visitJmlForLoop(JmlForLoop that, P p)                                      { return shouldNotBeCalled(that); }
    public R visitJmlGroupName(JmlGroupName that, P p)                                  { return shouldNotBeCalled(that); }
    public R visitJmlImport(JmlImport that, P p)                                        { return shouldNotBeCalled(that); }
    public R visitJmlnlinedLoop(JmlInlinedLoop that, P p)                               { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseCallable(JmlMethodClauseCallable that, P p)            { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseConditional(JmlMethodClauseConditional that, P p)      { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseDecl(JmlMethodClauseDecl that, P p)                    { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseExpr(JmlMethodClauseExpr that, P p)                    { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseGroup(JmlMethodClauseGroup that, P p)                  { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseSignals(JmlMethodClauseSignals that, P p)              { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that, P p)          { return shouldNotBeCalled(that); }
    public R visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that, P p)            { return shouldNotBeCalled(that); }
    public R visitJmlMethodDecl(JmlMethodDecl that, P p)                                { return shouldNotBeCalled(that); }
    public R visitJmlMethodSpecs(JmlMethodSpecs that, P p)                              { return shouldNotBeCalled(that); }
    public R visitJmlModelProgramStatement(JmlModelProgramStatement that, P p)          { return shouldNotBeCalled(that); }
    public R visitJmlSpecificationCase(JmlSpecificationCase that, P p)                  { return shouldNotBeCalled(that); }
    public R visitJmlStatement(JmlStatement that, P p)                                  { return shouldNotBeCalled(that); }
    public R visitJmlStatementShow(JmlStatementShow that, P p)                          { return shouldNotBeCalled(that); }
    public R visitJmlStatementDecls(JmlStatementDecls that, P p)                        { return shouldNotBeCalled(that); }
    public R visitJmlStatementExpr(JmlStatementExpr that, P p)                          { return shouldNotBeCalled(that); }
    public R visitJmlStatementHavoc(JmlStatementHavoc that, P p)                        { return shouldNotBeCalled(that); }
    public R visitJmlStatementLoopExpr(JmlStatementLoopExpr that, P p)                          { return shouldNotBeCalled(that); }
    public R visitJmlStatementLoopModifies(JmlStatementLoopModifies that, P p)                          { return shouldNotBeCalled(that); }
    public R visitJmlStatementSpec(JmlStatementSpec that, P p)                          { return shouldNotBeCalled(that); }
    public R visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that, P p)                { return shouldNotBeCalled(that); }
    public R visitJmlStoreRefKeyword(JmlStoreRefKeyword that, P p)                      { return shouldNotBeCalled(that); }
    public R visitJmlStoreRefListExpression(JmlStoreRefListExpression that, P p)        { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseConditional(JmlTypeClauseConditional that, P p)          { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that, P p)            { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseDecl(JmlTypeClauseDecl that, P p)                        { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseExpr(JmlTypeClauseExpr that, P p)                        { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseIn(JmlTypeClauseIn that, P p)                            { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that, P p)          { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseMaps(JmlTypeClauseMaps that, P p)                        { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that, P p)          { return shouldNotBeCalled(that); }
    public R visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that, P p)            { return shouldNotBeCalled(that); }
    public R visitJmlVariableDecl(JmlVariableDecl that, P p)                            { return shouldNotBeCalled(that); }
    public R visitJmlWhileLoop(JmlWhileLoop that, P p)                                  { return shouldNotBeCalled(that); }
}
