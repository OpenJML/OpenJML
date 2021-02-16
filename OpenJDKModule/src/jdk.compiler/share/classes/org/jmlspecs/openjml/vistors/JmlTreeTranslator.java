/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.vistors;

// FIXME - not ready for use - review and fix

import java.util.ArrayList;
import java.util.Iterator;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.JmlTree.JmlMatchExpression.MatchCase;

import com.sun.source.tree.NewClassTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeTranslator;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCLambda;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;

/** This class translates a parse tree in-place, extending
 * TreeTranslator to include JML nodes.  However, it adds to 
 * TreeTranslator the ability to make a deep copy of the input
 * tree along with translating.
 * 
 * @author David R. Cok
 */
public class JmlTreeTranslator extends TreeTranslator implements IJmlVisitor {
    // FIXME - TreeTranslator uses some specialized translate routines, e.g.
    // translateTypeParams, trnaslateVarDefs - find others and make sure that
    // Jml methods below use them as appropriate

    // FIXME - the copy functionality is barely started - perhaps it should be left to
    // JmlTreeCopier - or perhaps JmlTreeCopier should be combined into here to make one
    // less maintenance problem
    
    protected boolean copy = false;
    
    public JmlTreeTranslator() {
    }

    public <T extends JCTree> ListBuffer<T> translate(ListBuffer<T> trees) {
        if (trees == null) return null;
//        if (!copy) {
//            for (List<T> l = trees.elems; l.nonEmpty(); l = l.tail)
//                l.head = translate(l.head);
//            return trees;
//        } else {
            ListBuffer<T> newlist = new ListBuffer<T>();
            Iterator<T> iter = trees.iterator();
            while (iter.hasNext())
                newlist.append(translate(iter.next()));
            return newlist;
//        }
    }

    public <T extends JCTree> java.util.List<T> translate(java.util.List<T> trees) {
        if (trees == null) return null;
        java.util.List<T> newlist = new ArrayList<T>(trees.size());
        for (T t : trees) newlist.add(translate(t));
        return newlist;
    }

    //@ ensures \typeof(result) <: \type(JmlBinary);
    @Override
    public void visitJmlBinary(JmlBinary that) {
        JmlBinary r = copy ? new JmlBinary(that) : that;
        r.lhs = translate(that.lhs);
        r.rhs = translate(that.rhs);
        // Not translating: op, opcode, operator
        result = r;
    }
    
    @Override
    public void visitJmlChained(JmlChained that) {
        JmlChained r = copy ? new JmlChained(that) : that;
        r.conjuncts.head.lhs = translate(that.conjuncts.head.lhs);
        int i = 0;
        for (JCTree.JCBinary b: that.conjuncts) {
            r.conjuncts.get(i).rhs = translate(b.rhs);
            i++;
        }
        result = that;
    }

    @Override
    public void visitJmlBlock(JmlBlock that) {
        that.stats = translate(that.stats);
        that.cases = translate(that.cases);
        result = that;
    }
    

    @Override
    public void visitJmlChoose(JmlChoose that) {
        JmlChoose r = that;
        r.orBlocks = translate(that.orBlocks);
        r.elseBlock = translate(that.elseBlock);
        result = r;
    }

    @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        visitClassDef(that);
        JmlClassDecl r = (JmlClassDecl)result;
        r.docComment = that.docComment;
        r.toplevel = that.toplevel; // FIXME - need to adjust reference
        r.typeSpecs = that.typeSpecs;
        if (that.typeSpecs != null) {
            JmlSpecs.TypeSpecs rt = r.typeSpecs;// = new JmlSpecs.TypeSpecs();
            JmlSpecs.TypeSpecs tt = that.typeSpecs;
//            rt.blocks = (tt.blocks);
//            rt.checkInvariantDecl = (tt.checkInvariantDecl);
//            rt.checkStaticInvariantDecl = (tt.checkStaticInvariantDecl);
//            rt.clauses = translate(tt.clauses);
//            
        }
        // specsDecls, typeSpecs, env - FIXME
        // Not translating: FIXME
    }

    @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        visitTopLevel(that);
        JmlCompilationUnit r = (JmlCompilationUnit)result;
//        r.parsedTopLevelModelTypes = translate(that.parsedTopLevelModelTypes);
        //r.specsSequence
        //r.specsTopLevelModelTypes - FIXME
        // not translating: mode, FIXME
        result = r;
    }

    @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        visitDoLoop(that);
        JmlDoWhileLoop r = (JmlDoWhileLoop)result;
        r.loopSpecs = translate(that.loopSpecs);
        r.split = that.split;
        result = r;
        // Not translating: none
    }

    @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        visitForeachLoop(that);
        JmlEnhancedForLoop r = (JmlEnhancedForLoop)result;
        r.loopSpecs = translate(that.loopSpecs);
        r.split = that.split;
        result = r;
        // Not translating: none
    }

    @Override
    public void visitJmlForLoop(JmlForLoop that) {
        visitForLoop(that);
        JmlForLoop r = (JmlForLoop)result;
        r.loopSpecs = translate(that.loopSpecs);
        r.split = that.split;
        result = r;
        // Not translating: none
    }

    @Override
    public void visitJmlGroupName(JmlGroupName that) {
        JmlGroupName r = that;
        r.selection = translate(that.selection);
        result = r;
        // Not translating: sym
    }

    @Override
    public void visitJmlImport(JmlImport that) {
        visitImport(that);
        // not translating: isModel, staticImport
    }

    public void visitJmlLabeledStatement(JmlLabeledStatement that) {
        JmlLabeledStatement s = that;
        // that.extraStatements = // FIXME
        that.body = translate(that.body);
    }
    
    @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        JmlLblExpression r = that;
        r.expression = translate(that.expression);
        result = r;
        // Not translating: token, label
    }

    public void visitJmlMatchExpression(JmlMatchExpression that) {
        JmlMatchExpression r = that;
        r.expression = translate(that.expression);
        for (JmlMatchExpression.MatchCase c: that.cases) {
            c.caseExpression = translate(c.caseExpression);
            c. value = translate(c.value);
        }
    }

    @Override
    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable that) {
        JmlMethodClauseCallable r = that;
        r.keyword = translate(that.keyword);
        r.methodSignatures = translate(that.methodSignatures);
        result = r;
    }

    @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        JmlMethodClauseConditional r = that;
        r.expression = translate(that.expression);
        r.predicate = translate(that.predicate);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        JmlMethodClauseDecl r = that;
        r.decls = translate(that.decls);
        result = r;
        // Not translating: token, sourcefile
    }

    @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        JmlMethodClauseExpr r = that;
        r.expression = translate(that.expression);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        JmlMethodClauseGroup r = that;
        r.cases = translate(that.cases);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly that) {
        JmlMethodClauseSignalsOnly r = that;
        r.list = translate(that.list);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        JmlMethodClauseSignals r = that;
        r.vardef = translate(that.vardef);
        r.expression = translate(that.expression);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        JmlMethodClauseStoreRef r = that;
        r.list = translate(that.list);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);
        JmlMethodDecl r = (JmlMethodDecl)result;
        r.defaultValue = translate(that.defaultValue); // Should be in visitMethodDef - TODO
        r.methodSpecsCombined = that.methodSpecsCombined;
        r.isInitializer = that.isInitializer;
        if (that.methodSpecsCombined != null) {
            //r.methodSpecsCombined = new JmlSpecs.MethodSpecs(
            r.methodSpecsCombined.mods = translate(that.methodSpecsCombined.mods);
            r.methodSpecsCombined.cases = translate(that.methodSpecsCombined.cases);
        }
        // FIXME - cases, methodSpecs, specsDecl, owner, docComment, _this
        result = r;
        // Not translating: name, sym, ??? FIXME
    }

    @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        visitApply(that);
        JmlMethodInvocation r = (JmlMethodInvocation)result;
        r.kind = that.kind;
        r.varargsElement = (that.varargsElement); // FIXME
        r.typeargs = translate(that.typeargs);  // Should be in visitApply - TODO
        result = r;
        // Not translating: token, label
    }

    @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        // FIXME - decl, desugared
        JmlMethodSpecs r = that;
        r.cases = translate(that.cases);
        r.impliesThatCases = translate(that.impliesThatCases);
        r.forExampleCases = translate(that.forExampleCases);
        r.feasible = translate(that.feasible);
        result = r;
    }

    @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // nothing to translate
        result = that;
        // Not translating: token
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        JmlQuantifiedExpr r = that;
        r.decls = translate(that.decls);
        r.range = translate(that.range);
        r.value = translate(that.value);
        r.racexpr = translate(that.racexpr);
        r.triggers = translate(that.triggers);
        result = r;
        // Not translating: op
    }
    
    @Override
    public void visitLambda(JCLambda jthat) {
        JmlLambda that = (JmlLambda)jthat;
        JmlLambda r = that;
        r.params = translate(that.params);
        r.body = translate(that.body);
        r.jmlType = translate(that.jmlType);
        result = r;
    }

    @Override
    public void visitNewClass(JCNewClass jthat) {
        JmlNewClass that = (JmlNewClass)jthat;
        JmlNewClass r = that;
        r.encl = translate(that.encl);
        r.typeargs = translate(that.typeargs);
        r.clazz = translate(that.clazz);
        r.args = translate(that.args);
        r.def = translate(that.def);
        result = r;
    }


    @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        JmlSetComprehension r = that;
        r.newtype = translate(that.newtype);
        r.variable = translate(that.variable);
        r.predicate = translate(that.predicate);
        result = r;
        // Not translating: none
    }

    @Override
    public void visitJmlSingleton(JmlSingleton that) {
        result = that;
        // Not translating: info, symbol, token, (pos, type)
    }

    @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        JmlSpecificationCase r = that;
        r.modifiers = translate(that.modifiers);
        r.clauses = translate(that.clauses);
        r.block = translate(that.block);
        r.name = that.name;
        result = r;
        // Not translating: token, also, code, sourcefile
    }

    @Override
    public void visitJmlStatement(JmlStatement that) {
        JmlStatement r = that;
        r.statement = translate(that.statement);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlInlinedLoop(JmlInlinedLoop that) {
        result = that;
    }


    @Override
    public void visitJmlStatementShow(JmlStatementShow that) {
        JmlStatementShow r = that;
        ListBuffer<JCExpression> expressions = new ListBuffer<>();
        for (JCExpression e: that.expressions) expressions.add( translate(e));
        that.expressions = expressions.toList();
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        JmlStatementDecls r = that;
        r.list = translate(that.list);
        result = r;
        // Not translating: token
    }

    @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        JmlStatementExpr r = that;
        r.expression = translate(that.expression);
        r.optionalExpression = translate(that.optionalExpression);
        result = r;
        // Not translating: token, line, source, label, declPos - FIXME
    }

    @Override
    public void visitJmlStatementHavoc(JmlStatementHavoc that) {
        JmlStatementHavoc r = that;
        r.storerefs = translate(that.storerefs);
        result = r;
    }

    @Override
    public void visitJmlStatementLoopExpr(JmlStatementLoopExpr that) {
        JmlStatementLoopExpr r = that;
        r.expression = translate(that.expression);
        result = r;
        // Not translating: token, line, source - FIXME
    }

    @Override
    public void visitJmlStatementLoopModifies(JmlStatementLoopModifies that) {
        JmlStatementLoopModifies r = that;
        r.storerefs = translate(that.storerefs);
        result = r;
        // Not translating: token, line, source - FIXME
    }

    @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        JmlStatementSpec r = that;
        r.statementSpecs = translate(that.statementSpecs);
        r.statements = translate(that.statements);
        result = r;
        // Not translating: none
    }

    @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        JmlStoreRefArrayRange r = that;
        r.expression = translate(that.expression);
        r.hi = translate(that.hi);
        r.lo = translate(that.lo);
        result = r;
        // Not translating: ( pos, type)
    }

    @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // Not translating: token, ( pos, type )
        result = that;
    }

    @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        JmlStoreRefListExpression r = that;
        r.list = translate(that.list);
        // Not translating pos, token, type
        result = r;
    }

    @Override
    public void visitJmlTuple(JmlTuple that) {
        JmlTuple r = that;
        r.values = translate(that.values);
        // Not translating pos, token, type
        result = r;
    }

    @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        JmlTypeClauseConditional r = that;
        r.modifiers = translate(that.modifiers);
        r.identifier = translate(that.identifier);
        r.expression = translate(that.expression);
        // Not translating: source, token, pos, type
        result = r;
    }

    @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        JmlTypeClauseConstraint r = that;
        r.modifiers = translate(that.modifiers);
        r.expression = translate(that.expression);
        r.sigs = translate(that.sigs);
        // Not translating: source, token, pos, type, notlist
        result = r;
    }

    @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        JmlTypeClauseDecl r = that;
        r.modifiers = translate(that.modifiers);
        r.decl = translate(that.decl);
        // No change to source, token, pos, type
        result = r;
    }

    @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        JmlTypeClauseExpr r = that;
        r.modifiers = translate(that.modifiers);
        r.expression = translate(that.expression);
        // No change to source, token, pos, type
        result = r;
    }

    @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        JmlTypeClauseIn r = that;
        // r.modifiers is a reference FIXME
        r.list = translate(that.list);
        result = r;
        // Not translating: source token
    }

    @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        JmlTypeClauseInitializer r = that;
        r.modifiers = translate(that.modifiers);
        r.specs = translate(that.specs);
        // Not translating pos, source, token, type
        result = r;
    }

    @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        JmlTypeClauseMaps r = that;
        r.modifiers = translate(that.modifiers);
        r.expression = translate(that.expression);
        r.list = translate(that.list);
        result = r;
    }

    @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        JmlTypeClauseMonitorsFor r = that;
        r.modifiers = translate(that.modifiers);
        r.identifier = translate(that.identifier);
        r.list = translate(that.list);
        // Not translating pos, source, token, type
        result = r;
    }

    @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        JmlTypeClauseRepresents r = that;
        r.modifiers = translate(that.modifiers);
        r.ident = translate(that.ident);
        r.expression = translate(that.expression);
        // Not translating pos, source, token, type, suchthat
        result = r;
    }

    @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);
        JmlVariableDecl r = (JmlVariableDecl)result;
        if (that.fieldSpecsCombined == null) {
            r.fieldSpecsCombined = null;
        } else {
            // r.fieldSpecsCombined.mods = ??? FIXME
            // fieldSpecs???
            r.fieldSpecsCombined.mods = that.fieldSpecsCombined.mods;
            r.fieldSpecsCombined.list = translate(that.fieldSpecsCombined.list);
        }
        // FIXME - specsDecl, fieldSpecs, mods
        result = r;
        // Not translating: sourcefile, docComment, name, sym
    }

    @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        visitWhileLoop(that);
        JmlWhileLoop r = (JmlWhileLoop)result;
        r.loopSpecs = translate(that.loopSpecs);
        r.split = that.split;
        result = r;
        // Not translating: none
    }

    public void visitJmlMethodSig(JmlMethodSig that) {
        JmlMethodSig r = that;
        r.argtypes = translate(that.argtypes);
        r.expression = translate(that.expression);
        result = r;
        // Not translating: none
    }

    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        JmlModelProgramStatement r = that;
        r.item = translate(that.item);
        result = r;
    }

    public void visitJmlNewClass(JmlNewClass that) {
        visitNewClass(that);
    }


}
