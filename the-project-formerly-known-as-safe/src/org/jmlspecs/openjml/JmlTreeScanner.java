/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml;

import java.util.Iterator;

import org.jmlspecs.openjml.JmlTree.JmlDeclassifyClause;
import org.jmlspecs.openjml.JmlTree.JmlLevelStatement;
import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeScanner;

/**
 * This class is used to construct visitors that walk a Java/JML parse tree. The
 * visit methods each call the method 'scan' on any children, which in turn
 * causes those subtrees to be visited. A derived class that intends to do some
 * work while walking the tree will override selected visit methods to do some
 * work for that node and then will call the super method in order to continue
 * the walking.  The scan method can be overridden in order to do some processing
 * for every node.
 * 
 * @author David Cok
 * 
 */
public class JmlTreeScanner extends TreeScanner implements IJmlVisitor {

    public static final int AST_JAVA_MODE = 0;
    public static final int AST_JML_MODE = 1;
    public static final int AST_SPEC_MODE = 2;
    
    /** The mode in which subtrees are scanned:  <BR>
     * AST_JAVA_MODE scans the tree as it
     * was parsed, ignoring convenience fields in which links to specs are
     * placed, and ignoring the specs CU; <BR>
     * AST_JML_MODE scans the tree as an individual compilation unit
     * (no specs in other files, but including the specs that are part of that file)<BR>
     * SPEC_MODE ignores parsed specs and instead scans through the
     * summaries of specs (that come from the specification files).
     */
    public int scanMode;
    
    public JmlTreeScanner() {
        scanMode = AST_JML_MODE;
    }
    
    public JmlTreeScanner(int mode) {
        scanMode = mode;
    }
    
    public void scan(Iterable<? extends JCTree> list) {
        Iterator<? extends JCTree> iter = list.iterator();
        while (iter.hasNext()) scan(iter.next());
    }
    
    public void visitJmlBinary(JmlBinary that) {
        scan(that.lhs);
        scan(that.rhs);
    }
    
    public void visitJmlChoose(JmlChoose that) {
        scan(that.orBlocks);
        scan(that.elseBlock);
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        if (scanMode == AST_SPEC_MODE) {
            if (!that.isTypeChecked()) throw new RuntimeException("AST_SPEC_MODE requires that the Class be type-checked; class " + that.name + " is not.");
        }
        visitClassDef(that);
        if (scanMode == AST_SPEC_MODE) {
            JmlSpecs.TypeSpecs ms = that.typeSpecsCombined;
            if (ms != null) {
                scan(ms.modifiers);
                scan(ms.clauses);
            } else {
                // FIXME - why does this happen: System.out.println("No specs found for " + that.name);
            }
        }
        if (scanMode == AST_JML_MODE) {
            JmlSpecs.TypeSpecs ms = that.typeSpecs;
            // already done - scan(ms.modifiers);
            if (ms != null) scan(ms.clauses);
        }
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        scan(that.packageAnnotations);
        scan(that.pid); // package id
        scan(that.defs);
        if (scanMode == AST_JML_MODE) scan(that.parsedTopLevelModelTypes);
        if (scanMode == AST_SPEC_MODE) scan(that.specsTopLevelModelTypes);
    }

    public void visitJmlConstraintMethodSig(JmlConstraintMethodSig that) {
        scan(that.expression);
        scan(that.argtypes);
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        scan(that.loopSpecs);
        visitDoLoop(that);
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        scan(that.loopSpecs);
        visitForeachLoop(that);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        scan(that.loopSpecs);
        visitForLoop(that);
    }

    public void visitJmlGroupName(JmlGroupName tree) {
        scan(tree.selection);
    }

    public void visitJmlImport(JmlImport that) {
        visitImport(that);
    }
    
    public void visitJmlLblExpression(JmlLblExpression that) {
        scan(that.expression);
    }

    public void visitJmlMethodClauseCallable(JmlMethodClauseCallable tree) {
        scan(tree.keyword);
        scan(tree.methodSignatures);
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {
        scan(tree.expression);
        scan(tree.predicate);
    }

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
        for (JCTree.JCVariableDecl s: tree.decls) {
            scan(s);
        }
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        scan(tree.expression);
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        for (JCTree t: tree.cases) {
            scan(t);
        }
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
        scan(tree.expression);
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSignalsOnly tree) {
        scan(tree.list);
    }

    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef tree) {
        scan(tree.list);
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        if (scanMode == AST_SPEC_MODE) {
            JmlSpecs.MethodSpecs ms = that.methodSpecsCombined;
            scan(ms.mods);
            scan(ms.cases);
        }
        if (scanMode == AST_JML_MODE) {
            scan(that.cases);
        }
        visitMethodDef(that);
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        scan(that.args);
    }
    
    public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
        scan(tree.cases);
        scan(tree.impliesThatCases);
        scan(tree.forExampleCases);
    }

    public void visitJmlModelProgramStatement(JmlModelProgramStatement that) {
        scan(that.item);
    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree) {
        // no children to scan
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        scan(that.decls);
        scan(that.range);
        scan(that.value);
        scan(that.racexpr);
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        scan(that.newtype);
        scan(that.variable);
        scan(that.predicate);
    }

    public void visitJmlSingleton(JmlSingleton that) {
        // no children to scan
    }

    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
        scan(tree.modifiers);
        scan(tree.clauses);
        scan(tree.block);
    }

    public void visitJmlStatement(JmlStatement tree) {
        scan(tree.statement);
    }
    
    public void visitJmlStatementDecls(JmlStatementDecls tree) {
        for (JCTree.JCStatement s : tree.list) {
            scan(s);
        }
    }

    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        scan(tree.expression);
        scan(tree.optionalExpression);
    }

    public void visitJmlStatementHavoc(JmlStatementHavoc tree) {
        scan(tree.storerefs);
    }

    public void visitJmlStatementLoop(JmlStatementLoop tree) {
        scan(tree.expression);
    }
    
    public void visitJmlStatementSpec(JmlStatementSpec tree) {
        scan(tree.statementSpecs);
    }
    
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        scan(that.expression);
        scan(that.lo);
        scan(that.hi);
    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // nothing to scan
    }

    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        for (JCTree t: that.list) {
            scan(t);
        }
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
        scan(tree.modifiers);
        scan(tree.identifier);
        scan(tree.expression);
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
        scan(tree.modifiers);
        scan(tree.expression);
        scan(tree.sigs);
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
        scan(tree.modifiers);
        scan(tree.decl);
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
        scan(tree.modifiers);
        scan(tree.expression);
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
        scan(tree.modifiers);
        for (JmlGroupName g: tree.list) {
            scan(g);
        }
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
        scan(tree.modifiers);
        scan(tree.specs);
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
        scan(tree.modifiers);
        scan(tree.expression);
        for (JmlGroupName g: tree.list) {
            scan(g);
        }
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
        scan(tree.modifiers);
        scan(tree.identifier);
        for (JCTree.JCExpression e: tree.list) {
            scan(e);
        }
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
        scan(tree.modifiers);
        scan(tree.ident);
        scan(tree.expression);
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        visitVarDef(that);
        if (scanMode == AST_SPEC_MODE) {
            if (that.fieldSpecsCombined != null) {
                scan(that.fieldSpecsCombined.mods);
                scan(that.fieldSpecsCombined.list);
            }
        }
        if (scanMode == AST_JML_MODE) {
            if (that.fieldSpecs != null) {
                scan(that.fieldSpecs.mods);
                scan(that.fieldSpecs.list);
            }
        }
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        scan(that.loopSpecs);
        visitWhileLoop(that);
    }

    @Override
    public void visitJmlDeclassifyClause(JmlDeclassifyClause that) {
        scan(that.expression);
        scan(that.policy);
    }

    @Override
    public void visitJmlLevelStatement(JmlLevelStatement that) {
        scan(that.level);
    }

    @Override
    public void visitJmlChannelStatement(JmlChannelStatement that) {
        scan(that.level);
    }
    
}
