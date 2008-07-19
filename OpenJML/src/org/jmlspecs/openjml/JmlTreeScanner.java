package org.jmlspecs.openjml;

import static org.jmlspecs.openjml.JmlTree.*;

import java.util.Iterator;

import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlDoWhileLoop;
import org.jmlspecs.openjml.JmlTree.JmlEnhancedForLoop;
import org.jmlspecs.openjml.JmlTree.JmlForLoop;
import org.jmlspecs.openjml.JmlTree.JmlMethodClauseGroup;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefArrayRange;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefKeyword;
import org.jmlspecs.openjml.JmlTree.JmlStoreRefListExpression;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseDecl;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseRepresents;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTree.JmlWhileLoop;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeScanner;

/**
 * This class is used to construct visitors that walk a Java/JML parse tree. The
 * visit methods each call the method 'scan' on any children, which in turn
 * causes those subtrees to be visited. A derived class that intends to do some
 * work while walking the tree will override selected visit methods to do some
 * work for that node and then will call the super method in order to continue
 * the walking.
 * 
 * @author David Cok
 * 
 */
public class JmlTreeScanner extends TreeScanner implements IJmlVisitor {

    public final int AST_NO_MODEL_MODE = 0;
    public final int AST_WITH_MODEL_MODE = 1; // FIXME ????
    public final int SPEC_MODE = 2;
    
    /** The mode in which subtrees are scanned:  <BR>
     * AST_MODE scans the tree as it
     * was parsed, ignoring convenience fields in which links to specs are
     * placed, and ignoring refinement sequence; <BR>
     * SPEC_MODE ignores parsed specs and instead scans through the
     * summaries of specs (from all elements of the refinement sequence).
     */
    public int scanMode = AST_NO_MODEL_MODE;
    
    public void scan(Iterable<? extends JCTree> list) {
        Iterator<? extends JCTree> iter = list.iterator();
        while (iter.hasNext()) scan(iter.next());
    }
    
    public void visitJmlRefines(JmlRefines that) {
        // no subtrees
    }
    
    public void visitJmlImport(JmlImport that) {
        visitImport(that);
    }
    
    public void visitJmlSingleton(JmlSingleton that) {
        // no children to scan
    }
    
    public void visitJmlFunction(JmlFunction that) {
        // no children to scan
    }
    
    public void visitJmlBinary(JmlBinary that) {
        scan(that.lhs);
        scan(that.rhs);
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        scan(that.localtype);
        scan(that.range);
        scan(that.predicate);
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        scan(that.newtype);
        scan(that.variable);
        scan(that.predicate);
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        scan(that.expression);
    }

    public void visitJmlStatement(JmlStatement tree) {
        scan(tree.statement);
    }
    
    public void visitJmlStatementLoop(JmlStatementLoop tree) {
        scan(tree.expression);
    }
    
    public void visitJmlStatementSpec(JmlStatementSpec tree) {
        scan(tree.statementSpecs);
    }
    
    public void visitJmlStatementExpr(JmlStatementExpr tree) {
        scan(tree.expression);
        scan(tree.optionalExpression);
    }
    
    public void visitJmlStatementDecls(JmlStatementDecls tree) {
        for (JCTree.JCStatement s : tree.list) {
            scan(s);
        }
    }
    
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr tree) {
        scan(tree.expression);
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl tree) {
        scan(tree.decl);
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn tree) {
        for (JmlGroupName g: tree.list) {
            scan(g);
        }
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps tree) {
        scan(tree.expression);
        for (JmlGroupName g: tree.list) {
            scan(g);
        }
    }

    public void visitJmlGroupName(JmlGroupName tree) {
        scan(tree.selection);
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer tree) {
        scan(tree.specs);
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint tree) {
        scan(tree.expression);
        // FIXME - scan method list
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents tree) {
        scan(tree.ident);
        scan(tree.expression);
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional tree) {
        scan(tree.identifier);
        scan(tree.expression);
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor tree) {
        scan(tree.identifier);
        for (JCTree.JCExpression e: tree.list) {
            scan(e);
        }
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup tree) {
        for (JCTree t: tree.cases) {
            scan(t);
        }
    }
    
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl tree) {
        for (JCTree.JCStatement s: tree.stats) {
            scan(s);
        }
    }
    
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr tree) {
        scan(tree.expression);
    }
    
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional tree) {
        scan(tree.expression);
        scan(tree.predicate);
    }
    
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals tree) {
        scan(tree.expression);
    }
    
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly tree) {
        scan(tree.list);
    }
    
    public void visitJmlMethodClauseAssignable(JmlMethodClauseAssignable tree) {
        scan(tree.list);
    }
    
    public void visitJmlSpecificationCase(JmlSpecificationCase tree) {
        scan(tree.clauses);
    }
    
    public void visitJmlMethodSpecs(JmlMethodSpecs tree) {
        scan(tree.cases);
    }
    
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree tree) {
        // no children to scan
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
        for (JCTree t: that.list) scan(t);
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        scan(that.loopSpecs);
        super.scan(that);
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        scan(that.loopSpecs);
        super.scan(that);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        scan(that.loopSpecs);
        super.scan(that);
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        scan(that.loopSpecs);
        super.scan(that);
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        // scan specsDecl, typeSpecs?  // FIXME
        visitClassDef(that);
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        scan(that.packageAnnotations);
        scan(that.pid);
        scan(that.refinesClause);
        // scan - specs sequence, parsed model types, specs model types?  // FIXME
        if (scanMode == AST_WITH_MODEL_MODE) scan(that.parsedTopLevelModelTypes);
        scan(that.defs);
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        // scan specsDecl, methodSpecs?  // FIXME
        visitMethodDef(that);
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        // scan specsDecl, fieldSpecs?  // FIXME
        visitVarDef(that);
    }
}
