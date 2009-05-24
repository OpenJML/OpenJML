package org.jmlspecs.openjml;

import org.jmlspecs.openjml.JmlTree.*;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import com.sun.tools.javac.tree.TreeTranslator;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCLiteral;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;
import com.sun.tools.javac.util.Names;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

/** This class translates a parse tree in-place, extending
 * TreeTranslator to include JML nodes
 * @author David R. Cok
 */
// FIXME - it needs extensive fixing
public class JmlTreeTranslator extends TreeTranslator implements IJmlVisitor {

    protected boolean copy = false;
    
    public JmlTreeTranslator() {
    }

    public <T extends JCTree> ListBuffer<T> translate(ListBuffer<T> trees) {
        if (trees == null) return null;
        if (!copy) {
            for (List<T> l = trees.elems; l.nonEmpty(); l = l.tail)
                l.head = translate(l.head);
            return trees;
        } else {
            ListBuffer<T> newlist = new ListBuffer<T>();
            for (List<T> l = trees.elems; l.nonEmpty(); l = l.tail)
                newlist.append(translate(l.head));
            return newlist;
        }
    }

    //@ ensures \typeof(result) <: \type(JmlBinary);
    //JAVA16 @Override
    public void visitJmlBinary(JmlBinary that) {
        JmlBinary r = copy ? new JmlBinary(that) : that;
        r.lhs = translate(that.lhs);
        r.rhs = translate(that.rhs);
        // Not translating ops, type, op
        result = r;
    }

    //JAVA16 @Override
    public void visitJmlClassDecl(JmlClassDecl that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlForLoop(JmlForLoop that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlGroupName(JmlGroupName that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlImport(JmlImport that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlLblExpression(JmlLblExpression that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodDecl(JmlMethodDecl that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        translate(that.cases); // Presumes inplace translation
        translate(that.impliesThatCases);
        translate(that.forExampleCases);
        // Don't translate that.decl or that.desugared - when is desugared created???? it shares pieces with the cases // FIXME
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlRefines(JmlRefines that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlSetComprehension(JmlSetComprehension that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlSingleton(JmlSingleton that) {
        // Not translating: info, pos, symbol, token, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        if (that.clauses != null) for (JmlMethodClause c : that.clauses) {
            translate(c);  // Presumes in place
        }
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStatement(JmlStatement that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStatementExpr(JmlStatementExpr that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStatementLoop(JmlStatementLoop that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStatementSpec(JmlStatementSpec that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        that.expression = translate(that.expression);
        that.hi = translate(that.hi);
        that.lo = translate(that.lo);
        // Not translating pos, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        // Not translating pos, token, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        that.list = translate(that.list);
        // Not translating pos, token, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        that.expression = translate(that.expression);
        that.modifiers = translate(that.modifiers);
        that.identifier = translate(that.identifier);
        // No change to source, token, pos, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        that.expression = translate(that.expression);
        that.modifiers = translate(that.modifiers);
        that.sigs = translate(that.sigs);
        // No change to source, token, pos, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        that.modifiers = translate(that.modifiers);
        that.decl = translate(that.decl);
        // No change to source, token, pos, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        that.expression = translate(that.expression);
        that.modifiers = translate(that.modifiers);
        // No change to source, token, pos, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        // TODO Auto-generated method stub
        that.modifiers = translate(that.modifiers);
        that.specs = translate(that.specs);
        // Not translating pos, source, token, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        that.identifier = translate(that.identifier);
        that.list = translate(that.list);
        that.modifiers = translate(that.modifiers);
        // Not translating pos, source, token, type
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        that.expression = translate(that.expression);
        that.modifiers = translate(that.modifiers);
        that.ident = translate(that.ident);
        // Not translating pos, source, token, type, suchthat
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlVariableDecl(JmlVariableDecl that) {
        // TODO Auto-generated method stub
        result = that;
    }

    //JAVA16 @Override
    public void visitJmlWhileLoop(JmlWhileLoop that) {
        // TODO Auto-generated method stub
        result = that;
    }

}
