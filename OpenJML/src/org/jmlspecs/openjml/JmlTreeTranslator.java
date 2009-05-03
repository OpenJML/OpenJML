package org.jmlspecs.openjml;

import org.jmlspecs.annotations.NonNull;
import org.jmlspecs.openjml.JmlTree.*;
import org.jmlspecs.openjml.esc.Label;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTags;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Name;

public class JmlTreeTranslator extends com.sun.tools.javac.tree.TreeTranslator implements IJmlVisitor {
    
    /** The compilation context */
    @NonNull protected Context context;
    
    /** The log for error and warning messages */
    @NonNull protected Log log;
    
//    /** The specifications database for this compilation context, initialized in the constructor */
//    @NonNull protected JmlSpecs specs;
//    
    /** The symbol table from the compilation context, initialized in the constructor */
    @NonNull protected Symtab syms;
//    
//    /** The Names table from the compilation context, initialized in the constructor */
//    @NonNull protected Name.Table names;
//    
    /** The factory used to create AST nodes, initialized in the constructor */
    @NonNull protected JmlTree.Maker factory;
    
    public JmlTreeTranslator(Context context) {
        this.context = context;
        this.log = Log.instance(context);
        this.factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
//        this.names = Name.Table.instance(context);
        this.syms = Symtab.instance(context);
    }
    
    public JCLiteral makeLiteral(boolean v, int pos) {
        JCLiteral r = factory.at(pos).Literal(TypeTags.BOOLEAN,v?1:0);
        r.type = syms.booleanType;
        return r;
    }
    
    // We have to do something special here.  This translator only allows replacing
    // a tree by another tree - so a statement can only be replaced by a single 
    // statement.  Sometimes we want to insert a bunch of statements.  Now we
    // could insert a Block in place of a statement, but if the original statement
    // was a declaration we will have screwed up the visibility of that 
    public void visitBlock(JCBlock tree) {
        List<JCStatement> trees = (tree.stats);
        if (trees == null) return;
        tree.stats = expandableTranslate(trees);
        result = tree;
    }
    
    public List<JCStatement> expandableTranslate(List<JCStatement> trees) {
        for (List<JCStatement> l = trees; l.nonEmpty(); l = l.tail) {
            JCStatement r = translate(l.head);
            if (!(l.head instanceof JCBlock) && r instanceof JCBlock) {
                List<JCStatement> newtrees = ((JCBlock)r).stats;
                l.head = newtrees.head;
                newtrees = newtrees.tail;
                if (newtrees == null || newtrees.tail == null) continue;
                List<JCStatement> last = newtrees;
                while (last.tail.tail != null) last = last.tail;
                last.tail = l.tail;
                l.tail = newtrees;
                l = last;
            } else {
                l.head = r;
            }
        }
        return trees;
    }
    
    public void visitJmlBinary(JmlBinary that) {
        result = that;
    }

    public void visitJmlClassDecl(JmlClassDecl that) {
        visitClassDef(that);
    }

    public void visitJmlCompilationUnit(JmlCompilationUnit that) {
        System.out.println("CANT DO THIS");
    }

    public void visitJmlDoWhileLoop(JmlDoWhileLoop that) {
        visitDoLoop(that);
    }

    public void visitJmlEnhancedForLoop(JmlEnhancedForLoop that) {
        result = translate(((JmlEnhancedForLoop)that).implementation);
        //visitForeachLoop(that);
    }

    public void visitJmlForLoop(JmlForLoop that) {
        visitForLoop(that);
    }

    public void visitJmlGroupName(JmlGroupName that) {
        result = that;
    }

    public void visitJmlImport(JmlImport that) {
        visitImport(that);
    }

    public void visitJmlLblExpression(JmlLblExpression that) {
        result = that;
    }

    public void visitJmlMethodClauseStoreRef(JmlMethodClauseStoreRef that) {
        result = that;
    }

    public void visitJmlMethodClauseConditional(JmlMethodClauseConditional that) {
        result = that;
    }

    public void visitJmlMethodClauseDecl(JmlMethodClauseDecl that) {
        result = that;
    }

    public void visitJmlMethodClauseExpr(JmlMethodClauseExpr that) {
        result = that;
    }

    public void visitJmlMethodClauseGroup(JmlMethodClauseGroup that) {
        result = that;
    }

    public void visitJmlMethodClauseSigOnly(JmlMethodClauseSigOnly that) {
        result = that;
    }

    public void visitJmlMethodClauseSignals(JmlMethodClauseSignals that) {
        result = that;
    }

    public void visitJmlMethodDecl(JmlMethodDecl that) {
        visitMethodDef(that);
    }

    public void visitJmlMethodInvocation(JmlMethodInvocation that) {
        result = that;
    }

    public void visitJmlMethodSpecs(JmlMethodSpecs that) {
        result = that;
    }

    public void visitJmlPrimitiveTypeTree(JmlPrimitiveTypeTree that) {
        result = that;
    }

    public void visitJmlQuantifiedExpr(JmlQuantifiedExpr that) {
        result = that;
    }

    public void visitJmlRefines(JmlRefines that) {
        result = that;
    }

    public void visitJmlSetComprehension(JmlSetComprehension that) {
        result = that;
    }

    public void visitJmlSingleton(JmlSingleton that) {
        result = that;
    }

    public void visitJmlSpecificationCase(JmlSpecificationCase that) {
        result = that;
    }

    public void visitJmlStatement(JmlStatement that) {
        result = that;
    }

    public void visitJmlStatementDecls(JmlStatementDecls that) {
        // Treat this just like a declaration
        // FIXME - is this still actually a list of declarations?
        List<JCStatement> list = expandableTranslate(that.list.toList());
        result = factory.at(that.pos).Block(0,list);
    }

    public void visitJmlStatementExpr(JmlStatementExpr that) {
        if (that.token == JmlToken.UNREACHABLE) {
            result = factory.JmlExpressionStatement(JmlToken.ASSERT,Label.UNREACHABLE,makeLiteral(false,that.pos));
        } else { // assert, asssume
            result = that;
        }
    }

    public void visitJmlStatementLoop(JmlStatementLoop that) {
        result = that;
    }

    public void visitJmlStatementSpec(JmlStatementSpec that) {
        result = that;
    }

    public void visitJmlStoreRefArrayRange(JmlStoreRefArrayRange that) {
        result = that;
    }

    public void visitJmlStoreRefKeyword(JmlStoreRefKeyword that) {
        result = that;
    }

    public void visitJmlStoreRefListExpression(JmlStoreRefListExpression that) {
        result = that;
    }

    public void visitJmlTypeClauseConditional(JmlTypeClauseConditional that) {
        result = that;
    }

    public void visitJmlTypeClauseConstraint(JmlTypeClauseConstraint that) {
        result = that;
    }

    public void visitJmlTypeClauseDecl(JmlTypeClauseDecl that) {
        result = that;
    }

    public void visitJmlTypeClauseExpr(JmlTypeClauseExpr that) {
        result = that;
    }

    public void visitJmlTypeClauseIn(JmlTypeClauseIn that) {
        result = that;
    }

    public void visitJmlTypeClauseInitializer(JmlTypeClauseInitializer that) {
        result = that;
    }

    public void visitJmlTypeClauseMaps(JmlTypeClauseMaps that) {
        result = that;
    }

    public void visitJmlTypeClauseMonitorsFor(JmlTypeClauseMonitorsFor that) {
        result = that;
    }

    public void visitJmlTypeClauseRepresents(JmlTypeClauseRepresents that) {
        result = that;
    }

    public void visitJmlVariableDecl(JmlVariableDecl that) {
        result = that;
    }

    public void visitJmlWhileLoop(JmlWhileLoop that) {
        visitWhileLoop(that);
    }
}
