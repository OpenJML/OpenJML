package org.jmlspecs.openjml.esc;

import org.jmlspecs.openjml.JmlTree.JmlMethodInvocation;
import org.jmlspecs.openjml.visitors.JmlTreeScanner;
import org.jmlspecs.openjml.JmlTreeUtils;
import org.jmlspecs.openjml.Utils;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCAssignOp;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCIdent;
import com.sun.tools.javac.tree.JCTree.JCUnary;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;
import com.sun.tools.javac.util.Log;

/** This class is a tree walker that finds everything that is the target of
 * a modification in the tree being walked: assignments, assignment-ops, 
 * increment and decrement operators, fields specified as modified by a
 * method call.
 */
// FIXME - is the tree already in reduced BasicBlock form?
public class TargetFinder extends JmlTreeScanner {
    
    private Context context;
    private ListBuffer<JCExpression> vars;
    
    public TargetFinder(Context context) { this.context = context; }
    
    /** Finds variables in the given JCTree, adding them to the list that is the 
     * second argument; the second argument is returned.
     */
    public static /*@Nullable*/ListBuffer<JCExpression> findVars(JCTree that, /*@Nullable*/ListBuffer<JCExpression> v, Context context) {
        if (that == null) return v;
        TargetFinder vf = new TargetFinder(context);
        return vf.find(that,v);
    }
    
    /** Finds variables in the given JCTrees, adding them to the list that is the 
     * second argument; the second argument is returned.
     */
    public static ListBuffer<JCExpression> findVars(Iterable<? extends JCTree> list, /*@Nullable*/ListBuffer<JCExpression> v, Context context) {
        TargetFinder vf = new TargetFinder(context);
        return vf.find(list,v);
    }
    
    /** Finds variables in the given JCTrees, adding them to the list that is the 
     * second argument; the second argument is returned.
     */
    public ListBuffer<JCExpression> find(Iterable<? extends JCTree> list, /*@Nullable*/ListBuffer<JCExpression> v) {
        if (v == null) vars = new ListBuffer<JCExpression>();
        else vars = v;
        for (JCTree t: list) t.accept(this);
        return vars;
    }
    
    /** Finds variables in the given JCTrees, adding them to the list that is the 
     * second argument; the second argument is returned.
     */
    public ListBuffer<JCExpression> find(JCTree that, ListBuffer<JCExpression> v) {
        if (that == null) return v;
        if (v == null) vars = new ListBuffer<JCExpression>();
        else vars = v;
        that.accept(this);
        return vars;
    }
    
    @Override
    public void visitAssign(JCAssign that) {
        super.visitAssign(that);
        vars.add(that.lhs);
    }
    
    @Override
    public void visitAssignop(JCAssignOp that) {
        super.visitAssignop(that);
        vars.add(that.lhs);
    }
    
    @Override
    public void visitUnary(JCUnary that) {
        super.visitUnary(that);
        JCTree.Tag op = that.getTag();
        if (op == JCTree.Tag.POSTDEC || op == JCTree.Tag.POSTINC ||
                op == JCTree.Tag.PREINC || op == JCTree.Tag.PREDEC)
            vars.add(that.getExpression());
    }
    
    public void visitAnnotation(JCAnnotation tree) {
        //scan(tree.annotationType);
        //scan(tree.args);
    }
    
    public void visitMethodInvocation(JmlMethodInvocation that) {
        super.visitApply(that);
        JCExpression m = that.meth;
        Symbol sym = (m instanceof JCIdent ? ((JCIdent)m).sym : m instanceof JCFieldAccess ? ((JCFieldAccess)m).sym : null);
        if (that.meth != null && !JmlAttr.instance(context).isPureMethod((Symbol.MethodSymbol)sym)) {
            Utils.instance(context).warning("jml.message","Use an explicit loop_modifies clause");
        }
    }

    
    // FIXME - also need targets of method calls, update statements of loops,
    // initialization statements of loops, specs of method calls

}