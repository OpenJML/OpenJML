package org.jmlspecs.openjml.esc;

import static com.sun.tools.javac.code.TypeTag.CLASS;

import java.util.LinkedList;

import javax.tools.JavaFileObject;

import org.jmlspecs.openjml.JmlTree.JmlMethodClauseExpr;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;

import com.sun.tools.javac.code.Scope;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Types;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.ListBuffer;

/** This class holds a summary of specification and other useful data about a method.
 * It is only used during BasicBlock, but it is computed and cached on first request
 * (within the compilation context). The 'computeMethodInfo' call fills in the details.
 */
public class JmlMethodInfo {
    /** Creates an uninitialized instance from a method declaration */
    public JmlMethodInfo(JCMethodDecl d, Context context) { 
        this.decl = d; 
        this.owner = d.sym; 
        this.source = ((JmlMethodDecl)d).sourcefile;
        findOverrides(owner,context);
    }
    /** Creates an uninitialized instance from a method symbol */
    public JmlMethodInfo(MethodSymbol msym, Context context) { 
        this.decl = null; 
        this.owner = msym; 
        this.source = null;
        findOverrides(owner,context);
    }
    /** The symbol for this method */
    MethodSymbol owner;
    /** The declaration for this method, if there is one */
    /*@Nullable*/ JCMethodDecl decl;
    /** The JmlClassInfo stucture for the containing class */
    JmlClassInfo classInfo;
    /** The file in which the method is declared and implemented */
    JavaFileObject source;
    /** The name used as the result of the method - filled in during translation */
    String resultName;
    /** Whether the result is used - filled in during translation */
    boolean resultUsed = false;
    //FIXME
    JCExpression exceptionDecl;
    VarSymbol exceptionLocal;
    
    /** A list of all the forall predicates */ // FIXME - how interacts with spec cases
    java.util.List<JCVariableDecl> foralls = new LinkedList<JCVariableDecl>();
    /** A list of all the old predicates */ // FIXME - how interacts with spec cases
    ListBuffer<JCVariableDecl> olds = new ListBuffer<JCVariableDecl>();
    /** A list of the one combined requires predicate */ // FIXME - combined across inheritance?
    java.util.List<JmlMethodClauseExpr> requiresPredicates = new LinkedList<JmlMethodClauseExpr>();
    /** A list of desugared ensures predicates (i.e. in the form \old(precondition) ==> postcondition )*/
    java.util.List<JmlMethodClauseExpr> ensuresPredicates = new LinkedList<JmlMethodClauseExpr>();
    /** A list of desugared signals predicates (i.e. in the form \old(precondition) ==> postcondition )*/
    java.util.List<JmlMethodClauseExpr> exPredicates = new LinkedList<JmlMethodClauseExpr>();
    /** A list of desugared signals_only predicates (i.e. in the form \old(precondition) ==> postcondition )*/
    java.util.List<JmlMethodClauseExpr> sigPredicates = new LinkedList<JmlMethodClauseExpr>();
    /** A list of desugared diverges predicates (i.e. in the form \old(precondition) ==> postcondition )*/
    java.util.List<JmlMethodClauseExpr> divergesPredicates = new LinkedList<JmlMethodClauseExpr>();
    
    /** A structure holding information about desugared assignable clauses */
    public static class Entry {
        public Entry(JCExpression pre, java.util.List<JCExpression> list) {
            this.pre = pre;
            this.storerefs = list;
        }
        /** The precondition guarding this list of assignables */ // FIXME - with \old?
        public JCExpression pre;
        /** A list of storerefs for a particular spec case */
        public java.util.List<JCExpression> storerefs;
    }
    
    /** A list of assignable clause information */
    java.util.List<JmlMethodInfo.Entry> assignables = new LinkedList<JmlMethodInfo.Entry>();
    
    /** A list of overridden methods from super classes */
    java.util.List<MethodSymbol> overrides = new LinkedList<MethodSymbol>();
    
    /** A list of overridden methods from super interfaces */
    java.util.List<MethodSymbol> interfaceOverrides = new LinkedList<MethodSymbol>();
    
    /** Finds declarations of methods being overridden, so we can use thier
     * specifications.
     */
    // FIXME - need interfaces also
    protected void findOverrides(MethodSymbol sym, Context context) {
        MethodSymbol msym = sym;
        Types types = Types.instance(context);
        for (Type t = types.supertype(msym.owner.type); t.getTag() == CLASS; t = types.supertype(t)) {
            TypeSymbol c = t.tsym;
            Scope.Entry e = c.members().lookup(msym.name);
            while (e.scope != null) {
                if (msym.overrides(e.sym, (TypeSymbol)msym.owner, types, false)) {
                    msym = (MethodSymbol)e.sym;
                    if (msym != null) overrides.add(msym);
                    break;
                }
                e = e.next();
            }
        }
        
    }

}