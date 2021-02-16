package org.jmlspecs.openjml.esc;

import java.util.LinkedList;

import org.jmlspecs.annotation.*;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseConstraint;
import org.jmlspecs.openjml.JmlTree.JmlTypeClauseExpr;

import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;

/** This class holds specification information about a given class.
 * Note that all of the expressions are in conventional (i.e. not the
 * translated, basic) AST form.
 * @author David Cok
 */
public class JmlClassInfo {
    public JmlClassInfo(@NonNull JCClassDecl d) { this.decl = d; }
    /** The source code declaration - null if no source and no specs */ 
    @Nullable JCClassDecl decl;
    /** The symbol for the class */
    @NonNull ClassSymbol csym;
    
    /** The type specifications from the specs database */
    JmlSpecs.TypeSpecs typeSpecs = null; // Non-null once initialized
    /** The instance constraint clauses from typeSpecs */
    public java.util.@NonNull List<JmlTypeClauseConstraint> constraints = new LinkedList<JmlTypeClauseConstraint>();
    /** The static constraint clauses from typeSpecs */
    public java.util.@NonNull List<JmlTypeClauseConstraint> staticconstraints = new LinkedList<JmlTypeClauseConstraint>();
    /** The initially clauses from typeSpecs */
    public java.util.@NonNull List<JmlTypeClauseExpr> initiallys = new LinkedList<JmlTypeClauseExpr>();
    /** The instance invariant clauses from typeSpecs */
    @NonNull public java.util.List<JmlTypeClauseExpr> invariants = new LinkedList<JmlTypeClauseExpr>();
    /** The static invariant clauses from typeSpecs */
    public java.util.@NonNull List<JmlTypeClauseExpr> staticinvariants = new LinkedList<JmlTypeClauseExpr>();
    /** The axiom clauses from typeSpecs */
    public java.util.@NonNull List<JmlTypeClauseExpr> axioms = new LinkedList<JmlTypeClauseExpr>();

    JmlClassInfo superclassInfo;
    
}