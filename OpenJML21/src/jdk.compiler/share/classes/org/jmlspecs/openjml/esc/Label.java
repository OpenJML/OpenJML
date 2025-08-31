/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.esc;

import java.util.HashMap;
import java.util.Map;

/** This class defines labels used for identifying different kinds of assumptions
 * and assertions.  The human readable string may not have whitespace or any
 * non-alphanumeric characters (and must start with a letter).
 * <P>
 * This could be implemented with an enum, but that is not extendable by 
 * derived classes.  So instead we use a set of final objects of type Label.
 * Others can be easily created if needed.
 * 
 * Any Label that might be an assertion during RAC, and therefore would
 * issue a verification error should the assertion not be true, must have an entry in 
 * messages.java to define a value for compiler.warn.rac.<label>
 * 
 * @author David Cok
 */
public class Label {
    
    static protected Map<String,Label> map = new HashMap<String,Label>();

    /** Human-readable description of this kind of assertion or assumption */
    //@ non_null
    protected final String info;
    
    /** If false, these assumptions or assertions are not checked by RAC. Used for assumptions that are
     * purely 'internal' assumptions, such as definitions. */
    public final boolean racChecked;
    
    /** Constructs a label object 
     * @param s name of label, alphanumeric only (no spaces)
     */
    public Label(/*@ non_null */ String name, boolean checked) {
        this.info = name;
        this.racChecked = checked;
        map.put(name, this);
    }
    
    public Label(/*@ non_null */ String name) {
        this(name, true);
    }
    
    /** The descriptive name of the Label */
    public String info() {
        return info;
    }
    
    /** Returns the info String for this instance
      * @see java.lang.Object#toString()
     */
    //@ non_null
    public String toString() {
        return info;
    }
    
    static public Label find(String s) {
        return map.get(s);
    }
    
    /** Used for explicit, user-provided JML assume statements */
    /*@ non_null*/ public final static Label EXPLICIT_ASSUME = new Label("Assume");
    
    /** Used for implicit, miscellaneous JML assume statements */
    /*@ non_null*/ public final static Label IMPLICIT_ASSUME = new Label("ImplicitAssume");
    
    /** Used for implicit, miscellaneous JML assume statements */
    /*@ non_null*/ public final static Label METHOD_DEFINITION = new Label("MethodDefinition");
    
    /** Used for implicit, miscellaneous JML assume statements */
    /*@ non_null*/ public final static Label METHOD_ASSUME = new Label("MethodAssume");
    
    /** Used for assume statements generated from preconditions */
    /*@ non_null*/ public final static Label PRECONDITION = new Label("Precondition");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT = new Label("Invariant");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT_REENTER_CALLER = new Label("InvariantReenterCaller");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT_ENTRANCE = new Label("InvariantEntrance");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT_EXIT = new Label("InvariantExit");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT_EXCEPTION_EXIT = new Label("InvariantExceptionExit");
    
    /** Used for assume or assert statements generated from invariants */
    /*@ non_null*/ public final static Label INVARIANT_EXIT_CALLER = new Label("InvariantLeaveCaller");
    
    /** Out-of-range numerical conversion */
    /*@ non_null */ public final static Label ARITHMETIC_OP_RANGE = new Label("ArithmeticOperationRange");
    
    /** Out-of-range numerical conversion */
    /*@ non_null */ public final static Label ARITHMETIC_CAST_RANGE = new Label("ArithmeticCastRange");
    
    /** Used for assume or assert statements generated from axiom clauses */
    /*@ non_null*/ public final static Label AXIOM = new Label("Axiom");
    
    /** Used for assume statements generated to guard a catch block */
    /*@ non_null*/ public final static Label CATCH_CONDITION = new Label("CatchCondition");

    /** Used for assume statements generated to capture the switch value, in ESC only */
    /*@ non_null*/ public final static Label SWITCH_VALUE = new Label("SwitchValue");
    
    /** Used for assume statements generated to initialize a new array, only in ESC */
    /*@ non_null*/ public final static Label ARRAY_INIT = new Label("ArrayInit");
//    
//    /** Used for assume statements generated to capture the return value */
//    /*@ non_null*/ public final static Label RETURN = new Label("Return");
    
    /** Used for assert statements testing that termination metric decreases */
    /*@ non_null*/ public final static Label TERMINATION_DECREASES = new Label("TerminationDecreases");
    
    /** Used for assert statements testing that termination metric decreases */
    /*@ non_null*/ public final static Label TERMINATION_NONNEG = new Label("TerminationNonNegative");
    
    /** Used for assume statements generated to define auxiliary variables */
    /*@ non_null*/ public final static Label SYN = new Label("Synthetic");

    /** Used for assume statements generated to adjust DSA variables  -- only in ESC (BasicBlocker)*/
    /*@ non_null*/ public final static Label DSA = new Label("DSA", false);

    /** Used for assume statements generated to adjust DSA variables */
    /*@ non_null*/ public final static Label SOURCEBLOCK = new Label("SOURCEBLOCK", false);

    /** Used for explicit, user-specified assert statements */
    /*@ non_null*/ public final static Label EXPLICIT_ASSERT = new Label("Assert");
    
    /** Used for precondition completeness assert statements */
    /*@ non_null*/ public final static Label COMPLETENESS = new Label("CompletePreconditions");
    
    /** Used for precondition completeness assert statements */
    /*@ non_null*/ public final static Label DISJOINTNESS = new Label("DisjointPreconditions");
    
    /** Used to assert well-defindeness of \choose expressions */
    /*@ non_null*/ public final static Label CHOOSE = new Label("ChooseNotDefined");
    
    /** Used to assert well-defindeness of \choosex expressions */
    /*@ non_null*/ public final static Label CHOOSEX = new Label("ChoosexNotDefined");
    
    /** Used for asserts generated from user-specified reachable statements */
    /*@ non_null*/ public final static Label REACHABLE = new Label("Reachable");
    
    /** Used for asserts generated from user-specified unreachable statements */
    /*@ non_null*/ public final static Label UNREACHABLE = new Label("Unreachable");
    
    /** Used for asserts generated from readable clauses */
    /*@ non_null*/ public final static Label READABLE = new Label("Readable-if");
    
    /** Used for asserts generated from writable clauses */
    /*@ non_null*/ public final static Label WRITABLE = new Label("Writable-if");
    
    /** Used for asserts generated from diverges clauses */
    /*@ non_null*/ public final static Label DIVERGES = new Label("Diverges");
    
    /** Used for asserts generated from captures clauses */
    /*@ non_null*/ public final static Label CAPTURES = new Label("Captures");
    
    /** Used for asserts generated from assignable clauses */
    /*@ non_null*/ public final static Label ASSIGNABLE = new Label("Assignable");
    
    /** Used for asserts generated from accessible clauses */
    /*@ non_null*/ public final static Label ACCESSIBLE = new Label("Accessible");
    
    /** Used for asserts generated from callable clauses */
    /*@ non_null*/ public final static Label CALLABLE = new Label("Callable");
    
    /** Used for assume or assert statements generated from non-null designations */
    /*@ non_null*/ public final static Label NULL_CHECK = new Label("NullCheck");
    
    /** Used for assume or assert statements generated from non-null designations */
    /*@ non_null*/ public final static Label NULL_FIELD = new Label("NullField");
    
    /** Used for assume or assert statements generated from non-null designations */
    /*@ non_null*/ public final static Label NULL_FORMAL = new Label("NullFormal");
    
    /** Used for assume or assert statements generated from non-null designations */
    /*@ non_null*/ public final static Label NULL_ARGUMENT = new Label("NullArgument");
    
    /** Used for assume or assert statements generated from non-null designations */
    /*@ non_null*/ public final static Label NULL_ELEMENT = new Label("NullElement");
    
    /** Used for situations in which an method argument is illegal for some reason other than a null values */
    /*@ non_null*/ public final static Label ILLEGAL_ARGUMENT = new Label("IllegalArgument");
    
    /** Used for assume or assert statements for a cast to a NonNull type */
    /*@ non_null*/ public final static Label NULL_CAST = new Label("NullCast");
    
    /** Used for assume or assert statements generated when checking static initialization */
    /*@ non_null*/ public final static Label STATIC_INIT = new Label("StaticInit");
    
    /** Used for assert statements generated from postcondition checks */
    /*@ non_null*/ public final static Label POSTCONDITION = new Label("Postcondition");
    
    /** Used for assert statements generated from exceptional postcondition checks */
    /*@ non_null*/ public final static Label SIGNALS = new Label("ExceptionalPostcondition");
    
    /** Used for assert statements generated from signals_only checks */
    /*@ non_null*/ public final static Label SIGNALS_ONLY = new Label("ExceptionList");
    
    /** Used for assume statements generated from uses of pure methods in specifications */
    /*@ non_null*/ public final static Label METHODAXIOM = new Label("MethodAxiom", false);
    
    /** Used for assert statements generated from constraint checks */
    /*@ non_null*/ public final static Label CONSTRAINT = new Label("Constraint");
    
    /** Used for assert statements generated from initially checks */
    /*@ non_null*/ public final static Label INITIALLY = new Label("Initially");
    
    /** Used for assert statements generated to check that assume statements are feasible */
    /*@ non_null*/ public final static Label FEASIBILITY_CHECK = new Label("FeasibilityCheck");
    
    /** Used for the loop invariant assumption at beginning of loop body. */
    /*@ non_null*/ public final static Label LOOP_INVARIANT_ASSUMPTION = new Label("LoopInvariantAssumption");
    
    /** Used for the loop invariant assertion at end of loop body. */
    /*@ non_null*/ public final static Label LOOP_INVARIANT = new Label("LoopInvariant");
    
    /** Used for the loop invariant assertion or assumption. */
    /*@ non_null*/ public final static Label LOOP_INVARIANT_PRELOOP = new Label("LoopInvariantBeforeLoop");
    
    /** Used for the loop invariant assertion or assumption. */
    /*@ non_null*/ public final static Label LOOP_INVARIANT_ENDLOOP = new Label("LoopInvariantAfterLoop");
    
    /** Used for the assertion that the loop variant is decreasing. */
    /*@ non_null*/ public final static Label LOOP_DECREASES = new Label("LoopDecreases");
    
    /** Used for the assertion that the loop variant is never negative prior to executing a loop iteration. */
    /*@ non_null*/ public final static Label LOOP_DECREASES_NEGATIVE = new Label("LoopDecreasesNonNegative");
    
    /** Used to designate the conditional test of a loop, only in a do-while loop */
    /*@ non_null*/ public final static Label LOOP = new Label("LoopCondition");
    
    /** Used to designate an undefined pure expression because of a failed precondition in a called method */
    /*@ non_null*/ public final static Label UNDEFINED_PRECONDITION = new Label("UndefinedCalledMethodPrecondition");
    
    /** Used to designate an undefined pure expression because of a failed precondition in a called method */
    /*@ non_null*/ public final static Label UNDEFINED_NULL_PRECONDITION = new Label("UndefinedCalledMethodNullPrecondition");
    
    /** Used to designate an undefined pure expression because of a failed precondition for a lemma */
    /*@ non_null*/ public final static Label UNDEFINED_LEMMA = new Label("UndefinedLemmaPrecondition");
    
    /** Used to designate a possible exception because of a potential null reference */
    /*@ non_null*/ public final static Label POSSIBLY_NULL_DEREFERENCE = new Label("PossiblyNullDeReference");
    
    /** Used to designate an undefined pure expression because of a potential null dereference */
    /*@ non_null*/ public final static Label UNDEFINED_NULL_DEREFERENCE = new Label("UndefinedNullDeReference");
    
    /** Used to designate a possible exception because of a potential null return value */
    /*@ non_null*/ public final static Label POSSIBLY_NULL_RETURN = new Label("PossiblyNullReturn");
    
    /** Used to designate a possible exception because of a potential null reference */
    /*@ non_null*/ public final static Label POSSIBLY_NULL_VALUE = new Label("PossiblyNullValue");
    
    /** Used to designate a possible exception because of a potential null assignment to non_null */
    /*@ non_null*/ public final static Label POSSIBLY_NULL_ASSIGNMENT = new Label("PossiblyNullAssignment");
    
    /** Used to designate a possible exception because of a potential initialization of non_null target with null value */
    /*@ non_null*/ public final static Label POSSIBLY_NULL_INITIALIZATION = new Label("PossiblyNullInitialization");
    
    /** Used to designate a possible exception because of a potential initialization of non_null target with null value */
    /*@ non_null*/ public final static Label UNDEFINED_NULL_INITIALIZATION = new Label("UndefinedNullInitialization");
    
    /** Used for assert statements generated from non-null checks when unboxing */
    /*@ non_null*/ public final static Label POSSIBLY_NULL_UNBOX = new Label("PossiblyNullUnbox");
    
    /** Used for assert statements generated from non-null checks when unboxing */
    /*@ non_null*/ public final static Label UNDEFINED_NULL_UNBOX = new Label("UndefinedNullUnbox");
    
    /** Used to designate a possible exception because of a potential negative size */
    /*@ non_null*/ public final static Label POSSIBLY_NEGATIVESIZE = new Label("PossiblyNegativeSize");
    
    /** Used to designate an undefined pure expression because of a potential negative size */
    /*@ non_null*/ public final static Label UNDEFINED_NEGATIVESIZE = new Label("UndefinedNegativeSize");
    
    /** Used to designate a possible exception because of a potential negative index */
    /*@ non_null*/ public final static Label POSSIBLY_NEGATIVEINDEX = new Label("PossiblyNegativeIndex");
    
    /** Used to designate an undefined pure expression because of a potential negative index */
    /*@ non_null*/ public final static Label UNDEFINED_NEGATIVEINDEX = new Label("UndefinedNegativeIndex");
    
    /** Used to designate a possible exception because of a potential too-large index */
    /*@ non_null*/ public final static Label POSSIBLY_TOOLARGEINDEX = new Label("PossiblyTooLargeIndex");
    
    /** Used to designate an undefined pure expression because of a potential too-large index */
    /*@ non_null*/ public final static Label UNDEFINED_TOOLARGEINDEX = new Label("UndefinedTooLargeIndex");
    
    /** Used to designate a possible exception because of a potential divide by 0 */
    /*@ non_null*/ public final static Label POSSIBLY_DIV0 = new Label("PossiblyDivideByZero");

    /** Used to designate an undefined pure expression because of a potential divide by 0 */
    /*@ non_null*/ public final static Label UNDEFINED_DIV0 = new Label("UndefinedDivideByZero");
    
    /** Used to designate an undefined pure expression because of a potential unsigned shift on negative bigint */
    /*@ non_null*/ public final static Label UNDEFINED_USR = new Label("UndefinedBigintUSR");
    
    /** Used to designate a potentially large shift value */
    /*@ non_null*/ public final static Label POSSIBLY_LARGESHIFT = new Label("PossiblyLargeShift");

    /** Used to designate a possible exception because of a cast of a reference value to a type that is not the type of the dynamic value */
    /*@ non_null*/ public final static Label POSSIBLY_BADCAST = new Label("PossiblyBadCast");

    /** Used to designate a POSSIBLY_BAD_CAST that occurs within a JML expression */
    /*@ non_null*/ public final static Label UNDEFINED_BADCAST = new Label("UndefinedBadCast");
    
    /** Used to designate a possible ArrayStoreException because of an array assignment */
    /*@ non_null*/ public final static Label POSSIBLY_BAD_ARRAY_ASSIGNMENT = new Label("PossiblyBadArrayAssignment");

    /** Used for checks of compatible specifications for functional interfaces */
    /*@ non_null*/ public final static Label POSSIBLY_INCOMPATIBLE_FUNCTIONAL_SPECS = new Label("PossiblyIncompatibleFunctionalSpecs");

    /** Used for cases that likely indicate an internal error or unimplemented option */
    /*@ non_null*/ public final static Label UNKNOWN = new Label("Unknown");


    // The following labels are used in BasicBlocker in converting Java control flow statements to basic blocks.
    // They are only used as assumptions and only in ESC. Their names are significant because they are used in 
    // generating trace and counterexample information.
    
    /** Used for basic assume statements generated from assignments -- only used internally in ESC */
    /*@ non_null*/ public final static Label ASSIGNMENT = new Label("Assignment", false);
    
    /** Used for assume statements generated from branches (then branch) -- only in ESC (BasicBlocker) */
    /*@ non_null*/ public final static Label BRANCHT = new Label("BranchThen", false);
    
    /** Used for assume statements generated from branches (else branch) -- only in ESC (BasicBlocker) */
    /*@ non_null*/ public final static Label BRANCHE = new Label("BranchElse", false);
    
    /** Used for assume statements generated from case statements in switch statements -- only used internally in ESC (BasicBlocker) */
    /*@ non_null*/ public final static Label CASECONDITION = new Label("Case", false);
    
    /** Used for assume statements generated from assignable clauses  -- only in ESC (BasicBlocker)*/
    /*@ non_null*/ public final static Label HAVOC = new Label("Havoc", false);
    
    

}
