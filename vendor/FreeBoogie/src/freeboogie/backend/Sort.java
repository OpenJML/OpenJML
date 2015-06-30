package freeboogie.backend;

/**
 * The sorts supported by the backend. There is not much 
 * variation between the sorts supported by different provers
 * so we stick to a conservative set of sorts.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public enum Sort {
  /** supertype for all non-predicates */ ANY(null),
  /** a predicate */ PRED(null),
  /** a value */ VALUE(ANY),
  /** a boolean value (NOT a predicate) */ BOOL(VALUE),
  /** a boolean variable */ VARBOOL(BOOL),
  /** an integer */ INT(VALUE),
  /** an integer variable */ VARINT(INT),
  /** a real number */ REAL(VALUE),
  /** a real variable */ VARREAL(REAL),
  /** a reference */ REF(VALUE),
  /** a reference variable */ VARREF(REF);
  
  
  /* Note: The VARx sorts are used for better checking of quantifiers.
   * That is, in some places you want to enforce that you have a variable
   * of a certain type, not just an expression.
   */
  
  /** The supersort of {@code this}. */
  public final Sort superSort;

  /**
   * Constructs a sort, with a given super sort.
   * @param superSort the super sort
   */
  Sort(Sort superSort) {
    this.superSort = superSort;
  }
  
  /**
   * Tests whether {@code this} is a subsort of {@code other}.
   * @param other the potential supersort
   * @return whether {@code this <: other}
   */
  public boolean isSubsortOf(Sort other) {
    if (this == other) return true;
    if (superSort == null) return false;
    return superSort.isSubsortOf(other);
  }
}
