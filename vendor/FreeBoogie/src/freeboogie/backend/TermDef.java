package freeboogie.backend;

/**
 * Represents a term definition.
 * 
 * The most general type of term has a sort for each of its
 * |n| arguments and a sort for its result. In mathematical notation
 * that would be written {@code name : s1 x s2 x ... x sn -> s}.
 * If n is zero then we call the term a constant.
 * 
 * There are two convenience specializations.
 * 
 * It would be cumbersome to define (aka register) constants 1, 2, 3,...
 * individually, and not very efficient. Therefore this class provides
 * a way to register all instances of a certain Java type as constants
 * in one go.
 * 
 * Also, for operators that are associative and commutative it is
 * cumbersome to construct binary trees. Instead we allow definitions
 * of the form {@code name : [sa] -> sr}, which specify one sort for the
 * argument and one sort for the result. These functions are called "nary".
 * 
 * NOTE that the name being defined is not stored in this class.
 * So, strictly speacking, this is a term sort. The names, and relationship
 * to their sorts, are handled by the {@code Builder}.
 * 
 * TODO the terminology around here is not very clear
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TermDef {
  /**
   * Represents the Java type that is mapped to a prover sort
   * by this (set of) term definition(s).
   */
  public final Class cls;
  
  /**
   * Containes the required sorts for the arguments.
   * Please don't change the content of this if you hate (ugly) surprises.
   */
  public final Sort[] argSorts;
  
  /**
   * The required sort of the arguments of an associative-commutative term.
   */
  public final Sort naryArgSort;
  
  /**
   * The sort of this term.
   */
  public final Sort retSort;

  /**
   * Constructs a typical definition {@code name : s1 x ... x sn -> s}.
   * @param argSorts {@code s1 x ... x sn}
   * @param retSort {@code s}
   */
  public TermDef(Sort[] argSorts, Sort retSort) {
    this.cls = null;
    this.argSorts = argSorts;
    this.naryArgSort = null;
    this.retSort = retSort;
  }

  /**
   * Constructs a term definition that maps a Java type to a prover sort.
   * @param cls the Java type
   * @param retSort the prover sort
   */
  public TermDef(Class cls, Sort retSort) {
    this.cls = cls;
    this.argSorts = null;
    this.naryArgSort = null;
    this.retSort = retSort;
  }

  /**
   * Constructs a term definition for nary terms.
   * @param naryArgSort the sort of the arguments
   * @param retSort the sort of the result
   */
  public TermDef(Sort naryArgSort, Sort retSort) {
    this.cls = null;
    this.argSorts = null;
    this.naryArgSort = naryArgSort;
    this.retSort = retSort;
  }
}
