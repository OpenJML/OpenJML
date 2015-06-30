package freeboogie.backend;

/**
 * A term that knows its sort. This class is intended to
 * be subclassed (in conjunction with concrete prover classes).
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class Term {
  private Sort sort;
  
  /**
   * Constructs a term, and remembers its sort.
   * @param sort
   */
  public Term(Sort sort) {
    this.sort = sort;
  }
  
  /**
   * Returns the sort of this term.
   * @return the sort of this term
   */
  public Sort sort() {
    return sort;
  }
}
