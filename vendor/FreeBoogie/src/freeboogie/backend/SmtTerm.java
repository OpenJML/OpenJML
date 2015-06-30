package freeboogie.backend;

/**
 * S-expressions.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SmtTerm extends Term {
  
  static final private SmtTerm[] noChild = new SmtTerm[0]; 
  
  /** The identifier or this term. */
  final public String id;
  
  /** 
   * If {@code id} says this term is a constant then {@code data}
   * contains the actual value of the constant (and {@code children}
   * is empty).
   */
  final public Object data;
  
  /** The children of this term, nonnull. */
  final public Term[] children;
  
  /**
   * Creates a new term represented by an s-expression.
   * @param sort the sort of this term
   * @param id the identifier of this term
   * @param children the children of this term
   */
  public SmtTerm(Sort sort, String id, Term[] children) {
    super(sort); 
    this.id = id;
    this.data = null;
    this.children = children;
    //System.out.println("mk> " + id + " " + children.length);
    assert this.children.length > 0;
  }

  /**
   * Creates a new constant.
   * @param sort the sort of this constant
   * @param id the identifier of this constant type
   * @param data the constant
   */
  public SmtTerm(Sort sort, String id, Object data) {
    super(sort); 
    this.id = id;
    this.data = data;
    this.children = noChild;
    //System.out.println("mk2> " + id + " " + data);
  }
}
