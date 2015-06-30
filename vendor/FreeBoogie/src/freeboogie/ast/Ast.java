package freeboogie.ast;

/** Base class for the AST hierarchy. */
public abstract class Ast {
  /** The location of this AST node. */
  protected AstLocation location;
  
  /**
   * Returns the location of this AST node. 
   * @return the location of this AST node.
   */
  public AstLocation loc() {
    return location;
  }
  
  /**
   * Dispatches to {@code e.eval} based on the static type of the node
   * and the dynamic type of {@code e}.
   * @param <R> the type of the result computed by the evaluator
   * @param e the evaluator
   * @return the result computed by the evaluator
   */
  abstract public <R> R eval(Evaluator<R> e);
}
