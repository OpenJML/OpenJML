package freeboogie.ast.gen;

/**
 * Does not track location.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 * @param <T> type
 */
public class NullLocation<T> extends Location<T> {
  
  @Override
  public Location<T> advance(@SuppressWarnings("unused") T element) {
    return this;
  }
  
  @Override
  public String toString() {
    return "(location not tracked)";
  }
}
