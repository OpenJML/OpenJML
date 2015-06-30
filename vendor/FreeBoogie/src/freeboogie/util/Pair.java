package freeboogie.util;

/**
 * A pair.
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <F> the type of the first element
 * @param <S> the type of the second element
 */
public class Pair<F, S> {
  /**
   * Make a structure
   * @param f the first element
   * @param s the second element
   */
  public Pair(F f, S s) { first = f; second = s; }
  /** first */ public F first;
  /** second */ public S second;
}
