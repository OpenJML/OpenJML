package freeboogie.util;

/**
 * For functions that take {@code P} and return {@code R}
 *
 * @author rgrig 
 * @author reviewed by TODO
 * @param <P> the type of the parameter
 * @param <R> teh type of the result
 */
public abstract class ClosureR<P, R> {
  /**
   * Process {@code p}.
   * @param p what to process
   * @return whatever you want
   */
  public abstract R go(P p);
}
