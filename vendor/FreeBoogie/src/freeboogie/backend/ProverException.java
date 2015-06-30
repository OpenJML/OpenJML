package freeboogie.backend;

/**
 * Thrown when something goes wrong in the communication
 * with the prover. It might die, or talk rubbish, or...
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class ProverException extends Exception {

  /**
   * Constructs a prover exception.
   * @param reason what went wrong
   */
  public ProverException(String reason) {
    super(reason);
  }

  /**
   * Constructs a prover exception.
   * @param reason what went wrong
   */
  public ProverException(Throwable reason) {
    super(reason);
  }

  /**
   * Constructs a prover exception.
   * @param reason what went wrong
   * @param rootReason what is the cause of the reason (sic!)
   */
  public ProverException(String reason, Throwable rootReason) {
    super(reason, rootReason);
  }

}
