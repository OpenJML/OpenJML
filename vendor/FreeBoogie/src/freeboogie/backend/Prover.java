package freeboogie.backend;

/**
 * A prover can be used to check if a formula is satisfiable,
 * given a set of assumptions. The prover may need to be restarted
 * before being used.
 * 
 * TODO add properties, like timelimit
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public interface Prover {
  /**
   * Returns a term builder whose terms are understood by this prover.
   * @return a builder for terms and formulas
   */
  public TermBuilder getBuilder();
  
  /**
   * Adds {@code t} as an assumption.
   * @param t teh assumption
   * @throws ProverException if something goes wrong
   */
  public void assume(Term t) throws ProverException;
  
  /**
   * Retract the last assumption. This discards all the empty 
   * assumption frames created after the last assumption.
   * @throws ProverException if something goes wrong
   */
  public void retract() throws ProverException;
  
  /**
   * Make a new frame of assumptions.
   * @throws ProverException if something goes wrong
   */
  public void push() throws ProverException;
  
  /**
   * Removes the last frame of assumptions.
   * @throws ProverException if something goes wrong
   */
  public void pop() throws ProverException;

  /**
   * Checks whether {@code t} is satisfiable, given the existing
   * assumptions.
   * 
   * @param t the query, must have sort PRED 
   * @return whether {@code t} is satisfiable
   * @throws ProverException if something goes wrong
   */
  public boolean isSat(Term t) throws ProverException;
  
  /**
   * Returns a detailed answer to the last {@code isSat}
   * query. This can be either a proof of unsatisfiability,
   * or a probable model. It can also be "sorry, no more info".
   * 
   * @return details of the last prover answer
   */
  public ProverAnswer getDetailedAnswer();

  /**
   * Kills and restarts the prover process. Then it resends
   * all the assumptions that are on the stack. 
   * @throws ProverException if something goes wrong
   */
  public void restartProver() throws ProverException;
}
