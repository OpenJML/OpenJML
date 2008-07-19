package org.jmlspecs.openjml.proverinterface;


import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;

/**
 * A prover can be used to check if a formula is satisfiable,
 * given a set of assumptions. The prover may need to be restarted
 * before being used.
 * 
 * TODO add properties, like timelimit
 *
 * @author David Cok, based on previous work by rgrig 
 * @author reviewed by TODO
 */
public interface IProver {
//  /**
//   * Returns a term builder whose terms are understood by this prover.
//   * @return a builder for terms and formulas
//   */
//  public TermBuilder getBuilder();
  
  /**
   * Adds {@code t} as an assumption.
   * @param t the assumption
   * @throws ProverException if something goes wrong
   */
    public int assume(Term t) throws ProverException;
    
    public int assume(Term t, int weight) throws ProverException;

    public int assume(Context context, JCTree tree) throws ProverException;

    public int assume(Context context, JCTree tree, int weight) throws ProverException;

  // DRC - added FIXME - definition
  public void define(String id, Type t) throws ProverException;
  
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
  
  public IProverResult check() throws ProverException;
  
  /**
   * Checks whether the set of current assumptions is satisfiable.
   * 
   * @return whether the assumptions are satisfiable
   * @throws ProverException if something goes wrong
   */
  public boolean isSat() throws ProverException;
  
  /**
   * Returns a detailed answer to the last {@code isSat}
   * query. This can be either a proof of unsatisfiability,
   * or a probable model. It can also be "sorry, no more info".
   * 
   * @return details of the last prover answer
   */
  public IProverResult getDetailedAnswer();

  /**
   * Kills and restarts the prover process. Then it resends
   * all the assumptions that are on the stack. 
   * @throws ProverException if something goes wrong
   */
  public void restartProver() throws ProverException;
}
