/*
 * This file is part of the OpenJML project. 
 * Author: David R. Cok
 */
package org.jmlspecs.openjml.proverinterface;


import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;

import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCExpression;

/**
 * A prover can be used to check if a formula is satisfiable,
 * given a set of assumptions. The prover may need to be restarted
 * before being reused.
 * <P>
 * The assume calls take a JCExpression encoding the logical expression
 * that the prover is to assume.  This is a OpenJDK AST but of restricted
 * form.  In particular, only the following AST nodes are allowed (there is
 * no runtime check of this restriction):
 * <UL>
 * <LI>JCBinary - with any Java operator
 * <LI>JmlBinary - with any JML operator
 * <LI>JCUnary - with any Java operator
 * <LI>JCIdent - the identifier for a logical variable, with the
 *      type field giving the Java type of the variable
 * <LI>JCConditional - an if-then-else (i.e. ?:) construct
 * <LI>JmlBBFieldAccess - encodes field access (replaces JCFieldAccess)
 * <LI>JmlBBArrayAccess - array access, replacing JCArrayAccess
 * <LI>JCParens - not needed but helps to keep pretty printed expressions less confusing
 * <LI>JCLiteral - for boolean, integer, null literals
 * <LI>JCMethodInvocation - FIXME - needs explanation
 * </UL>
 * 
 * 
 * 
 * TODO add properties, like timelimit
 *
 * @author David Cok, based on previous work by rgrig 
 */
// FIXME - appears not used
public interface IProver {

    /** Returns an identifying name for the prover */
    public String name();

    /**
     * Adds {@code tree} as an assumption; the concrete IProver is
     * responsible to translate the AST into prover-dependent form.
     * @param tree the assumption
     * @return an integer id for the assumption (or 0 if ids are not supported)
     * @throws ProverException if something goes wrong
     */
    public int assume(/*@ non_null*/JCExpression tree) throws ProverException;

    /**
     * Adds {@code tree} as an assumption; the concrete IProver is
     * responsible to translate the AST into prover-dependent form.
     * @param tree the assumption
     * @param weight a weight to be associated with the assertion (may be
     *      ignored if the prover does not support weights)
     * @return an integer id for the assumption (or 0 if ids are not supported)
     * @throws ProverException if something goes wrong
     */
    public int assume(/*@ non_null*/JCExpression tree, int weight) throws ProverException;

    /** Tells the prover to define a given variable as the stated type
     * (not all provers need this)
     * @param id the name of the variable
     * @param type the type of the variable
     * @throws ProverException if something goes wrong
     */
    public void define(/*@ non_null*/String id, /*@ non_null*/Type type) throws ProverException;

    /** Tells the prover to define a given variable as the stated type and with the given value
     * (not all provers need this)
     * @param id the name of the variable
     * @param type the type of the variable
     * @param value the value the variable is an abbreviation for
     * @throws ProverException if something goes wrong
     */
    public void define(/*@ non_null*/String id, /*@ non_null*/Type type, /*@ non_null*/ JCExpression value) throws ProverException;

    /**
     * Retract the last assumption.
     * @throws ProverException if something goes wrong
     */
    public void retract() throws ProverException;

    /**
     * Retracts a specific assumption.
     * @param i the assertion to retract
     * @throws ProverException if something goes wrong
     */
    public void retract(int i) throws ProverException;

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

    /** Checks whether the set of assertions known to the prover so far
     * is satisfiable or not
     * @return an object containing the details of the prover answer
     * @throws ProverException if something goes wrong
     */
//    /*@ non_null*/
//    public IProverResult check() throws ProverException;
    /*@ non_null*/
    public IProverResult check(boolean details) throws ProverException;

    /**
     * Kills and restarts the prover process. Then it resends
     * all the assumptions that are on the stack. 
     * @throws ProverException if something goes wrong
     */
    public void restartProver() throws ProverException;
    
    /** Kills the prover 
     * @throws ProverException if something goes wrong
     */
    public void kill() throws ProverException;
    
    
    public void reassertCounterexample(ICounterexample ce);
    
    public Supports supports();

    static public class Supports {
        public Supports() {
            retract = false;
            unsatcore = false;
        }
        public boolean retract;
        public boolean unsatcore;
    }
        

}
