package org.jmlspecs.lang;

/** This is the counterpart for model types to Iterable<E>.
 * @author DRCok
 *
 * @param <E> the type of the element returned by iterators
 */
public interface JMLIterable<E> {

    //@ ensures \fresh(\result);
    /*@non_null*/
    JMLIterator<E> iterator();
}
