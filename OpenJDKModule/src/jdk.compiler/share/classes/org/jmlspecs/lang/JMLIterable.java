package org.jmlspecs.lang;
import org.jmlspecs.annotation.*;

/** This is the counterpart for model types to Iterable<E>.
 * @author DRCok
 *
 * @param <E> the type of the element returned by iterators
 */
public interface JMLIterable<E> {

    //@ ensures \fresh(\result);
    @NonNull
    JMLIterator<E> iterator();
}
