package org.jmlspecs.utils;

import org.jmlspecs.annotations.*;

/** This class is an interface for types within JML.  This could simply
 * encapsulate something like TypeMirror, but we want an implementation
 * that works on 1.5 as well.
 * 
 * @author David R. Cok
 *
 */
@Pure
public interface IJMLType {

    public boolean equals(IJMLType t);
    public boolean equals(Object t);

    public boolean isSubtypeOf(IJMLType t);
}
