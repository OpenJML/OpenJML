package org.jmlspecs.utils;

import org.jmlspecs.annotation.*;

/** This class is an interface for types within JML.  This could simply
 * encapsulate something like TypeMirror, but we want an implementation
 * that works on 1.5 as well.
 * 
 * @author David R. Cok
 *
 */
@Pure
public interface IJMLTYPE {

    public boolean equals(IJMLTYPE t);
    public boolean equals(Object t);

    public boolean isSubtypeOf(IJMLTYPE t);
    public Class<?> erasure();
    //public int numargs();
    //public IJMLTYPE arg(int i);
    public IJMLTYPE[] typeargs();
    public boolean isArray();
    public IJMLTYPE getComponentType();
}
