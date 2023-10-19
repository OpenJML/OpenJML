package org.jmlspecs.runtime;

import org.jmlspecs.annotation.*;

/** The runtime representation of the \TYPE type in JML.
 * FIXME - why is it an interface?
 * 
 * @author David R. Cok
 *
 */
/*@ pure */
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
