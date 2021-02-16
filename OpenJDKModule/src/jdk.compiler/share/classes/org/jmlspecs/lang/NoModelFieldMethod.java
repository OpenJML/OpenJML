package org.jmlspecs.lang;

/** This method is thrown at runtime by RAC if there is no implementation for
 * a model field
 */
public class NoModelFieldMethod extends RuntimeException {
    private static final long serialVersionUID = -7921925714647145483L;

    public NoModelFieldMethod() { // FIXME - fix to take an argument
        super("There is no implementation (represents clause) for model field " );
    }

}
