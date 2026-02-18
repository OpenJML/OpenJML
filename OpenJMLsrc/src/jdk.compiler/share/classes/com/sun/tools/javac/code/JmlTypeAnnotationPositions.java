package com.sun.tools.javac.code;

import org.jmlspecs.openjml.visitors.IJmlVisitor;

import com.sun.tools.javac.code.TypeAnnotations.TypeAnnotationPositions;

/** This class is defined so that it implements IJmlVisitor, but keeps all the functionality of its parent class. */

// FIXME - not at all sure that this implementation is correct for its intended use
public class JmlTypeAnnotationPositions extends TypeAnnotationPositions implements IJmlVisitor {

    JmlTypeAnnotationPositions(TypeAnnotations typeAnnotations, boolean sigOnly) {
        typeAnnotations.super(sigOnly);
        // TODO Auto-generated constructor stub
    }

}
