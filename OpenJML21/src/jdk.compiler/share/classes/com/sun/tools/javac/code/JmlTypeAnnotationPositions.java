package com.sun.tools.javac.code;

import org.jmlspecs.openjml.visitors.IJmlVisitor;

import com.sun.tools.javac.code.TypeAnnotations.TypeAnnotationPositions;

public class JmlTypeAnnotationPositions extends TypeAnnotationPositions implements IJmlVisitor {

	JmlTypeAnnotationPositions(TypeAnnotations typeAnnotations, boolean sigOnly) {
		typeAnnotations.super(sigOnly);
		// TODO Auto-generated constructor stub
	}

}
