/**
 * This file is part of the OpenJML project.
 * Copyright (c) 2005-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.internal.compiler.classfmt.ClassFileConstants;

/**
 * A class of generally useful quantities that are expected to be
 * constant throughout an execution.
 */
public class Env {

	/**
	 * When true, affects some output production to be more amenable to
	 * automated testing.  For example, filenames are not printed in
	 * error messages, since they will change with changes in testing 
	 * platform location of workspace, and reorganization of test sources.
	 */
	public static boolean testingMode = false;

	/**
	 * A convenience field holding the local system definition of the 
	 * end of line character sequence
	 */
	public static final String eol = System.getProperty("line.separator"); //$NON-NLS-1$

	/** An enum used to indicate the level of compiler compliance level.  It
	 *  is translated into the appropriate value from the internal class.
	 */
	static public enum Level {
		/**
		 * An enum value corresponding to the 1.3 version of Java
		 */
		JLS1_3(ClassFileConstants.JDK1_3,"1.3"),  //$NON-NLS-1$
		/**
		 * An enum value corresponding to the 1.4 version of Java
		 */
		JLS1_4(ClassFileConstants.JDK1_4,"1.4"),  //$NON-NLS-1$
		/**
		 * An enum value corresponding to the 1.5(5.0) version of Java
		 */
		JLS1_5(ClassFileConstants.JDK1_5,"1.5"), //$NON-NLS-1$

		/**
		 * An enum value corresponding to the 1.6 version of Java
		 */
		JLS1_6(ClassFileConstants.JDK1_6,"1.6"), //$NON-NLS-1$

		/**
		 * An enum value corresponding to the 1.7 version of Java
		 */
		JLS1_7(ClassFileConstants.JDK1_7,"1.7"); //$NON-NLS-1$

		/**
		 * The ClassFileConstants value corresponding to this enum instance.
		 */
		final private long javaLevel;

		/**
		 * The source level as a String
		 */
		final private String sourceLevel;

		/**
		 * Constructs an enum value given a value of ClassFileContants, such as
		 * JDK1_5.
		 * @param j the value of the compiler compliance level to use
		 * @param source the compiler compliance level as a String
		 */
		private Level(long j, String source) { 
			javaLevel = j; 
			sourceLevel = source;
		}

		/**
		 * @return the internal ClassFileConstants value that corresponds to the
		 *         enum
		 */
		public long classFileConstant() { return javaLevel; }

		/**
		 * The level of source code to be parsed expressed as a String.
		 * @return the source code level in String form
		 */
		public String sourceLevel() { return sourceLevel; }
	};

	/**
	 * The value of Java language level handled by this code
	 * (particularly by the parser). 
	 */
	public static Level jlsLevel = Level.JLS1_7;

}
