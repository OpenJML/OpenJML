/**
 * Copyright (c) 2005-2010 David R. Cok
 * @author David R. Cok
 * Created Jul 5, 2005
 */
package org.jmlspecs.openjml.eclipse;

// The ClassFileConstants import is an internal class - is the same
// information available in a public API?  (FIXME)
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
	public static final String eol = System.getProperty("line.separator");

	/** An enum used to indicate the level of compiler compliance level.  It
	 *  is translated into the appropriate value from the internal class.
	 */
	static public enum Level {
		/**
		 * An enum value corresponding to the 1.3 version of Java
		 */
		JLS1_3(ClassFileConstants.JDK1_3,"1.3"), 
		/**
		 * An enum value corresponding to the 1.4 version of Java
		 */
		JLS1_4(ClassFileConstants.JDK1_4,"1.4"), 
		/**
		 * An enum value corresponding to the 1.5(5.0) version of Java
		 */
		JLS1_5(ClassFileConstants.JDK1_5,"1.5"),

		/**
		 * An enum value corresponding to the 1.6 version of Java
		 */
		JLS1_6(ClassFileConstants.JDK1_6,"1.6"),

		/**
		 * An enum value corresponding to the 1.7 version of Java
		 */
		JLS1_7(ClassFileConstants.JDK1_7,"1.7");

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
	 * (particularly by the parser).  This is set for Java 1.5;
	 * there has been no testing at all for other values.
	 */
	public static Level jlsLevel = Level.JLS1_5;

	/**
	 * This is the version of AST nodes to use in constructing abstract
	 * syntax trees.  It cannot be changed without reprogramming the
	 * code used to generate trees - between changes of this value, the
	 * structure of the nodes changes and the existence of different node
	 * classes.
	 */
	//  final static public int astLevel = org.jmlspecs.eclipse.jmldom.AST.JLS3;

	/** The ast generator used in type bindings and in Eclipse ASTs. */
	//  final static public org.eclipse.jdt.core.dom.AST ast = org.eclipse.jdt.core.dom.AST.newAST(Env.astLevel);

	// Some hard-coded strings

	//  /** The default name of the specs project */
	//  final static public String defaultSpecsProjectName = "specsProject";  // FIXME - delete this

	/** The fixed name of the folder that holds all the source folders for the specs path items. */
	final static public String specsContainerName = "specspath";

	/** The root of the source folder names, each on of which is linked to the 
	 * location of an item on the specs path; the names have numerical suffixes, in
	 * order - that is, specs1, specs2, specs3, ...
	 */
	final static public String specsFolderRoot = "specs";

	//  /** The name of the folder containing the specification library. */  // FIXME
	//  final static public String specsLibraryName = "specs";

	//  /** The root of the source folder names, each one of which is linked to the 
	//   * location of an item on the class path that might contain compilable java
	//   * files; the names have numerical suffixes, in
	//   * order - that is, srcs1, srcs2, srcs3, ...
	//   * It is also used as the name of the folder containing all of these
	//   * source folders.
	//   */
	//  final static public String srcFolderRoot = "srcs";
}
