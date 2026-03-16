/**
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2005-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.io.StringReader;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.internal.compiler.problem.DefaultProblem;
import org.jmlspecs.annotation.Nullable;

import com.sun.tools.javac.code.Symbol;

// FIXME - perhaps should be using DefaultProblem.errorReportSource
// instead of carting the lineStart and end positions around
// FIXME - should we inherit from CategorizedProblem directly? but then we need to copy errorReportSource
// FIXME - clean up this file; severities, file position, error range info
/**
 * This is a class that implements the eclipse IProblem interface
 * tailored for the JmlParser.  It is mostly present to provide an
 * interface between the OpenJML plugin and the internal class that this class
 * extends, but it also provides some utility functions to produce 
 * and report errors and warnings.  It also adds some additional
 * information to its parent class to hold information relevant to
 * line and print oriented problem reporting.
 */
public class JmlEclipseProblem extends DefaultProblem {

	/** This holds a reference to the source text as known
	 *  at the time the problem was created, or null if
	 *  the source text is not available.
	 */
	public @Nullable String sourceText;

	/** Holds the symbol, such as a MethodSymbol, to which the problem relates */
	public @Nullable Symbol sourceSymbol;
	/**
	 * Holds the 1-based character position of the beginning of the line indicated
	 * by the line argument (and on which startPosition resides); the
	 * value is -1 if the lineStart information is not available.
	 */
	public int lineStart;

	/**
	 * Holds the 1-based character position of the end of the line indicated
	 * by the line argument (and on which startPosition resides); this is
	 * the character position of the line termination or end of file;
	 * the value is -1 if the line end information is not available.
	 */
	public int lineEnd;

	/** The severity of the problem.  This duplicates a private field in the 
	 * super class, but we have to because isError() just returns the opposite of
	 * isWarning(), and we cannot get at other severities.
	 */
	final public int severity;

	// These are copied here for reference from the internal superinterface ProblemSeverities
	//    final int Ignore = -1; // during handling only
	//    final int Warning = 0; // during handling only
	//
	//    final int Error = 1; // when bit is set: problem is error, if not it is a warning
	//    final int AbortCompilation = 2;
	//    final int AbortCompilationUnit = 4;
	//    final int AbortType = 8;
	//    final int AbortMethod = 16;
	//    final int Abort = 30; // 2r11110
	//    final int SecondaryError = 64;

	/**
	 * Constructor for a new problem.
	 * @param ifile    The workspace IFile in which the offending source text is located, if any (otherwise null)
	 * @param message  The problem message
	 * @param id       A numerical id for the problem
	 * @param severity The severity of the problem, using one of the constants listed above (e.g. Error, Warning)
	 * @param startPosition The 1-based character position within the line that begins the offending region
	 * @param endPosition   The 1-based character position within the line that ends (not one after) the offending region
	 * @param line     The 1-based line within the source text containing the offending source text
	 * @param source   A reference to the source text, or null
	 * @param lineStart The 1-based character position of the beginning of the stated line in the IFile or source text, or -1 if not known
	 * @param lineEnd   The 1-based character position of the end of the stated line (that is, where the line termination character is) in the IFile or source text, or -1 if not known
	 */
	public JmlEclipseProblem(IFile ifile, String message, int id, int severity,
			int startPosition, int endPosition, int line, String source,
			int lineStart, int lineEnd) {
		super(ifile == null ? null : ifile.getFullPath().toString().toCharArray(),
				message, id, null, severity,
				startPosition, endPosition, line, 
				startPosition - lineStart);
		// The last argument is the column number of the beginning of the problem;
		// it does not appear to be used in anything the OpenJML plug-in does.
		// The null argument between the id and the severity is for arguments to
		// the problem message.  We don't use those in CompilerProblems.
		this.sourceText = source;
		this.lineStart = lineStart;
		this.lineEnd = lineEnd;
		this.severity = severity;
	}

	/** An identifier for the JML category of problems.  This is a randomly chosen
	 * number that needs to be different than the numbers defined in
	 *  org.eclipse.jdt.core.compiler.CategorizedProblem.
	 */
	private final int JML_CAT = 15423;

	/** An identifier for the JML category of problems.  This is a randomly chosen
	 * number that needs to be different than the numbers defined in
	 *  org.eclipse.jdt.core.compiler.CategorizedProblem.
	 */
	public int getCategoryID() {
		return JML_CAT;
	}

//	/**
//	 * A utility method to obtain a reference to the source text for
//	 * an ICompilationUnit, or null if it could not be obtained.
//	 * @param icu The ICompilationUnit
//	 * @return The source text for the ICompilationUnit
//	 */
//	private static /*@Nullable*/ String getSource(ICompilationUnit icu) {
//		if (icu == null) return null;
//		try {
//			return icu.getSource();
//		} catch (Exception e) {
//			return null;
//		}
//	}

//	/**
//	 * Converts the given IProblem into an instance of JmlEclipseProblem,
//	 * using additional information from the given ICompilationUnit.
//	 * The line start and end information is not available.
//	 * @param p  The base problem
//	 * @param icu The ICompilationUnit from which to get position information
//	 */
//	public JmlEclipseProblem(IProblem p, ICompilationUnit icu) {
//		this((IFile)icu.getResource(), p.getMessage(), p.getID(), 
//				p.isError() ? ProblemSeverities.Error : p.isWarning() ? ProblemSeverities.Warning : -1,
//				p.getSourceStart(), p.getSourceEnd(), p.getSourceLineNumber(),
//				getSource(icu), -1, -1);
//	}

	/**
	 * A utility method that prints the given problem on the given PrintStream
	 * @param out the stream on which to write the problem
	 * @param p   The IProblem to print
	 */
	static public void printProblem(PrintStream out, IProblem p) {

		char[] filenameAsChars = p.getOriginatingFileName();
		// The above is the workspace-relative filename
		String filename = null;
		IResource resource = null;

		// translate the workspace-relative filename into a file-system
		// filename
		if (filenameAsChars != null) {
			filename = String.valueOf(p.getOriginatingFileName());
			IWorkspace workspace = ResourcesPlugin.getWorkspace();
			IWorkspaceRoot root = workspace.getRoot();
			resource = root.findMember(filename);
			if (resource != null) {
				filename = resource.getLocation().toOSString();
				// FIXME make relative to user directory?
			}
		}

		// Print the filename, line number and message
		int line = p.getSourceLineNumber();
		String lineString = line <= 0 ? "" : String.valueOf(line);
		if (Env.testingMode) {
			// This format has been historically used for test outputs.
			// If you change it you will need to regenerate and recheck the 
			// test output files.
			out.println((filename == null ? "" : "FILE") + " " +
					lineString + 
					": [" + (p.getID() & IProblem.IgnoreCategoriesMask)+ "] " + 
					p.getMessage());
		} else {
			// This format generates links to the source code in the Eclipse console
			String ff = filename == null ? null : filename.replaceAll("\\\\","/");
			out.println((filename == null ? lineString : ("("+ff+":"+lineString+")")) +
					" [" + (p.getID() & IProblem.IgnoreCategoriesMask)+ "] " + 
					p.getMessage());
		}

		if (p.getSourceStart() < 0) return;

		// Get the line of text, if possible
		String sline = null;
		int lineStart = -1;
		if (p instanceof JmlEclipseProblem) {
			// We're here if the problem is a JmlEclipseProblem.  We have source text.
			// If we have line start and end information, we can get the offending
			// line immediately.
			JmlEclipseProblem cp = (JmlEclipseProblem)p;
			String stext = cp.sourceText;
			lineStart = cp.lineStart;
			if (lineStart >= 0 && stext != null) {
				// Caution: cp.lineEnd is the characterPosition of the last
				// line-termination character, if any.  
				int k = cp.lineEnd + 1;// since the end index in substring is one beyond the end
				sline = stext.substring(lineStart,k > 0 && k <= stext.length() ? k : stext.length());
			}
		}
		BufferedReader r = null;
		try {
			if (sline == null) try {
				if (p instanceof JmlEclipseProblem) {
					// We're here if we have JmlEclipseProblem without line start and end
					// information.  This happens if we have a non-JmlEclipseProblem that
					// was converted to a JmlEclipseProblem.  It typically then has source
					// text but not line start information.
					String stext = ((JmlEclipseProblem)p).sourceText;
					if (stext != null) r = new BufferedReader(new StringReader(stext));
				}
				if (r == null && resource != null && (resource instanceof IFile)) {
					// We're here if we have a non-JmlEclipseProblem, and consequently we
					// have neither source text nor line start information.  So we have to
					// open the resource and read the requisite number of lines.
					// This is a bit expensive, but we only do it once for each 
					// error message.
					r = new BufferedReader(new InputStreamReader(((IFile)resource).getContents())); 
				} 

				if (r == null) return;

				// Skip (line-1) lines of text, including line terminations,
				// and count the number of characters read.

				int count = 0; // Number of chars read
				int c = 0;

				--line;
				if (line > 0) {
					// TODO: This could perhaps be more efficient, but it is
					// only used once per error message.
					c = r.read();
					count++;
					while (line > 0) {
						if (c == -1) return; // SHould not end before getting 
						                     // to the beginning of the desired line
						                     // If we do, we just pretend that
						                     // no text is available
						if (c == '\r') {
							do {
								--line;
								c = r.read();
								count++;
								if (c == '\n') {
									// Ignore this following NL
									c = r.read();
									count++;
								}
							} while (c == '\r');
						} else if (c == '\n') {
					        --line;
							c = r.read();
							count++;
						} else {
							c = r.read();
							count++;
						}
					}
				}
				// Have read the first character beyond the end of the requisite 
				// number of lines to be skipped.
				if (c == '\r' || c == '\n') {
					// The next line is empty
					sline = Env.eol;
				} else if (c == -1) {
					// Still not enough data
					return;
				} else {
					sline = (char)c + r.readLine() + Env.eol;
				}
				if (lineStart == -1) lineStart = count; // lineStart is 1-based
				r.close();
			} catch (Exception e) {
				Log.errorlog("INTERNAL ERROR - Exception occurred while printing a Problem: "
						+ e,e);
				return;
				// OK to quit since we just leave out some detail of the error
			}
			if (sline != null) {
				// Print the line of source text on which the error lies
				out.print(sline);  // line termination usually included, except perhaps if
				// this is the last line of a file or if the source was
				// provided directly as a string by a test or if the line was too
				// long and has been truncated.
				{ int last = sline.length() -1;
				int c = sline.charAt(last);
				if (!(c == '\n' || c == '\r')) out.println();
				}
				
				// Now mark the error itself with ^^ characters from
				// getSourceStart() through getSourceEnd()
				// st is the beginning of the error section to mark
				int st = p.getSourceStart();
				int length = p.getSourceEnd() - st + 1;
				st -= lineStart; // Now st is the amount of white space to put before the first ^
				
				// Do some adjustment in case st points into the line termination characters
				// This is needed because when problems are marked by highlighting
				// in the Eclipse editors, no highlighting occurs if the error
				// is completely in the line termination characters.
				int extra = 0;
				if (st >= sline.length()) {
					extra = st - sline.length();
					st = sline.length();
				}
				
				// The end of the error region can be on the next line, in which
				// case we still just print one line and put ellipsis at the end
				// of the string of ^^s
				boolean ellipsis = false;
				if (st + extra + length > sline.length() + 2) {
					length = sline.length() + 2 - st - extra;
					if (length <= 0) length = 1;
					ellipsis = true;
				}
				int i = 0;
				while (--st >= 0) out.print(sline.charAt(i++) == '\t'?"\t":" ");
				while (--extra >= 0) out.print(" ");
				while (--length >= 0) out.print("^");
				if (ellipsis) out.print("...");
				out.println();
			}
		} finally {
			if (r != null) {
				try { r.close(); } 
				catch (java.io.IOException e) {
					Log.errorlog("Failed to close a BufferedReader",e);
				}
			}
		}
	}

}
