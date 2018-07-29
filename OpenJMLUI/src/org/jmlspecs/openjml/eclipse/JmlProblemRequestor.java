/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.io.PrintStream;
import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.annotation.SpecPublic;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.code.Symbol;

// TODO - The plugin tool reports problems by directly calling an instance
// of this IProblemRequestor.  The Eclipse framework actually uses
// a combination of a ProblemReporter to which problems are reported
// and requestors that can subscribe to problem reports.  Perhaps we
// should correct to that model.

/**
 * This is an implementation of the Eclipse IProblemRequestor
 * interface as used in this application.  Upon receiving problem
 * reports (by calls of acceptProblem), it creates and records an Eclipse
 * problem marker specific to this plugin.
 */
/*
 * It also adds this bit of functionality - the ability to provide a mapping from 
 * IFile paths to working copies so that the right source text 
 * can be associated with a given problem message without having
 * to be sure that potential changes are written to disk.
 * TODO - this is not used at present, but is left in for now in case we 
 * implement this later.
 */
public class JmlProblemRequestor implements IProblemRequestor {

	/**
	 * This is a map of filename to compilation unit.
	 * The filename is gotten from IResource.getFullPath().toString().  
	 * The compilation unit is typically a working copy, not necessarily 
	 * saved to disk. Its text information can be obtained from 
	 * getSource() after reconciliation.
	 */
	private Map<String,ICompilationUnit> map = null;

	/** The Eclipse project associated with this problem requestor */
	@SpecPublic @Nullable 
	protected IProject project;

	/**
	 * Returns the ICompilationUnit corresponding to the given path,
	 * or null if none found
	 * @param p the path used as a key
	 * @return the associated ICompilationUnit
	 */
	public @Nullable ICompilationUnit getICU(String p) {
		return map == null ? null : map.get(p);
	}

	/** Creates a problem requestor for a particular java project.  */
	public JmlProblemRequestor(@Nullable IJavaProject jp) {
		this.project = jp == null ? null : jp.getProject();
	}

	/** Eclipse calls this when a problem is reported
	 * @param p the reported problem
	 * @see org.eclipse.jdt.core.IProblemRequestor#acceptProblem(org.eclipse.jdt.core.compiler.IProblem)
	 */
	public void acceptProblem(/*@ non_null */ IProblem p) {
		// JML checking produces CompilerProblems (in OpenJMLInterface); 
		// Eclipse produces other kinds of problems;
		// Eclipse problems are already reported, so don't report them 
		// over again if JML encounters it as part of getting the Java AST.
		// Except: We swallow silently two errors - that a method requires a
		// body and uninitialized blank final fields, both of which occur in
		// specification files by design.
		if (!(p instanceof JmlEclipseProblem)) {
			int id = p.getID();
			if (!(id == IProblem.MethodRequiresBody || id == IProblem.UninitializedBlankFinalField)) return;
			String s = new String(p.getOriginatingFileName());
			if (s.endsWith(Utils.dotJava)) return;
			// FIXME - we are not actually doing anything.  SHould we?
			//          Log.log("JAVA Problem: " + id + " " + new String(p.getOriginatingFileName()) + " " + p.getMessage());
			//          p.delete();
			return;
		}
		if (p.getID() == 0 && p.getMessage().contains("is public, should be declared in a file named")
				&& String.valueOf(p.getOriginatingFileName()).endsWith(Utils.dotJML)) {
			return;
		}
		
		// Ignore warnings if level is 2
		if (p.isWarning() && level == 2) return;

		try {
			IResource f = null;
			char[] ch = p.getOriginatingFileName();
			IWorkspace w = ResourcesPlugin.getWorkspace();
			IWorkspaceRoot root = w.getRoot();
			if (ch != null) {
				Path path = new Path(new String(ch));
				f = root.findMember(path);
			} else {
				// No originating file name, so use the project or the workspace root
				f = project != null ? project : root;
			}
			
			// If this is a parsing problem, there will be no symbol
			Symbol sym = ((JmlEclipseProblem)p).sourceSymbol;
			
			// Use the following if you want problems printed to the console
			// as well as producing markers and annotations
			if (Options.uiverboseness) {
				JmlEclipseProblem.printProblem(new PrintStream(Log.log.listener().getStream()), p);
			}

			JmlEclipseProblem jmlproblem = (JmlEclipseProblem)p;
			final IResource r = f;
			final int finalLineNumber = p.getSourceLineNumber();
			final int column = p.getSourceStart();
			// FIXME - review 0-1-based: documentation says both getSourceStart()
			// and lineStart are 1-based which would make this computation off by one
			final int finalOffset = p.getSourceStart() + jmlproblem.lineStart;
			final int finalEnd = p.getSourceEnd() + 1 + jmlproblem.lineStart;
			String source = "";
			if (sym != null) source = sym.owner.toString() + "." + sym.toString() + ": " + Strings.eol;
			final String finalErrorMessage = source + p.getMessage();
			int severity = jmlproblem.severity;
			
			if (jmlproblem.lineStart < 0) {
				Log.log(p.getMessage());
				if (Options.isOption(Options.showErrorPopupsKey)) {
				    Activator.utils().showMessageInUI(null,"OpenJML ESC Error",finalErrorMessage);
				}
			}
			
			// FIXME - this looks like a hack - at least explain
			final boolean staticCheckWarning = 
				// The 64 is ProblemSeverities.SecondaryError, which has discouraged access
				severity == 64 || finalErrorMessage.contains("The prover") 
				|| finalErrorMessage.contains("Associated declaration");
			// The OpenJML note is translated to ProblemSeverities.Ignore, for
			// lack of a better mapping. The p.isWarning() includes the Ignore
			// category - so we can't use it directly. Actually(), p.isError()
			// does not include all error categories (TODO - clean this up?)
			final int finalSeverity = 
				staticCheckWarning ? IMarker.SEVERITY_WARNING :
					p.isError() ? IMarker.SEVERITY_ERROR :
					severity == ProblemSeverities.Ignore ? IMarker.SEVERITY_INFO :
					severity > 0  ? IMarker.SEVERITY_ERROR :
					                IMarker.SEVERITY_WARNING ;

			// Eclipse recommends that things that modify the resources
			// in a workspace be performed in a IWorkspaceRunnable
			IWorkspaceRunnable runnable = new IWorkspaceRunnable() {
				public void run(IProgressMonitor monitor) throws CoreException {
					IMarker marker = r.createMarker(
										staticCheckWarning ? Env.ESC_MARKER_ID 
															: Env.JML_MARKER_ID);
					marker.setAttribute(IMarker.LINE_NUMBER, 
										finalLineNumber >= 1? finalLineNumber : 1);
					if (column >= 0) {
						marker.setAttribute(IMarker.CHAR_START, finalOffset); 
						marker.setAttribute(IMarker.CHAR_END, finalEnd); // One beyond the last highlighted
					}
					// Note - it appears that CHAR_START is measured from the beginning of the
					// file and overrides the line number when drawing the squiggly 
					// The line number is used in the information about the problem in
					// the Problem View

					// Note - if the marked characters are the line termination characters,
					// no highlighting happens, though the marker still appears as a problem.
					marker.setAttribute(IMarker.SEVERITY,finalSeverity);
					marker.setAttribute(IMarker.MESSAGE, finalErrorMessage);
				}
			};
	        IResourceRuleFactory ruleFactory = 
	                ResourcesPlugin.getWorkspace().getRuleFactory();
	        ISchedulingRule rule = ruleFactory.markerRule(r);
			r.getWorkspace().run(runnable, rule, IWorkspace.AVOID_UPDATE, (IProgressMonitor)null);
		} catch (Exception e) {
			Log.errorKey("openjml.ui.failed.to.create.marker",e); //$NON-NLS-1$
		}
	}

	/** What to accept: level == 2 ==> errors only; level == 1; errors and
	 * warnings
	 */
	protected int level = 1;

	/** What to accept: level == 2 ==> errors only; level == 1; errors and
	 * warnings
	 * @param level whether to print warnings and info messages
	 */
	public void setLevel(int level) {
		this.level = level;
	}

	/** This implementation does nothing in this call - all reported problems
	 * are handled.
	 * @see org.eclipse.jdt.core.IProblemRequestor#beginReporting()
	 */
	public void beginReporting() {
		// do nothing
	}

	/** This implementation does nothing in this call - all reported problems
	 * are handled.
	 * @see org.eclipse.jdt.core.IProblemRequestor#endReporting()
	 */
	public void endReporting() {
		// do nothing
	}

	/** This implementation is always active
	 * @return always returns true
	 * @see org.eclipse.jdt.core.IProblemRequestor#isActive()
	 */
	public boolean isActive() {
		return true;
	}

}
