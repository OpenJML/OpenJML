/**
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.progress.UIJob;

/**
 * A UIJob to reconfigure a SourceViewer with a new SourceViewerConfiguration.
 * 
 * @author dhouck
 */
public class SourceViewerReconfigurer extends UIJob {

	/**
	 * The SourceViewerConfiguration to set as the new configuration of the
	 * viewer.
	 */
	private final SourceViewerConfiguration config;
	
	/**
	 * The SourceViewer to reconfigure.
	 */
	private final SourceViewer viewer;
	
	/**
	 * Create the SourceViewerReconfigurer.
	 * 
	 * @param config The SourceViewerConfiguration to install
	 * @param viewer The SourceViewer on which to install it
	 * 
	 * @see UIJob.UIJob(String)
	 */
	public SourceViewerReconfigurer(String name,
			SourceViewerConfiguration config, SourceViewer viewer) {
		super(name);
		this.config = config;
		this.viewer = viewer;
	}

	/**
	 * Create the SourceViewerReconfigurer.
	 * 
	 * @param config The SourceViewerConfiguration to install
	 * @param viewer The SourceViewer on which to install it
	 * 
	 * @see UIJob.UIJob(org.eclipse.swt.widgets.Display, String)
	 */
	public SourceViewerReconfigurer(Display jobDisplay, String name,
			SourceViewerConfiguration config, SourceViewer viewer) {
		super(jobDisplay, name);
		this.config = config;
		this.viewer = viewer;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.progress.UIJob#runInUIThread(org.eclipse.core.runtime.IProgressMonitor)
	 */
	@Override
	public IStatus runInUIThread(IProgressMonitor monitor) {
		if (monitor.isCanceled())
		{
			return Status.CANCEL_STATUS;
		}
		
		/*
		 * I can't find anywhere that says the SourceViewer needs to be able to
		 * do formatting, but it makes sense and we get NullPointerExceptions at
		 * JavaSourceViewer.initializeViewerColors(JavaSourceViewer.java:265)
		 * without this check.
		 */
		if (viewer.canDoOperation(SourceViewer.FORMAT))
		{
			viewer.unconfigure();
			viewer.configure(config);
		}
		return Status.OK_STATUS;
	}
}
