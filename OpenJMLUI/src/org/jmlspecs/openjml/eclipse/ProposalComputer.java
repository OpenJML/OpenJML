package org.jmlspecs.openjml.eclipse;

import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.ui.text.java.CompletionProposalCollector;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposal;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.internal.Workbench;
import org.jmlspecs.openjml.JmlToken;
import org.osgi.framework.Bundle;

public class ProposalComputer implements IJavaCompletionProposalComputer {
	protected enum JMLProposalType { 
		KEYWORD("icons/jml-logo-16x16.png"), 
		MODEL_FIELD("icons/jml-logo-16x16.png"),
		MODEL_METHOD("icons/jml-logo-16x16.png");
		
		/**
		 * The filename for this proposal type.
		 */
		private final String myFilename;
		
		/**
		 * Constructs a proposal type with the specified filename.
		 * 
		 * @param filename
		 */
		private JMLProposalType(final String filename) {
			myFilename = filename;
		}
		
		/**
		 * @return the file name for the icon for this type.
		 */
		public String getFilename() { return myFilename; }
	};
    // some kind of static data structure like a map that maps image enum values to images
	/* image types: JML_KEYWORD (or multiple groups based on JmlTokens groupings), JML_MODEL_FIELD, 
	 * JML_MODEL_METHOD
	 */
	public final static Map<JMLProposalType, Image> proposalImages;
	static {
		final Map<JMLProposalType, Image> tempImages = new HashMap<JMLProposalType, Image>();
		// put images in the map
		Bundle bundle = Platform.getBundle(Env.PLUGIN_ID);
		for(JMLProposalType p : JMLProposalType.values()) {
			Path path = new Path(p.getFilename());
			URL fileURL = FileLocator.find(bundle, path, null);
			try {
				tempImages.put(p, 
						       new Image(Workbench.getInstance().getDisplay(), fileURL.openStream()));
			} catch (IOException e) {
				// No image
				
			}
		}
		proposalImages = Collections.unmodifiableMap(tempImages);
	}
	
	@Override
	public void sessionStarted() {
	}

	public final static EnumSet<JmlToken> keywords = EnumSet.range(
			JmlToken.ASSUME, JmlToken.NOWARN);
	boolean hasLoaded = true;
	
	/**
	 * Get a list of combined jml and java proposals. Currently, it just searches
	 * for the prefix to make jml suggestions and makes java suggestions as if the cursor is
	 * located 
	 */
	@Override
	public List<ICompletionProposal> computeCompletionProposals(
			ContentAssistInvocationContext context, IProgressMonitor monitor) {

		List<ICompletionProposal> proposals = new LinkedList<ICompletionProposal>();
		int pos = context.getInvocationOffset();

		// cast the context to JavaContentAssistInvocationContext, get
		// ICompilationUnit
		IJavaCompletionProposal[] javaProposals = null;

		IDocument doc = context.getDocument();
		if (context instanceof JavaContentAssistInvocationContext) {
			// creates java proposals
			JavaContentAssistInvocationContext jcaic = (JavaContentAssistInvocationContext) context;
			ICompilationUnit unit = jcaic.getCompilationUnit();
			CompletionProposalCollector collector = new CompletionProposalCollector(
					unit);

			/*
			 * FIXME - work with completion unit, for filtering out stupid
			 * proposals
			 * CompletionContext cc = jcaic.getCoreContext(); IJavaElement ije =
			 * cc.getEnclosingElement(); String aefa = ije.
			 */

			// search for where the next method starts or ends and run java
			// autocompletion there
			try {
				int start = pos;
				char c;
				int location;
				while (true) {
					start++;
					c = doc.getChar(start);
					if (c == '{') {
						break;
					}
					if (c == '}') {
						break;
					}
				}
				// point java compiler to method immediately after jml comment
				unit.codeComplete(start + 1, collector);
				javaProposals = collector.getJavaCompletionProposals();
			} catch (Exception e1) {
				// TODO Auto-generated catch block
				System.err.println("Problem getting Java Proposals"); //$NON-NLS-1$
				e1.printStackTrace();
			}
		}

		CharSequence identifierPrefix = null;
		try {
			identifierPrefix = context.computeIdentifierPrefix();
			System.err.println("identifier prefix from context = "
					+ identifierPrefix);
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		// Find general context, for length and replacement
		int backslashPos = -1;
		int firstSpace = -1;
		int p = pos - 1;
		try {
			while (p >= 0) {
				char c = doc.getChar(p);
				if (c == ' ' || c == '\t' || c == ';' || c == '@') {
					firstSpace = p;
					break;
				} else if (c == '\\') {
					backslashPos = p;
					break;
				} else {

					--p;
				}
			}
			// FIXME - want to allow code completion for modifiers that are not
			// necessarily first
			// FIXME - want to add code completion for variables as well; what
			// about expressions?

			if (backslashPos >= 0) {
				String prefix = identifierPrefix.toString();
				// try to load an image
				Image img = proposalImages.get(JMLProposalType.KEYWORD);
				
				
				//Workbench.getInstance().getDisplay();
				for (String s : JmlToken.backslashTokens.keySet()) {
					if (s.startsWith(prefix)) {
						proposals.add(new OpenJMLCompletionProposal(s, backslashPos, pos -
								backslashPos, s.length(), img, s, null, "", new StyledString(s)));
					}
				}
				// add all the java proposals to the list of jml proposals
				if (javaProposals != null) {
					for (int i = 0; i < javaProposals.length; i++) {

					String s = javaProposals[i].getDisplayString();
					if (s.startsWith(prefix)) {
						proposals.add(new OpenJMLCompletionProposal(javaProposals[i], backslashPos, pos
								- backslashPos, s.length() /* we need to calculate this later */ ));
					}
					}
				}
			} else {
				String prefix = identifierPrefix.toString();
				for (JmlToken t : keywords) {
					String s = t.internedName();
					if (s.startsWith(prefix)) {
						proposals.add(new CompletionProposal(s, firstSpace + 1,
								pos - firstSpace - 1, s.length()));
					}
				}
				for (String s : JmlToken.backslashTokens.keySet()) {
					if (s.startsWith(prefix)) {
						proposals.add(new CompletionProposal(s, firstSpace + 1,
								pos - firstSpace - 1, s.length()));
					}
				}
				// add all the java proposals to the list of jml proposals
				if (javaProposals != null) {
				for (int i = 0; i < javaProposals.length; i++) {
					String s = javaProposals[i].getDisplayString();
					if (s.startsWith(prefix)) {
						proposals.add(new OpenJMLCompletionProposal(javaProposals[i],
								firstSpace + 1, pos - firstSpace - 1, 1 /* revisit this calculation later */ ));
					}
				}
				}
			}
		} catch (BadLocationException e) {
			// go on to propose nothing
		}
		return proposals;
	}

	@Override
	public List<IContextInformation> computeContextInformation(
			ContentAssistInvocationContext context, IProgressMonitor monitor) {
		// TODO: Not sure when this is used or what the appropriate result
		// should be
		return null;
	}

	@Override
	public String getErrorMessage() {
		// TODO: Not sure when this is used
		return "No JML keywords match this prefix";
	}

	@Override
	public void sessionEnded() {
	}

}
