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
import org.eclipse.core.runtime.IPath;
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
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.internal.Workbench;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;
import org.jmlspecs.openjml.JmlTreeScanner;
import org.osgi.framework.Bundle;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;

public class ProposalComputer implements IJavaCompletionProposalComputer {
	protected enum JMLProposalType {
		KEYWORD("icons/jml-logo-16x16.png"), GHOST_FIELD(
				"icons/jml-ghost-16x16.png"), MODEL_FIELD(
				"icons/jml-model-16x16.png"), MODEL_METHOD(
				"icons/jml-method-16x16.png");

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
		public String getFilename() {
			return myFilename;
		}
	};

	/**
	 * image types: JML_KEYWORD (or multiple groups based on JmlTokens
	 * groupings), JML_MODEL_FIELD, JML_MODEL_METHOD
	 */
	public final static Map<JMLProposalType, Image> proposalImages;
	static {
		final Map<JMLProposalType, Image> tempImages = new HashMap<JMLProposalType, Image>();
		// put images in the map
		Bundle bundle = Platform.getBundle(Env.PLUGIN_ID);
		for (JMLProposalType p : JMLProposalType.values()) {
			Path path = new Path(p.getFilename());
			URL fileURL = FileLocator.find(bundle, path, null);
			try {
				tempImages.put(p, new Image(Workbench.getInstance()
						.getDisplay(), fileURL.openStream()));
			} catch (IOException e) {
				// No image

			}
		}
		proposalImages = Collections.unmodifiableMap(tempImages);
	}

	@Override
	public void sessionStarted() {
	}

	/**
	 * All JML keywords suggestions
	 */
	public final static EnumSet<JmlToken> keywords = EnumSet.range(
			JmlToken.ASSUME, JmlToken.NOWARN);

	/**
	 * Get a list of combined jml and java proposals. Currently, it searches for
	 * the prefix to make jml suggestions and makes java suggestions as if the
	 * cursor is located at the first opening or closing bracket after. There is
	 * an attempt to filter out non-useful proposals, but can still be improved. The order
	 * can also be improved, currently suggests in alphabetical order.
	 * 
	 * @param context
	 *            The location of where the cursor is in the document, along
	 *            with other relevant information about the document
	 * @param monitor
	 *            Not sure when this is used?
	 */
	@Override
	public List<ICompletionProposal> computeCompletionProposals(
			ContentAssistInvocationContext context, IProgressMonitor monitor) {

		List<ICompletionProposal> proposals = new LinkedList<ICompletionProposal>();
		final int pos = context.getInvocationOffset();

		IJavaCompletionProposal[] javaProposals = null;
		IDocument doc = context.getDocument();
		int start = pos;
		JavaContentAssistInvocationContext jcaic = null;
		// it seems that this method is only called when context is a
		// JavaContentAssistInvocationContext
		if (context instanceof JavaContentAssistInvocationContext) {
			// creates java proposals with ICompilation Unit
			jcaic = (JavaContentAssistInvocationContext) context;
			ICompilationUnit unit = jcaic.getCompilationUnit();

			CompletionProposalCollector collector = new CompletionProposalCollector(
					unit);

			// search for where the next method starts or ends and run java
			// autocompletion there
			try {
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

		// try to compute the identifierPrefix, which is the word right before
		// the cursor, is defined as either the first space or backslash
		String prefix = "";
		try {
			CharSequence identifierPrefix = context.computeIdentifierPrefix();
			prefix = identifierPrefix.toString();
		} catch (BadLocationException e) {
			e.printStackTrace();
		}

		// Find general context, for length and replacement
		int p = pos - 1;
		boolean hasBackslash = false;
		try {
			p = p - prefix.length();
			char c = doc.getChar(p);
			if (c == '\\') {
				hasBackslash = true;
			}
		} catch (BadLocationException e) {
			// Something wrong with page, just return nothing
			return null;
		}

		// Load images, then assign image depending on what kind of proposal it
		// is
		Image JmlIMG = proposalImages.get(JMLProposalType.KEYWORD);

		final OpenJMLInterface jmlContext = Activator.utils().getInterface(
				jcaic.getProject());
		IPath ip = jcaic.getProject().getProject().getLocation();
		JmlCompilationUnit jcu;
		OpenJMLTreeScanner tempVisitor = new OpenJMLTreeScanner(pos, p, prefix);
		try {
			// pass the entire document as a string
			jcu = jmlContext.api.parseString(ip.toString(), doc.get());
			jcu.accept(tempVisitor);
		} catch (Exception e1) {
			e1.printStackTrace();
		}

		// check if the location in the file is in a java variable declaration
		if (tempVisitor.ourTreeNode instanceof JmlVariableDecl) {
			// just suggest modifier keywords
			final JmlVariableDecl ourVar = (JmlVariableDecl) tempVisitor.ourTreeNode;
			for (JmlToken t : JmlToken.modifiers) {
				String s = t.internedName();
				if (doesntHaveAnnotation(ourVar, t) && s.startsWith(prefix)) {
					proposals.add(new OpenJMLCompletionProposal(s, p + 1, pos
							- p - 1, s.length(), JmlIMG, s, null, "",
							new StyledString(s)));
				}
			}
			return proposals;
		} else if (tempVisitor.ourTreeNode instanceof JmlMethodDecl) {
			// do method declaration stuff
			final JmlMethodDecl ourVar = (JmlMethodDecl) tempVisitor.ourTreeNode;
			for (JmlToken t : JmlToken.modifiers) {
				String s = t.internedName();
				if (doesntHaveAnnotation(ourVar, t) && s.startsWith(prefix)) {
					proposals.add(new OpenJMLCompletionProposal(s, p + 1, pos
							- p - 1, s.length(), JmlIMG, s, null, "",
							new StyledString(s)));
				}
			}
			return proposals;
		}

		// if there is a backslash, we need to check the backslashTokens
		if (hasBackslash) {
			for (String s : JmlToken.backslashTokens.keySet()) {
				// remove backslash and compare actual characters
				String checkString = s.substring(1);
				if (checkString.startsWith(prefix)) {
					proposals.add(new OpenJMLCompletionProposal(s, p, pos - p,
							s.length(), JmlIMG, s, null, "",
							new StyledString(s)));
				}
			}
		} else {
			for (JmlToken t : keywords) {
				String s = t.internedName();
				if (s.startsWith(prefix)) {
					proposals.add(new OpenJMLCompletionProposal(s, p + 1, pos
							- p - 1, s.length(), JmlIMG, s, null, "",
							new StyledString(s)));
				}
			}

			for (String s : JmlToken.backslashTokens.keySet()) {
				if (s.startsWith(prefix)) {
					proposals.add(new OpenJMLCompletionProposal(s, p + 1, pos
							- p - 1, s.length(), JmlIMG, s, null, "",
							new StyledString(s)));
				}
			}

			// add all the java proposals to the list of jml proposals
			if (javaProposals != null) {
				for (int i = 0; i < javaProposals.length; i++) {

					String s = javaProposals[i].getDisplayString();
					if (s.startsWith(prefix)) {
						proposals.add(new OpenJMLCompletionProposal(
								javaProposals[i], p + 1, pos - p - 1, s
										.length()));
					}
				}
			}
		}
		// combine JML comment proposals with regular jml keyword and java
		// suggestions

		List<ICompletionProposal> JMLProposals = tempVisitor.myProposals;
		JMLProposals.addAll(0, proposals);
		return JMLProposals;

	}
	/**
	 * Helper function to check if a modifier is already in the annotation. If it is,
	 * don't suggest it again as a CompletionProposal
	 * @param v
	 * 	Either a JmlVariableDecl or a JmlMethodDecl, we can get annotations from each
	 * 	and check for the token
	 * @param token
	 * 	The desired annotation token
	 * @return
	 */
	private boolean doesntHaveAnnotation(Object v, JmlToken token) {
		boolean result = true;
		if (v instanceof JmlVariableDecl) {
			// also want to check for modifiers
			JmlVariableDecl var = (JmlVariableDecl) v;
			for (JCAnnotation a : var.getModifiers().getAnnotations()) {
				// if the annotation matches the token, set result to false
				if (token.annotationType != null) {
					String name = token.annotationType.getSimpleName();
					if (name.equals(a.toString().substring(1))) {
						result = false;
					}
				}
			}
		}
		if (v instanceof JmlMethodDecl) {
			// also want to check for modifiers
			JmlMethodDecl var = (JmlMethodDecl) v;
			for (JCAnnotation a : var.getModifiers().getAnnotations()) {
				// if the annotation matches the token, set result to false
				if (token.annotationType != null) {
					String name = token.annotationType.getSimpleName();
					if (name.equals(a.toString().substring(1))) {
						result = false;
					}
				}
			}
		}
		return result;
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

	private static class OpenJMLTreeScanner extends JmlTreeScanner {
		private final int myOffset;
		private final int myPos;
		private final String myPrefix;

		public final List<ICompletionProposal> myProposals = new LinkedList<ICompletionProposal>();

		/**
		 * checks if current location is in variable declaration, by default we
		 * are not. If we crawl the tree and find out we are, set it to true.
		 * This is used later to filter out suggestions that dont' make sense in
		 * context.
		 */
		public JCTree ourTreeNode = null;

		/**
		 * Crawl the entire document to get the JML variables and mdoel methods.
		 * 
		 * @param img
		 *            The image used in suggestion
		 * @param pos
		 *            The starting location in document
		 * @param offset
		 *            Where the insert of suggestion starts
		 */
		public OpenJMLTreeScanner(int pos, int offset, String prefix) {

			myOffset = offset;
			myPos = pos;
			myPrefix = prefix;
		}

		/**
		 * Retrieves variables initialized in JML comments. Used as proposals
		 */
		@Override
		public void visitJmlVariableDecl(JmlVariableDecl that) {
			// if the current location is in that JML comment location
			// and there are no annotations, then we are in a normal java
			// variable declaration
			if (that.getStartPosition() < myPos
					&& that.getPreferredPosition() >= myPos) {
				ourTreeNode = that;
			}

			// add JML defined variables to auto suggestion
			for (JCAnnotation o : that.getModifiers().getAnnotations()) {
				if (o.toString().equals("@Model")) {
					// create a proposal for it
					String name = that.getName().toString();
					if (name.startsWith(myPrefix)) {
						myProposals.add(new OpenJMLCompletionProposal(name,
								myOffset + 1, myPos - myOffset - 1, name
										.length(), proposalImages.get(JMLProposalType.KEYWORD), name, null, "",
								new StyledString(name)));
					}
				} else if (o.toString().equals("@Ghost")) {
					// create a proposal for it
					String name = that.getName().toString();
					if (name.startsWith(myPrefix)) {
						myProposals.add(new OpenJMLCompletionProposal(name,
								myOffset + 1, myPos - myOffset - 1, name
										.length(), proposalImages.get(JMLProposalType.GHOST_FIELD), name, null, "",
								new StyledString(name)));
					}
				}
			}
		}

		/**
		 * Suggest model methods in JML comments for auto-completion
		 */
		@Override
		public void visitJmlMethodDecl(JmlMethodDecl that) {
			
			// if the current location is in that JML comment location
			// and there are no annotations, then we are in a normal java
			// variable declaration
			if (that.getStartPosition() < myPos
					&& that.getPreferredPosition() >= myPos) {

				ourTreeNode = that;
			}

			// use that.cases to get spec cases and see which one we're inside
			// of, for context purposes
			for (Object o : that.getModifiers().getAnnotations()) {
				if (o.toString().equals("@Model")) {
					// create a proposal for it
					String name = that.getName().toString();
					if (name.startsWith(myPrefix)) {
						myProposals.add(new OpenJMLCompletionProposal(name + "()",
								myOffset + 1, myPos - myOffset - 1, name
										.length() + 2, proposalImages.get(JMLProposalType.MODEL_METHOD), name, null, "",
								new StyledString(name + "()")));
					}
				}
			}
		}
	}
}
