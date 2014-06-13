package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.internal.ui.text.java.AbstractJavaCompletionProposal;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposalExtension6;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;

public class OpenJMLCompletionProposal implements
		ICompletionProposal, ICompletionProposalExtension6 {
	// JML_
	
	//We cast to a different objects to take advantage of internal
	//JDP APIs. These are used to get replacement string, image,
	//and styled text

	/**
	 * The CompletionProposal that does most of the work; we delegate to this
	 * for all the methods it implements, since CompletionProposal is final and
	 * we can't just extend it.
	 */
	private final CompletionProposal myDelegate;
	
	/**
	 * The styled display string (from ICompletionProposalExtension6).
	 */
	private final StyledString myStyledDisplayString;
	
	/**
	 * Constructs an OpenJMLCompletionProposal from an ICompletionProposal and
	 * additional parameters. If the replacement string can be retrieved from the 
	 * specified proposal, it is used; otherwise, the display string is used as the
	 * replacement string. If the styled display string can be retrieved from the 
	 * specified proposal, it is used; otherwise, the styled display string is just
	 * the display string.
	 * 
	 * @param proposal The completion proposal to build from.
	 * @param replacementOffset The offset of the text to be replaced.
	 * @param replacementLength The length of the text to be replaced.
	 * @param cursorPosition The position of the cursor following the insert relative to replacementOffset.	 
	 */
	public OpenJMLCompletionProposal(final ICompletionProposal proposal, 
			                         final int replacementOffset, final int replacementLength,
			                         final int cursorPosition) {
		// if we can, we get the styled display string from ICompletionProposal6; otherwise,
		// it's just an unstyled version of the display string.
		StyledString styledDisplayString = new StyledString(proposal.getDisplayString());
		if (proposal instanceof ICompletionProposalExtension6) {
			styledDisplayString = ((ICompletionProposalExtension6) proposal).getStyledDisplayString();
		}
		
		myStyledDisplayString = styledDisplayString;
		
		// if we can, we get the replacement string from the Java proposal; otherwise,
		// the replacement string is the display string.
		String replacementString = proposal.getDisplayString(); 
		if (proposal instanceof AbstractJavaCompletionProposal) {
			replacementString = ((AbstractJavaCompletionProposal) proposal).getReplacementString();
		}
		
		
		myDelegate = new CompletionProposal(replacementString, replacementOffset, replacementLength,
				                            cursorPosition, proposal.getImage(), proposal.getDisplayString(),
				                            proposal.getContextInformation(), proposal.getAdditionalProposalInfo());
	}
	
	/**
	 * Constructs an OpenJMLCompletionProposal from scratch. 
	 * 
	 * @param replacementString The replacement string.
	 * @param replacementOffset The offset of the text to be replaced.
	 * @param replacementLength The length of the text to be replaced.
	 * @param cursorPosition The position of the cursor following the insert relative to replacementOffset.
	 * @param image The image to display for this proposal.
	 * @param displayString The string to be displayed for the proposal.
	 * @param contextInformation The context information associated with this proposal.
	 * @param additionalProposalInfo the additional information associated with this proposal
	 * @param styledDisplayString Nice looking display string
	 */
	public OpenJMLCompletionProposal(final String replacementString, final int replacementOffset,
			                         final int replacementLength, final int cursorPosition,
			                         final Image image, final String displayString, 
			                         final IContextInformation contextInformation,
			                         final String additionalProposalInfo,
			                         final StyledString styledDisplayString) {
		myDelegate = new CompletionProposal(replacementString, replacementOffset, replacementLength,
				                          	cursorPosition, image, displayString, contextInformation,
				                          	additionalProposalInfo);
		myStyledDisplayString = styledDisplayString; 
	}
	
	@Override
	//currently not really used
	public StyledString getStyledDisplayString() {
		return myStyledDisplayString;
		
	}

	@Override
	public void apply(IDocument document) {
		myDelegate.apply(document);
	}

	@Override
	public Point getSelection(IDocument document) {
		return myDelegate.getSelection(document);
	}

	@Override
	public String getAdditionalProposalInfo() {
		return myDelegate.getAdditionalProposalInfo();
	}

	@Override
	public String getDisplayString() {
		return myDelegate.getDisplayString();
	}

	@Override
	public Image getImage() {
		return myDelegate.getImage();
	}

	@Override
	public IContextInformation getContextInformation() {
		return myDelegate.getContextInformation();
	}
}
