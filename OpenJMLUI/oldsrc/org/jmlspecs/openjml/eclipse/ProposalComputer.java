package org.jmlspecs.openjml.eclipse;

import java.util.EnumSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.jmlspecs.openjml.JmlTokenKind;

public class ProposalComputer implements org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer {

	@Override
	public void sessionStarted() {
	}
	
	public final static EnumSet<JmlTokenKind> keywords = EnumSet.allOf(JmlTokenKind.class);

	@Override
	public List<ICompletionProposal> computeCompletionProposals(
			ContentAssistInvocationContext context, IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		List<ICompletionProposal> proposals = new LinkedList<ICompletionProposal>();
		int pos = context.getInvocationOffset();
		IDocument doc = context.getDocument();
		
		// Keyword proposals
		int backslashPos = -1;
		int firstSpace = -1;
		int p = pos - 1;
		kw: try {
			while (p >= 0) {
				char c = doc.getChar(p);
				if (c == ' ' || c == '\t') {
					if (firstSpace < 0) firstSpace = p;
				} else if (c == ';' || c == '@') {
					if (firstSpace < 0) firstSpace = p;
					break;
				} else if (c == '\\') {
					backslashPos = p;
					break;
				} else {
					if (firstSpace >= 0) break kw; // Not in a position for keywords
				}
				--p;
			}
			// FIXME - want to allow code completion for modifiers that are not necessarily first
			// FIXME - want to add code completion for variables as well; what about expressions?
			if (backslashPos >= 0) {
				String prefix = doc.get(backslashPos,pos-backslashPos);
				for (String s: JmlTokenKind.backslashTokens.keySet()){
					if (s.startsWith(prefix)) {
						proposals.add(new CompletionProposal(s,backslashPos,pos-backslashPos,s.length()));
					}
				}
			} else {
				String prefix = doc.get(firstSpace+1,pos-firstSpace-1);
				for (JmlTokenKind t: keywords) {
					String s = t.internedName();
					if (s != null && s.startsWith(prefix)) {
						proposals.add(new CompletionProposal(s,firstSpace+1,pos-firstSpace-1,s.length()));
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
		// TODO: Not sure when this is used or what the appropriate result should be
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
