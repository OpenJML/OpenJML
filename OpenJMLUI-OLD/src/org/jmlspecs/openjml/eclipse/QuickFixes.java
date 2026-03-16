package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.ui.text.java.IInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposal;
import org.eclipse.jdt.ui.text.java.IProblemLocation;
import org.eclipse.jdt.ui.text.java.IQuickFixProcessor;

public class QuickFixes implements IQuickFixProcessor {

        @Override
        public boolean hasCorrections(ICompilationUnit unit, int problemId) {

                System.out.println(problemId);

                return true;
        }

        @Override
        public IJavaCompletionProposal[] getCorrections(IInvocationContext context, IProblemLocation[] locations)
                        throws CoreException {

        	ICompilationUnit cunit = context.getCompilationUnit();
        	ASTNode n = context.getCoveringNode();
        	ASTNode nn = context.getCoveredNode();
        	int len = context .getSelectionLength();
        	int off = context.getSelectionOffset();
        	for (IProblemLocation loc: locations) {
        		boolean error = loc.isError();
        		int offset = loc.getOffset();
        		int id = loc.getProblemId();
        		int length = loc.getLength();
        		String mtype = loc.getMarkerType();
        		System.out.println();
        	}
            return null;
        }

}