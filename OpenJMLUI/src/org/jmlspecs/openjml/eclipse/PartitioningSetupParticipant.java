/**
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;

/**
 * @author dhouck
 *
 */
public class PartitioningSetupParticipant
	implements org.eclipse.core.filebuffers.IDocumentSetupParticipant {

	/**
	 * Add the JML partitioning to the given document.
	 */
	@Override
	public void setup(IDocument document) {
		
		Partitioner partitioner = new Partitioner();
		partitioner.connect(document);
		
		if (document instanceof IDocumentExtension3)
		{
			IDocumentExtension3 doc3 = (IDocumentExtension3) document;
			doc3.setDocumentPartitioner(Partitioner.PARTITIONING, partitioner);
		}
		else
		{
			System.err.println("Couldn't add partitioning because the document"
					+ "doesn't support IDocumentExtension3"
					+ "(multiple partitionings)");
		}
	}

}
