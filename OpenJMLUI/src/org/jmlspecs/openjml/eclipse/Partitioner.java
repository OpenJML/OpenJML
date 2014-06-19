/**
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jdt.ui.text.JavaTextTools;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.TypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.ui.PlatformUI;

/**
 * @author dhouck
 *
 */
public class Partitioner extends FastPartitioner {

	/**
	 * A unique string representing the partition type for JML specs. Because
	 * the only requirement is that it's unique the fully qualified name of the
	 * string seems to be a good choice.
	 */
	public static final String JML_SPEC = 
			"org.jmlspecs.openjml.eclipse.Partitioner.JML_SPEC"; //$NON-NLS-1$
	
	/**
	 * A unique string representing this partitioning within the document. The
	 * only requirement is that it's unique, so the fully qualified name of the
	 * string is used.
	 * 
	 * @see IDocumentExtension3
	 */
	public static final String PARTITIONING =
			"org.jmlspecs.openjml.eclipse.Partitioner.PARTITIONING"; //$NON-NLS-1$
	
	/**
	 * Create and return a Java partition scanner.
	 * 
	 * This class works by creating the Java partitions, and then changing some
	 * of the comments to the <code>{@link JML_SPEC}</code> type. To do this, we
	 * need to be able to scan for Java partitions.
	 * 
	 * @return A new Java partition scanner.
	 */
	private static IPartitionTokenScanner getJavaScanner()
	{
		/*
		 * TODO: The JavaTextTools don't currently use the preference store in
		 * the creation of the partitioner, but that's an internal detail. We
		 * need to figure out which preference store the JDT actually uses; I
		 * don't think this is the right one.
		 */
		IPreferenceStore store = PlatformUI.getPreferenceStore();
		return new JavaTextTools(store).getPartitionScanner();
	}
	
	/**
	 * Get the content types that a JML partitioner supports. This is the
	 * complete set a Java partitioner supports, with the addition of the
	 * <code>JML_SPEC</code> type.
	 * 
	 * @return The list of content types supported by the partitioner.
	 */
	private static String[] getContentTypes() {
		/*
		 *  TODO: This list is hardcoded. It'll break if Java gets a new
		 *  partition type. I'm not sure if the list is actually used (I think
		 *  we can return a partition type not in this list, for example), but
		 *  it would still be better to get this programmatically.
		 */
		return new String [] {
				IJavaPartitions.JAVA_CHARACTER,
				IJavaPartitions.JAVA_DOC,
				IJavaPartitions.JAVA_MULTI_LINE_COMMENT,
				IJavaPartitions.JAVA_SINGLE_LINE_COMMENT,
				IJavaPartitions.JAVA_STRING,
				JML_SPEC
		};
	}
	
	/**
	 * Create a new partitioner for JML documents.
	 */
	public Partitioner() {
		super(getJavaScanner(), getContentTypes());
	}

	//TODO: Do this in another method for performance reasons
	/**
	 * Compute the partitioning as with plain Java, then change some of the
	 * comment partitions to <code>JML_SPEC</code> partitions.
	 * 
	 * @see http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_4.html#SEC29
	 */
	@Override
	public ITypedRegion[] computePartitioning(int offset, int length,
			boolean includeZeroLengthPartitions)
	{
		ITypedRegion[] returnVal = super.computePartitioning(offset, length,
				includeZeroLengthPartitions);
		clearPositionCache();
		
		/*
		 *  We don't need to worry about merging adjacent JML partitions; each
		 *  annotation must hold a complete grammatical unit (section 4.4 of the
		 *  JML spec). Thus, strings, informal expressions, etc. must not span
		 *  JML annotations, and we can treat each annotation separately for
		 *  highlighting purposes.
		 */
		// TODO: Detect JML in doc comments (<jml> and <esc> tags).
		for (int i = 0; i < returnVal.length; ++i)
		{
			ITypedRegion region = returnVal[i];
			//TODO: Better annotation detection in case of annotation keys
			if ((region.getType() == IJavaPartitions.JAVA_MULTI_LINE_COMMENT
					|| region.getType() == IJavaPartitions.JAVA_SINGLE_LINE_COMMENT)
					&& region.getLength() >= 3)
			{
				try
				{
					if (fDocument.getChar(region.getOffset() + 2) == '@')
					{
						returnVal[i] = new TypedRegion(region.getOffset(),
								region.getLength(), JML_SPEC);
					}
				}
				catch (org.eclipse.jface.text.BadLocationException e)
				{
					assert false; // We made sure the region was long enough
				}
			}
		}
		
		return returnVal;
	}
}
