/**
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.ui.text.IJavaPartitions;
import org.eclipse.jdt.ui.text.JavaTextTools;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

/**
 * @author dhouck
 *
 */
public class Partitioner extends FastPartitioner {

	/**
	 * A string to append to a JAVA comment type to get the JML partition type
	 * that is seen by Java as that kind of comment. We need separate multi-line
	 * and single-line types to get the partition token scanner to work easily.
	 */
	private static final String JML_Addition = "+JML"; //$NON-NLS-1$ 

	/**
	 * A unique string representing the partition type for JML multi-line specs.
	 */
	public static final String JML_MULTI_LINE =
			IJavaPartitions.JAVA_MULTI_LINE_COMMENT + JML_Addition;

	/**
	 * A unique string representing the partition type for JML multi-line specs.
	 */
	public static final String JML_SINGLE_LINE =
			IJavaPartitions.JAVA_SINGLE_LINE_COMMENT + JML_Addition;
	
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
	 * This scans for the various Java partitions using a Java partition token
	 * scanner (obtained from the JDT's <code>JavaTextTools</code>), and
	 * checking the comment tokens to see if they need to be replaced with JML
	 * tokens.
	 * 
	 * {@inheritDoc}
	 */
	private static class JMLScanner  implements IPartitionTokenScanner
	{
		/**
		 * The Java single-line comment content type.
		 * @see IJavaPartitions.JAVA_SINGLE_LINE_COMMENT
		 */
		private static final String JAVA_SINGLE_LINE = IJavaPartitions.JAVA_SINGLE_LINE_COMMENT;
		
		/**
		 * The Java multi-line comment content type.
		 * @see IJavaPartitions.JAVA_MULTI_LINE_COMMENT
		 */
		private static final String JAVA_MULTI_LINE = IJavaPartitions.JAVA_MULTI_LINE_COMMENT;
		
		/**
		 * The document this scanner is currently connected to. Despite the name,
		 * this field works on operating systems that are not Windows in addition
		 * to Windows operating systems.
		 */
		private IDocument my_document;
		
		/**
		 * The Java partition token scanner that this is wrapping.
		 */
		private final IPartitionTokenScanner scanner;
		
		/**
		 * Constructs a JMLScanner wrapping a new Java partition scanner obtained
		 * from the <code>JavaTextTools</code> class.
		 */
		public JMLScanner()
		{
			IPreferenceStore store = JavaPlugin.getDefault().getCombinedPreferenceStore();
			scanner =  new JavaTextTools(store).getPartitionScanner();
			my_document = null;
		}

		@Override
		public void setRange(IDocument document, int offset, int length) {
			scanner.setRange(document, offset, length);
			my_document = document;
		}

		/**
		 * This method looks for the next token in the document. If that token
		 * is a single- or multi-line comment, we look to see if it is a JML
		 * annotation. If so, we return the appropriate token. If it's not a
		 * Java single- or multi-line comment, or if it is such a comment but
		 * not a JML annotation, we return the original token.
		 * 
		 * {@inheritDoc}
		 */
		@Override
		public IToken nextToken() {
			IToken javaToken = scanner.nextToken();
			Object data = javaToken.getData();
			if (JAVA_MULTI_LINE.equals(data) || JAVA_SINGLE_LINE.equals(data))
			{
				int offset = scanner.getTokenOffset();
				int end = offset + scanner.getTokenLength();
				try {
					//System.err.println(my_document.get(offset, length));
					boolean jml_comment = false; // We set to true if found
					boolean in_ident = false;
					// See if it's a JML comment. Start at offset + 2 to skip "/*"
					for (int i = offset + 2; i < end; i++)
					{
						char c = my_document.getChar(i);
						// Skip over identifiers
						if (in_ident)
						{
							if (Character.isJavaIdentifierPart(c))
							{
								continue; // Keep going through ident
							}
							else
							{
								in_ident = false;
								// Keep checking out-of-identifier
							}
						}
						
						if (c == '@') // Check for end of JML comment
						{
							jml_comment = true;
							break;
						}
						else if (c == '+' || c == '-') // Check JML for key
						{
							if (i + 1 < end) // There's another character
							{
								char next = my_document.getChar(i + 1);
								if (next == '@')
								{
									 // Deprecated //+@ syntax
									jml_comment = true;
									break;
								}
								else if (Character.isJavaIdentifierStart(next))
								{
									i++; // Don't bother checking ident part
									in_ident = true;
								}
								else // Neither an identifier start nor an @
								{
									break;
								}
							}
						}
						else // Neither key nor @
						{
							break;
						}
					}
					// We got through the whole comment; no JML start marker
					if (jml_comment)
					{
						return new Token(data + JML_Addition);
					}
					else
					{
						return javaToken;
					}
				} catch (BadLocationException e) {
					System.err.println("Accessed bad location in document");
					e.printStackTrace();
					return javaToken;
				}
			}
			else // Neither a single-line comment nor a multi-line comment.
			{
				/*
				 *  TODO: Detect JML in doc comments (<jml> and <esc> tags). Or not;
				 *  OpenJML doesn't support them and claims JML will soon deprecate them
				 */
				return javaToken;
			}
		}

		@Override
		public int getTokenOffset() {
			return scanner.getTokenOffset();
		}

		@Override
		public int getTokenLength() {
			return scanner.getTokenLength();
		}

		/**
		 * Set the partial range for the partition tokenizer. If the provided
		 * <code>contentType</code> is a JML annotation content type, we
		 * replace it with the appropriate Java equivalent for the inner scanner
		 * so that we will see the whole comment when <code>nextToken</code> is
		 * called. 
		 */
		@Override
		public void setPartialRange(IDocument document, int offset, int length,
				String contentType, int partitionOffset) {
			// Reversed equality comparisons because contentType may be null.
			if (JML_MULTI_LINE.equals(contentType))
			{
				contentType = JAVA_MULTI_LINE;
			}
			else if (JML_SINGLE_LINE.equals(contentType))
			{
				contentType = JAVA_SINGLE_LINE;
			}
			scanner.setPartialRange(document, offset, length, contentType, partitionOffset);
		}
	}
	
	/**
	 * Get the content types that a JML partitioner supports. This is the
	 * complete set a Java partitioner supports, with the addition of the
	 * <code>JML_SPEC</code> type.
	 * 
	 * {@inheritDoc}
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
				JML_MULTI_LINE,
				JML_SINGLE_LINE
		};
	}
	
	/**
	 * Create a new partitioner for JML documents.
	 */
	public Partitioner() {
		super(new JMLScanner(), getContentTypes());
	}
}
