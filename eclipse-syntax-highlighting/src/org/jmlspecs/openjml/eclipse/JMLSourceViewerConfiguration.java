package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.ui.text.IColorManager;
import org.eclipse.jdt.ui.text.IJavaColorConstants;
import org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.PatternRule;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Configure JML source code viewers. The only difference between this and the
 * JavaSourceViewerConfiguration is that this also highlights JML comments.
 * Currently this is done using an internal class which does almost nothing,
 * but it could be extended to do a lot more using a better JML tokenizer.
 * 
 * <p>
 * Note that this class inherits from {@link JavaSourceViewerConfiguration},
 * which is labeled as soft final. This means that clients, like us, are not
 * supposed to inherit from it.
 * </p>
 * 
 * @author dhouck
 */
public class JMLSourceViewerConfiguration extends JavaSourceViewerConfiguration {
	
	/**
	 * Constructs a JMLSourceViewerConfiguration. This only calls super() and
	 * does nothing of its own.
	 * 
	 * @see org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration#JavaSourceViewerConfiguration(IColorManager, IPreferenceStore, ITextEditor, String)
	 */
	public JMLSourceViewerConfiguration(IColorManager colorManager,
			IPreferenceStore preferenceStore, ITextEditor editor,
			String partitioning) {
		super(colorManager, preferenceStore, editor, partitioning);
	}
	
	/**
	 * Scan JML comments and tokenize them, with the tokens carrying highlighting
	 * information. Currently more of a proof-of-concept, though still potentially
	 * useful.
	 * 
	 * TODO:
	 * <ol>
	 * 	<li>
	 * 		Inherit from AbstractJavaScanner or similar for better access to
	 * 		the details of Java syntax highlighting information.
	 * 	</li>
	 * 	<li>
	 * 		Use the existing JML scanner, if it's fast enough, or at least
	 * 		improve this one.
	 * 	</li>
	 * </ol>
	 * @author dhouck
	 *
	 */
	private class JMLScanner extends RuleBasedScanner
	{
		private final IColorManager fColorManager = getColorManager();
		private Token getToken(String key)
		{
			return new Token(new TextAttribute(fColorManager.getColor(key)));
		}
		
		private Token getToken(RGB rgb)
		{
			return new Token(new TextAttribute(fColorManager.getColor(rgb)));
		}
		
		public JMLScanner()
		{
			super();
			RGB color = PreferenceConverter.getColor(
					Activator.getDefault().getPreferenceStore(),
					Options.highlightDefaultKey);
			setDefaultReturnToken(getToken(color));
			List<IRule> rules = new ArrayList<IRule>();

			// Region-type rules
			rules.add(new MultiLineRule("(*", "*)", //$NON-NLS-1$ //$NON-NLS-2$
					getToken(IJavaColorConstants.JAVA_MULTI_LINE_COMMENT)));
			rules.add(new PatternRule("\"", "\"", //$NON-NLS-1$ //$NON-NLS-2$
					getToken(IJavaColorConstants.JAVA_STRING), '\\', true));
			rules.add(new PatternRule("'", "'", //$NON-NLS-1$ //$NON-NLS-2$
					getToken(IJavaColorConstants.JAVA_STRING), '\\', true));
			
			setRules(rules.toArray(new IRule[rules.size()]));
		}
	}
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration#getPresentationReconciler(org.eclipse.jface.text.source.ISourceViewer)
	 */
	@Override
	public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer)
	{
		// This works currently, but obviously isn't guaranteed.
		PresentationReconciler returnVal =
				(PresentationReconciler) super.getPresentationReconciler(sourceViewer);
		
		JMLScanner scanner = new JMLScanner();
		
		// Set the damager and repairer for JML comments to our JML scanner
		DefaultDamagerRepairer dr = new DefaultDamagerRepairer(scanner);
		returnVal.setDamager(dr, Partitioner.JML_MULTI_LINE);
		returnVal.setRepairer(dr, Partitioner.JML_MULTI_LINE);
		returnVal.setDamager(dr, Partitioner.JML_SINGLE_LINE);
		returnVal.setRepairer(dr, Partitioner.JML_SINGLE_LINE);
		
		return returnVal;
	}
}
