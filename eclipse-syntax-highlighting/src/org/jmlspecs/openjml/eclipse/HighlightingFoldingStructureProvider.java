package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.text.folding.JavaFoldingStructureProviderDescriptor;
import org.eclipse.jdt.internal.ui.text.folding.JavaFoldingStructureProviderRegistry;
import org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProvider;
import org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * Currently, this is just a FoldingStructureProvider which creates an inner
 * FoldingStructureProvider and forwards all requests there. This also implements
 * IJavaFoldingStructureProviderExtension; it forwards those calls to the inner
 * FoldingStructureProvider if that also implements the interface, and otherwise
 * does nothing.
 * 
 * @author dhouck
 */
public class HighlightingFoldingStructureProvider implements
		IJavaFoldingStructureProvider, IJavaFoldingStructureProviderExtension {
	
	/** 
	 * The ID of the this FoldingStructureProvider, as recorded in plugin.xml.
	 * It's reproduced here so it can be accessed programatically. The only
	 * requirement is that it is unique, so we use the fully-qualified name of
	 * the variable itself.
	 */
	public static final String PROVIDER_ID =
			"org.jmlspecs.openjml.eclipse.HighlightingFoldingStructureProvider.PROVIDER_ID"; //$NON-NLS-1$
	
	/**
	 * This is the provider that actually provides folding structure. All calls
	 * to folding-related methods are forwarded here. This is null iff the
	 * provider isn't installed.
	 */
	private /*@nullable*/ IJavaFoldingStructureProvider containedProvider;
	
	/**
	 * The editor the FoldingStructureProvider is currently installed on. This
	 * is null iff the FoldingStructureProvider is not currently installed. 
	 */
	private /*@nullable*/ ITextEditor installedEditor;
	
	/**
	 * The viewer the FoldingStructureProvider is currently installed on. This
	 * is null iff the FoldingStructureProvider is not currently installed. 
	 */
	private /*@nullable*/ ProjectionViewer installedViewer;
	
	private final IPropertyChangeListener containedProviderPropertyChangeListener =
			new IPropertyChangeListener() {
				@Override
				public void propertyChange(PropertyChangeEvent event) {
					if (event.getProperty().equals(Options.innerFoldingProvider))
					{
						if (! event.getNewValue().equals(event.getOldValue()))
						{
							updateContainedProvider();
						}
					}
				}
			};
	
	/**
	 * Update the containedProvider to match the current preference and whether
	 * or not this is installed.
	 * 
	 * <p>
	 * If there already is a contained provider, it is uninstalled. If this
	 * FoldingStructureProvider is installed on an editor and viewer,
	 * then the new contained provider will be installed similarly; otherwise,
	 * the new contained provider will be set to null.
	 * </p>
	 * 
	 * <p>
	 * This procedure is the same one used by the JDT when changing the current
	 * FoldingStructureProvider, except of course that we use our settings for
	 * choosing the FoldingStructureProvider instead of the JDT's settings.
	 * </p>
	 */
	private void updateContainedProvider()
	{
		// Uninstall the old provider, if applicable
		if (containedProvider != null)
		{
			containedProvider.uninstall();
		}
		
		// If we aren't installed, then there's no need to have a contained
		// provider.
		if (installedEditor == null || installedViewer == null)
		{
			containedProvider = null;
			return;
		}
		
		// Find out what type of provider we need to create
		String providerType = Options.value(Options.innerFoldingProvider);
		
		JavaFoldingStructureProviderRegistry registry =
				JavaPlugin.getDefault().getFoldingStructureProviderRegistry();
		JavaFoldingStructureProviderDescriptor desc =
				registry.getFoldingProviderDescriptor(providerType);
		
		// If we can't find details, or if those details don't make sense,
		// reset to trying the default JDT provider.
		if (desc == null || desc.getId().equals(PROVIDER_ID))
		{
			// Our inner provider is either us (and we don't want that) or it
			// doesn't exist. Reset to default and try again.
			Activator.getDefault().getPreferenceStore().setToDefault(
					Options.innerFoldingProvider);
			
			providerType = Options.value(Options.innerFoldingProvider);
			desc = registry.getFoldingProviderDescriptor(providerType);
		}
		
		try {
			containedProvider = desc.createProvider();
		} catch (Exception e) {
			// For some reason we can't use our FoldingStructureProvider.
			// Log the error, and make a dummy provider instead.
			Log.errorlog("Error creating inner FoldingStructureProvider", e); //$NON-NLS-1$

			containedProvider = new IJavaFoldingStructureProvider() {
				@Override public void uninstall() {}
				@Override public void install(ITextEditor e, ProjectionViewer v) {}
				@Override public void initialize() {}
			};
		}
		
		containedProvider.install(installedEditor, installedViewer);
	}
	
	/**
	 * Create an inner FoldingStructureProvider to forward requests to, and
	 * install it.
	 * 
	 * {@inheritDoc}
	 */
	@Override
	public void install(final ITextEditor editor, final ProjectionViewer viewer) {
		// Keep track of our editor and viewer
		installedEditor = editor;
		installedViewer = viewer;
		
		// Forward to the folding provider that does the actual work
		updateContainedProvider();
		
		// Handle changes to the inner folding provider
		Activator.getDefault().getPreferenceStore().addPropertyChangeListener(
				containedProviderPropertyChangeListener);
	}

	/**
	 * Uninstall the inner FoldingStructureProvider
	 * 
	 * {@inheritDoc}
	 */
	@Override
	public void uninstall() {
		// We no longer care about whether the contained provider changes.
		Activator.getDefault().getPreferenceStore().removePropertyChangeListener(
				containedProviderPropertyChangeListener);
		
		// We are no longer installed
		installedEditor = null;
		installedViewer = null;
		updateContainedProvider();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProvider#initialize()
	 */
	@Override
	public void initialize() {
		containedProvider.initialize();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#collapseMembers()
	 */
	@Override
	public void collapseMembers() {
		if (containedProvider instanceof IJavaFoldingStructureProviderExtension)
		{
			((IJavaFoldingStructureProviderExtension) containedProvider).collapseMembers();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#collapseComments()
	 */
	@Override
	public void collapseComments() {
		if (containedProvider instanceof IJavaFoldingStructureProviderExtension)
		{
			((IJavaFoldingStructureProviderExtension) containedProvider).collapseComments();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#collapseElements(org.eclipse.jdt.core.IJavaElement[])
	 */
	@Override
	public void collapseElements(IJavaElement[] elements) {
		if (containedProvider instanceof IJavaFoldingStructureProviderExtension)
		{
			((IJavaFoldingStructureProviderExtension) containedProvider).collapseElements(elements);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingStructureProviderExtension#expandElements(org.eclipse.jdt.core.IJavaElement[])
	 */
	@Override
	public void expandElements(IJavaElement[] elements) {
		if (containedProvider instanceof IJavaFoldingStructureProviderExtension)
		{
			((IJavaFoldingStructureProviderExtension) containedProvider).expandElements(elements);
		}
	}
}
