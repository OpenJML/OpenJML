/**
 * 
 */
package org.jmlspecs.openjml.eclipse;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.text.folding.JavaFoldingStructureProviderDescriptor;
import org.eclipse.jdt.internal.ui.text.folding.JavaFoldingStructureProviderRegistry;
import org.eclipse.jdt.ui.text.folding.IJavaFoldingPreferenceBlock;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ComboViewer;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;

/**
 * @author dhouck
 *
 */
public class HighlightingFoldingStructureProviderPreferences implements
		IJavaFoldingPreferenceBlock {
	
	/**
	 * The ComboViewer for selecting which folding provider to use for the
	 * actual folding.
	 */
	private ComboViewer providerSelectorViewer;
	
	/**
	 * A map from the other folders' IDs to their display names.
	 */
	private static final Map<String, String> otherProviders = createProviderMap();
	
	private static Map<String, String> createProviderMap()
	{
		// Get a list of all descriptors
		JavaFoldingStructureProviderRegistry registry =
				JavaPlugin.getDefault().getFoldingStructureProviderRegistry();
		JavaFoldingStructureProviderDescriptor[] descriptors =
				registry.getFoldingProviderDescriptors();
		 // At least ours and the default provider should exist.
		assert descriptors.length > 1;
		
		// Put them into a map, except for the JML one (it can't be its own
		// inner provider)
		Map<String, String> descMap =
				new HashMap<String, String>(descriptors.length - 1);
		for (JavaFoldingStructureProviderDescriptor desc : descriptors)
		{
			if (!desc.getId().equals(
					HighlightingFoldingStructureProvider.PROVIDER_ID))
			{
				descMap.put(desc.getId(), desc.getName());
			}
		}
		assert descMap.size() == descriptors.length - 1;
		return descMap;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingPreferenceBlock#createControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public Control createControl(Composite parent) {
		Group controlGroup = new Group(parent, SWT.NONE);
		controlGroup.setText(Messages.OPENJMLUI_FoldingPreferences_GroupboxHeader);
		controlGroup.setLayout(new GridLayout(2, false));
		
		Label lblExplanation = new Label(controlGroup, SWT.WRAP);
		GridDataFactory.generate(lblExplanation, 2, 1);
		lblExplanation.setText(Messages.OPENJMLUI_FoldingPreferences_HeaderNote);		
		
		Label lblActualProvider = new Label(controlGroup, SWT.LEAD);
		lblActualProvider.setText(Messages.OPENJMLUI_FoldingPreferences_InnerFolderLabel);
		
		providerSelectorViewer = new ComboViewer(new Combo(controlGroup,
				SWT.READ_ONLY));
		providerSelectorViewer.setContentProvider(ArrayContentProvider.getInstance());
		providerSelectorViewer.setLabelProvider(new LabelProvider() {
			@Override
			public String getText(Object element) {
				return otherProviders.get(element);
			}
		});
		providerSelectorViewer.setInput(otherProviders.keySet());
		providerSelectorViewer.refresh();
		
		Label lblInstructions = new Label(controlGroup, SWT.WRAP);
		GridDataFactory.generate(lblInstructions, 2, 1);
		lblInstructions.setText(Messages.OPENJMLUI_FoldingPreferences_FooterNote);
		
		return controlGroup;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingPreferenceBlock#initialize()
	 */
	@Override
	public void initialize() {
		providerSelectorViewer.setSelection(new StructuredSelection(
				Options.value(Options.innerFoldingProvider)),
				true);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingPreferenceBlock#performOk()
	 */
	@Override
	public void performOk() {
		StructuredSelection sel = (StructuredSelection) providerSelectorViewer.
				getSelection();
		String newID = (String) sel.getFirstElement();
		Options.setValue(Options.innerFoldingProvider, newID);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingPreferenceBlock#performDefaults()
	 */
	@Override
	public void performDefaults() {
		Activator.getDefault().getPreferenceStore().setToDefault(
				Options.innerFoldingProvider);
		initialize();
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jdt.ui.text.folding.IJavaFoldingPreferenceBlock#dispose()
	 */
	@Override
	public void dispose() {
		// No need to do anything
	}

}
