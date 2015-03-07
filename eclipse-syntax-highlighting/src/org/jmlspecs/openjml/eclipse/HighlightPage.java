package org.jmlspecs.openjml.eclipse;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.eclipse.widgets.LabelFieldEditor;

/**
 * This class represents a preference page that
 * is contributed to the Preferences dialog. By 
 * subclassing <samp>FieldEditorPreferencePage</samp>, we
 * can use the field support built into JFace that allows
 * us to create a page that is small and knows how to 
 * save, restore and apply itself.
 * <p>
 * This page is used to modify preferences only. They
 * are stored in the preference store that belongs to
 * the main plug-in class. That way, preferences can
 * be accessed directly via the preference store.
 */

public class HighlightPage extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	/**
	 * A map from color editors to their parents.
	 */
	private final Map<ColorFieldEditor, Composite> colorFieldEditors = 
			new HashMap<ColorFieldEditor, Composite>();
	
	/**
	 * The enabled field.
	 */
	private BooleanFieldEditor enabledEditor;
	
	public HighlightPage() {
		super(GRID);
		setPreferenceStore(Activator.getDefault().getPreferenceStore());
	}
	
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		enabledEditor = new BooleanFieldEditor(Options.highlightEnableKey, 
				Messages.OpenJMLUI_HighlightPage_Enable, getFieldEditorParent());
		addField(enabledEditor);
		
		Composite parent = getFieldEditorParent();
		ColorFieldEditor editor = new ColorFieldEditor(Options.highlightDefaultKey, 
				Messages.OpenJMLUI_HighlightPage_Default, parent);
		addField(editor);
		colorFieldEditors.put(editor, parent);
		parent = getFieldEditorParent();
		editor = new ColorFieldEditor(Options.highlightKeywordKey, 
				Messages.OpenJMLUI_HighlightPage_Keyword, parent);
		addField(editor);
		colorFieldEditors.put(editor, parent);
		parent = getFieldEditorParent();
		editor = new ColorFieldEditor(Options.highlightOperatorKey, 
				Messages.OpenJMLUI_HighlightPage_Operator, parent);
		addField(editor);
		colorFieldEditors.put(editor, parent);
		
		addField(new LabelFieldEditor("", "", SWT.NONE, getFieldEditorParent()));
		
		addField(new LabelFieldEditor("", Messages.OpenJMLUI_HighlightPage_Footer, 
				SWT.NONE, getFieldEditorParent()));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
	
	public void propertyChange(final PropertyChangeEvent event) {
		if (event.getProperty().equals(Options.highlightEnableKey))
		{
			for (ColorFieldEditor c : colorFieldEditors.keySet()) {
				c.setEnabled(enabledEditor.getBooleanValue(), colorFieldEditors.get(c));
			}
		}
	}
}
