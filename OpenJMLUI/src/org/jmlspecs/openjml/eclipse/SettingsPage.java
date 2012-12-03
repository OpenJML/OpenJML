/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004-2011 David R. Cok
 * 
 */
package org.jmlspecs.openjml.eclipse;

import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.Strings;

// FIXME - organize this page with some headings; tool tips;
// FIXME - path editor, keys editor, other options, solvers page

/**
 * This class creates a Preferences page in Eclipse
 * This page hold data needed for CodeSonar and Eclipse interaction
 */
public class SettingsPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

	static public class POptions {
		/** The prefix to be put on each key. */
		final static public String prefix = Strings.optionPropertyPrefix;

		/** A fake preference store key for the update button. */
		final static public String updateKey = prefix + "update";

//		/** The preference store key for the jmldebug option. */
//		final static public String debugKey = prefix + "debug";
		/** The preference store key for the checkSpecsPath option. */
		final static public String checkSpecsPathKey = prefix + "checkSpecsPath";
		/** The preference store key for the nonnullByDefault option. */
		final static public String nonnullByDefaultKey = prefix + "nonnullByDefault";
//		/** The preference store key for JML verbosity option. */
//		final static public String jmlverbosityKey = prefix + "jmlverbosity";
//		/** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
		final static public String verbosityKey = prefix + "verbosity";
		/** The preference store key for the uiverbosity option. */
//		final static public String uiverbosityKey = prefix + "uiverbosity";
//		/** The preference store key for the source option. */
//		final static public String sourceKey = prefix + "javaSourceVersion";
//		/** The preference store key for the specsProjectName option. */
//		final static public String specsProjectNameKey = prefix + "specsProjectName";
//		/** The preference store key for the parsePlus option. */
//		final static public String parsePlusKey = prefix + "parsePlus";
		/** The preference store key for the check purity option. */
		final static public String checkPurityKey = prefix + "noPurityCheck";
		/** The preference store key for the keys option. */
		final static public String optionalKeysKey = prefix + "optionalKeys";
		/** The preference store key for the showNotImplemented option. */
		final static public String showNotImplementedKey = prefix + "showNotImplemented";
		/** The preference store key for the showNotExecutable option. */
		final static public String showNotExecutableKey = prefix + "showNotExecutable";
		/** The preference store key for the noInternalSpecs option. */
		final static public String internalSpecsKey = prefix + "noInternalSpecs";
		/** The preference store key for the noInternalRuntime option. */
		final static public String noInternalRuntimeKey = prefix + "noInternalRuntime";
		/** The preference store key for the autoAddRuntimeToProject option */
		final static public String autoAddRuntimeToProjectKey = prefix + "autoAddRuntimeToProject";
	}

	public SettingsPage() {
		super(FLAT);
//		setPreferenceStore(Activator.getDefault().getPreferenceStore());
//		setDescription("A demonstration of a preference page implementation");
	}
	
    public void init(IWorkbench workbench) {
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
    }
    
    @Override
    public void addField(FieldEditor field) {
    	super.addField(field);
    	fieldMap.put(field.getPreferenceName(), field);
    }
    
    protected Map<String,FieldEditor> fieldMap = new HashMap<String,FieldEditor>();

    @Override
    protected void createFieldEditors() {
    	
    	// JML

    	MouseListener listener = new MouseAdapter() {
    		@Override
			public void mouseUp(MouseEvent e) {
				Properties properties = org.jmlspecs.openjml.Utils.findProperties(null);
				for (Map.Entry<Object,Object> entry : properties.entrySet()) {
					Object keyobj = entry.getKey();
					if (!(keyobj instanceof String)) continue;
					String key = (String)keyobj;
					if (!(entry.getValue() instanceof String)) continue;
					String value = (String)entry.getValue();
					if (key.startsWith(Strings.optionPropertyPrefix)) {
						FieldEditor field = fieldMap.get(key);
						if (field != null) {
							System.out.println("SETTING " + key + " " + value);
							if (field instanceof BooleanFieldEditor) {
								getPreferenceStore().setValue(key,!value.isEmpty());
							} else if (field instanceof StringFieldEditor) {
								getPreferenceStore().setValue(key,value);
							} else if (field instanceof ComboFieldEditor) {
								getPreferenceStore().setValue(key,value); // FIXME - how do we know it is a valid value
							} else {
								System.out.println("Ignoring unknown field editor type " + field.getClass() + " for property " + key + "=" + value);
							}
						} else {
							System.out.println("No field editor for property " + key + "=" + value);
						}
					} else {
						System.out.println("Ignoring property " + key + "=" + value);
					}
				}
				initialize();
			}
		};
		addField(new ButtonFieldEditor(POptions.updateKey,"",
				"Update from properties files",
				listener,
				getFieldEditorParent())
		);

		addField(new LabelFieldEditor("zzzzz.JML","",SWT.NONE,
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.JML","JML Options",SWT.SEPARATOR|SWT.HORIZONTAL,
				getFieldEditorParent()));

		// FIXME - i10n these strings

        addField(new BooleanFieldEditor(POptions.nonnullByDefaultKey, "NonNull By Default",
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(POptions.checkPurityKey, "Skip Purity Check",
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(POptions.showNotImplementedKey, "Warn about not-implemented constructs",
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(POptions.showNotExecutableKey, "Warn about not-executable constructs",
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(POptions.checkSpecsPathKey, "Check Specification Path",
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(POptions.internalSpecsKey, "Use internal specs",
                getFieldEditorParent()));
        addField(new StringFieldEditor(POptions.optionalKeysKey, "Optional Annotation Keys",
                getFieldEditorParent()));
        
        
        // RAC
        
		addField(new LabelFieldEditor("zzzzz.RAC","",SWT.NONE,
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.RAC","Options relating to RAC",SWT.SEPARATOR|SWT.HORIZONTAL,
				getFieldEditorParent()));

        addField(new BooleanFieldEditor(POptions.checkSpecsPathKey, "Use the internal runtime library",
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(POptions.checkSpecsPathKey, "Add runtime library to project automatically",
                getFieldEditorParent()));

        // Debug and verbosity

		addField(new LabelFieldEditor("zzzzz.VERBOSE","",SWT.NONE,
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.VERBOSE","Verboseness and Debugging",SWT.SEPARATOR|SWT.HORIZONTAL,
				getFieldEditorParent()));

        addField(new ComboFieldEditor(POptions.verbosityKey, "Verbosity Level",
        		new String[][]{ { "quiet", "quiet" }, {"normal", "normal"}, {"verbose", "verbose"}, {"debug", "debug"}},
                getFieldEditorParent()));
        

    }
    
	static class LabeledSeparator extends Composite {
		/**
		 * @param parent  The container this widget is made part of
		 * @param label	  The text to be used as the label in the widget
		 */
		public LabeledSeparator(/*@ non_null */ Composite parent, 
				/*@ non_null */ String label) {
			super(parent, SWT.NONE);
			GridLayout layout = new GridLayout();
			layout.numColumns = 2;
			setLayout(layout);
			GridData data = new GridData();
			data.verticalAlignment = GridData.FILL;
			data.horizontalAlignment = GridData.FILL;
			setLayoutData(data);
			new Label(this,SWT.SEPARATOR|SWT.HORIZONTAL);
			new Label(this,SWT.NONE).setText(label);
		}
	}


}
