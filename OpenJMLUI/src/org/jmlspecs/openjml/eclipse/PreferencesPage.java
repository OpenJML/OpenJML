/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2004-2013 David R. Cok
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
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.eclipse.widgets.ButtonFieldEditor;
import org.jmlspecs.openjml.eclipse.widgets.LabelFieldEditor;

/**
 * This class creates a Preferences page in Eclipse
 * This page hold data needed for CodeSonar and Eclipse interaction
 * <P>
 * The preferences page manages various JML and OpenJML and plug-in specific
 * options. As usual these are stored in the preferences store.
 * Some project specific properties are stored differently.
 * <P>
 * The key used for preferences is the same as the key used in System properties.
 * <P>
 * Notes: Field editors are a convenient way to create a preferences page,
 * but not quite convenient enough on a couple of counts. 
 * <UL>
 * <LI> We need to observe when fields are changed. The normal way to do this
 * would be to register a listener, but only one listener is allowed, and 
 * the implementation of FieldEditorPreferencePage overwrites (during initialize())
 * any listener added when a field editor is created.
 * <LI> So we have to put the propertyChange call on the derived SettingsPage
 * itself, which means that it is the same listener for all fields.
 * <LI> There is insufficient access to FieldEditorPreferencePage functionality
 * such as the list of all fields or being able to force loads and stores.
 * </UL>
 */

/* To add a new Preference do the following, using the existing contents of 
 * the files as a guide:
 * a) Declare a key in Options.java
 * b) Add a declaration in Messages.java
 * c) Add a preference field in PreferencesPage.java, which uses the key from
 * Options.java and the String from Messages.java
 * d) Add a property in messages.properties that will initialize the variable in
 * Messages.java
 * e) In OpenJMLInterface.getOptions, convert the Preference into an OpenJML
 * option, as appropriate.
 */

public class PreferencesPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

	public PreferencesPage() {
		super(FLAT);
		// No descriptive text needed. setDescription("Options for OpenJML");
	}
	
    public void init(IWorkbench workbench) {
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
    }
    
    /** A mapping of option keys to field names */
    protected Map<String,FieldEditor> fieldMap = new HashMap<String,FieldEditor>();

    /** Overridden to add the field to the fieldMap */
    @Override
    public void addField(FieldEditor field) {
    	super.addField(field);
    	fieldMap.put(field.getPreferenceName(), field);
    }
    

    /** Overriding performOk() callback in order to maintain copies
     * of the option values appropriately. This is called when
     * 'Apply' or 'OK' is clicked.
     */
	@Override
	public boolean performOk() {
		super.performOk();
        Options.init();
        return true;
	}
	
	/** The method that constructs all the editors and arranges them on the
	 * settings page.
	 */
    @Override
    protected void createFieldEditors() {
    	
    	// JML
    	
    	MouseListener listener = new MouseAdapter() {
    		@Override
			public void mouseUp(MouseEvent e) {
				Properties properties = Utils.getProperties();
				for (Map.Entry<Object,Object> entry : properties.entrySet()) {
					Object keyobj = entry.getKey();
					if (!(keyobj instanceof String)) continue;
					String key = (String)keyobj;
					if (!(entry.getValue() instanceof String)) continue;
					String value = (String)entry.getValue();
					if (key.contains(Env.OPENJML)) {
						if (Options.uiverboseness) {
							Log.log("Reading property: " + key + " = " + value); //$NON-NLS-1$ //$NON-NLS-2$
						}
						FieldEditor field = fieldMap.get(key);
						if (field != null) {
							if (field instanceof BooleanFieldEditor) {
								getPreferenceStore().setValue(key,!value.isEmpty());
							} else if (field instanceof StringFieldEditor) {
								getPreferenceStore().setValue(key,value);
							} else if (field instanceof ComboFieldEditor) {
								getPreferenceStore().setValue(key,value); // FIXME - how do we know it is a valid value
							} else {
								Log.errorKey("openjml.ui.unknown.field.editor",null,field.getClass(),key,value);  //$NON-NLS-1$
							}
							Options.init();
						} else {
							// Assume anything else has a String value
							getPreferenceStore().setValue(key,value);
						}
					} else {
						// There are lots of these - mostly Java or Eclipse related
						//Log.log("Ignoring property " + key + "=" + value);
					}
				}
				initialize();
			}
		};
		
		addField(new ButtonFieldEditor(Options.updateKey,"", //$NON-NLS-1$
				Messages.OpenJMLUI_PreferencesPage_UpdateFromPropertiesFiles,
				listener,
				getFieldEditorParent())
		);

		addField(new LabelFieldEditor("zzzzz.JML","",SWT.NONE, //$NON-NLS-1$ //$NON-NLS-2$
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.JML",Messages.OpenJMLUI_PreferencesPage_JmlOptions,SWT.SEPARATOR|SWT.HORIZONTAL, //$NON-NLS-1$
				getFieldEditorParent()));

        addField(new BooleanFieldEditor(Options.nullableByDefaultKey, Messages.OpenJMLUI_PreferencesPage_NullableByDefault,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.strictKey, Messages.OpenJMLUI_PreferencesPage_strictCheck,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.noCheckPurityKey, Messages.OpenJMLUI_PreferencesPage_SkipPurityCheck,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.showNotImplementedKey, Messages.OpenJMLUI_PreferencesPage_WarnAboutNonImplementedConstructs,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.checkSpecsPathKey, Messages.OpenJMLUI_PreferencesPage_CheckSpecificationPath,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.noInternalSpecsKey, Messages.OpenJMLUI_PreferencesPage_UseExternalSystemSpecs,
                getFieldEditorParent()));
        addField(new StringFieldEditor(Options.optionalKeysKey, Messages.OpenJMLUI_PreferencesPage_OptionalAnnotationKeys,
                getFieldEditorParent()));
        addField(new StringFieldEditor(Options.otherOptionsKey, Messages.OpenJMLUI_PreferencesPage_OtherOptions,
                getFieldEditorParent()));
        
        
        // ESC
        
		addField(new LabelFieldEditor("zzzzz.ESC","",SWT.NONE, //$NON-NLS-1$ //$NON-NLS-2$
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.ESC",Messages.OpenJMLUI_PreferencesPage_OptionsRelatingToESC,SWT.SEPARATOR|SWT.HORIZONTAL, //$NON-NLS-1$
				getFieldEditorParent()));

        addField(new BooleanFieldEditor(Options.enableESCKey, Messages.OpenJMLUI_PreferencesPage_EnableAutoESCChecking,
                getFieldEditorParent()));
        addField(new ComboFieldEditor(Options.maxWarningsKey, Messages.OpenJMLUI_PreferencesPage_MaxWarnings,
        		new String[][]{ 
        			{"All", Integer.toString(Integer.MAX_VALUE) },  //$NON-NLS-1$
        			{"1","1"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"2","2"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"3","3"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"4","4"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"5","5"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"6","6"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"7","7"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"8","8"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"9","9"},   //$NON-NLS-1$ //$NON-NLS-2$
        		    },
                getFieldEditorParent()));

        addField(new StringFieldEditor(Options.timeoutKey, Messages.OpenJMLUI_PreferencesPage_timeout,
                getFieldEditorParent()));

//        addField(new BooleanFieldEditor(Options.traceKey, Messages.OpenJMLUI_PreferencesPage_Trace,
//                getFieldEditorParent()));
//        addField(new BooleanFieldEditor(Options.subexpressionsKey, Messages.OpenJMLUI_PreferencesPage_Subexpressions,
//                getFieldEditorParent()));
        
        addField(new ComboFieldEditor(Options.feasibilityKey, Messages.OpenJMLUI_PreferencesPage_Feasibility,
        		new String[][]{ 
        			{"all", "all" },  //$NON-NLS-1$
        			{"preconditions","preconditions"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"exit", "exit"},   //$NON-NLS-1$ //$NON-NLS-2$
        			{"none", "none"},   //$NON-NLS-1$ //$NON-NLS-2$
        		    },
                getFieldEditorParent()));
        
        // RAC
        
		addField(new LabelFieldEditor("zzzzz.RAC","",SWT.NONE, //$NON-NLS-1$ //$NON-NLS-2$
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.RAC",Messages.OpenJMLUI_PreferencesPage_OptionsRelatingToRAC,SWT.SEPARATOR|SWT.HORIZONTAL, //$NON-NLS-1$
				getFieldEditorParent()));

        addField(new BooleanFieldEditor(Options.enableRacKey, Messages.OpenJMLUI_PreferencesPage_EnableAutoRuntimeAssertionChecking,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.noInternalRuntimeKey, Messages.OpenJMLUI_PreferencesPage_UseExternalRuntimeLibrary,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.compileToJavaAssert, Messages.OpenJMLUI_PreferencesPage_CompileToJavaAssert,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.racCheckJavaFeatures, Messages.OpenJMLUI_PreferencesPage_racCheckJavaFeatures,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.racCheckAssumptions, Messages.OpenJMLUI_PreferencesPage_racCheckAssumptions,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.racPreconditionEntry, Messages.OpenJMLUI_PreferencesPage_racPreconditionEntry,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.racNoShowSource, Messages.OpenJMLUI_PreferencesPage_racNoShowSource,
                getFieldEditorParent()));
        addField(new BooleanFieldEditor(Options.showNotExecutableKey, Messages.OpenJMLUI_PreferencesPage_WarnAboutNonExecutableConstructs,
                getFieldEditorParent()));
        addField(new StringFieldEditor(Options.racbinKey, Messages.OpenJMLUI_PreferencesPage_DirectoryForRACOutput,
                getFieldEditorParent()));

        // Debug and verbosity

		addField(new LabelFieldEditor("zzzzz.VERBOSE","",SWT.NONE, //$NON-NLS-1$ //$NON-NLS-2$
				getFieldEditorParent()));
		addField(new LabelFieldEditor("zzzzz.VERBOSE",Messages.OpenJMLUI_PreferencesPage_VerbosenessAndDebugging,SWT.SEPARATOR|SWT.HORIZONTAL, //$NON-NLS-1$
				getFieldEditorParent()));

        addField(new BooleanFieldEditor(Options.javaverboseKey, Messages.OpenJMLUI_PreferencesPage_JavaVerbose,
                getFieldEditorParent()));
        
        addField(new BooleanFieldEditor(Options.showKey, Messages.OpenJMLUI_PreferencesPage_Show,
                getFieldEditorParent()));
        
        addField(new ComboFieldEditor(Options.verbosityKey, Messages.OpenJMLUI_PreferencesPage_VerbosityLevel,
        		new String[][]{ 
        			{Messages.OpenJMLUI_PreferencesPage_quiet, Integer.toString(Utils.QUIET) }, 
        			{Messages.OpenJMLUI_PreferencesPage_normal, Integer.toString(Utils.NORMAL)}, 
        		    {Messages.OpenJMLUI_PreferencesPage_progress, Integer.toString(Utils.PROGRESS)}, 
        		    {Messages.OpenJMLUI_PreferencesPage_verbose, Integer.toString(Utils.VERBOSE)}, 
        		    {Messages.OpenJMLUI_PreferencesPage_debug, Integer.toString(Utils.DEBUG)}},
                getFieldEditorParent()));
        
        addField(new BooleanFieldEditor(Options.uiverbosityKey, Messages.OpenJMLUI_PreferencesPage_UIVerbose,
                getFieldEditorParent()));
        
        
    }
    

}
