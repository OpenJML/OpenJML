/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2004-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.eclipse.widgets.ButtonFieldEditor;
import org.jmlspecs.openjml.eclipse.widgets.LabelFieldEditor;

/**
 * This class creates a Preferences page in Eclipse
 * <P>
 * The preferences page manages various JML and OpenJML and plug-in specific options. As usual these are stored in the preferences store. Some project specific properties are stored differently.
 * <P>
 * Notes: Field editors are a convenient way to create a preferences page, but not quite convenient enough on a couple of counts.
 * <UL>
 * <LI>We need to observe when fields are changed. The normal way to do this would be to register a listener, but only one listener is allowed, and the implementation of FieldEditorPreferencePage
 * overwrites (during initialize()) any listener added when a field editor is created.
 * <LI>So we have to put the propertyChange call on the derived SettingsPage itself, which means that it is the same listener for all fields.
 * <LI>There is insufficient access to FieldEditorPreferencePage functionality such as the list of all fields or being able to force loads and stores.
 * </UL>
 */

/*
 * To add a new Preference do the following, using the existing contents of the files as a guide: 
 * a) Declare a key in Options.java. This must be either key(<option>) for items that have a
 * corresponding JmlOption or key(<name>) for this with a String name that does not correspond 
 * to a command-line OpeJML option. The key(<option>) String value is the same as the name of the option
 * when used as a system Property. 
 * b) Add declarations in Messages.java and corresponding text strings in messages.java; these are natural language strings used in the creation of the GUI widget 
 * c) Add a preference field in PreferencesPage.java, which uses the key from Options.java and the String fields from Messages.java 
 * d) In OpenJMLInterface.getOptions, convert the Preference into an
 * OpenJML option, as appropriate.
 */

public class PreferencesPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

    public PreferencesPage() {
        super(FLAT);
    }

    /**
     * Called by the framework when the preferences page is created; it initializes the preference store that the preference page should use to the preference store defined for the whole plugin.
     */
    public void init(IWorkbench workbench) {
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
    }

    /**
     * Sets all OpenJML store elements and correspoding fields to defaults (which actually removes the preference from the store)
     */
    public void setStoreAndFieldsToDefaults() {
        IPreferenceStore store = getPreferenceStore();
        for (Field f : Options.class.getDeclaredFields()) {
            String fieldName = f.getName();
            if (fieldName.contains("Key")) {
                try {
                    String key = f.get(null).toString(); // value of the field in class Options
                    store.setToDefault(key);
                    FieldEditor field = fieldMap.get(key);
                    if (field != null) {
                        field.load();
                    }
                } catch (IllegalAccessException e) {
                    // Should never happen
                }
            }
        }
    }

    /**
     * Initializes the preferences and the GUI widgets from the System properties (and command-line tool defaults); preferences without properties are set to defaults.
     */
    public void initializeFieldEditorsAndPreferencesFromProperties() {
        setStoreAndFieldsToDefaults(); // Need this for UI only fields that are not in the OpenML options
        Properties properties = Utils.getProperties();
        for (Map.Entry<Object, Object> entry : properties.entrySet()) {
            Object keyobj = entry.getKey();
            if (!(keyobj instanceof String))
                continue;
            String key = (String) keyobj;
            if (!(entry.getValue() instanceof String))
                continue;
            String value = (String) entry.getValue();
            if (key.contains(Env.OPENJML)) {
                if (Options.uiverboseness) {
                    Log.log("Reading property: " + key + " = " + value); //$NON-NLS-1$ //$NON-NLS-2$
                }
                FieldEditor field = fieldMap.get(key);
                if (field != null) {
                    if (field instanceof BooleanFieldEditor) {
                        getPreferenceStore().setValue(key, Boolean.parseBoolean(value));
                    } else if (field instanceof StringFieldEditor) {
                        getPreferenceStore().setValue(key, value);
                    } else if (field instanceof ComboFieldEditor) {
                        getPreferenceStore().setValue(key, value); // FIXME - how do we know it is a valid value
                    } else {
                        Log.errorKey("openjml.ui.unknown.field.editor", null, field.getClass(), key, value); //$NON-NLS-1$
                        continue;
                    }
                    field.load();
                } else {
                    // Assume anything else has a String value
                    getPreferenceStore().setValue(key, value);
                }
            } else {
                // There are lots of these - mostly Java or Eclipse related
                // Log.log("Ignoring property " + key + "=" + value);
            }
        }
    }

    /** A mapping of option keys to field names */
    static protected Map<String, FieldEditor> fieldMap = new HashMap<String, FieldEditor>();

    /** Overridden to add the field to the fieldMap */
    @Override
    public void addField(FieldEditor field) {
        super.addField(field);
        fieldMap.put(field.getPreferenceName(), field);
    }

    /**
     * Overriding performOk() callback in order to maintain copies of the option values appropriately. 
     * This is called when either 'Apply' or 'OK' is clicked.
     */
    @Override
    public boolean performOk() {
        boolean b = super.performOk();
        if (b) Options.cache();
        return b;
    }
    
    private void addBooleanField(String key, String text) {
        addField(new BooleanFieldEditor(key, 
                                text, 
                                getFieldEditorParent()));
    }

    private void addStringEditorField(String key, String text) {
        addField(new StringFieldEditor(key, 
                                text, 
                                getFieldEditorParent()));
    }
    
    private void addLabel(String text, int swtoptions) {
        addField(new LabelFieldEditor(
                                "zzzzz.ESC", //$NON-NLS-1$ // Duplicate keys for labels are OK
                                text, 
                                swtoptions, 
                                getFieldEditorParent()));
    }
    
    private void addSpace() {
        addLabel(Strings.empty, SWT.NONE);
    }
    
    private void addComboFieldEditor(String key, String text, String[][] options) {
        addField(new ComboFieldEditor(key, text, options, getFieldEditorParent()));
    }

    /**
     * The method that constructs all the editors and arranges them on the settings page.
     */
    @Override
    protected void createFieldEditors() {

        // JML

        MouseListener listener = new MouseAdapter() {
            @Override
            public void mouseUp(MouseEvent e) {
                initializeFieldEditorsAndPreferencesFromProperties();
            }
        };

        addField(new ButtonFieldEditor(Options.updateKey, "", //$NON-NLS-1$
                                Messages.OpenJMLUI_PreferencesPage_UpdateFromPropertiesFiles, 
                                listener, 
                                getFieldEditorParent()));

        addBooleanField(Options.initializeOnStartupKey, Messages.OpenJMLUI_PreferencesPage_InitializeOnStartup);

        addSpace();
        addLabel(Messages.OpenJMLUI_PreferencesPage_JmlOptions, SWT.SEPARATOR | SWT.HORIZONTAL);

        addBooleanField(Options.nullableByDefaultKey,   Messages.OpenJMLUI_PreferencesPage_NullableByDefault);
        addBooleanField(Options.strictKey,              Messages.OpenJMLUI_PreferencesPage_strictCheck);
        addBooleanField(Options.purityCheckKey,         Messages.OpenJMLUI_PreferencesPage_PurityCheck);
        addBooleanField(Options.showNotImplementedKey,  Messages.OpenJMLUI_PreferencesPage_WarnAboutNonImplementedConstructs);
        addBooleanField(Options.checkSpecsPathKey,      Messages.OpenJMLUI_PreferencesPage_CheckSpecificationPath);
        addBooleanField(Options.useInternalSpecsKey,    Messages.OpenJMLUI_PreferencesPage_UseInternalSystemSpecs);
        addStringEditorField(Options.optionalKeysKey,   Messages.OpenJMLUI_PreferencesPage_OptionalAnnotationKeys);
        addStringEditorField(Options.otherOptionsKey,   Messages.OpenJMLUI_PreferencesPage_OtherOptions);

        // ESC

        addSpace();
        addLabel(Messages.OpenJMLUI_PreferencesPage_OptionsRelatingToESC, SWT.SEPARATOR | SWT.HORIZONTAL);

        addBooleanField(Options.enableESCKey,           Messages.OpenJMLUI_PreferencesPage_EnableAutoESCChecking);

        addComboFieldEditor(Options.escMaxWarningsKey, Messages.OpenJMLUI_PreferencesPage_MaxWarnings, new String[][] { { "all", Integer.toString(Integer.MAX_VALUE) }, //$NON-NLS-1$
                                { "1", "1" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "2", "2" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "3", "3" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "4", "4" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "5", "5" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "6", "6" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "7", "7" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "8", "8" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "9", "9" }, //$NON-NLS-1$ //$NON-NLS-2$
        });

        addStringEditorField(Options.timeoutKey, Messages.OpenJMLUI_PreferencesPage_timeout);

        // addField(new BooleanFieldEditor(Options.traceKey, Messages.OpenJMLUI_PreferencesPage_Trace,
        // getFieldEditorParent()));
        // addField(new BooleanFieldEditor(Options.subexpressionsKey, Messages.OpenJMLUI_PreferencesPage_Subexpressions,
        // getFieldEditorParent()));

        addComboFieldEditor(Options.feasibilityKey, Messages.OpenJMLUI_PreferencesPage_Feasibility, new String[][] { { "all", "all" }, //$NON-NLS-1$
                                { "preconditions", "preconditions" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "exit", "exit" }, //$NON-NLS-1$ //$NON-NLS-2$
                                { "none", "none" }, //$NON-NLS-1$ //$NON-NLS-2$
        });

        // RAC

        addSpace();
        addLabel(Messages.OpenJMLUI_PreferencesPage_OptionsRelatingToRAC, SWT.SEPARATOR | SWT.HORIZONTAL);

        addBooleanField(Options.enableRacKey, Messages.OpenJMLUI_PreferencesPage_EnableAutoRuntimeAssertionChecking);
        addBooleanField(Options.useInternalRuntimeKey, Messages.OpenJMLUI_PreferencesPage_UseInternalRuntimeLibrary);
        addBooleanField(Options.compileToJavaAssert, Messages.OpenJMLUI_PreferencesPage_CompileToJavaAssert);
        addBooleanField(Options.racCheckJavaFeatures, Messages.OpenJMLUI_PreferencesPage_racCheckJavaFeatures);
        addBooleanField(Options.racCheckAssumptions, Messages.OpenJMLUI_PreferencesPage_racCheckAssumptions);
        addBooleanField(Options.racPreconditionEntry, Messages.OpenJMLUI_PreferencesPage_racPreconditionEntry);
        addBooleanField(Options.racShowSource, Messages.OpenJMLUI_PreferencesPage_racNoShowSource);
        addBooleanField(Options.showNotExecutableKey, Messages.OpenJMLUI_PreferencesPage_WarnAboutNonExecutableConstructs);
        addStringEditorField(Options.racbinKey, Messages.OpenJMLUI_PreferencesPage_DirectoryForRACOutput);

        // Debug and verbosity

        addSpace();
        addLabel(Messages.OpenJMLUI_PreferencesPage_VerbosenessAndDebugging, SWT.SEPARATOR | SWT.HORIZONTAL);

        addBooleanField(Options.javaverboseKey, Messages.OpenJMLUI_PreferencesPage_JavaVerbose);

        addBooleanField(Options.showKey, Messages.OpenJMLUI_PreferencesPage_Show);

        addComboFieldEditor(Options.verbosityKey, Messages.OpenJMLUI_PreferencesPage_VerbosityLevel, new String[][] {
                                { Messages.OpenJMLUI_PreferencesPage_quiet, Integer.toString(Utils.QUIET) }, 
                                { Messages.OpenJMLUI_PreferencesPage_normal, Integer.toString(Utils.NORMAL) },
                                { Messages.OpenJMLUI_PreferencesPage_progress, Integer.toString(Utils.PROGRESS) }, 
                                { Messages.OpenJMLUI_PreferencesPage_verbose, Integer.toString(Utils.VERBOSE) },
                                { Messages.OpenJMLUI_PreferencesPage_debug, Integer.toString(Utils.DEBUG) } }
                                );

        addBooleanField(Options.showErrorPopupsKey, Messages.OpenJMLUI_PreferencesPage_ShowErrorPopups);

        addBooleanField(Options.uiverbosityKey, Messages.OpenJMLUI_PreferencesPage_UIVerbose);

    }

}
