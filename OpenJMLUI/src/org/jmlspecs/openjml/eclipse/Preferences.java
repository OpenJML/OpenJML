/*
 * Copyright (c) 2006-2010 David R. Cok
 * @author David R. Cok
 * Created Nov 22, 2006
 */
package org.jmlspecs.openjml.eclipse;


import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class implements the preference page for the plugin.
 * A preference is the persistent object typically associated with a processing 
 * option (as in the Options class),
 * for either the plug-in or the OpenJML application itself.
 * If you want to add new preferences, do all the following:
 * <UL>
 * <LI> Define the corresponding new option in Options
 * <LI> Declare a key for the preference (like nonnullByDefaultKey below)
 * <LI> Initialize an AbstractPreference object that controls the reading and 
 * writing of the preference (cf. nonnullByDefault).
 * Pick a child class of AbstractPreference that matches the type of the option 
 * value (Boolean, Int, Choice, File, ...)
 * <LI> Add a statement to extractOptions that sets the value of the option from the preference.
 * <LI> Add a new PreferenceWidget to one of the PreferenceWidget arrays
 * (e.g. eclipseOptions, jmlOptions, javaOptions, debugOptions).
 * This is the GUI element on the preference page that controls the preference and the option.
 * </UL>
 * 
 * @author David Cok
 * 
 */ // FIXME - review the instructions above
// FIXME - other options
// FIXME - consider reimplementing using standard preference page widgets

public class Preferences extends org.eclipse.jface.preference.PreferencePage 
implements IWorkbenchPreferencePage {

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}

	/** This class defines all the items that have a persistent
	 * presence in the Preferences store. */
	static public class POptions {
		/** The prefix to be put on each key. */
		final static public String prefix = "org.jmlspecs.JML.";

		/** The preference store key for the jmldebug option. */
		final static public String debugKey = prefix + "debug";
		/** The preference store key for the checkSpecsPath option. */
		final static public String checkSpecsPathKey = prefix + "checkSpecsPath";
		/** The preference store key for the nonnullByDefault option. */
		final static public String nonnullByDefaultKey = prefix + "nonnullByDefault";
		/** The preference store key for JML verbosity option. */
		final static public String jmlverbosityKey = prefix + "jmlverbosity";
		/** The preference store key for the verbosity (quiet, nowarnings, verbose) option. */
		final static public String verbosityKey = prefix + "verbosity";
		/** The preference store key for the uiverbosity option. */
		final static public String uiverbosityKey = prefix + "uiverbosity";
		/** The preference store key for the source option. */
		final static public String sourceKey = prefix + "javaSourceVersion";
		/** The preference store key for the classpath option. */
		final static public String classpathKey = prefix + "classpath";
		/** The preference store key for the destination option. */
		final static public String destinationKey = prefix + "destination";
		/** The preference store key for the specsProjectName option. */
		final static public String specsProjectNameKey = prefix + "specsProjectName";
		/** The preference store key for the parsePlus option. */
		final static public String parsePlusKey = prefix + "parsePlus";
		/** The preference store key for the parsePlus option. */
		final static public String checkPurityKey = prefix + "checkPurity";
		/** The preference store key for the showNotImplemented option. */
		final static public String showNotImplementedKey = prefix + "showNotImplemented";
		/** The preference store key for the showNotExecutable option. */
		final static public String showNotExecutableKey = prefix + "showNotExecutable";
		/** The preference store key for the noInternalSpecs option. */
		final static public String noInternalSpecsKey = prefix + "noInternalSpecs";
		/** The preference store key for the noInternalRuntime option. */
		final static public String noInternalRuntimeKey = prefix + "noInternalRuntime";
		/** The preference store key for the autoAddRuntimeToProject option */
		final static public String autoAddRuntimeToProjectKey = prefix + "autoAddRuntimeToProject";
		
		/** A temporary copy of the options structure, just used to get
		 * the initial defaults.
		 */
		private Options defaultOptions = new Options();

		/** The object controlling the preference store entry for the debug option. */
		public AbstractPreference.BooleanOption debug = 
			new AbstractPreference.BooleanOption(debugKey,defaultOptions.debug,"OpenJML debugging","When on, debug information is emitted");

		/** The object controlling the preference store entry for the debugast option. */
		public AbstractPreference.BooleanOption nonnullByDefault = 
			new AbstractPreference.BooleanOption(nonnullByDefaultKey,defaultOptions.nonnullByDefault,"NonNull by default","When on, references are non-null by default");

		/** The object controlling the preference store entry for the checkSpecsPath option. */
		public AbstractPreference.BooleanOption checkSpecsPath = 
			new AbstractPreference.BooleanOption(checkSpecsPathKey,defaultOptions.checkSpecsPath,"Check specs path entries","When on, all specs path entries must be directories that exist");

		/** The object controlling the preference store entry for the verbosity option. */
		public AbstractPreference.IntOption verbosity = 
			new AbstractPreference.IntOption(verbosityKey,
					defaultOptions.verbosity,"Java verbosity","Amount of information emitted by the compiler");

		/** The object controlling the preference store entry for the uiverbosity option. */
		public AbstractPreference.IntOption uiverbosity = 
			new AbstractPreference.IntOption(uiverbosityKey,defaultOptions.uiverbosity,"UI verbosity","Amount of information emitted about the UI");

		/** The object controlling the preference store entry for the JML verbosity option. */
		public AbstractPreference.BooleanOption jmlverbosity = 
			new AbstractPreference.BooleanOption(jmlverbosityKey,defaultOptions.jmlverbose,"JML verbosity","Enable verbose output about JML");

		/** The object controlling the preference store entry for the source option. */
		public AbstractPreference.ChoiceOption source = 
			new AbstractPreference.ChoiceOption(sourceKey,
					new String[]{"1.4","1.5","1.6","1.7"},
					defaultOptions.source,"Java source","Version of Java source that is recognized");

		/** The object controlling the preference store entry for the destination option. */
		public AbstractPreference.StringOption destination = 
			new AbstractPreference.StringOption(destinationKey,defaultOptions.destination,"Destination directory","Directory in which to put compiled files");

		/** The object controlling the preference store entry for the parsePlus option. */
		public AbstractPreference.BooleanOption parsePlus = 
			new AbstractPreference.BooleanOption(parsePlusKey,defaultOptions.parsePlus,"Parse /*+@ comments","When on, comments beginning with +@ are JML comments, as well as those beginning with @");

		/** The object controlling the preference store entry for the check purity option. */
		public AbstractPreference.BooleanOption checkPurity = 
			new AbstractPreference.BooleanOption(checkPurityKey,defaultOptions.checkPurity,"Check Purity","When on, comments beginning with +@ are JML comments, as well as those beginning with @");

		/** The object controlling the preference store entry for the showNotImplemented option. */
		public AbstractPreference.BooleanOption showNotImplemented = 
			new AbstractPreference.BooleanOption(showNotImplementedKey,defaultOptions.showNotImplemented,"Warn Not Implemented Features","When on, warnings are issued about features used but not implemented");

		/** The object controlling the preference store entry for the showNotExecutable option. */
		public AbstractPreference.BooleanOption showNotExecutable = 
			new AbstractPreference.BooleanOption(showNotExecutableKey,defaultOptions.showNotExecutable,"Warn Not Executable Features","When on, warnings are issued about features used in RAC but not implemented");

		/** The object controlling the preference store entry for the noInternalSpecs option. */
		public AbstractPreference.BooleanOption noInternalSpecs = 
			new AbstractPreference.BooleanOption(noInternalSpecsKey,defaultOptions.noInternalSpecs,"Do not use internal specs","When on, internal library specifications are not used (user must supply them)");

		/** The object controlling the preference store entry for the noInternalRuntime option. */
		public AbstractPreference.BooleanOption noInternalRuntime = 
			new AbstractPreference.BooleanOption(noInternalRuntimeKey,defaultOptions.noInternalRuntime,"Do not use internal runtime library","When on, default runtime library is not used (user must supply it)");

		/** The object controlling the preference store entry for the autoAddRuntimeToProject option. */
		public AbstractPreference.BooleanOption autoAddRuntimeToProject = 
			new AbstractPreference.BooleanOption(autoAddRuntimeToProjectKey,defaultOptions.autoAddRuntimeToProject,"Automatically add annotation library to project classpath when checked","When on, the annotation library is automatically added to the project classpath when the project is checked");

		
	}
	/** An instance of the object that holds all of the preference store items. */
	static POptions poptions = new POptions();

	/** This method fills in an Options structure whose values are set from
	 * the current preference store settings (which should match those in the UI).
	 * We use the preference store instead of the UI widgets so that this method
	 * works even if the preference page has not yet been generated.  If the 
	 * argument is null, a new Options structure is allocated; otherwise the
	 * fields of the argument are filled in.  The argument or newly allocated 
	 * object is returned.
	 * @param options if not null, the structure to fill in
	 * @return An Options structure initialized to the current preference store settings.
	 */
	static public Options extractOptions(Options options) {
		if (options == null) options = new Options();
		options.debug = poptions.debug.getValue();
		options.verbosity = poptions.verbosity.getValue();
		options.uiverbosity = poptions.uiverbosity.getValue();
		options.source = poptions.source.getStringValue();
		options.destination = poptions.destination.getValue();
		options.jmlverbose = poptions.jmlverbosity.getValue();
		options.parsePlus = poptions.parsePlus.getValue();
		options.checkPurity = poptions.checkPurity.getValue();
		options.nonnullByDefault = poptions.nonnullByDefault.getValue();
		options.checkSpecsPath = poptions.checkSpecsPath.getValue();
		options.showNotImplemented = poptions.showNotImplemented.getValue();
		options.showNotExecutable = poptions.showNotExecutable.getValue();
		options.noInternalSpecs = poptions.noInternalSpecs.getValue();
		options.noInternalRuntime = poptions.noInternalRuntime.getValue();
		options.autoAddRuntimeToProject = poptions.autoAddRuntimeToProject.getValue();
		return options;
	}


	/**
	 * This is the list of widgets in the JmlEclipse options section of the
	 * preferences page
	 */
	final static private PreferenceWidget<?>[] javaOptions = {
		new PreferenceWidget.ChoiceWidget(poptions.source),
		new PreferenceWidget.DirectoryWidget(poptions.destination)
	};

	/**
	 * An array of the JML option widgets.
	 */
	static final private PreferenceWidget<?>[] jmlOptions = {
		new PreferenceWidget.BooleanWidget(poptions.parsePlus),
		new PreferenceWidget.BooleanWidget(poptions.checkPurity),
		new PreferenceWidget.BooleanWidget(poptions.nonnullByDefault),
		new PreferenceWidget.BooleanWidget(poptions.checkSpecsPath),
		new PreferenceWidget.BooleanWidget(poptions.showNotImplemented),
		new PreferenceWidget.BooleanWidget(poptions.showNotExecutable),
		new PreferenceWidget.BooleanWidget(poptions.noInternalSpecs),
		new PreferenceWidget.BooleanWidget(poptions.noInternalRuntime),
		new PreferenceWidget.BooleanWidget(poptions.autoAddRuntimeToProject),
	};

	/**
	 * An array of widgets for verbosity and debugging options.
	 */
	static final private PreferenceWidget<?>[] debugOptions = {
		new PreferenceWidget.IntChoiceWidget(
				poptions.verbosity,new String[]{"errors only","errors and warnings (quiet)","normal","verbose"}),
		new PreferenceWidget.IntChoiceWidget(
						poptions.uiverbosity,new String[]{"quiet","timing info","progress info","verbose"}),
		new PreferenceWidget.BooleanWidget(poptions.jmlverbosity),
		new PreferenceWidget.BooleanWidget(poptions.debug),
	};
	
	static final private PreferenceWidget<?>[][] allOptions = {
		javaOptions,
		jmlOptions,
		debugOptions
	};

	/**
	 * Creates the property page controls and initializes them.
	 * 
	 * @param parent The UI object into which to insert the controls
	 * @return The new control that is added to 'parent'
	 */
	protected Control createContents(Composite parent) {

		// Creates the contents of the property page view.

		Control composite = addControl(parent);
		return composite;
	}

	/**
	 * Constructs the view of the property page by adding different features like
	 * labels, and setting the layout. Just a helper to <code>createContents()
	 * </code>.
	 * 
	 * @param parent The parent composite to which the controls are added
	 * @return The resulting control that defined the looking of the property page
	 */
	private Control addControl(Composite parent) {
		Composite composite0 = new Widgets.VComposite(parent);

		new Label(composite0, SWT.CENTER)
		.setText("OpenJML version: " + OpenJMLInterface.version());
		new Label(composite0, SWT.CENTER)
		.setText("These options are workspace options that apply to every JML-enabled Java project.");

		// FIXME - Rearrange?
		//  Composite composite0 = new Widgets.HComposite(composite0a, 2);
		//  Composite composite1 = new Widgets.VComposite(composite0);
		//  Composite composite2a = new Widgets.VComposite(composite0);
		//  Composite composite2 = new Widgets.HComposite(composite2a, 2);
		//  Composite composite3 = new Widgets.VComposite(composite2);
		//  Composite composite4 = new Widgets.VComposite(composite2);

//		new Widgets.LabeledSeparator(composite0, "Options relating to the UI");
//		addWidgets(eclipseOptions, composite0);
		new Widgets.LabeledSeparator(composite0, "Options relating to JML");
		addWidgets(jmlOptions, composite0);
		new Widgets.LabeledSeparator(composite0, "Options relating to Java");
		addWidgets(javaOptions, composite0);
		new Widgets.LabeledSeparator(composite0, "Options controlling verboseness and debugging");
		addWidgets(debugOptions, composite0);

		return composite0;
	}

	/**
	 * @see org.eclipse.jface.preference.IPreferencePage#performOk()
	 */
	public boolean performOk() {
		// When OK is pressed, set all the options selected.
		for (int i=0; i<allOptions.length; ++i) {
			for (PreferenceWidget<?> p: allOptions[i]) {
				p.setOptionValue();
			}
		}
		AbstractPreference.notifyListeners();
		return true;
	}

	public void performDefaults() {
		// When OK is pressed, set all the options selected.    
		for (int i = 0; i<allOptions.length; ++i) {
			for (PreferenceWidget<?> p: allOptions[i]) {
				p.setDefault();
			}
		}
	}

	// Inherited method
	@Override
	protected IPreferenceStore doGetPreferenceStore() {
		return Activator.getDefault().getPreferenceStore();
	}

	// Default implementation does a performOk()
	//public void performApply();

	// Default implementation does nothing and returns true, closing the dialog
	//public boolean performCancel();

	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.IDialogPage#performHelp()
	 */
	// Default does nothing
	@Override
	public void performHelp() {} // TODO ? What should we do?

	/**
	 * Calls 'addWidget' on all the items in the list of PreferenceWidgets, in
	 * order to add them to the given composite.
	 * @param ws    The list of widgets to be added
	 * @param composite The composite to add them to
	 */
	//@ requires ws != null && composite != null;
	//@ requires \nonnullelements(ws);
	protected void addWidgets(PreferenceWidget<?>[] ws, Composite composite) {
		addWidgets(ws,0,ws.length,composite);
	}

	/**
	 * Calls 'addWidget' on some of the items in the list of PreferenceWidgets, in
	 * order to add them to the given composite.
	 * @param ws    The list of widgets to be added
	 * @param offset The index in the array at which to begin
	 * @param num The number of widgets to add
	 * @param composite The composite to add them to
	 */
	//@ requires ws != null && composite != null;
	//@ requires offset >= 0 && offset < ws.length;
	//@ requires num >= 0 && offset + num < ws.length;
	//@ requires \nonnullelements(ws);
	protected void addWidgets(PreferenceWidget<?>[] ws, int offset, int num, Composite composite) {
		for (int i=0; i<num; ++i) {
			ws[offset+i].addWidget(composite);
		}
	}
}
