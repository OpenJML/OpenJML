/*
 * This file is part of the OpenJML plugin project.
 * Copyright 2004-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.osgi.util.NLS;

/** The strings defined here are initialized from the messages.properties file;
 * they are used as labels, titles, etc. in the UI. Error messages needing
 * formatting are mostly in the errors.properties file.
 */
public class Messages extends NLS {
	private static final String BUNDLE_NAME = "org.jmlspecs.openjml.eclipse.messages"; //$NON-NLS-1$
	public static String OpenJMLUI_Activator_JmlConsoleTitle;
	public static String OpenJMLUI_ExceptionTitle;
	public static String OpenJMLUI_JMLBuilder_Title;
	public static String OpenJMLUI_PathItem_AllSourceFolders;
	public static String OpenJMLUI_PathItem_ClassPath;
	public static String OpenJMLUI_PathItem_PROJECT;
	public static String OpenJMLUI_PathItem_SourcePath;
	public static String OpenJMLUI_PathItem_SysSpecs;
	public static String OpenJMLUI_PathItem_WORKSPACE;
	public static String OpenJMLUI_PathsEditor_ClassPath;
	public static String OpenJMLUI_PathsEditor_ClassPathTitle;
	public static String OpenJMLUI_PathsEditor_ClassPathTitle2;
	public static String OpenJMLUI_PathsEditor_DirectoryDialogMessage;
	public static String OpenJMLUI_PathsEditor_ErrorDialogTitle;
	public static String OpenJMLUI_PathsEditor_PersistentPropertyError;
	public static String OpenJMLUI_PathsEditor_SourcePath;
	public static String OpenJMLUI_PathsEditor_SourcePathTitle;
	public static String OpenJMLUI_PathsEditor_SpecsPath;
	public static String OpenJMLUI_PathsEditor_SpecsPathTitle;
	public static String OpenJMLUI_PathsEditor_UnparsableError;
	public static String OpenJMLUI_PathsEditor_Default;
	public static String OpenJMLUI_PathsEditor_AddJar;
	public static String OpenJMLUI_PathsEditor_AddFolder;
	public static String OpenJMLUI_PathsEditor_AddSpecial;
	public static String OpenJMLUI_PathsEditor_Remove;
	public static String OpenJMLUI_PathsEditor_Up;
	public static String OpenJMLUI_PathsEditor_Down;
	//public static String OpenJMLUI_PreferencesPage_AddRuntimeLibraryAutomatically;
	public static String OpenJMLUI_PreferencesPage_CheckSpecificationPath;
	public static String OpenJMLUI_PreferencesPage_debug;
	public static String OpenJMLUI_PreferencesPage_DirectoryForRACOutput;
	public static String OpenJMLUI_PreferencesPage_EnableAutoRuntimeAssertionChecking;
	public static String OpenJMLUI_PreferencesPage_JavaVerbose;
	public static String OpenJMLUI_PreferencesPage_JmlOptions;
	public static String OpenJMLUI_PreferencesPage_NonNullByDefault;
	public static String OpenJMLUI_PreferencesPage_normal;
	public static String OpenJMLUI_PreferencesPage_OptionalAnnotationKeys;
	public static String OpenJMLUI_PreferencesPage_OptionsRelatingToRAC;
	public static String OpenJMLUI_PreferencesPage_progress;
	public static String OpenJMLUI_PreferencesPage_quiet;
	public static String OpenJMLUI_PreferencesPage_SkipPurityCheck;
	public static String OpenJMLUI_PreferencesPage_UpdateFromPropertiesFiles;
	public static String OpenJMLUI_PreferencesPage_UseExternalRuntimeLibrary;
	public static String OpenJMLUI_PreferencesPage_UseExternalSystemSpecs;
	public static String OpenJMLUI_PreferencesPage_verbose;
	public static String OpenJMLUI_PreferencesPage_VerbosenessAndDebugging;
	public static String OpenJMLUI_PreferencesPage_VerbosityLevel;
	public static String OpenJMLUI_PreferencesPage_WarnAboutNonExecutableConstructs;
	public static String OpenJMLUI_PreferencesPage_WarnAboutNonImplementedConstructs;
	public static String OpenJMLUI_OpenSpecsEditor_DialogTitle;
	public static String OpenJMLUI_RACDialog_AddFile;
	public static String OpenJMLUI_RACDialog_AddFolder;
	public static String OpenJMLUI_RACDialog_Clear;
	public static String OpenJMLUI_RACDialog_DialogTitle;
	public static String OpenJMLUI_RACDialog_DirDialogTitle;
	public static String OpenJMLUI_RACDialog_ErrorDialogMessage;
	public static String OpenJMLUI_RACDialog_ErrorDialogTitle;
	public static String OpenJMLUI_SolversPage_DefaultLabel;
	public static String OpenJMLUI_SolversPage_Title;
	static {
		// initialize resource bundle
		NLS.initializeMessages(BUNDLE_NAME, Messages.class);
	}

	private Messages() {
	}
}
