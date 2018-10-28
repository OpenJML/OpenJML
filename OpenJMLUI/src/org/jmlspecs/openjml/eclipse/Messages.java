/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2004-2013 David R. Cok
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
	public static String OpenJMLUI_Editor_ClassPath;
	public static String OpenJMLUI_Editor_ClassPathTitle;
	public static String OpenJMLUI_Editor_ClassPathTitle2;
	public static String OpenJMLUI_Editor_DirectoryDialogMessage;
	public static String OpenJMLUI_Editor_ErrorDialogTitle;
	public static String OpenJMLUI_Editor_PersistentPropertyError;
	public static String OpenJMLUI_Editor_SourcePath;
	public static String OpenJMLUI_Editor_SourcePathTitle;
	public static String OpenJMLUI_Editor_SpecsPath;
	public static String OpenJMLUI_Editor_SpecsPathTitle;
	public static String OpenJMLUI_Editor_UnparsableError;
	public static String OpenJMLUI_Editor_Default;
	public static String OpenJMLUI_Editor_AddJar;
	public static String OpenJMLUI_Editor_AddFolder;
	public static String OpenJMLUI_Editor_AddSpecial;
	public static String OpenJMLUI_Editor_Add;
	public static String OpenJMLUI_Editor_Remove;
	public static String OpenJMLUI_Editor_Up;
	public static String OpenJMLUI_Editor_Down;
	public static String OpenJMLUI_PreferencesPage_CheckSpecificationPath;
	public static String OpenJMLUI_PreferencesPage_debug;
	public static String OpenJMLUI_PreferencesPage_DirectoryForRACOutput;
	public static String OpenJMLUI_PreferencesPage_EnableAutoESCChecking;
	public static String OpenJMLUI_PreferencesPage_EnableAutoRuntimeAssertionChecking;
	public static String OpenJMLUI_PreferencesPage_Show;
	public static String OpenJMLUI_PreferencesPage_JavaVerbose;
	public static String OpenJMLUI_PreferencesPage_JmlOptions;
	public static String OpenJMLUI_PreferencesPage_InitializeOnStartup;
	public static String OpenJMLUI_PreferencesPage_NullableByDefault;
	public static String OpenJMLUI_PreferencesPage_INFER_DEBUG;
	public static String OpenJMLUI_PreferencesPage_INFER_TIMEOUT;
	public static String OpenJMLUI_PreferencesPage_INFER_MAX_DEPTH;
	public static String OpenJMLUI_PreferencesPage_INFER_DEV_TOOLS;
	public static String OpenJMLUI_PreferencesPage_INFER_PERSIST_MODE;
	public static String OpenJMLUI_PreferencesPage_INFER_DEFAULT_PRECONDITIONS;	
	
	public static String OpenJMLUI_StrongarmPage_Title;
	public static String OpenJMLUI_PreferencesPage_normal;
	public static String OpenJMLUI_PreferencesPage_timeout;
	public static String OpenJMLUI_PreferencesPage_OptionalAnnotationKeys;
	public static String OpenJMLUI_PreferencesPage_OptionsRelatingToESC;
	public static String OpenJMLUI_PreferencesPage_OptionsRelatingToRAC;
	public static String OpenJMLUI_PreferencesPage_CompileToJavaAssert;
	public static String OpenJMLUI_PreferencesPage_strictCheck;
	public static String OpenJMLUI_PreferencesPage_racCheckJavaFeatures;
	public static String OpenJMLUI_PreferencesPage_racCheckAssumptions;
	public static String OpenJMLUI_PreferencesPage_racPreconditionEntry;
	public static String OpenJMLUI_PreferencesPage_racNoShowSource;
	public static String OpenJMLUI_PreferencesPage_progress;
	public static String OpenJMLUI_PreferencesPage_quiet;
	public static String OpenJMLUI_PreferencesPage_PurityCheck;
	public static String OpenJMLUI_PreferencesPage_UIVerbose;
	public static String OpenJMLUI_PreferencesPage_UpdateFromPropertiesFiles;
	public static String OpenJMLUI_PreferencesPage_UseInternalRuntimeLibrary;
	public static String OpenJMLUI_PreferencesPage_UseInternalSystemSpecs;
	public static String OpenJMLUI_PreferencesPage_verbose;
	public static String OpenJMLUI_PreferencesPage_VerbosenessAndDebugging;
	public static String OpenJMLUI_PreferencesPage_VerbosityLevel;
	public static String OpenJMLUI_PreferencesPage_WarnAboutNonExecutableConstructs;
	public static String OpenJMLUI_PreferencesPage_WarnAboutNonImplementedConstructs;
	public static String OpenJMLUI_PreferencesPage_MaxWarnings;
	public static String OpenJMLUI_PreferencesPage_Trace;
	public static String OpenJMLUI_PreferencesPage_Subexpressions;
	public static String OpenJMLUI_PreferencesPage_Feasibility;
	public static String OpenJMLUI_PreferencesPage_ShowErrorPopups;
	public static String OpenJMLUI_OpenSpecsEditor_DialogTitle;
	public static String OpenJMLUI_PreferencesPage_OtherOptions;
	public static String OpenJMLUI_RACDialog_AddFile;
	public static String OpenJMLUI_RACDialog_AddFolder;
	public static String OpenJMLUI_RACDialog_Clear;
	public static String OpenJMLUI_RACDialog_DialogTitle;
	public static String OpenJMLUI_RACDialog_DirDialogTitle;
	public static String OpenJMLUI_RACDialog_ErrorDialogMessage;
	public static String OpenJMLUI_RACDialog_ErrorDialogTitle;
	public static String OpenJMLUI_SolversPage_DialogTitle;
	public static String OpenJMLUI_SolversPage_DefaultLabel;
	public static String OpenJMLUI_SolversPage_Title;
	public static String OpenJMLUI_JobControlPage_Title;
	public static String OpenJMLUI_SolversListEditor_Title;
	public static String OpenJMLUI_SolversPage_EditButton;
	static {
		// initialize resource bundle
		NLS.initializeMessages(BUNDLE_NAME, Messages.class);
	}

	private Messages() {
	}
}
