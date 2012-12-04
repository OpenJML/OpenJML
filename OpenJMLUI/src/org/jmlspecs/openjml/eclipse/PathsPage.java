/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004-2011 David R. Cok
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.preference.DirectoryFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.PathEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class creates a Preferences page in Eclipse
 * This page hold data needed for CodeSonar and Eclipse interaction
 */
public class PathsPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

	// FIXME - fix the prefix
	
	/** The prefix to be put on each key. */
	final static public String prefix = "org.jmlspecs.openjml.preferences.";


	/** The preference store key for the classpath option. */
	final static public String classpathKey = prefix + "classpath";
	/** The preference store key for the classpath option. */
	final static public String sourcepathKey = prefix + "sourcepath";
	/** The preference store key for the classpath option. */
	final static public String specspathKey = prefix + "specspath";
	/** The preference store key for the destination option. */
	final static public String destinationKey = prefix + "destination";

	public PathsPage() {
		super(FLAT);
	}
	
    public void init(IWorkbench workbench) {
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
		setDescription("Directory paths for finding class files, source files and specification files");
    }

    @Override
    protected void createFieldEditors() {
        // Paths

        addField(new PathEditor(classpathKey, "Class Path",
                "X", getFieldEditorParent()));
        addField(new PathEditor(sourcepathKey, "Source Path",
                "Y",getFieldEditorParent()));
        addField(new PathEditor(specspathKey, "Specifications Path",
                "Z",getFieldEditorParent()));
        addField(new DirectoryFieldEditor(destinationKey, "Output Files Directory",
                getFieldEditorParent()));

    }
    

}
