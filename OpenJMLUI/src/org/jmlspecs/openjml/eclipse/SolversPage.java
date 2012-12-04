/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004-2011 David R. Cok
 * 
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

// FIXME - organize this page ; tool tips;
// FIXME - command arguments; adapter; adding/deleting solvers
// FIXME - be able to reset to the incoming properties
// FIXME - internationalize
// FIXME - fix keys

/**
 * This class creates a Preferences page in Eclipse
 * This page hold data needed for CodeSonar and Eclipse interaction
 */
public class SolversPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

	public SolversPage() {
		super(GRID);
	}
	
    public void init(IWorkbench workbench) {
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
        setDescription("File system paths to executables");
    }
    
    final static public String enableKey = "org.jmlspecs.openjml.solvers.enabled.";
    final static public String execKey = "org.jmlspecs.openjml.solvers.exec.";

	String[] solvers = { "Simplify", "Yices", "Z3", "CVC3", "CVC4" };
	
    @Override
    protected void createFieldEditors() {
    	
    	for (String solver: solvers) {
    	
	        addField(new FileFieldEditor(execKey + solver, solver + ": ",
	                getFieldEditorParent()));

    	}

    }
    

}
