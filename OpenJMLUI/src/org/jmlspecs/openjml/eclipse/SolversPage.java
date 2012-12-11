/*
 * This file is part of the OpenJML plugin project.
 * Copyright 2004-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.Strings;

// FIXME - adding/deleting solvers
// FIXME - internationalize

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
    	IPreferenceStore istore = Activator.getDefault().getPreferenceStore();
        setPreferenceStore(istore);
        setDescription("File system paths to executables for individual provers");
        
//        String[] prefs = ((ScopedPreferenceStore)Activator.getDefault().getPreferenceStore()).preferenceNames();
//        List<String> solverList = new ArrayList<String>(10);
//        for (String pref: prefs) {
//        	if (pref.startsWith(execKey)) {
//        		solverList.add(pref.substring(execKey.length()));
//        	}
//        }
//        solvers = solverList.toArray(new String[solverList.size()]);
//        Arrays.sort(solvers);
        solvers = new String[]{ "simplify", "boogie", "cvc3", "cvc4", "yices", "z3" };
    }
    
    final static public String execKey = Strings.proverPropertyPrefix;

	protected String[] solvers;
	
    @Override
    protected void createFieldEditors() {
    	
    	String[][] choices = new String[solvers.length][];
    	int i = 0;
    	for (String solver: solvers) {
    		// The two strings are the label and the value
    		choices[i++] = new String[]{ solver, solver};
    	}
    	
    	addField(new ComboFieldEditor(Strings.defaultProverProperty,
    			"default: ",
    			choices,
    			getFieldEditorParent()));
    	
    	for (String solver: solvers) {
    	
	        addField(new FileFieldEditor(execKey + solver, solver + ": ",
	                getFieldEditorParent()));
    	}

    }
    

}
