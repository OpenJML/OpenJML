/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2004-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Arrays;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.eclipse.JobControl.JobStrategy;
import org.jmlspecs.openjml.eclipse.JobControl.JobControlDialog.BButton;
import org.jmlspecs.openjml.eclipse.widgets.ButtonFieldEditor;
import org.jmlspecs.openjml.eclipse.widgets.EnumDialog;
import org.jmlspecs.openjml.eclipse.widgets.LabelFieldEditor;

// FIXME - adding/deleting solvers

/**
 * This class creates a Preferences page in Eclipse
 */
public class JobControlPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

	
	public JobControlPage() {
		super(FLAT);
	}
	

    public void init(IWorkbench workbench) {
    	IPreferenceStore istore = Activator.getDefault().getPreferenceStore();
        setPreferenceStore(istore);
        setDescription(Messages.OpenJMLUI_JobControlPage_Title);
        
    }
    
    public void setValue(String out) {
    	Options.setValue(Options.solversKey,out);   
    }
    
    public String getValue() {
		return Options.value(Options.solversKey);
    }
    
    @Override
    protected void createFieldEditors() {

        addField(new BooleanFieldEditor(Options.showJobControlDialogKey, "Show the job control dialog when an ESC job is launched",
                                getFieldEditorParent()));
        
        addField(new LabelFieldEditor("","",SWT.NONE,getFieldEditorParent()));

//        int procs = Runtime.getRuntime().availableProcessors();
//        addField(new LabelFieldEditor("zzz.JC","This computer has " + procs + " available processors", SWT.NONE, getFieldEditorParent()));

        addField(new ComboFieldEditor(Options.jobQueuesKey,"How many job queues should be used? ",
        		new String[][]{ 
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
        
        String[][] choices = new String[JobControl.strategies.length][2];
        for (int i = 0; i<JobControl.strategies.length; i++) {
            choices[i][0] = JobControl.strategies[i].description();
            choices[i][1] = JobControl.strategies[i].getClass().getName();
        }
        
    	addField(new RadioGroupFieldEditor(Options.jobStrategyKey,
    			"What job scheduling policy should be used? ",
    			1, // number of columns
    				choices,
    				getFieldEditorParent()));


    }
    
    /** Overridden to add the field to the fieldMap */
    @Override
    public void addField(FieldEditor field) {
    	super.addField(field);
    	PreferencesPage.fieldMap.put(field.getPreferenceName(), field);
    }
    

}
