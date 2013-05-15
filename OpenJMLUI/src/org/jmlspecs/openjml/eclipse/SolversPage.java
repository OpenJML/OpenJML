/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2004-2013 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.Map;
import java.util.Properties;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
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
import org.jmlspecs.openjml.eclipse.widgets.ButtonFieldEditor;

// FIXME - adding/deleting solvers

/**
 * This class creates a Preferences page in Eclipse
 */
public class SolversPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

	public SolversPage() {
		super(FLAT);
	}
	
	/** A fake preference store key for the add button. */
	final static public String editKey = Options.prefix + "edit"; //$NON-NLS-1$

    public void init(IWorkbench workbench) {
    	IPreferenceStore istore = Activator.getDefault().getPreferenceStore();
        setPreferenceStore(istore);
        setDescription(Messages.OpenJMLUI_SolversPage_Title);
        
        String ss = Options.value(Options.solversKey);
        if (ss == null || ss.isEmpty()) {
    		setValue("simplify,yices2,z3_4_3");
    		ss = Options.value(Options.solversKey);
        }
        solvers = ss.split(Utils.comma);
        for (int i = 0; i < solvers.length; i++) solvers[i] = solvers[i].trim();
    }
    
    public void setValue(String out) {
		Activator.getDefault().getPreferenceStore().setValue(Options.solversKey,out);
    }
    
    public String getValue() {
		return Activator.getDefault().getPreferenceStore().getString(Options.solversKey);
    }
    
    final static public String execKey = Strings.proverPropertyPrefix;

	protected String[] solvers;
	
    @Override
    protected void createFieldEditors() {

    	MouseListener listener = new MouseAdapter() {
    		@Override
			public void mouseUp(MouseEvent e) {
    			Dialog d = new EditDialog(null,"Edit the list of solvers");
    			d.create();
    			d.open();
    			d.close();
    			return; 
			}
		};
		

    	String[][] choices = new String[solvers.length][];
    	int i = 0;
    	for (String solver: solvers) {
    		// The two strings are the label and the value
    		choices[i++] = new String[]{ solver, solver};
    	}
    	
    	addField(new ComboFieldEditor(Strings.defaultProverProperty,
    			Messages.OpenJMLUI_SolversPage_DefaultLabel,
    			choices,
    			getFieldEditorParent()));
    	
		addField(new ButtonFieldEditor(editKey,"", //$NON-NLS-1$
				"Edit list of solvers", // Messages.OpenJMLUI_PreferencesPage_UpdateFromPropertiesFiles,
				listener,
				getFieldEditorParent())
		);

    	for (String solver: solvers) {
	        addField(new FileFieldEditor(execKey + solver, solver + ": ", //$NON-NLS-1$
	                getFieldEditorParent()));
    	}
    }
}


/** Implements a dialog that allows editing of the source and specs path of a Java project */
class EditDialog extends Dialog { 
	
	/** Window title */
	protected String title;
	/** The current shell */
	protected Shell shell;
	
	/** The list object */
	protected SolverListEditor listEditor;
	
	/** Constructor for the dialog
	 * @param parentShell parent shell for the dialog
	 * @param title text on the title bar
	 * @param jproject Java project whose paths are to be edited
	 */
	public EditDialog(Shell parentShell, String title) {
		super(parentShell);

		this.title = title;
	}

	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		newShell.setText(title);
		setShellStyle(SWT.CLOSE | SWT.MODELESS | SWT.BORDER | SWT.TITLE);
		setBlockOnOpen(false);
		shell = newShell;
	}

	@Override
	public Control createDialogArea(Composite parent) {
		
		String label = Messages.OpenJMLUI_SolversPage_DialogTitle;
		listEditor = new SolverListEditor(shell,parent,Env.racKey,label);
		
		return null;
	}
	
	@Override
	public void okPressed() {
		StringBuilder sb = new StringBuilder();
		for (String i: listEditor.items) {
			sb.append(i.trim());
			sb.append(Utils.comma);
		}
		if (sb.length() > 0) sb.setLength(sb.length()-1); // remove last comma

		try {
			//jproject.getProject().setPersistentProperty(PathItem.racKey, PathItem.concat(racListEditor.pathItems));
			if (Options.uiverboseness) {
//				Log.log("Saved solvers " + solverList); //$NON-NLS-1$
			}
//		} catch (CoreException e) {
//			Activator.getDefault().utils.showExceptionInUI(shell,Messages.OpenJMLUI_PathsEditor_PersistentPropertyError,e);
		} finally {
			super.okPressed();
		}
	}

}

// TODO: Unify this with the PathEditor ListEditor and perhaps with the ListFieldEditor

class SolverListEditor {
	
	/**
	 * The list widget; <code>null</code> if none
	 * (before creation or after disposal).
	 */
	protected List list;

	/** The list of items. This must be kept in synch with the Strings in
	 * 'list'.
	 */
	protected java.util.List<String> items = new java.util.ArrayList<String>();
	
	/** The key for the persistent copy of the path */
	protected QualifiedName key;
	
	/**
	 * The button box containing the buttons;
	 * <code>null</code> if none (before creation or after disposal).
	 */
	protected Composite buttonBox;

	protected Button addButton;
	protected Button removeButton;
	protected Button upButton;
	protected Button downButton;
	protected Label label;
	protected String labelText;

	/**
	 * The selection listener.
	 */
	protected SelectionListener selectionListener;

	protected Shell shell;

	/** Constructs a widget to edit the path corresponding to the given key and for
	 * the given project.
	 */
	// The GridLayout code is copied from FieldEditor
	public SolverListEditor(Shell shell, Composite parent, QualifiedName key, String labelText) {

		this.shell = shell;
		this.key = key;
		this.labelText = labelText;
		
		GridLayout layout = new GridLayout(2,false);
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		layout.horizontalSpacing = 8; //HORIZONTAL_GAP;
		parent.setLayout(layout);
		doFillIntoGrid(parent, layout.numColumns); // uses fileDialog
		
	}
	
	/** Initializes the widget from the persistent property. */
	protected void init() {
		items.clear();
		String prop = Options.value(Options.solversKey);
		prop = "simplify,yices2,z3_4_3";
		String[] strings = prop.split(",");
		for (String s : strings) {
			s = s.trim();
			if (s.isEmpty()) continue;
			items.add(s);
			list.add(s);
		}
	}

	/** Manages the layout of controls */
	// The GridLayout code is copied from FieldEditor
	protected void doFillIntoGrid(Composite parent, int numColumns) {
		Control control = getLabelControl(parent);
		GridData gd = new GridData();
		gd.horizontalSpan = numColumns;
		control.setLayoutData(gd);

		list = getListControl(parent);
		gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.verticalAlignment = GridData.FILL;
		gd.horizontalSpan = numColumns - 1;
		gd.grabExcessHorizontalSpace = true;
		gd.minimumWidth = 300;
		list.setLayoutData(gd);

		buttonBox = getButtonBoxControl(parent);
		gd = new GridData();
		gd.verticalAlignment = GridData.BEGINNING;
		buttonBox.setLayoutData(gd);

	}
	
	protected void addPressed() {
		String item = "zzz";
		int index = list.getSelectionIndex();
		if (index >= 0) {
			list.add(item, index + 1);
			items.add(index + 1, item);
		} else {
			list.add(item, 0);
			items.add(0, item);
		}
	}


	protected void removePressed() {
		int index = list.getSelectionIndex();
		if (index >= 0) {
			list.remove(index);
			items.remove(index);
			selectionChanged();
		}
	}

	protected void upPressed() {
		swap(true);
	}


	protected void downPressed() {
		swap(false);
	}
	
	/**
	 * Moves the currently selected item up or down.
	 *
	 * @param up <code>true</code> if the item should move up,
	 *  and <code>false</code> if it should move down
	 */
	protected void swap(boolean up) {
		int index = list.getSelectionIndex();
		int target = up ? index - 1 : index + 1;

		if (index >= 0) {
			String[] selection = list.getSelection();
			if (selection.length == 0) return;
			list.remove(index);
			list.add(selection[0], target);
			list.setSelection(target);
			String p = items.remove(index);
			items.add(target,p);
		}
		selectionChanged();
	}

	/**
	 * Creates the buttons in the given button box.
	 *
	 * @param box the box for the buttons
	 */
	private void createButtons(Composite box) {
		addButton = createPushButton(box, Messages.OpenJMLUI_Editor_Add);
		removeButton = createPushButton(box, Messages.OpenJMLUI_Editor_Remove);
		upButton = createPushButton(box, Messages.OpenJMLUI_Editor_Up);
		downButton = createPushButton(box, Messages.OpenJMLUI_Editor_Down);
	}

	/**
	 * Helper method to create a push button.
	 * 
	 * @param parent the parent control
	 * @param key the resource name used to supply the button's label text
	 * @return Button
	 */
	private Button createPushButton(Composite parent, String label) {
		Button button = new Button(parent, SWT.PUSH);
		button.setText(label);
		button.setFont(parent.getFont());
		GridData data = new GridData(GridData.FILL_HORIZONTAL);
		int widthHint = convertHorizontalDLUsToPixels(button,
				IDialogConstants.BUTTON_WIDTH);
		data.widthHint = Math.max(widthHint, button.computeSize(SWT.DEFAULT,
				SWT.DEFAULT, true).x);
		button.setLayoutData(data);
		button.addSelectionListener(getSelectionListener());
		return button;
	}

	protected int convertHorizontalDLUsToPixels(Control control, int dlus) {
		GC gc = new GC(control);
		gc.setFont(control.getFont());
		int averageWidth = gc.getFontMetrics().getAverageCharWidth();
		gc.dispose();
		double horizontalDialogUnitSize = averageWidth * 0.25;
		return (int) Math.round(dlus * horizontalDialogUnitSize);
	}

	private SelectionListener getSelectionListener() {
		if (selectionListener == null) {
			createSelectionListener();
		}
		return selectionListener;
	}


	/**
	 * Creates a selection listener.
	 */
	// Note - we could add a specific listener to each button, which would be
	// much more object-oriented, but also means many more objects created.
	// This code copies how the ListEditor did it.
	public void createSelectionListener() {
		selectionListener = new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) {
				Widget widget = event.widget;
				if (widget == addButton) {
					addPressed();
				} else if (widget == removeButton) {
					removePressed();
				} else if (widget == upButton) {
					upPressed();
				} else if (widget == downButton) {
					downPressed();
				} else if (widget == list) {
					selectionChanged();
				}
			}
		};
	}

	/**
	 * Returns this field editor's label component.
	 * <p>
	 * The label is created if it does not already exist
	 * </p>
	 *
	 * @param parent the parent
	 * @return the label control
	 */
	public Label getLabelControl(Composite parent) {
		if (label == null) {
			label = new Label(parent, SWT.LEFT);
			label.setFont(parent.getFont());
			String text = getLabelText();
			if (text != null) {
				label.setText(text);
			}
			label.addDisposeListener(new DisposeListener() {
				public void widgetDisposed(DisposeEvent event) {
					label = null;
				}
			});
		} else {
			checkParent(label, parent);
		}
		return label;
	}

	/**
	 * Returns this field editor's label text.
	 *
	 * @return the label text
	 */
	public String getLabelText() {
		return labelText;
	}


	protected void selectionChanged() {
		int index = list.getSelectionIndex();
		int size = list.getItemCount();
		removeButton.setEnabled(index >= 0);
		upButton.setEnabled(size > 1 && index > 0);
		downButton.setEnabled(size > 1 && index >= 0 && index < size - 1);
	}

	public void setFocus() {
		if (list != null) {
			list.setFocus();
		}
	}

	public void setEnabled(boolean enabled, Composite parent) {
		getListControl(parent).setEnabled(enabled);
		addButton.setEnabled(enabled);
		removeButton.setEnabled(enabled);
		upButton.setEnabled(enabled);
		downButton.setEnabled(enabled);
		selectionChanged();
	}


	public List getListControl(Composite parent) {
		if (list == null) {
			list = new List(parent, SWT.BORDER | SWT.SINGLE | SWT.V_SCROLL
					| SWT.H_SCROLL);
			list.setFont(parent.getFont());
			list.addSelectionListener(getSelectionListener());
			list.addDisposeListener(new DisposeListener() {
				public void widgetDisposed(DisposeEvent event) {
					list = null;
				}
			});
		} else {
			checkParent(list, parent);
		}
		init(); // Sets list
		return list;
	}

	public Composite getButtonBoxControl(Composite parent) {
		if (buttonBox == null) {
			buttonBox = new Composite(parent, SWT.NULL);
			GridLayout layout = new GridLayout();
			layout.marginWidth = 0;
			buttonBox.setLayout(layout);
			createButtons(buttonBox);
			buttonBox.addDisposeListener(new DisposeListener() {
				public void widgetDisposed(DisposeEvent event) {
					addButton = null;
					removeButton = null;
					upButton = null;
					downButton = null;
					buttonBox = null;
				}
			});

		} else {
			checkParent(buttonBox, parent);
		}

		selectionChanged();
		return buttonBox;
	}
	
	protected void checkParent(Control control, Composite parent) {
		Assert.isTrue(control.getParent() == parent, "Different parents");//$NON-NLS-1$
	}

}

