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
import org.eclipse.jface.preference.ComboFieldEditor;
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
import org.jmlspecs.openjml.eclipse.widgets.ButtonFieldEditor;
import org.jmlspecs.openjml.eclipse.widgets.EnumDialog;

// FIXME - adding/deleting solvers

/**
 * This class creates a Preferences page in Eclipse
 */
public class SolversPage extends FieldEditorPreferencePage implements
IWorkbenchPreferencePage {

    final static public String execKeyPrefix = Strings.proverPropertyPrefix;
    final static public String execLocKeyPrefix = "openjml.exec.loc.";

	protected String[] solvers;
	
	public SolversPage() {
		super(FLAT);
	}
	
	/** A fake preference store key for the add button. */
	final static public String editKey = Options.prefix + "edit"; //$NON-NLS-1$

    public void init(IWorkbench workbench) {
    	IPreferenceStore istore = Activator.getDefault().getPreferenceStore();
        setPreferenceStore(istore);
        setDescription(Messages.OpenJMLUI_SolversPage_Title);
        
        String ss = getValue();
        //if (ss == null || ss.isEmpty()) {
    		setValue("z3_4_3,cvc4,simplify,yices2"); // FIXME - temporary default
    		ss = getValue();
        //}
        solvers = ss.split(Utils.comma);
        for (int i = 0; i < solvers.length; i++) solvers[i] = solvers[i].trim();
    }
    
    public void setValue(String out) {
    	Options.setValue(Options.solversKey,out);    }
    
    public String getValue() {
		return Options.value(Options.solversKey);
    }
    
    @Override
    protected void createFieldEditors() {

    	MouseListener listener = new MouseAdapter() {
    		@Override
			public void mouseUp(MouseEvent e) {
    			SolversEditorDialog d = new SolversEditorDialog(null,
    					Messages.OpenJMLUI_SolversListEditor_Title);
    			d.create();
    			if (d.open() == Status.OK) {
    				// reset the field editors
    				// FIXME;
    			}
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
				Messages.OpenJMLUI_SolversPage_EditButton, // Messages.OpenJMLUI_PreferencesPage_UpdateFromPropertiesFiles,
				listener,
				getFieldEditorParent())
		);
		
        final String[][] locchoices = new String[][]{{"internal","internal"},{"external","external"}};

    	for (String solver: solvers) {
    		addField(new RadioGroupFieldEditor(execLocKeyPrefix + solver,
        			solver,
        			2, // number of columns
        				locchoices,
        				getFieldEditorParent()));
	        addField(new FileFieldEditor(execKeyPrefix + solver, solver + ": ", //$NON-NLS-1$
	                getFieldEditorParent()));
    	}
    }
    
    class SolversEditorDialog extends Dialog { 
    	
    	/** Window title */
    	protected String title;
    	/** The current shell */
    	protected Shell shell;
    	/** Reference to the internal control for editing the set of files to RAC */
    	protected SolversListEditor solversListEditor;
    	
    	/** Constructor for the dialog
    	 * @param parentShell parent shell for the dialog
    	 * @param title text on the title bar
    	 * @param jproject Java project whose paths are to be edited
    	 */
    	public SolversEditorDialog(Shell parentShell, String title) {
    		super(parentShell);

    		this.title = title;
    	}

    	@Override
    	protected void configureShell(Shell newShell) {
    		super.configureShell(newShell);
    		newShell.setText(title);
    		setShellStyle(SWT.CLOSE | SWT.BORDER | SWT.TITLE);
    		setBlockOnOpen(true);
    		shell = newShell;
    	}

    	@Override
    	public Control createDialogArea(Composite parent) {
    		
    		solversListEditor = new SolversListEditor(shell,parent,
    				getValue().split(Utils.comma),null);
    		
    		return null;
    	}
    	
    	String concat(String[] items) {
    		StringBuilder sb = new StringBuilder();
    		for (String s: items) {
    			sb.append(s.trim());
    			sb.append(Utils.comma);
    		}
    		sb.setLength(sb.length()-1);
    		return sb.toString();
    	}
    	
    	@Override
    	public void okPressed() {
    		try {
    			setValue(concat(solversListEditor.list.getItems()));
    			if (Options.uiverboseness) {
    				Log.log("Saved solver list: " + getValue()); //$NON-NLS-1$
    			}
    		} finally {
    			super.okPressed();
    		}
    	}

    }

}



enum Solvers {
	z3_4_3,
	cvc4,
	simplify,
	yices2,
}

// TODO: Unify this with the PathEditor ListEditor and perhaps with the ListFieldEditor

class SolversListEditor {
	
	/**
	 * The list widget; <code>null</code> if none
	 * (before creation or after disposal).
	 */
	protected List list;

	/** The list of items. This must be kept in synch with the Strings in
	 * 'list'.
	 */
	protected String[] items;
	
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
	protected Composite parent;

	/** Constructs a widget to edit the path corresponding to the given key and for
	 * the given project.
	 */
	// The GridLayout code is copied from FieldEditor
	public SolversListEditor(Shell shell, Composite parent, String[] items, String labelText) {

		this.shell = shell;
		this.parent = parent;
		this.labelText = labelText;
		this.items = items;
		
		GridLayout layout = new GridLayout(2,false);
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		layout.horizontalSpacing = 8; //HORIZONTAL_GAP;
		parent.setLayout(layout);
		doFillIntoGrid(parent, layout.numColumns); // uses fileDialog
		
	}
	
	/** Initializes the widget. */
	protected void init() {
		list.setItems(items);
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
		int index = list.getSelectionIndex();
		EnumDialog<Solvers> d = 
				new EnumDialog<Solvers>(
						shell,
						Solvers.values(),
						null);
		shell.setText("Solver to add");
		d.create();
		if (d.open() == Dialog.OK) {
			String s = d.selection().toString();
			if (index >= 0) {
				list.add(s, index + 1);
			} else {
				list.add(s, 0);
			}
			selectionChanged();
		}

	}


	protected void removePressed() {
		int index = list.getSelectionIndex();
		if (index >= 0) {
			list.remove(index);
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

