/*
 * This file is part of the OpenJML project.
 * Copyright (c) 2006-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Widget;

public class PathsEditor extends Dialog { //PopupDialog {
	protected String title;
	protected IJavaProject jproject;
	protected Shell shell;
	protected ListEditor sourceListEditor;
	protected ListEditor specsListEditor;
	
	public PathsEditor(Shell parentShell, String title, IJavaProject jproject) {
		super(parentShell);

		this.title = title;
		this.jproject = jproject;
	}

	@Override
	protected void configureShell(Shell newShell) {
		super.configureShell(newShell);
		newShell.setText(title);
		shell = newShell;
	}

	@Override
	public Control createDialogArea(Composite parent) {
		//    		Text t = new Text(composite,SWT.READ_ONLY|SWT.READ_ONLY);
		//    		t.setText(content);
		//    		t.setSize(500,500);
		//    		return getListControl(composite);
		
		CTabFolder tabs = new CTabFolder(parent,SWT.NONE);
		CTabItem classtab = new CTabItem(tabs,SWT.NONE);
		CTabItem sourcetab = new CTabItem(tabs,SWT.NONE);
		CTabItem specstab = new CTabItem(tabs,SWT.NONE);
		Composite classcomp = new Composite(tabs,SWT.NONE);
		Composite sourcecomp = new Composite(tabs,SWT.NONE);
		Composite specscomp = new Composite(tabs,SWT.NONE);
		tabs.setSelection(specstab);
		specstab.setText("Specifications Path");
		sourcetab.setText("Source Path");
		classtab.setText("Class Path");
		specstab.setControl(specscomp);
		sourcetab.setControl(sourcecomp);
		classtab.setControl(classcomp);
		
		Utils utils = Activator.getDefault().utils;
		
//		Label label = new Label(classcomp,SWT.NONE);
		StringBuilder text = new StringBuilder();
		text.append("Folders and jar files in which to find class files:");
		text.append(Env.eol);
		text.append("(Edit the classpath using the Project Properties - Java Build Path dialog)");
		text.append(Env.eol);
		text.append(Env.eol);
		for (String s: utils.getClasspath(jproject)) {
			text.append(s);
			text.append(Env.eol);
		}
		Text t = new Text(classcomp,SWT.READ_ONLY|SWT.MULTI);
		t.setText(text.toString());
		t.setSize(500,200);
		
		Label label2 = new Label(sourcecomp,SWT.NONE);
		label2.setText("Folders and jar files in which to find .java source files");
		sourceListEditor = new ListEditor(shell,sourcecomp,jproject,PathItem.sourceKey);
		
		Label label3 = new Label(specscomp,SWT.NONE);
		label3.setText("Folders and jar files in which to find specifications files (.jml and .java)");
		specsListEditor = new ListEditor(shell,specscomp,jproject,PathItem.specsKey);
		return tabs;
	}
	
	
	protected String concat(java.util.List<PathItem> items) {
		StringBuilder sb = new StringBuilder();
		for (PathItem i: items) {
			sb.append(i.toEncodedString());
			sb.append(PathItem.split);
		}
		if (!items.isEmpty()) sb.setLength(sb.length()-PathItem.split.length());
		return sb.toString();
	}

	@Override
	public void okPressed() {
		try {
			jproject.getProject().setPersistentProperty(PathItem.sourceKey, concat(sourceListEditor.pathItems));
			jproject.getProject().setPersistentProperty(PathItem.specsKey, concat(specsListEditor.pathItems));
			Log.log("Saved " + jproject.getProject().getPersistentProperty(PathItem.sourceKey));
			Log.log("Saved " + jproject.getProject().getPersistentProperty(PathItem.specsKey));
			
		} catch (CoreException e) {
			// FIXME - report ERROR
		} finally {
			super.okPressed();
		}
	}

}

class ListEditor {
	
	
	/**
	 * The list widget; <code>null</code> if none
	 * (before creation or after disposal).
	 */
	protected List list;

	protected java.util.List<PathItem> pathItems = new java.util.ArrayList<PathItem>();
	
	protected IJavaProject jproject;
	
	protected QualifiedName key;
	
	public ListEditor(Shell shell, Composite parent, IJavaProject jproject, QualifiedName key) {

		this.jproject = jproject;
		this.key = key;
		
		GridLayout layout = new GridLayout(2,false);
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		layout.horizontalSpacing = 8; //HORIZONTAL_GAP;
		parent.setLayout(layout);
		doFillIntoGrid(parent, layout.numColumns);
		
		fileDialog = new FileDialog(shell);
		fileDialog.setFilterExtensions(new String[]{"*.jar"});
		dirDialog = new DirectoryDialog(shell);
		dirDialog.setMessage("Select a folder to add to the path");
		String path = jproject.getProject().getLocation().toOSString();
		dirDialog.setFilterPath(path);

	}
	
	protected void init(QualifiedName key) {
//		try{
//		jproject.getProject().setPersistentProperty(PathItem.sourceKey, null);
//		jproject.getProject().setPersistentProperty(PathItem.specsKey, null);
//		} catch (CoreException e) {}
		pathItems.clear();
		String prop = PathItem.getEncodedPath(jproject,key);
		String[] paths = prop.split(PathItem.split);
		PathItem p;
		for (String s : paths) {
			p = PathItem.parse(s);
			if (p != null) {
				pathItems.add(p);
				list.add(p.display());
			}
		}
	}

	protected Control doFillIntoGrid(Composite parent, int numColumns) {
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

		return control;
	}

	/**
	 * The button box containing the buttons;
	 * <code>null</code> if none (before creation or after disposal).
	 */
	protected Composite buttonBox;

	protected Button addJarButton;
	protected Button addDirButton;
	protected Button removeButton;
	protected Button upButton;
	protected Button downButton;

	/**
	 * The selection listener.
	 */
	protected SelectionListener selectionListener;

	protected FileDialog fileDialog;
	protected DirectoryDialog dirDialog;

	/**
	 * Notifies that the Add button has been pressed.
	 */
	protected void addJarPressed() {
		//setPresentsDefaultValue(false);
		String input = fileDialog.open();
		if (input != null) {
			PathItem item = PathItem.create(input);
			String rep = item.display();
			int index = list.getSelectionIndex();
			if (index >= 0) {
				list.add(rep, index + 1);
				pathItems.add(index + 1, item);
			} else {
				list.add(rep, 0);
				pathItems.add(0, item);
			}
			selectionChanged();
		}
	}

	protected void addDirPressed() {
		//setPresentsDefaultValue(false);
		String input = dirDialog.open();
		if (input != null) {
			PathItem item = PathItem.create(input);
			String rep = item.display();
			int index = list.getSelectionIndex();
			if (index >= 0) {
				list.add(rep, index + 1);
				pathItems.add(index + 1, item);
			} else {
				list.add(rep, 0);
				pathItems.add(0, item);
			}
			selectionChanged();
		}
	}

	protected void removePressed() {
		int index = list.getSelectionIndex();
		if (index >= 0) {
			list.remove(index);
			pathItems.remove(index);
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
			Assert.isTrue(selection.length == 1);
			list.remove(index);
			list.add(selection[0], target);
			list.setSelection(target);
			PathItem p = pathItems.remove(index);
			pathItems.add(target,p);
		}
		selectionChanged();
	}

//	/* (non-Javadoc)
//	 * Method declared on FieldEditor.
//	 */
//	protected void adjustForNumColumns(int numColumns) {
//		Control control = getLabelControl();
//		((GridData) control.getLayoutData()).horizontalSpan = numColumns;
//		((GridData) list.getLayoutData()).horizontalSpan = numColumns - 1;
//	}

	/**
	 * Creates the Add, Remove, Up, and Down button in the given button box.
	 *
	 * @param box the box for the buttons
	 */
	private void createButtons(Composite box) {
		// FIXME - use properties
		addJarButton = createPushButton(box, "New Jar ...");//$NON-NLS-1$
		addDirButton = createPushButton(box, "New Folder ...");//$NON-NLS-1$
		removeButton = createPushButton(box, "Remove");//$NON-NLS-1$
		upButton = createPushButton(box, "Up");//$NON-NLS-1$
		downButton = createPushButton(box, "Down");//$NON-NLS-1$
	}

	protected int convertHorizontalDLUsToPixels(Control control, int dlus) {
		GC gc = new GC(control);
		gc.setFont(control.getFont());
		int averageWidth = gc.getFontMetrics().getAverageCharWidth();
		gc.dispose();

		double horizontalDialogUnitSize = averageWidth * 0.25;

		return (int) Math.round(dlus * horizontalDialogUnitSize);
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
		button.setText(label); // JFaceResources.getString(key));
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

	private SelectionListener getSelectionListener() {
		if (selectionListener == null) {
			createSelectionListener();
		}
		return selectionListener;
	}


	/**
	 * Creates a selection listener.
	 */
	public void createSelectionListener() {
		selectionListener = new SelectionAdapter() {
			public void widgetSelected(SelectionEvent event) {
				Widget widget = event.widget;
				if (widget == addJarButton) {
					addJarPressed();
				} else if (widget == addDirButton) {
					addDirPressed();
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
	 * Returns the label control. 
	 *
	 * @return the label control, or <code>null</code>
	 *  if no label control has been created
	 */
	protected Label getLabelControl() {
		return label;
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

	Label label;
	String labelText;

	/**
	 * Returns this field editor's label text.
	 *
	 * @return the label text
	 */
	public String getLabelText() {
		return labelText;
	}

//	/* (non-Javadoc)
//	 * Method declared on FieldEditor.
//	 */
//	protected void doLoad() {
//		//            if (list != null) {
//		//                String s = getPreferenceStore().getString(getPreferenceName());
//		//                String[] array = parseString(s);
//		//                for (int i = 0; i < array.length; i++) {
//		//                    list.add(array[i]);
//		//                }
//		//            }
//	}
//
//	/* (non-Javadoc)
//	 * Method declared on FieldEditor.
//	 */
//	protected void doLoadDefault() {
//		//            if (list != null) {
//		//                list.removeAll();
//		//                String s = getPreferenceStore().getDefaultString(
//		//                        getPreferenceName());
//		//                String[] array = parseString(s);
//		//                for (int i = 0; i < array.length; i++) {
//		//                    list.add(array[i]);
//		//                }
//		//            }
//	}
//
//	/* (non-Javadoc)
//	 * Method declared on FieldEditor.
//	 */
//	protected void doStore() {
//		//            String s = createList(list.getItems());
//		//            if (s != null) {
//		//    			getPreferenceStore().setValue(getPreferenceName(), s);
//		//    		}
//	}


	protected void selectionChanged() {

		int index = list.getSelectionIndex();
		int size = list.getItemCount();

		removeButton.setEnabled(index >= 0);
		upButton.setEnabled(size > 1 && index > 0);
		downButton.setEnabled(size > 1 && index >= 0 && index < size - 1);
	}

	/* (non-Javadoc)
	 * Method declared on FieldEditor.
	 */
	public void setFocus() {
		if (list != null) {
			list.setFocus();
		}
	}
	/*
	 * @see FieldEditor.setEnabled(boolean,Composite).
	 */
	public void setEnabled(boolean enabled, Composite parent) {
		//            super.setEnabled(enabled, parent);
		getListControl(parent).setEnabled(enabled);
		addJarButton.setEnabled(enabled);
		addDirButton.setEnabled(enabled);
		removeButton.setEnabled(enabled);
		upButton.setEnabled(enabled);
		downButton.setEnabled(enabled);
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
		init(key); // Sets list
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
					addJarButton = null;
					addDirButton = null;
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
