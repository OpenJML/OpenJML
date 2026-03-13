/*
 * This file is part of the OpenJML plugin project.
 * Copyright (c) 2012-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.EnumSet;

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
import org.jmlspecs.openjml.eclipse.widgets.EnumDialog;

/** Implements a dialog that allows editing of the source and specs path of a Java project */
public class PathsEditor extends Utils.ModelessDialog { 
	/** Window title */
	protected String title;
	/** Java project whose paths are being edited */
	protected IJavaProject jproject;
	/** The current shell */
	protected Shell shell;
	/** Reference to the internal control for editing the source path */
	protected ListEditor sourceListEditor;
	/** Reference to the internal control for editing the specs path */
	protected ListEditor specsListEditor;
	
	/** Constructor for the dialog
	 * @param parentShell parent shell for the dialog
	 * @param title text on the title bar
	 * @param jproject Java project whose paths are to be edited
	 */
	public PathsEditor(Shell parentShell, String title, IJavaProject jproject) {
		super(parentShell);

		this.title = title;
		this.jproject = jproject;
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
		
		CTabFolder tabs = new CTabFolder(parent,SWT.NONE);
		CTabItem classtab = new CTabItem(tabs,SWT.NONE);
		CTabItem sourcetab = new CTabItem(tabs,SWT.NONE);
		CTabItem specstab = new CTabItem(tabs,SWT.NONE);
		Composite classcomp = new Composite(tabs,SWT.NONE);
		Composite sourcecomp = new Composite(tabs,SWT.NONE);
		Composite specscomp = new Composite(tabs,SWT.NONE);
		tabs.setSelection(specstab);
		specstab.setText(Messages.OpenJMLUI_Editor_SpecsPath);
		sourcetab.setText(Messages.OpenJMLUI_Editor_SourcePath);
		classtab.setText(Messages.OpenJMLUI_Editor_ClassPath);
		specstab.setControl(specscomp);
		sourcetab.setControl(sourcecomp);
		classtab.setControl(classcomp);
		
		Utils utils = Activator.utils();
		
		StringBuilder text = new StringBuilder();
		text.append(Messages.OpenJMLUI_Editor_ClassPathTitle + Env.eol
			+ Messages.OpenJMLUI_Editor_ClassPathTitle2);
		text.append(Env.eol);
		text.append(Env.eol);
		for (String s: utils.getClasspath(jproject)) {
			text.append(s);
			text.append(Env.eol);
		}
		Text t = new Text(classcomp,SWT.READ_ONLY|SWT.MULTI);
		t.setText(text.toString());
		t.setSize(500,200);
		
		String label = Messages.OpenJMLUI_Editor_SourcePathTitle;
		sourceListEditor = new ListEditor(shell,sourcecomp,jproject,Env.sourceKey,label);
		
		label = Messages.OpenJMLUI_Editor_SpecsPathTitle;
		specsListEditor = new ListEditor(shell,specscomp,jproject,Env.specsKey,label);
		return tabs;
	}
	
	@Override
	public void okPressed() {
		try {
			jproject.getProject().setPersistentProperty(Env.sourceKey, PathItem.concat(sourceListEditor.pathItems));
			jproject.getProject().setPersistentProperty(Env.specsKey, PathItem.concat(specsListEditor.pathItems));
			if (Options.uiverboseness) {
				Log.log("Saved " + jproject.getProject().getPersistentProperty(Env.sourceKey)); //$NON-NLS-1$
				Log.log("Saved " + jproject.getProject().getPersistentProperty(Env.specsKey)); //$NON-NLS-1$
			}
		} catch (CoreException e) {
			Activator.utils().showExceptionInUI(shell,Messages.OpenJMLUI_Editor_PersistentPropertyError,e);
		} finally {
			super.okPressed();
		}
	}

}

/** A SWT control for editing a list of PathItems */
class ListEditor {
	
	/**
	 * The list widget; <code>null</code> if none
	 * (before creation or after disposal).
	 */
	protected List list;

	/** The list of path items. This must be kept in synch with the Strings in
	 * 'list'.
	 */
	protected java.util.List<PathItem> pathItems = new java.util.ArrayList<PathItem>();
	
	/** The project whose path is being edited. */
	protected IJavaProject jproject;
	
	/** The key for the persistent copy of the path */
	protected QualifiedName key;
	
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
	protected Button defaultButton;
	protected Button addSpecialButton;
	protected Label label;
	protected String labelText;


	/**
	 * The selection listener.
	 */
	protected SelectionListener selectionListener;

	/** The cached dialog for selecting jar files */
	protected FileDialog fileDialog;
	
	/** The cached dialog for selecting folders */
	protected DirectoryDialog dirDialog;

	/** Constructs a widget to edit the path corresponding to the given key and for
	 * the given project.
	 */
	// The GridLayout code is copied from FieldEditor
	public ListEditor(Shell shell, Composite parent, IJavaProject jproject, QualifiedName key, String labelText) {

		this.jproject = jproject;
		this.key = key;
		this.labelText = labelText;
		
		fileDialog = new FileDialog(shell);
		fileDialog.setFilterExtensions(new String[]{"*.jar"}); //$NON-NLS-1$
		dirDialog = new DirectoryDialog(shell);
		dirDialog.setMessage(Messages.OpenJMLUI_Editor_DirectoryDialogMessage);
		String path = jproject.getProject().getLocation().toString();
		dirDialog.setFilterPath(path);

		GridLayout layout = new GridLayout(2,false);
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		layout.horizontalSpacing = 8; //HORIZONTAL_GAP;
		parent.setLayout(layout);
		doFillIntoGrid(parent, layout.numColumns); // uses fileDialog
		
	}
	
	/** Initializes the widget from the persistent property. */
	protected void init(QualifiedName key) {
		pathItems.clear();
		String prop = PathItem.getEncodedPath(jproject,key);
		if (Options.uiverboseness) {
			Log.log("Read path property: " + prop); //$NON-NLS-1$
		}

		String[] paths = prop.split(PathItem.split);
		for (String s : paths) {
			s = s.trim();
			if (s.isEmpty()) continue;
			PathItem p = PathItem.parse(s);
			if (p != null) {
				pathItems.add(p);
				list.add(p.display());
			} else {
				Activator.utils().showMessageInUI(fileDialog.getParent(),
			        Messages.OpenJMLUI_Editor_ErrorDialogTitle,
					Messages.OpenJMLUI_Editor_UnparsableError + s);
			}
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
	
	protected void add(PathItem item) {
		String rep = item.display();
		int index = list.getSelectionIndex();
		if (index >= 0) {
			list.add(rep, index + 1);
			pathItems.add(index + 1, item);
		} else {
			list.add(rep, 0);
			pathItems.add(0, item);
		}
	}

	protected void addJarPressed() {
		String input = fileDialog.open();
		if (input != null) {
			PathItem item = PathItem.create(jproject,input);
			add(item);
			selectionChanged();
		}
	}

	protected void addDirPressed() {
		String input = dirDialog.open();
		if (input != null) {
			PathItem item = PathItem.create(jproject,input);
			add(item);
			selectionChanged();
		}
	}

	protected void defaultPressed() {
		list.removeAll();
		pathItems.clear();
		java.util.List<PathItem> defaults = key == Env.specsKey ? PathItem.defaultSpecsPath : PathItem.defaultSourcePath;
		for (PathItem item : defaults) {
			list.add(item.display());
			pathItems.add(item);
		}
		selectionChanged();
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
	
	protected void specialPressed() {
		EnumSet<PathItem.SpecialPath.Kind> disable = EnumSet.noneOf(PathItem.SpecialPath.Kind.class);
		if (key == Env.sourceKey) disable.add(PathItem.SpecialPath.Kind.SOURCEPATH);
		for (PathItem k : pathItems) {
			if (k instanceof PathItem.SpecialPath){
				disable.add(((PathItem.SpecialPath)k).kind);
			}
		}
		EnumDialog<PathItem.SpecialPath.Kind> d = 
				new EnumDialog<PathItem.SpecialPath.Kind>(
						fileDialog.getParent(),
						PathItem.SpecialPath.Kind.values(),
						disable);
		d.create();
		if (d.open() == Dialog.OK) {
			PathItem item = new PathItem.SpecialPath(d.selection());
			add(item);
			selectionChanged();
		}
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

	/**
	 * Creates the buttons in the given button box.
	 *
	 * @param box the box for the buttons
	 */
	private void createButtons(Composite box) {
		addJarButton = createPushButton(box, Messages.OpenJMLUI_Editor_AddJar);
		addDirButton = createPushButton(box, Messages.OpenJMLUI_Editor_AddFolder);
		addSpecialButton = createPushButton(box, Messages.OpenJMLUI_Editor_AddSpecial);
		removeButton = createPushButton(box, Messages.OpenJMLUI_Editor_Remove);
		upButton = createPushButton(box, Messages.OpenJMLUI_Editor_Up);
		downButton = createPushButton(box, Messages.OpenJMLUI_Editor_Down);
		defaultButton = createPushButton(box, Messages.OpenJMLUI_Editor_Default);
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
				} else if (widget == defaultButton) {
					defaultPressed();
				} else if (widget == addSpecialButton) {
					specialPressed();
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
		addJarButton.setEnabled(enabled);
		addDirButton.setEnabled(enabled);
		removeButton.setEnabled(enabled);
		upButton.setEnabled(enabled);
		downButton.setEnabled(enabled);
		defaultButton.setEnabled(enabled);
		addSpecialButton.setEnabled(enabled);
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
					addSpecialButton = null;
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
