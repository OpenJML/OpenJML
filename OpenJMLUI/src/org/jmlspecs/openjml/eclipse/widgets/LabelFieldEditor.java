/*
 * This file is part of the OpenJML project.
 * Copyright (c) 2013-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse.widgets;


import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;

/**
 * A fake field editor that is just a label to be used as a separator; the st.
 */
public class LabelFieldEditor extends FieldEditor {

	/**
	 * The Label widget.
	 */
	private Label fLabel;
	
	/** The style of the field - typically either SWT.NONE or SWT.SEPARATOR|SWT.HORIZONTAL */
	private int style;
	
	/**
	 * Create the combo box field editor.
	 * 
     * @param name the key of the preference this field editor works on
     * @param labelText the label text of the field editor
	 * @param style use SWT.SEPARATOR|SWT.HORIZONTAL to get a labeled horizontal rule, use SWT.NONE for no rule
	 * @param parent the parent composite
	 */
	public LabelFieldEditor(String name, String labelText, int style, Composite parent) {
		init(name, labelText);
		this.style = style;
		createControl(parent);		
	}


	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#adjustForNumColumns(int)
	 */
	protected void adjustForNumColumns(int numColumns) {
		if (numColumns > 1) {
			Control control = getLabelControl();
			int left = numColumns;
			if (control != null) {
				((GridData)control.getLayoutData()).horizontalSpan = 1;
				left = left - 1;
			}
			((GridData)fLabel.getLayoutData()).horizontalSpan = left;
		} else {
			Control control = getLabelControl();
			if (control != null) {
				((GridData)control.getLayoutData()).horizontalSpan = 1;
			}
			((GridData)fLabel.getLayoutData()).horizontalSpan = 1;			
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doFillIntoGrid(org.eclipse.swt.widgets.Composite, int)
	 */
	protected void doFillIntoGrid(Composite parent, int numColumns) {
		int comboC = 1;
		if (numColumns > 1) {
			comboC = numColumns - 1;
		}
		Control control = getLabelControl(parent);
		GridData gd = new GridData();
		gd.horizontalSpan = 1;
		control.setLayoutData(gd);
		control = getLabel(parent);
		gd = new GridData();
		gd.horizontalSpan = comboC;
		gd.horizontalAlignment = GridData.FILL;
		control.setLayoutData(gd);
		control.setFont(parent.getFont());
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doLoad()
	 */
	protected void doLoad() {
		// no state to load
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doLoadDefault()
	 */
	protected void doLoadDefault() {
		// no state to load
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doStore()
	 */
	protected void doStore() {
		// no state to store
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#getNumberOfControls()
	 */
	public int getNumberOfControls() {
		return 2;
	}

	/*
	 * Lazily create and return the Combo control.
	 */
	private Label getLabel(Composite parent) {
		if (fLabel == null) {
			fLabel = new Label(parent,style);
			// FIXME - want the label itself to be bold
			// FIXME - would rather use the light box around a group of controls as in other Preference pages
		}
		return fLabel;
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.FieldEditor#setEnabled(boolean,
	 *      org.eclipse.swt.widgets.Composite)
	 */
	public void setEnabled(boolean enabled, Composite parent) {
		super.setEnabled(enabled, parent);
		getLabel(parent).setEnabled(enabled);
	}
}
