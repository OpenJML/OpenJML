/*
 * This file is part of the OpenJML project.
 * Copyright (c) 2012-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse.widgets;


import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

/**
 * A fake field editor that is just a button that can instigate an action when
 * the button is pushed.
 */
public class ButtonFieldEditor extends FieldEditor {

	/**
	 * The Button widget.
	 */
	private Button fButton;
	
	/** The text on the button. */
	private String buttonText;
	
	/** The listener for button presses (typically a mouse up or down event). */
	private MouseListener listener;
	
	/**
	 * Create the combo box field editor.
	 * 
     * @param name the key of the preference this field editor works on
     * @param labelText the label text of the field editor
	 * @param listener the action to take when the button is pressed or released
	 * @param parent the parent composite
	 */
	public ButtonFieldEditor(String name, String labelText, String buttonText, MouseListener listener, Composite parent) {
		init(name, labelText);
		this.buttonText = buttonText;
		this.listener = listener;
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
			((GridData)fButton.getLayoutData()).horizontalSpan = left;
		} else {
			Control control = getLabelControl();
			if (control != null) {
				((GridData)control.getLayoutData()).horizontalSpan = 1;
			}
			((GridData)fButton.getLayoutData()).horizontalSpan = 1;			
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
		control = getButton(parent);
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
		// There is no state to update
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doLoadDefault()
	 */
	protected void doLoadDefault() {
		// There is no state to update
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doStore()
	 */
	protected void doStore() {
		// There is no state to store
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#getNumberOfControls()
	 */
	public int getNumberOfControls() {
		return 2;
	}

	/*
	 * Lazily create and return the control.
	 */
	private Button getButton(Composite parent) {
		if (fButton == null) {
			fButton = new Button(parent, SWT.PUSH);
			fButton.setFont(parent.getFont());
			fButton.setText(buttonText);
			fButton.addMouseListener(listener);
		}
		return fButton;
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.preference.FieldEditor#setEnabled(boolean,
	 *      org.eclipse.swt.widgets.Composite)
	 */
	public void setEnabled(boolean enabled, Composite parent) {
		super.setEnabled(enabled, parent);
		getButton(parent).setEnabled(enabled);
	}
}
