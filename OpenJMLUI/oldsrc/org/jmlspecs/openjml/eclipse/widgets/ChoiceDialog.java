/*
 * This file is part of the OpenJML project.
 * Copyright (c) 2012-2013 David R. Cok
 * @author David R. Cok
 */
package org.jmlspecs.openjml.eclipse.widgets;

import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.jmlspecs.annotation.Nullable;

/** Implements a dialog that allows the user to choose among the values of an 
 * array of some type,
 * using radio buttons.
 * <P>
 * Typical use :<BR>
 * <BR>ChoiceDialog&lt;E&gt; d = new ChoiceDialog&lt;E&gt;(shell, array, disabled);
 * <BR>d.create();
 * <BR>if (d.open() == Dialog.OK) {
 * <BR>  String value = d.selection();
 * <BR>  ...
 * <BR>}
 * @param <E> the Enum whose values are being selected
 */
public class ChoiceDialog<E> extends Dialog {
	
	/** Which value is selected on exit from open() */
	protected E selected;
	
	/** Which values are to be disabled */
	/*@ nullable */
	protected E[] disabled;
	
	/** Which values are to be included */
	protected E[] values;
	
	// Would like to subclass Button to add an E value - but that is not allowed;
	// so we resort to a map
	/** A map from buttons to their Enum values */
	final protected Map<Button,E> buttonToValue = new HashMap<Button,E>();
	
	/** The constructor for the dialog
	 * @param shell the parent shell, passed to the Dialog parent class
	 * @param values the values to display (e.g., E.values())
	 * @param disabled the values to disable (may be null, indicating nothing is disabled)
	 */
	public ChoiceDialog(Shell shell, E[] values, /*@ nullable */ E[] disabled) {
		super(shell);
		shell.setText("TITLE");
		this.values = values;
		this.disabled = disabled;
	}
	
	// FIXME - need a way to add a title to these dialogs
	
	@Override
	public Control createDialogArea(Composite parent) {
		Control c = super.createDialogArea(parent);
		for (E v: values) {
			Button b = createRadioButton(parent,v,v.toString());
			for (E w: disabled) if (w.equals(v)) b.setEnabled(false);
		}
		return c;
	}
	
	/** The currently selected value */
	public E selection() {
		return selected;
	}
	
	/** Helper method to create individual radio buttons */
	protected Button createRadioButton(Composite parent, E value, String label) {
		final Button button = new Button(parent, SWT.RADIO);
		buttonToValue.put(button, value);
		button.setText(label); // JFaceResources.getString(key));
		button.setFont(parent.getFont());
		GridData data = new GridData(GridData.FILL_HORIZONTAL);
		int widthHint = convertHorizontalDLUsToPixels(button,
				IDialogConstants.BUTTON_WIDTH);
		data.widthHint = Math.max(widthHint, button.computeSize(SWT.DEFAULT,
				SWT.DEFAULT, true).x);
		button.setLayoutData(data);
		button.addSelectionListener(
				new SelectionAdapter() {
					public void widgetSelected(SelectionEvent event) {
						selected = buttonToValue.get(button);
					}});
		return button;
	}

	/** Helper method for layout */
	protected int convertHorizontalDLUsToPixels(Control control, int dlus) {
		GC gc = new GC(control);
		gc.setFont(control.getFont());
		int averageWidth = gc.getFontMetrics().getAverageCharWidth();
		gc.dispose();
		double horizontalDialogUnitSize = averageWidth * 0.25;
		return (int) Math.round(dlus * horizontalDialogUnitSize);
	}
}
