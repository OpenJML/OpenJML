package org.jmlspecs.openjml.eclipse;


import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;

/**
 * A fake field editor that is just a label.
 */
public class LabelFieldEditor extends FieldEditor {

	/**
	 * The <code>Combo</code> widget.
	 */
	private Label fLabel;
	
	private String labelText;
	
	private int style;
	
	/**
	 * Create the combo box field editor.
	 * 
     * @param name the name of the preference this field editor works on
     * @param labelText the label text of the field editor
	 * @param entryNamesAndValues the names (labels) and underlying values to populate the combo widget.  These should be
	 * arranged as: { {name1, value1}, {name2, value2}, ...}
	 * @param parent the parent composite
	 */
	public LabelFieldEditor(String name, String labelText, int style, Composite parent) {
		init(name, labelText);
		this.labelText = labelText;
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
		// Do nothing
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doLoadDefault()
	 */
	protected void doLoadDefault() {
		// Do nothing
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.FieldEditor#doStore()
	 */
	protected void doStore() {
		// Do nothing
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
			Font f = parent.getFont();
			FontData[] fd = f.getFontData();
			fd[0].setStyle(SWT.BOLD);
			fLabel.setFont(f);
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
