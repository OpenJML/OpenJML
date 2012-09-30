/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2011 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;

/**
 * This class just holds a bunch of related classes which are
 * custom widgets for building dialogs.
 * 
 * @author David Cok
 *
 */
public class Widgets {


	/** 
	 * A composite that lays its children out in a number of
	 * columns.
	 * 
	 * @author David Cok
	 *
	 */
	public static class HComposite extends Composite {
		/**
		 * Constructs the composite as a member of the given
		 * parent and with the given number of columns.
		 * 
		 * @param parent  The container into which to place this new widget
		 * @param cols    The number of columns of this widget
		 */
		//@ requires cols > 0;
		public HComposite(/*@ non_null */ Composite parent,int cols) {
			super(parent, SWT.NONE);
			GridLayout layout = new GridLayout();
			layout.numColumns = cols;
			setLayout(layout);
			GridData data = new GridData();
			data.verticalAlignment = GridData.FILL;
			data.horizontalAlignment = GridData.FILL;
			setLayoutData(data);
		}
	}

	/**
	 * A custom widget that lays out its children in one vertical
	 * column.
	 */
	public static class VComposite extends Composite {
		/**
		 * Constructs the composite as a member of the given
		 * parent.
		 * 
		 * @param parent  The container into which to place this new widget
		 */
		public VComposite(/*@ non_null */ Composite parent) {
			super(parent, SWT.NONE);
			GridLayout layout = new GridLayout();
			layout.numColumns = 1;
			setLayout(layout);
			GridData data = new GridData();
			data.verticalAlignment = GridData.FILL;
			data.horizontalAlignment = GridData.FILL;
			setLayoutData(data);
		}
	}

	/**
	 * A custom widget that is a separator followed by a label,
	 * typically used as a title to a set of widgets below it.
	 * 
	 * @author David Cok
	 */
	public static class LabeledSeparator extends Composite {
		/**
		 * @param parent  The container this widget is made part of
		 * @param label	  The text to be used as the label in the widget
		 */
		public LabeledSeparator(/*@ non_null */ Composite parent, 
				/*@ non_null */ String label) {
			super(parent, SWT.NONE);
			GridLayout layout = new GridLayout();
			layout.numColumns = 2;
			setLayout(layout);
			GridData data = new GridData();
			data.verticalAlignment = GridData.FILL;
			data.horizontalAlignment = GridData.FILL;
			setLayoutData(data);
			new Label(this,SWT.SEPARATOR|SWT.HORIZONTAL);
			new Label(this,SWT.NONE).setText(label);
		}
	}


	/**
	 * A custom widget that is used to provide a way for the user
	 * to specify a file; it combines a label, a Browse button,
	 * and a text field.  The Browse button pops up a file browser;
	 * that lets the user browse for a file; the path of the selected
	 * file is then put into the text field.  Or the user can type into
	 * the text field directly.
	 * 
	 * @author David Cok
	 */
	public static class FileTextField extends VComposite {
		/** The text field that shows the file path */
		private Text text;
		/** A String used for spaces */
		final private static String tenspaces = "          ";
		// The length of this string defines the minimum size of the text field.
		// FIXME - there must be a better way to set the size,
		// and a better way to make a long string
		/** A String used for spaces that helps set the size of the text widget */
		final private static String spaces = tenspaces + tenspaces + tenspaces
		+ tenspaces + tenspaces + tenspaces + tenspaces + tenspaces + tenspaces;


		// TODO: Unify FileTextField and DirTextField
		/**
		 * Constructs the composite widget as a member of the given
		 * parent and with the given parameters.
		 * @param parent	The container this new widget is made part of
		 * @param label		The label to be used for this widget (e.g. the purpose of the directory being identified)
		 * @param initialValue  The initial value for the text field (a directory path)
		 * @param toolTipText   The explanatory text used as a tooltip
		 * @param length    The size of the visible part of the field, in characters
		 *		 */
		public FileTextField(/*@ non_null */ Composite parent,
				/*@ non_null */ String label, 
				/*@ non_null */ String initialValue,
				/*@ non_null */ String toolTipText,
				int length) {
			super(parent);
			final Shell shell = parent.getShell();
			final FileDialog fileDialog = new FileDialog(shell,SWT.OPEN);

			// This is a composite widget with internals
			// arranged as follows:
			//   *********************************************
			//   *   label     *  Browse button              *
			//   *********************************************
			//   *        Text field                         *
			//   *********************************************

			Composite hc = new HComposite(this,2);

			new Label(hc,SWT.NONE).setText(label);

			text = new Text(this,SWT.SINGLE);
			String s = initialValue;
			int n = spaces.length();
			if (length < n) n = length;
			if (s.length() < n) s += spaces.substring(0,n-s.length());
			text.setText(s);
			text.setToolTipText(toolTipText);
			// Make the text fixed width and bold
			Font f = JFaceResources.getFontRegistry().getBold(JFaceResources.TEXT_FONT);
			text.setFont(f);
			final Text t = text;

			Button browse = new Button(hc, SWT.PUSH);
			browse.setText("Browse");
			browse.setToolTipText(toolTipText);
			browse.addMouseListener(new MouseAdapter() {
				public void mouseUp(MouseEvent e) {
					String result = fileDialog.open();
					if (result != null) t.setText(result);
				}
			});
		}

		/** Returns the current value of the specified directory path.
		 *
		 * @return the current value of the specified directory path
		 */
		//@ modifies \nothing;
		//@ ensures \result != null;
		public String value() {
			return text.getText();
		}

		/**
		 * Sets the current value in the text field.
		 * 
		 * @param v The text to display
		 */
		public void setText(String v) {
			text.setText(v);
		}
	}

	/**
	 * A custom widget that is used to provide a way for the user
	 * to specify a directory; it combines a label, a Browse button,
	 * and a text field.  The Browse button pops up a file system browser;
	 * that lets the user browse for a directory; the path of the selected
	 * directory is then put into the text field.  Or the user can type into
	 * the text field directly.
	 * 
	 * @author David Cok
	 */
	public static class DirTextField extends VComposite {
		/** The text field that shows the directory path */
		private Text text;
		/** A String used for spaces */
		final private static String tenspaces = "          ";
		// The length of this string defines the minimum size of the text field.
		// FIXME - there must be a better way to set the size,
		// and a better way to make a long string
		/** A String used for spaces that helps set the size of the text widget */
		final private static String spaces = tenspaces + tenspaces + tenspaces
		+ tenspaces + tenspaces + tenspaces + tenspaces + tenspaces + tenspaces;


		/**
		 * Constructs the composite widget as a member of the given
		 * parent and with the given parameters.
		 * @param parent    The container this new widget is made part of
		 * @param label     The label to be used for this widget (e.g. the purpose of the directory being identified)
		 * @param initialValue  The initial value for the text field (a directory path)
		 * @param toolTipText   The explantory text used as a tooltip
		 * @param length    The size of the visible part of the field, in characters
		 *       */
		public DirTextField(/*@ non_null */ Composite parent,
				/*@ non_null */ String label, 
				/*@ non_null */ String initialValue,
				/*@ non_null */ String toolTipText,
				int length) {
			super(parent);
			final Shell shell = parent.getShell();

			final DirectoryDialog dirdialog = new DirectoryDialog(shell);;
			
			// This is a composite widget with internals
			// arranged as follows:
			//   *********************************************
			//   *   label     *  Browse button              *
			//   *********************************************
			//   *        Text field                         *
			//   *********************************************

			Composite hc = new HComposite(this,2);

			new Label(hc,SWT.NONE).setText(label);

			text = new Text(this,SWT.SINGLE);
			String s = initialValue;
			int n = spaces.length();
			if (length < n) n = length;
			if (s.length() < n) s += spaces.substring(0,n-s.length());
			text.setText(s);
			text.setToolTipText(toolTipText);
			// Make the text fixed width and bold
			Font f = JFaceResources.getFontRegistry().getBold(JFaceResources.TEXT_FONT);
			text.setFont(f);
			final Text t = text;

			Button browse = new Button(hc, SWT.PUSH);
			browse.setText("Browse");
			browse.setToolTipText(toolTipText);
			browse.addMouseListener(new MouseAdapter() {
				public void mouseUp(MouseEvent e) {
					String result = dirdialog.open();
					if (result != null) t.setText(result);
				}
			});
		}

		/** Returns the current value of the specified directory path.
		 *
		 * @return the current value of the specified directory path
		 */
		//@ modifies \nothing;
		//@ ensures \result != null;
		public String value() {
			return text.getText();
		}

		/**
		 * Sets the current value in the text field.
		 * 
		 * @param v The text to display
		 */
		public void setText(String v) {
			text.setText(v);
		}
	}

}
