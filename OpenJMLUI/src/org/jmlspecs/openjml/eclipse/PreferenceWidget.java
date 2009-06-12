/*
 * This file is part of the OpenJML plugin project. 
 * Copyright 2006-2009 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;


import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;

/**
 * This class is a base class for the controls that are used in
 * the property page; each control is connected to an Option object.
 * 
 * @author David Cok
 *
 */
abstract public class PreferenceWidget {
	
	/** The option object represented by this PreferenceWidget */
	AbstractPreference option;
	
	
	/**
	 * Base class constructor, taking some common arguments.
	 * 
	 * @param option The option that this widget represents.
	 */
	public PreferenceWidget(AbstractPreference option) {
		this.option = option;
	}
	
	/**
	 * Creates and adds the widget to the given control
	 * @param parent The composite to add the widget to.
	 */
	abstract public void addWidget(Composite parent);
	
	/**
	 * Sets the UI widget to the built-in default value
	 *
	 */
	abstract public void setDefault();
	
	/**
	 * Sets the value of the associated option based on the
	 * current UI setting.
	 * 
	 */
	abstract public void setOptionValue();

	
	/**
	 * A UI widget that offers a selection from a fixed 
	 * set of strings,
	 * corresponding to a ChoiceOption.
	 *  
	 * @author David Cok
	 *
	 */
	public static class ChoiceWidget extends PreferenceWidget {
		
		/** The widget used to get input from the user. */
		protected Combo widget = null;
		
		/**
		 * A constructor that creates a Combo widget, initializing
		 * it from the associated property.
		 * 
		 * @param option The option with which the widget is associated
		 */
		//@ pure
		public ChoiceWidget(AbstractPreference.ChoiceOption option) {
			super(option);
		}
        
		/**
		 * Creates the corresponding widget and adds it to the given
		 * Composite widget; the UI widgets are recreated for each
		 * instance of a property page.
		 * @param parent The Composite that holds all of the option widgets
		 */
		//@ ensures widget != null;
		public void addWidget(Composite parent) {
			AbstractPreference.ChoiceOption opt = (AbstractPreference.ChoiceOption)option;
			Composite composite = new Widgets.HComposite(parent,2);
			widget = new Combo(composite, SWT.READ_ONLY);
			widget.setItems(opt.choices());
			widget.select(opt.getIndexValue());
			widget.setVisibleItemCount(opt.choices().length);
			widget.setToolTipText(opt.tooltip());
			org.eclipse.swt.widgets.Label label2 = new org.eclipse.swt.widgets.Label(composite,SWT.NONE);
			label2.setText(opt.label());
			label2.setToolTipText(opt.tooltip());
		}
		
		/**
		 * Returns the current setting of the widget; this method
		 * may be called only when there is a current Properties Page.
		 * @return The current setting of the widget
		 */
		//@ requires widget != null;
		//@ ensures \result != null;
		//@ pure
		public String value() { return widget.getText(); }
		
		
		/**
		 * Sets the UI widget to the option's default value
		 *
		 */
		public void setDefault() {
			widget.select(((AbstractPreference.ChoiceOption)option).getDefaultIndex());
		}		
		
		/**
		 * Sets the option value to be consistent with the
		 * current setting of the UI's widget.
		 */
		public void setOptionValue() { ((AbstractPreference.ChoiceOption)option).setValue(value()); } 
	}
	
	/**
	 * This class implements an PreferenceWidget for a text field
	 * property that holds a file name, using the FileTextField widget, which 
	 * incorporates a Browse button.
	 * 
	 * @author David Cok
	 *
	 */
	public static class FileWidget extends PreferenceWidget {
		
		/** The UI widget representing a file browser. */
		protected Widgets.FileTextField widget = null;

		/**
		 * Creates a FileWidget (the underlying widget is not
		 * created until createContents is called).
		 * @param option The option on which this widget is based
		 */
		//@ reqiures option != null;
		//@ ensures widget == null;
		//@ ensures this.option == option;
		//@ pure
		public FileWidget(AbstractPreference.StringOption option) {
			super(option);
		}
		
		
		/**
		 * Creates the corresponding widget and adds it to the given
		 * Composite widget; the UI widgets are recreated for each
		 * instance of a property page.
		 * @param parent The Composite that holds all of the option widgets
		 */
		//@ ensures widget != null;
		public void addWidget(Composite parent) {
			String fn = ((AbstractPreference.StringOption)option).getValue();
			widget = new Widgets.FileTextField(parent,option.label(),fn,option.tooltip(),50);
		}
		
		/**
		 * Returns the current setting of the widget; this method
		 * may be called only when there is a current Properties Page.
		 * @return The current setting of the widget
		 */
		//@ requires widget != null;
		public String value() { return widget.value().trim(); }
		
		/**
		 * Sets the UI widget to the built-in default value
		 *
		 */
		//@ requires widget != null;
		//@ requires option != null;
		public void setDefault() {
			widget.setText(((AbstractPreference.StringOption)option).getDefault());
		}
				
		/**
		 * Sets the option value to be consistent with the
		 * current setting of the UI's widget.
		 */
		//@ requires widget != null;
		//@ requires option != null;
		public void setOptionValue() { ((AbstractPreference.StringOption)option).setValue(value()); } 
	}
	
	/**
	 * This class implements a PropertyWidget for a boolean-valued
	 * property, associating it with a check-box Button in the UI.
	 * 
	 * @author David Cok
	 *
	 */
	public static class BooleanWidget extends PreferenceWidget {
		
		/** The UI widget representing a boolean choice. */
		protected Button widget = null;
		
		/**
		 * Creates a checkbox widget on the given parent Composite widget;
		 * initializes the widget with the value of the given option
		 * @param option The option on which this widget is based
		 */
		//@ requires option != null;
		//@ ensures this.option == option;
		//@ pure
		public BooleanWidget(AbstractPreference.BooleanOption option) {
			super(option);
		}
		
		/**
		 * Creates the corresponding widget and adds it to the given
		 * Composite widget; the UI widgets are recreated for each
		 * instance of a property page.
		 * @param parent The Composite that holds all of the option widgets
		 */
		//@ requires option != null;
		//@ ensures widget != null;
		public void addWidget(Composite parent) {
			widget = new Button(parent,SWT.CHECK);
			widget.setText(option.label());
			widget.setToolTipText(option.tooltip());
			widget.setSelection(((AbstractPreference.BooleanOption)option).getValue());
		}
		
		/**
		 * Returns the current setting of the widget; this method
		 * may be called only when there is a current Properties Page.
		 * @return The current setting of the widget
		 */
		//@ requires widget != null;
		public boolean value() { return widget.getSelection(); }
		
		/**
		 * Sets the UI widget to the built-in default value
		 *
		 */
		//@ requires widget != null;
		//@ requires option != null;
		public void setDefault() {
			widget.setSelection(((AbstractPreference.BooleanOption)option).getDefault());
		}
		
		/**
		 * Sets the workspace property value to be consistent with the
		 * current setting of the UI's widget.
		 */
		//@ requires widget != null;
		//@ requires option != null;
		public void setOptionValue() { ((AbstractPreference.BooleanOption)option).setValue(value()); } 
	}

    /**
     * This class implements a PropertyWidget for a boolean-valued
     * property, associating it with a check-box Button in the UI.
     * 
     * @author David Cok
     *
     */
    public static class IntWidget extends PreferenceWidget {
        
        /** The UI widget representing a choice. */
        protected Combo widget = null;
        
        /** The strings giving the specific choices displayed. */
        protected String[] choices;
        
        /**
         * Creates a checkbox widget on the given parent Composite widget;
         * initializes the widget with the value of the given option
         * @param option The option on which this widget is based
         * @param choices the specific alternates displayed as choices
         */
        //@ requires option != null;
        //@ ensures this.option == option;
        //@ pure
        public IntWidget(AbstractPreference.IntOption option, String[] choices) {
            super(option);
            this.choices = choices;
        }
        
        /**
         * Creates the corresponding widget and adds it to the given
         * Composite widget; the UI widgets are recreated for each
         * instance of a property page.
         * @param parent The Composite that holds all of the option widgets
         */
        //@ requires option != null;
        //@ ensures widget != null;
        public void addWidget(Composite parent) {
            AbstractPreference.IntOption opt = (AbstractPreference.IntOption)option;
            Composite composite = new Widgets.HComposite(parent,2);
            org.eclipse.swt.widgets.Label label2 = new org.eclipse.swt.widgets.Label(composite,SWT.NONE);
            label2.setText(opt.label());
            label2.setToolTipText(opt.tooltip());
            widget = new Combo(composite, SWT.READ_ONLY);
            widget.setItems(choices);
            widget.select(opt.getValue());
            widget.setVisibleItemCount(choices.length);
            widget.setToolTipText(opt.tooltip());

//            widget = new Button(parent,SWT.CHECK);
//            widget.setText(option.label());
//            widget.setToolTipText(option.tooltip());
//            widget.setSelection(((AbstractPreference.BooleanOption)option).getValue());
        }
        
        /**
         * Returns the current setting of the widget; this method
         * may be called only when there is a current Properties Page.
         * @return The current setting of the widget
         */
        //@ requires widget != null;
        public int value() { return widget.getSelectionIndex(); }
        
        /**
         * Sets the UI widget to the built-in default value
         *
         */
        //@ requires widget != null;
        //@ requires option != null;
        public void setDefault() {
            widget.select(((AbstractPreference.IntOption)option).getDefault());
        }
        
        /**
         * Sets the workspace property value to be consistent with the
         * current setting of the UI's widget.
         */
        //@ requires widget != null;
        //@ requires option != null;
        public void setOptionValue() { ((AbstractPreference.IntOption)option).setValue(value()); } 
    }
    

    /**
     * This class implements a PropertyWidget for a String-valued
     * property, associating it with an editable text box in the UI.
     * 
     * @author David Cok
     *
     */
    public static class StringWidget extends PreferenceWidget {
        
        /** The UI widget representing a String value. */
        protected Text widget = null;
        
        /**
         * Creates a checkbox widget on the given parent Composite widget;
         * initializes the widget with the value of the given option
         * @param option The option on which this widget is based
         */
        //@ requires option != null;
        //@ ensures this.option == option;
        //@ pure
        public StringWidget(AbstractPreference.StringOption option) {
            super(option);
        }
        
        /**
         * Creates the corresponding widget and adds it to the given
         * Composite widget; the UI widgets are recreated for each
         * instance of a property page.
         * @param parent The Composite that holds all of the option widgets
         */
        //@ requires option != null;
        //@ ensures widget != null;
        public void addWidget(Composite parent) {
          Composite composite = new Widgets.HComposite(parent,2);
          org.eclipse.swt.widgets.Label label2 = new org.eclipse.swt.widgets.Label(composite,SWT.NONE);
          label2.setText(option.label());
          label2.setToolTipText(option.tooltip());
          widget = new Text(composite, SWT.SINGLE);
          widget.setText(((AbstractPreference.StringOption)option).getValue());
          widget.setToolTipText(option.tooltip());
        }

        /**
         * Returns the current setting of the widget; this method
         * may be called only when there is a current Properties Page.
         * @return The current setting of the widget
         */
        //@ requires widget != null;
        public String value() { return widget.getText(); }
        
        /**
         * Sets the UI widget to the built-in default value
         *
         */
        //@ requires widget != null;
        //@ requires option != null;
        public void setDefault() {
            widget.setText(((AbstractPreference.StringOption)option).getDefault());
        }
        
        /**
         * Sets the workspace property value to be consistent with the
         * current setting of the UI's widget.
         */
        //@ requires widget != null;
        //@ requires option != null;
        public void setOptionValue() {
          ((AbstractPreference.StringOption)option).setValue(value()); 
        } 
    }
	/**
	 * This class implements an PreferenceWidget that is a Label, so
	 * that it can sit in lists of PreferenceWidgets.  However, it does
	 * not have an option associated with it.
	 * 
	 * @author David Cok
	 *
	 */
	public static class Label extends PreferenceWidget {
		
		/** The UI widget that is a label. */
		protected Widgets.LabeledSeparator widget = null;
		
		/** The label value */
		protected String label;
	
		/** 
		 * Creates a Label widget on the given parent Composite widget.
		 * @param label The label text for the widget
		 */
		//@ requires label != null;
		//@ ensures this.label == label;
		//@ pure
		public Label(String label) {
			super(null);
			this.label = label;
		}
		
		/**
		 * Creates the corresponding widget and adds it to the given
		 * Composite widget; the UI widgets are recreated for each
		 * instance of a property page.
		 * @param parent The Composite that holds all of the option widgets
		 */
		//@ ensures widget != null;
		public void addWidget(Composite parent) {
			widget = new Widgets.LabeledSeparator(parent,label);
		}

		/**
		 * Does nothing.
		 */
		public void setDefault() { } 
		
		/**
		 * Does nothing.
		 */
		public void setOptionValue() { } 
	}

}
