package org.jmlspecs.openjml.eclipse;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.jmlspecs.annotation.Nullable;
import org.jmlspecs.openjml.Main.Cmd;

public class JobControl {
    
    public IProgressMonitor progressGroup;

    public static JobParameters launchJobControlDialog(ISelection selection,
                            @Nullable IWorkbenchWindow window, @Nullable final Shell shell) {
        JobParameters jp = new JobParameters();
        if (!Options.isOption(Options.showJobControlDialogKey)) return jp;
        JobControlDialog j = new JobControlDialog(jp);
        int ok = j.open();
        if (ok == IStatus.OK) {
            Options.setOption(Options.showJobControlDialogKey, !jp.noShowAgain);
            return jp;
        } else {
            return null;
        }
    }
    
    
    /** Create a JobParameters structure, initialized from preferences */
    public static class JobParameters {
        public int queues;
        {try {
        	String jq = Options.value(Options.jobQueuesKey);
        	if (jq != null) jq = jq.trim();
        	queues = jq == null || jq.isEmpty() ? 1 : Integer.valueOf(jq);
        } catch (NumberFormatException e) {
        	queues = 1;
        }}
        public Class<? extends JobStrategy> strategy;
        { try {
            strategy = (Class<? extends JobStrategy>)Class.forName(Options.value(Options.jobStrategyKey));
        } catch (Exception e) {
            strategy = SelectedItemStrategy.class;
        }}
        
        public boolean noShowAgain = !Options.isOption(Options.showJobControlDialogKey);
        public boolean alwaysSave = Options.isOption(Options.alwaysSaveJobControlDialogKey);
        
        /** Save the field values back to preferences */
        public void save() {
            Options.setOption(Options.alwaysSaveJobControlDialogKey, this.alwaysSave);
            Options.setOption(Options.showJobControlDialogKey, !this.noShowAgain);
            Options.setValue(Options.jobQueuesKey, Integer.toString(this.queues));
            Options.setValue(Options.jobStrategyKey, this.strategy.getName());
        }
    }
    
    public static class JobControlDialog extends MessageDialog {
 
        JobParameters jp;

        public JobControlDialog(JobParameters jp) {
            super(null,"OpenJML Job Control",null,"",MessageDialog.NONE,0,"OK","CANCEL");
            this.jp = jp;
        }

        class BButton {
            Button b;
            Class<? extends JobStrategy> strategy;
            public BButton(Composite pp, String title, Class<? extends JobStrategy> strategy) { 
                b = new Button (pp,SWT.RADIO); 
                try { b.setText(strategy.newInstance().description()); } catch (Exception e) { b.setText("<FAILED TO INSTANTIATE>"); }
                this.strategy = strategy; 
                if (strategy==null) b.setEnabled(false);
                b.addSelectionListener(new SelectionAdapter() { public void widgetSelected(SelectionEvent event) { if (b.isEnabled()) jp.strategy = strategy; }});
            }
        };
        
        Combo queues;

        @Override
        public Control createCustomArea(Composite parent) {
            int procs = Runtime.getRuntime().availableProcessors();
            new Label(parent,SWT.NONE).setText("This computer has " + procs + " available processors");

            Composite p = new Composite(parent,SWT.NONE);
            p.setLayout(new RowLayout());
            new Label(p,SWT.NONE).setText("How many job queues should be used? ");
            //new org.eclipse.swt.widgets.List(parent,SWT.SINGLE).setItems(new String[]{"1","2","3","4","5","6","7","8","9"});
            queues = new Combo(p,SWT.DROP_DOWN|SWT.READ_ONLY);
            queues.setItems(new String[]{"1"}); // ,"2","3","4","5","6","7","8","9"});
            int defaultSelection = jp.queues - 1;
            if (defaultSelection < 0) defaultSelection = 0;
            queues.select(defaultSelection);
            // FIXME - else an error
            jp.queues = defaultSelection + 1;
            queues.addSelectionListener(new SelectionAdapter() { public void widgetSelected(SelectionEvent event) { jp.queues = ((Combo)event.widget).getSelectionIndex()+1; }});
 
            new Label(parent,SWT.NONE).setText("What job scheduling policy should be used? ");
            String defaultStrategy = Options.value(Options.jobStrategyKey);
            Class<?> defaultStrategyClass;
            try {
            	defaultStrategyClass = Class.forName(defaultStrategy);
            } catch (ClassNotFoundException e) {
            	defaultStrategyClass = strategies[0].getClass();
            }
            Composite pp = new Composite(parent,SWT.NONE);
            pp.setLayout(new GridLayout(1,true));
            for (JobStrategy s: strategies) {
            	boolean select = s.getClass() == defaultStrategyClass;
            	if (select) jp.strategy = s.getClass();
                new BButton(pp,s.description(),s.getClass()).b.setSelection(select);
            }
            
            Button noShowAgain = new Button(parent, SWT.CHECK);
            noShowAgain.setText("Do not show this item again (always use job settings from Preferences page)");
            noShowAgain.setSelection(jp.noShowAgain);
            noShowAgain.addSelectionListener(new SelectionAdapter() { public void widgetSelected(SelectionEvent event) { jp.noShowAgain = noShowAgain.isEnabled(); }});
            
            Button alwaysSave = new Button(parent, SWT.CHECK);
            alwaysSave.setText("Save these settings back to Preferences");
            alwaysSave.setSelection(jp.alwaysSave);
            alwaysSave.addSelectionListener(new SelectionAdapter() { public void widgetSelected(SelectionEvent event) { jp.alwaysSave = alwaysSave.isEnabled(); }});
            return null;
        }
    }
    
    public static abstract class JobStrategy {
        List<?> elements;
        String title;
        IJavaProject jp;
        public abstract String description();
        public abstract int queues();
        public abstract Job nextJob(OpenJMLInterface iface, int queue, SubMonitor parentMonitor);
        public abstract int totalWork();
        public void cancel() {}
    }
    
    public static JobStrategy[] strategies = new JobStrategy[]{
        new OneJobStrategy(),
        new SelectedItemStrategy(),
//        new MultiSelectedItemStrategy(),
    };

    public static class OneJobStrategy extends JobStrategy {
        
        public OneJobStrategy() {}
        
        public OneJobStrategy(IJavaProject jp, List<Object> elements, int availableProcessors, String title) {
            this.elements = elements;
            this.title = title;
            this.jp = jp;
            if (elements == null) {
                elements = new LinkedList<Object>();
                elements.add(jp);
            }
            work = Activator.utils().countMethods(elements);
        }
        
        private boolean done = false;
        
        public int work;
        
        public OpenJMLInterface iface;
        
        public String description() { return "As one sequential job"; }
        
        public int queues() { return 1; }
        
        public int totalWork() { return work; }
        
        public void cancel() { }
        
        public /*@ nullable */ Job nextJob(OpenJMLInterface iface, int queue, SubMonitor parentMonitor) {
            if (done || elements == null || elements.isEmpty()) return null;
            this.iface = iface;
            String description = "Static checks of items in project " + jp.getElementName();
            Job j = new Job(title) {
                public IStatus run(IProgressMonitor mon) {
                    // The actual amount of work will be determined in executeESCCommand
                	parentMonitor.beginTask(title, IProgressMonitor.UNKNOWN);
                	parentMonitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
                    boolean c = false;
                    try {
                        iface.executeESCCommand(Cmd.ESC, elements, parentMonitor, description);
                    } catch (Exception e) {
                        // FIXME - this will block, preventing progress on the rest of the projects
                        Log.errorlog("Exception during Static Checking - " + jp.getElementName(), e);
                        Utils.showExceptionInUI(null, "Exception during Static Checking - " + jp.getElementName(), e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            done = true;
            return j;
        }
    }
    
    public static class SelectedItemStrategy extends JobStrategy {

        public SelectedItemStrategy() {}

        public SelectedItemStrategy(IJavaProject jp, List<Object> elements, int availableProcessors, String title) {
            this.elements = elements;
            this.title = title;
            this.jp = jp;
            if (elements == null) {
                elements = new LinkedList<Object>();
                elements.add(jp);
            }
            work = Activator.utils().countMethods(elements);

            iter = elements.iterator();
        }
        
        int work;
        
        public String description() { return "Split by selected items"; }
        
        public int queues() { return 1; }
        
        public int totalWork() { return work; }
        
        public Iterator<Object> iter;
        
        public /*@ nullable */ Job nextJob(OpenJMLInterface iface, int queue, SubMonitor parentMonitor) {
            if (!iter.hasNext()) return null;
            Object o = iter.next();
            String id1 = o.toString();
            int k = id1.indexOf('[');
            id1 = o instanceof IMethod ? id1.substring(0, k > 0 ? k : id1.length()):
                o instanceof IJavaElement ? ((IJavaElement)o).getElementName() : 
                o instanceof IResource ? ((IResource)o).getName() :
                id1;
            String id = id1;
            String description = "Static checks in project " + jp.getElementName() + " - " + id;
            Job j = new Job(title) {
                public IStatus run(IProgressMonitor mon) {
                	// The monitor passed in here is not shown to the user, so we ignore it
                    // The actual amount of work will be determined in executeESCCommand
                    parentMonitor.beginTask(description, IProgressMonitor.UNKNOWN);
                    parentMonitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
                    boolean c = false;
                    try {
                        List<Object> list = new LinkedList<Object>();
                        list.add(o);
                        iface.executeESCCommand(Cmd.ESC, list, parentMonitor, description);
                    } catch (Exception e) {
                        // FIXME - this will block, preventing progress on the rest of the projects
                        Log.errorlog("Exception during Static Checking - " + jp.getElementName() + " _ " + id, e);
                        Utils.showExceptionInUI(null, "Exception during Static Checking - " + jp.getElementName() + " - " + id, e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            return j;
        }
    }
    
    public static class MultiSelectedItemStrategy extends JobStrategy {

        public MultiSelectedItemStrategy() {}

        public MultiSelectedItemStrategy(IJavaProject jp, List<Object> elements, int availableProcessors, String title) {
            this.elements = elements;
            this.title = title;
            this.jp = jp;
            if (elements == null) {
                elements = new LinkedList<Object>();
                elements.add(jp);
            }
            iter = elements.iterator();
        }
        
        public boolean done = false;
        
        public String description() { return "Split by selected items - parallel execution"; }
        
        public int queues() { return 2; }
        
        public int totalWork() { return 100; }
        
        public Iterator<Object> iter;
        
        public /*@ nullable */ Job nextJob(OpenJMLInterface iface, int queue, SubMonitor parentMonitor) {
            if (!iter.hasNext()) return null;
            Object o = iter.next();
            String description = "Static checks of items in project " + jp.getElementName();
            Job j = new Job(title) {
                public IStatus run(IProgressMonitor mon) {
                    // The actual amount of work will be determined in executeESCCommand
                    parentMonitor.beginTask(description, IProgressMonitor.UNKNOWN);
                    parentMonitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
                    boolean c = false;
                    try {
                        List<Object> list = new LinkedList<Object>();
                        list.add(o);
                        iface.executeESCCommand(Cmd.ESC, list, parentMonitor, description);
                    } catch (Exception e) {
                        // FIXME - this will block, preventing progress on the rest of the projects
                        Log.errorlog("Exception during Static Checking - " + jp.getElementName(), e);
                        Utils.showExceptionInUI(null, "Exception during Static Checking - " + jp.getElementName(), e);
                        c = true;
                    }
                    return c ? Status.CANCEL_STATUS : Status.OK_STATUS;
                }
            };
            done = true;
            return j;
        }
    }
    

}