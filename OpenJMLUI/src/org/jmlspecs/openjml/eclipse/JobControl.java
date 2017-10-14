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
        JobControlDialog j = new JobControlDialog(jp);
        int ok = j.open();
        if (ok == IStatus.OK) {
            return jp;
        } else {
            return null;
        }
    }
    
    
    public static class JobParameters {
        public int queues;
        public Class<? extends JobStrategy> strategy;
    }
    
    public static int defaultQueues = 2;
    
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
//        BButton b0,b1,b2,b3;
       
        @Override
        public Control createCustomArea(Composite parent) {
            int procs = Runtime.getRuntime().availableProcessors();
            new Label(parent,SWT.NONE).setText("This computer has " + procs + " available processors");
            Composite p = new Composite(parent,SWT.NONE);
            p.setLayout(new RowLayout());
            new Label(p,SWT.NONE).setText("How many job queues should be used? ");
            //new org.eclipse.swt.widgets.List(parent,SWT.SINGLE).setItems(new String[]{"1","2","3","4","5","6","7","8","9"});
            Combo c = queues = new Combo(p,SWT.DROP_DOWN|SWT.READ_ONLY);
            c.setItems(new String[]{"1","2","3","4","5","6","7","8","9"});
            c.select(defaultQueues-1);
            jp.queues = defaultQueues;
            c.addSelectionListener(new SelectionAdapter() { public void widgetSelected(SelectionEvent event) { jp.queues = ((Combo)event.item).getSelectionIndex()+1; }});
            new Label(parent,SWT.NONE).setText("What job scheduling policy should be used? ");
            Composite pp = new Composite(parent,SWT.NONE);
            pp.setLayout(new GridLayout(1,true));
            for (JobStrategy s: strategies) {
                new BButton(pp,s.description(),s.getClass()).b.setSelection(s==defaultJobStrategy);
            }
            jp.strategy = defaultJobStrategy.getClass();
            return null;
        }
    }
    
    public static abstract class JobStrategy {
        List<?> elements;
        String title;
        IJavaProject jp;
        public abstract String description();
        public abstract int queues();
        public abstract Job nextJob(OpenJMLInterface iface, int queue);
    }
    
    public static JobStrategy[] strategies = new JobStrategy[]{
        new OneJobStrategy(),
        new SelectedItemStrategy(),
        new MultiSelectedItemStrategy(),
    };

    public static JobStrategy defaultJobStrategy = strategies[1];

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
        }
        
        public boolean done = false;
        
        public String description() { return "As one sequential job"; }
        
        public int queues() { return 1; }
        
        public /*@ nullable */ Job nextJob(OpenJMLInterface iface, int queue) {
            if (done || elements == null || elements.isEmpty()) return null;
            String description = "Static checks of items in project " + jp.getElementName();
            Job j = new Job(title) {
                public IStatus run(IProgressMonitor mon) {
                    SubMonitor monitor = SubMonitor.convert(mon);
                    // The actual amount of work will be determined in executeESCCommand
//                    monitor.beginTask(title, IProgressMonitor.UNKNOWN);
//                    // FIXME - perhaps just set verbosity to at least progress
//                    monitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
                    boolean c = false;
                    try {
                        iface.executeESCCommand(Cmd.ESC, elements, monitor, description);
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
            iter = elements.iterator();
        }
        
        public String description() { return "Split by selected items"; }
        
        public int queues() { return 1; }
        
        public Iterator<Object> iter;
        
        public /*@ nullable */ Job nextJob(OpenJMLInterface iface, int queue) {
            if (!iter.hasNext()) return null;
            Object o = iter.next();
            String id1 = o.toString();
            int k = id1.indexOf('[');
//            try {
            id1 = o instanceof IMethod ? id1.substring(0, k > 0 ? k : id1.length()):
                o instanceof IJavaElement ? ((IJavaElement)o).getElementName() : 
                o instanceof IResource ? ((IResource)o).getName() :
                id1;
//            } catch (JavaModelException e) {
//                id1 = "<JavaModelException>";
//            }
            String id = id1;
            String description = "Static checks in project " + jp.getElementName() + " - " + id;
            Job j = new Job(title) {
                public IStatus run(IProgressMonitor mon) {
                    SubMonitor monitor = SubMonitor.convert(mon);
                    // The actual amount of work will be determined in executeESCCommand
//                    monitor.beginTask(description, IProgressMonitor.UNKNOWN);
//                    // FIXME - perhaps just set verbosity to at least progress
//                    monitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
                    boolean c = false;
                    try {
                        List<Object> list = new LinkedList<Object>();
                        list.add(o);
                        iface.executeESCCommand(Cmd.ESC, list, monitor, description);
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
        
        public Iterator<Object> iter;
        
        public /*@ nullable */ Job nextJob(OpenJMLInterface iface, int queue) {
            if (!iter.hasNext()) return null;
            Object o = iter.next();
            String description = "Static checks of items in project " + jp.getElementName();
            Job j = new Job(title) {
                public IStatus run(IProgressMonitor mon) {
                    SubMonitor monitor = SubMonitor.convert(mon);
                    // The actual amount of work will be determined in executeESCCommand
//                    monitor.beginTask(reason, IProgressMonitor.UNKNOWN);
//                    // FIXME - perhaps just set verbosity to at least progress
//                    monitor.subTask("Detailed progress will be shown only if the verbosity preference is at least 'progress'");
                    boolean c = false;
                    try {
                        List<Object> list = new LinkedList<Object>();
                        list.add(o);
                        iface.executeESCCommand(Cmd.ESC, list, monitor, description);
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