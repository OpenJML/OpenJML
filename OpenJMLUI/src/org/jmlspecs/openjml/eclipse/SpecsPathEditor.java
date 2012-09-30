/*
 * This file is part of the OpenJML plugin project. 
 * Copyright (c) 2006-2011 David R. Cok
 */
package org.jmlspecs.openjml.eclipse;

import java.util.ArrayList;
import java.util.Arrays;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;

/** This class implements a custom dialog that enables editing the
 * Specifications Path for a java Project in Eclipse.
 * @author David R. Cok
 */
// FIXME - needs repair and review - SpecsPathEditor
// TODO: Remaining problems
// - Dialog is not resizable
// - Dialog buttons are too big
// - Adding new lines requires a pack to show them, but that shrinks the width of the viewer area also, which looks bad
// - Would like to unify the browsing for files and directories
// - Can only select one directory at a time
// - if a selected file or directory is not in the workspace, should we link it?
// - if a persisted entry is not in the workspace, should we give a more prominent error message?  Should we keep it? [Maybe store everything as IPath entries instead of IResource?]
// FIXME - cannot add a File because getFileForLocation appears not to work???? - won't work as is for files that are linked into the project or not part ofthe project at all
public class SpecsPathEditor extends Dialog {

    final protected java.util.List<IResource> savedSpecsPath;
    final protected java.util.List<IResource> specsPath;
    final protected IJavaProject javaProject;
    protected Button useInternalSpecs;
    
    final protected Shell shell;
    
    /** Constructs the editor, caching appropriate stuff.  Note that specsPath is 
     * a mutable reference to the external commonly held list, so internally here
     * we modify the list itself, rather than replace it with a new list.
     * @param shell the current shell which owns dialogs
     * @param jp  the relevant JavaProject
     * @param specsPath a mutable reference to the current specs path for the Java Project
     */
    public SpecsPathEditor(Shell shell, IJavaProject jp, java.util.List<IResource> specsPath) {
        super(shell);
        this.shell = shell;
        this.savedSpecsPath = specsPath;
        this.javaProject = jp;
        this.specsPath = new ArrayList<IResource>();
        this.specsPath.addAll(specsPath);
    }
    
    /** Sets the title of the dialog */
    @Override
    protected void configureShell(Shell newShell) {
        super.configureShell(newShell);
        newShell.setText("Specifications path entries");
        // FIXME - should we be resetting the shell field here?
     }
    
    /** Creates the whole dialog area, as elements of the given Composite 
     * @param parent the parent of the new dialog area
     */
    @Override
    protected Control createDialogArea(final Composite parent) {
        final Composite composite = (Composite)super.createDialogArea(parent);
        composite.setLayout(new FillLayout(SWT.VERTICAL));
        final List list = new List(composite, SWT.BORDER|SWT.MULTI);
        final ListViewer viewer = new ListViewer(list);
        for (IResource f: specsPath) viewer.add(display(f));
        useInternalSpecs = new Button(composite,SWT.CHECK);
        useInternalSpecs.setSelection(!Activator.options.noInternalSpecs);
        useInternalSpecs.setText("Use internal library specs");
        Composite buttonArea = new Composite(composite,SWT.NONE);
        buttonArea.setLayout(new FillLayout(SWT.HORIZONTAL));
        
        Button b = new Button(buttonArea,SWT.PUSH|SWT.FLAT);
        b.setText("Clear");
        b.addSelectionListener(
                new SelectionAdapter() {
                    public void widgetSelected(SelectionEvent e) {
                        specsPath.clear();
                        for (int i=list.getItemCount()-1; i>=0; i--) list.remove(i);
                    }
                }
        );
        b = new Button(buttonArea,SWT.PUSH|SWT.FLAT);
        b.setText("Up");
        b.addSelectionListener(
                new SelectionAdapter() {
                    public void widgetSelected(SelectionEvent e) {
                        int[] indices = list.getSelectionIndices();
                        Arrays.sort(indices);
                        if (indices.length == 0 || indices[0] == 0) return;
                        for (int i: list.getSelectionIndices()) {
                            String o = list.getItem(i);
                            list.remove(i);
                            list.add(o,i-1);
                            IResource f = specsPath.remove(i);
                            specsPath.add(i-1,f);
                        }
                        for (int k=0; k<indices.length; k++) indices[k]--;
                        list.select(indices);
                    }
                }
        );
        b = new Button(buttonArea,SWT.PUSH|SWT.FLAT);
        b.setText("Down");
        b.addSelectionListener(
                new SelectionAdapter() {
                    public void widgetSelected(SelectionEvent e) {
                        int[] indices = list.getSelectionIndices();
                        Arrays.sort(indices);
                        if (indices.length == 0 || indices[indices.length-1] == list.getItemCount()-1) return;
                        for (int k = indices.length-1; k>=0; k--) {
                            int i = indices[k];
                            String o = list.getItem(i);
                            list.remove(i);
                            list.add(o,i+1);
                            IResource f = specsPath.remove(i);
                            specsPath.add(i+1,f);
                        }
                        for (int k=0; k<indices.length; k++) indices[k]++;
                        list.select(indices);
                    }
                }
        );
        b = new Button(buttonArea,SWT.PUSH|SWT.FLAT);
        b.setText("Add File...");
        b.addSelectionListener(
                new SelectionAdapter() {
                    public void widgetSelected(SelectionEvent e) {
                        FileDialog fd = new FileDialog(shell,SWT.OPEN|SWT.MULTI);
                        fd.open();
                        String dir = fd.getFilterPath();
                        String[] filenames = fd.getFileNames();
                        for (String filename : filenames) {
                            Path pp = new Path(dir);
                            IPath p = pp.append(filename);
                            IFile f = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(p);
                            if (f != null) {
                                specsPath.add(0,f);
                                list.add(display(f),0);
                                list.pack();
                            } else {
                                Utils.showMessage(shell,"JML - Edit Specifications Path","The selected location does not appear to be present in an open project in the current workspace: " + p);
                                // FIXME - should we offer to link to the resource; this can happen even if linked, I think, because the getPath gives the file system path, not the project path
                            }
                        }
                    }
                }
        );
        b = new Button(buttonArea,SWT.PUSH|SWT.FLAT);
        b.setText("Add Dir...");
        b.addSelectionListener(
                new SelectionAdapter() {
                    public void widgetSelected(SelectionEvent e) {
                        DirectoryDialog fd = new DirectoryDialog(shell,SWT.OPEN|SWT.MULTI);
                        fd.setFilterPath(javaProject.getProject().getLocation().toOSString());
                        String filename = fd.open();
                        if (filename == null) return; // Canceled
                        IResource f = ResourcesPlugin.getWorkspace().getRoot().getContainerForLocation(new Path(filename));
                        if (f != null) {
                            specsPath.add(0,f);
                            list.add(display(f),0);
                            list.pack();
                        } else {
                            Utils.showMessage(shell,"JML - Edit Specifications Path","The selected location does not appear to be present in an open project in the current workspace: " + filename);
                               // FIXME - should we offer to link to the resource
                        }
                    }
                }
        );
        b = new Button(buttonArea,SWT.PUSH|SWT.FLAT);
        b.setText("Remove");
        b.addSelectionListener(
                new SelectionAdapter() {
                    public void widgetSelected(SelectionEvent e) {
                        int[] indices = list.getSelectionIndices();
                        list.remove(indices);
                        Arrays.sort(indices);
                        for (int i = indices.length-1; i>=0; i--) specsPath.remove(indices[i]);
                    }
                }
        );
        buttonArea.pack();
        return composite;
     }
    
    /** When OK is pressed, we commit the changes that have been made and also
     * store them persistently.
     */
    @Override
    protected void okPressed() {
        savedSpecsPath.clear();
        savedSpecsPath.addAll(specsPath);
        Activator.options.noInternalSpecs = !useInternalSpecs.getSelection();
        Preferences.poptions.noInternalSpecs.setValue(Activator.options.noInternalSpecs);
        super.okPressed();
    }

    /** A helper method that gives the display form of a given specs path
     * entry
     * @param r an entry in the specs path
     * @return the String form to use in the dialog
     */
    protected String display(IResource r) {
        String s = r.getFullPath().toPortableString();
        // S has the form '/' + projectName + '/' + path-in-project
        int k = s.indexOf('/',1);
        s = s.substring(1,k) + " - " + s.substring(k+1);
        return s;
    }
}
