package org.jmlspecs.openjml.eclipse;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.GroupMarker;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.*;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.internal.dialogs.ViewContentProvider;
import org.eclipse.ui.internal.dialogs.ViewLabelProvider;
import org.eclipse.ui.part.ViewPart;
import org.jmlspecs.openjml.Strings;
import org.jmlspecs.openjml.esc.MethodProverSMT.Counterexample;
import org.jmlspecs.openjml.proverinterface.IProverResult;
import org.jmlspecs.openjml.proverinterface.IProverResult.ICounterexample;
import org.jmlspecs.openjml.proverinterface.IProverResult.Kind;
import org.jmlspecs.openjml.proverinterface.ProverResult;
import org.w3c.dom.Document;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.PackageSymbol;

public class OpenJMLView extends ViewPart implements SelectionListener, MouseListener {

    public static final String ID = "org.openjml.proofview"; //$NON-NLS-1$
    
    Document doc;
    
    String currentFileName;
    String currentFilePath;
    IJavaProject currentProject;
    Symbol currentSymbol;
    IPartListener aListener;
    Label lblFileName;
    TreeViewer viewer;
    
    //Table tree;
    Tree tree;
    TreeItem treeroot;
    
    IAction clearProofResults;
    

    public OpenJMLView() {
    }
    
    /**
     * Create contents of the view part.
     * @param parent
     */
    @Override
    public void createPartControl(Composite parent) {
    	// FIXME - to get a context menu we need to use a TreeViewer, but that means some complex coding of
    	// a content and label provider - do it later.
        ScrolledComposite sc = new ScrolledComposite(parent, SWT.V_SCROLL | SWT.H_SCROLL | SWT.BORDER);
        sc.setExpandHorizontal(true);
        sc.setExpandVertical(true);
//    	viewer = new TreeViewer(parent, SWT.MULTI|SWT.V_SCROLL|SWT.H_SCROLL);
//    	viewer.setContentProvider(new ViewContentProvider());
////    	viewer.setLabelProvider(new ViewLabelProvider());
//    	viewer.setInput(getViewSite());

        tree = new Tree(sc, SWT.NONE);
        sc.setContent(tree);
//    	tree = (Tree)viewer.getControl();
        treeroot = new TreeItem(tree, SWT.NONE);
        tree.addSelectionListener(this);
        tree.addMouseListener(this);
        
        aListener = new IPartListener(){

            @Override
            public void partActivated(IWorkbenchPart part) {
                if(part instanceof IEditorInput){
                    if(getCurrentFileData()) {
                        refresh();
                    }
                }
            }

            @Override
            public void partBroughtToTop(IWorkbenchPart part) {
                if(part instanceof IEditorInput){
                	refresh();
                }
            }

            @Override
            public void partClosed(IWorkbenchPart part) {}

            @Override
            public void partDeactivated(IWorkbenchPart part) {}

            @Override
            public void partOpened(IWorkbenchPart part) {}
        };
        PlatformUI.getWorkbench().getActiveWorkbenchWindow().getPartService().addPartListener(aListener);
        
        createActions();
        initializeToolBar();
//        initializeMenu();
        if (viewer != null) createContextMenu(viewer);
        refresh();
        
    }
    
    private void createContextMenu(TreeViewer viewer) {
    	// Create menu manager.
    	MenuManager menuMgr = new MenuManager();
    	menuMgr.setRemoveAllWhenShown(true);
    	menuMgr.addMenuListener(new IMenuListener() {
    		public void menuAboutToShow(IMenuManager mgr) {
                mgr.add(new GroupMarker(IWorkbenchActionConstants.MB_ADDITIONS));
    		}
    	});

    	// Create menu.
    	Menu menu = menuMgr.createContextMenu(viewer.getControl());
    	viewer.getControl().setMenu(menu);

    	// Register menu for extension.
    	getSite().registerContextMenu(menuMgr, viewer);
    }
    
    public final static Color white = new Color(null,255,255,255);
    public final static Color red = new Color(null,255,0,0);
    public final static Color green = new Color(null,0,255,0);
    public final static Color orange = new Color(null,255,128,0);
    public final static Color yellow = new Color(null,255,255,0);
    public final static Color blue = new Color(null,0,0,255);

    Map<String,TreeItem> treeitems = new HashMap<String,TreeItem>();
    Map<TreeItem,Symbol> treesyms = new HashMap<TreeItem,Symbol>();
    Map<TreeItem,ICounterexample> treece = new HashMap<TreeItem,ICounterexample>();

    // FIXME: Would like to update incrementally
    // FIXME: Would like to have summary colors on class names. On pacakges as well?
    // FIXME: Leave closed if all OK
    // FIXME: Select - opens editor to correct method; opens trace view if available
    // FIXME: what about multiple counterexamples (update trace and path in editor)
    // FIXME: right click menu items - open trace, rerun action on method, clear contents
    // FIXME: clearing contents 
    // FIXME: do TreeItem objects need to be disposed? YES
    public void refresh() {
    	
    	getCurrentFileData();
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	Map<String,IProverResult> results = iface.getProofResults();

    	this.setPartName("OpenJML: " + currentProject.getElementName());
        treeroot.setText("Static Checks for: " + currentProject.getElementName());
        
        // FIXME - would like to sort these
        for (String symname : results.keySet()) {
        	refresh(symname);
        }
        treeroot.setExpanded(true);
        //viewer.refresh();
    }
    
    public void refresh(String symname) {
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	Map<String,IProverResult> results = iface.getProofResults();
    	
        	Symbol sym = iface.proofSymbols.get(symname);
        	PackageSymbol p = sym.packge();
    		String pname = p.getQualifiedName().toString();
    		if (pname.isEmpty()) pname = "<default package>";
        	TreeItem ti = treeitems.get(pname);
        	if (ti == null) {
        		ti = new TreeItem(treeroot, SWT.NONE);
        		ti.setText(pname);
        		treeitems.put(pname, ti);
        		treesyms.put(ti,p);
        	}
    		
        	Symbol classSym = sym.owner;
        	String scname = iface.keyForSym(classSym);
        	String cname = classSym.getSimpleName().toString();
        	TreeItem tii = treeitems.get(scname);
        	if (tii == null) {
        		tii = new TreeItem(ti,SWT.NONE);
        		tii.setText(cname); // FIXME - what about nested classes
        		treeitems.put(scname, tii);
        		treesyms.put(tii,classSym);
        	}
    		
        	String text = sym.toString();
        	TreeItem tiii = treeitems.get(symname);
        	if (tiii == null) {
    			tiii = new TreeItem(tii,SWT.NONE);
    			treeitems.put(symname, tiii);
    			treesyms.put(tiii,sym);
        	}
        	
        	IProverResult result = results.get(symname);
        	Kind k = result == null ? null : result.result();
        	tiii.removeAll();
        	if (k == IProverResult.SAT || k == IProverResult.POSSIBLY_SAT) {
        		tiii.setText("[INVALID] " + text);
        		tiii.setBackground(orange);
    			List<IProverResult.Item> presults = ((org.jmlspecs.openjml.proverinterface.ProverResult)result).details();
        		if (presults.size() == 1) {
    				treece.put(tiii, result.counterexample());
        		} else if (presults.size() == 0) {
    				treece.put(tiii, null);
        			// FIXME - no counterexample
        		} else {
        			int i = 0;
        			for (IProverResult.Item ce : presults) {
        				if (i == 0) treece.put(tiii, (ICounterexample)ce);
        				if (ce instanceof IProverResult.ICounterexample) {
        					TreeItem tiiii = new TreeItem(tiii,SWT.NONE);
        					// FIXME - say more about the failed assertion
        					tiiii.setText("CE#" + (++i));
        					tiiii.setBackground(orange);
        					treece.put(tiiii, (ICounterexample)ce);
        				}
        			}
        			tiii.setExpanded(true);
        		}
        	} else if (k == IProverResult.UNSAT) {
        		tiii.setText("[VALID]   " + text);
            	tiii.setBackground(green);
        	} else if (k == IProverResult.ERROR) {
        		tiii.setText("[ERROR]   " + text);
            	tiii.setBackground(red);
        	} else if (k == IProverResult.INFEASIBLE) {
        		tiii.setText("[INFEASIBLE] " + text);
            	tiii.setBackground(yellow);
        	} else if (k == IProverResult.SKIPPED) {
        		tiii.setText("[SKIPPED] " + text);
            	tiii.setBackground(blue);
        	} else if (k == null) {
        		tiii.setText(text);
            	tiii.setBackground(white);
        	} else {
        		tiii.setText("[?????] " + text);
        		tiii.setBackground(red);
        	}
            treeroot.setExpanded(true);
    		ti.setExpanded(true);
    		tii.setExpanded(true);
    }
    
    private boolean getCurrentFileData() {
        
    	try {
    		IWorkbenchPage page = PlatformUI.getWorkbench()
    				.getActiveWorkbenchWindow()
    				.getActivePage();

    		if(page == null) return false;

    		IEditorPart activeEditor = page.getActiveEditor();

    		if(activeEditor == null) return false;
    		
    		IEditorInput einput = activeEditor.getEditorInput();

    		if(!(einput instanceof IFileEditorInput)) return false;

    		IFileEditorInput input = (IFileEditorInput) einput;

    		String newFilePath = input.getFile().getRawLocation().toOSString();
    		if (newFilePath == null) {
    			return false;
    		} else if (newFilePath.equals(currentFilePath)) {
    			return false;
    		}
    		
    		// Get project name

    		currentFileName = input.getFile().getName();

    		IProject p = input.getFile().getProject();
    		currentProject = p.hasNature(JavaCore.NATURE_ID) ? JavaCore.create(p) : null;

    		currentFilePath = newFilePath;
    				
    		return true;
    	} catch (Exception e) {
    		return false;
    	}
    }

    /**
     * Create the actions.
     */
    private void createActions() {
        clearProofResults = new Action("Clear Proof Results"){
            public void run(){
            	clearProofResults();
            	Activator.utils().setTraceView(null,null);
            }
        };
    }
    
    public void clearProofResults() {
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	iface.clear(currentProject);
    	treesyms.clear();
    	treeitems.clear();
    	treece.clear();
    	treeroot.removeAll();
    	refresh();
    	selected = null;
    }
    
    public void clearSelectedProofResults() {
    	Symbol sym = treesyms.get(selected);
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	String key = iface.keyForSym(sym);
    	clearResults(iface,selected);
    	iface.getProofResults().put(iface.keyForSym(sym),null);
    	treeroot.removeAll();
    	treesyms.clear();
    	treeitems.clear();
    	treece.clear();
    	treeroot.removeAll();
    	refresh();
    	selected = treeitems.get(key);
    	tree.setSelection(selected);
    	selected.setBackground(white);
    	selected.setExpanded(false);
    	String text = selected.getText();
    	if (text.charAt(0) == '[') text = text.substring(text.indexOf(']') + 2);
    	selected.setText(text);
    }
    
    private void clearResults(OpenJMLInterface iface, TreeItem ti) {
    	Symbol sym = treesyms.get(ti);
    	if (sym != null) iface.getProofResults().remove(iface.keyForSym(sym));
    	for (TreeItem t: ti.getItems()) {
    		clearResults(iface,t);
    	}
    }

    /**
     * Initialize the toolbar.
     */
    private void initializeToolBar() { // FIXME - does this really do anything?
        getViewSite().getActionBars().getToolBarManager();
    }

    /**
     * Initialize the menu.
     */
    private void initializeMenu() {
        IMenuManager menuManager = getViewSite().getActionBars()
                .getMenuManager();
//        MenuManager menu = new MenuManager("Get New Auto-Generated Expressions");
//        
//        menuManager.add(menu);
//        menu.add(updateExpressionsAll);
//        menu.add(updateExpressionsCS);
//        menu.add(updateExpressionsDaikon);
        menuManager.add(clearProofResults);
//        menuManager.add(reloadExpressions);
//        menuManager.add(processExpressions);
//        menuManager.add(processExpressionsWP);
//        menuManager.add(saveExpressions);
    }

    @Override
    public void setFocus() {
        // Set the focus
    }
    
    public void dispose(){
        PlatformUI.getWorkbench()
                  .getActiveWorkbenchWindow()
                  .getPartService()
                  .removePartListener(aListener);
    }
    
    public String getFileName(){
        return currentFileName;
    }
    
    public String getFilePath(){
        return currentFilePath;
    }
    
    TreeItem selected;

	@Override
	public void widgetSelected(SelectionEvent e) {
		TreeItem ti = selected = (TreeItem)e.item;
		if (ti == null) Log.log("SELECTED null");
		else {
			Symbol sym = treesyms.get(ti);
			TreeItem pi = ti;
			if (sym == null) {
				pi = ti.getParentItem();
				sym = treesyms.get(pi);
			}
			String symname = sym == null ? "null" : sym.toString();
			Log.log("SELECTED " + ti.getText() + " " + symname);
			if (sym != null) { 
	    		OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
	    		currentSymbol = sym;
				IProverResult pr = sym instanceof MethodSymbol ? iface.getProofResult((MethodSymbol)sym) : null;
				IResource r = iface.getResourceFor(sym);
				Activator.utils().deleteHighlights(r,null);
				if (pr != null) {
					ICounterexample ce = treece.get(ti);
					if (ce instanceof Counterexample) {
						((ProverResult)pr).selected = ce;
						String text = ((Counterexample)ce).traceText; // FIXME - change to method on interface
						Activator.utils().setTraceView(symname,text);
						if (sym instanceof MethodSymbol) {
							MethodSymbol msym = (MethodSymbol)sym;
							iface.highlightCounterexamplePath(iface.convertMethod(msym),msym,ce);
						}
						if (pi != ti) treece.put(pi, ce);
					} else {
						Kind k = pr.result();
						String desc = k == IProverResult.UNSAT ? "consistent" 
								: k == IProverResult.SAT ? "inconsistent"
								: k == IProverResult.SKIPPED ? " skipped"
								: k == IProverResult.POSSIBLY_SAT ? "probably inconsistent"
								: k == IProverResult.INFEASIBLE ? "infeasible"
								: k == IProverResult.UNKNOWN ? "unknown" : "???";
						Activator.utils().setTraceView(symname,"Method and its specifications are " + desc + ": " 
								+ sym.owner.getQualifiedName() + Strings.dot + sym.toString());
					}
				}
			}
		}
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) {
		widgetSelected(e);
	}

	@Override
	public void mouseDoubleClick(MouseEvent e) {
		// TODO Auto-generated method stub
		Widget w = e.widget;
		if (!(w instanceof Tree)) return;
		TreeItem ti = selected;
		Symbol sym = treesyms.get(ti);
		if (sym == null) sym = treesyms.get(ti.getParentItem());
		OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
		if (sym instanceof MethodSymbol) {
			IType m = iface.convertType((Symbol.ClassSymbol)sym.owner);
			IFile f = (IFile)m.getCompilationUnit().getResource();
			Activator.utils().launchJavaEditor(f);
		} else if (sym instanceof Symbol.ClassSymbol) {
			IType m = iface.convertType((Symbol.ClassSymbol)sym);
			IFile f = (IFile)m.getCompilationUnit().getResource();
			Activator.utils().launchJavaEditor(f);
		}
		
		Log.log("DOUBLE CLICK ");
	}

	@Override
	public void mouseDown(MouseEvent e) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void mouseUp(MouseEvent e) {
		// TODO Auto-generated method stub
		
	}

//    private MessageConsole findConsole(String name) {
//        ConsolePlugin plugin = ConsolePlugin.getDefault();
//        IConsoleManager conMan = plugin.getConsoleManager();
//        IConsole[] existing = conMan.getConsoles();
//        for (int i = 0; i < existing.length; i++)
//           if (name.equals(existing[i].getName()))
//              return (MessageConsole) existing[i];
//        //no console found, so create a new one
//        MessageConsole myConsole = new MessageConsole(name, null);
//        conMan.addConsoles(new IConsole[]{myConsole});
//        return myConsole;
//     }
}
