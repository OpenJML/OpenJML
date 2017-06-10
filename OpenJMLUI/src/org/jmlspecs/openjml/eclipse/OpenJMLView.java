package org.jmlspecs.openjml.eclipse;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
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
import org.jmlspecs.openjml.JmlOption;
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

	/** Eclipse ID of the viewer - must match the ID defined in the plugin.xml file */
    public static final String ID = "org.openjml.proofview"; //$NON-NLS-1$
    
    Document doc;
    
    IJavaProject currentProject;
    IPartListener aListener;
    TreeViewer viewer;
    
    //Table tree;
    Tree tree;
    TreeItem treeroot;
    

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
    public final static Color blue = new Color(null,128,128,255);

    Map<String,TreeItem> treeitems = new HashMap<String,TreeItem>();
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
    	if (currentProject == null) {
    		this.setPartName("OpenJML Checks");
    		treeroot.setText("<No project set>");
    	} else {
    		OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    		Map<String,IProverResult> results = iface.getProofResults();

    		this.setPartName("OpenJML: " + currentProject.getElementName());
    		treeroot.setText("Static Checks for: " + currentProject.getElementName());
            
            // FIXME - would like to sort these; remember the tree is built incrementally
            for (String key : results.keySet()) {
            	refresh(key);
            }
            treeroot.setExpanded(true);
    	}
    }
    
    public void refresh(String key) {
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	Map<String,IProverResult> results = iface.getProofResults();
    	IProverResult result = results.get(key);
    	Symbol sym = result.methodSymbol();
    	
        	PackageSymbol p = sym.packge();
    		String pname = p.getQualifiedName().toString();
    		if (pname.isEmpty()) pname = "<default package>";
        	TreeItem ti = treeitems.get(pname);
        	if (ti == null) {
        		ti = new TreeItem(treeroot, SWT.NONE);
        		ti.setText(pname);
        		treeitems.put(pname, ti);
        	}
    		
        	Symbol classSym = sym.owner;
        	String scname = iface.keyForSym(classSym);
        	String cname = classSym.getSimpleName().toString();
        	TreeItem tii = treeitems.get(scname);
        	if (tii == null) {
        		tii = new TreeItem(ti,SWT.NONE);
        		tii.setText(scname); // FIXME - what about nested classes
        		treeitems.put(scname, tii);
            	{
            		Info iteminfo = new Info();
            		iteminfo.key = scname;
            		iteminfo.proofResult = null;
            		iteminfo.javaElement = iface.convertType((Symbol.ClassSymbol)classSym);
            		iteminfo.signature = classSym.getSimpleName().toString();
            		tii.setData(iteminfo);
            	}
        	}
    		
        	String text = sym.toString();
        	TreeItem tiii = treeitems.get(key);
        	if (tiii == null) {
    			tiii = new TreeItem(tii,SWT.NONE);
    			treeitems.put(key, tiii);
        	}
        	
        	Kind k = result == null ? null : result.result();
        	String info = result == null ? "" : (" ["
        			+ (org.jmlspecs.openjml.Utils.testingMode ? "TIME" : result.duration()) 
        			+ " " + result.prover() + "]");
        	tiii.removeAll();
        	{
        		Info iteminfo = new Info();
        		iteminfo.key = key;
        		iteminfo.proofResult = result;
        		iteminfo.javaElement = iface.convertMethod((MethodSymbol)sym);
        		iteminfo.signature = key;
        		tiii.setData(iteminfo);
        	}
        	if (k == IProverResult.SAT || k == IProverResult.POSSIBLY_SAT) {
        		tiii.setText("[INVALID] " + text + info);
        		tiii.setBackground(orange);
    			List<IProverResult.Item> presults = ((org.jmlspecs.openjml.proverinterface.ProverResult)result).details();
    			if (presults == null) {
    			  // Put nothing
    			} else if (presults.size() == 1) {
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
        		tiii.setText("[VALID]   " + text + info);
            	tiii.setBackground(green);
        	} else if (k == IProverResult.ERROR) {
        		tiii.setText("[ERROR]   " + text + info);
            	tiii.setBackground(red);
        	} else if (k == IProverResult.TIMEOUT) {
        		tiii.setText("[TIMEOUT]   " + text + info);
            	tiii.setBackground(yellow);
        	} else if (k == IProverResult.UNKNOWN) {
        		tiii.setText("[UNKNOWN]   " + text + info);
            	tiii.setBackground(red);
        	} else if (k == IProverResult.INFEASIBLE) {
        		tiii.setText("[INFEASIBLE] " + text + info);
            	tiii.setBackground(yellow);
        	} else if (k == IProverResult.SKIPPED) {
        		tiii.setText("[SKIPPED] " + text + info);
            	tiii.setBackground(blue);
        	} else if (k == null) {
        		tiii.setText(text);
            	tiii.setBackground(white);
        	} else {
        		tiii.setText("[?????] " + text + info);
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

    		// Get project name

    		IProject p = input.getFile().getProject();
    		currentProject = p.hasNature(JavaCore.NATURE_ID) ? JavaCore.create(p) : null;

    		return true;
    	} catch (Exception e) {
    		return false;
    	}
    }

    public void clearProofResults() {
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	iface.clearProofResults(currentProject);
    	treeitems.clear();
    	treece.clear();
    	treeroot.removeAll();
    	refresh();
    	selected = null;
    }
    
    public void clearSelectedProofResults() {
    	if (selected == null) return;
    	OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	clearResults(iface,selected);
    	treeroot.removeAll();
    	treeitems.clear();
    	treece.clear();
    	refresh();
    	selected = null;
    }
    
    private void clearResults(OpenJMLInterface iface, TreeItem ti) {
    	Info info = (Info)ti.getData();
    	ti.setData(null);
    	if (info != null) iface.getProofResults().remove(info.key);
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
//        menuManager.add(clearProofResults);
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
    
    TreeItem selected;

	@Override
	public void widgetSelected(SelectionEvent e) {
		TreeItem ti = selected = (TreeItem)e.item;
		if (ti == null) return;
		Info info = (Info)ti.getData();
		TreeItem pi = ti;
		if (info == null) {
			pi = ti.getParentItem();
			if (pi != null) info = (Info)pi.getData();
		}
		if (info != null) { 
			OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
			IProverResult pr = info.proofResult;
			IJavaElement je = info.javaElement; // This can be null for default constructors that have no code
			IResource r = je == null ? null : je.getResource();
			if (r != null) Activator.utils().deleteHighlights(r,null); // FIXME - would like to clear just the java element, not the whole compilation unit
			if (pr != null) {
				ICounterexample ce = treece.get(ti);
				if (ce instanceof Counterexample) {
					String text = ((Counterexample)ce).traceText; // FIXME - change to method on interface
					Activator.utils().setTraceViewUI(null,info.signature,text);
					if (info.javaElement instanceof IMethod) {
						iface.highlightCounterexamplePath((IMethod)info.javaElement,info.proofResult,ce);
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
					Activator.utils().setTraceViewUI(null, info.signature,"Method and its specifications are " + desc + ": " 
							+ info.key);
				}
			}
		}
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) {
		widgetSelected(e);
	}

	/** Launches a Java editor for the merthod or class that was clicked */
	@Override
	public void mouseDoubleClick(MouseEvent e) {
		// Presumes a selection happened as part of the double click
		Widget w = e.widget;
		if (!(w instanceof Tree)) return;
		TreeItem ti = selected;
		Info info = ti != null ? (Info)ti.getData() : null;
		IJavaElement je = info == null ? null : info.javaElement;
		if (je != null) {
			IFile f = (IFile)je.getResource();
			Activator.utils().launchJavaEditor(f);
		}
	}

	@Override
	public void mouseDown(MouseEvent e) {
	}

	@Override
	public void mouseUp(MouseEvent e) {
	}
	
	public static class Info {
		public IProverResult proofResult;
		public String key;
		public IJavaElement javaElement;
		public String signature;
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
