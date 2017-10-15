package org.jmlspecs.openjml.eclipse;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.State;
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
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.handlers.RadioState;
import org.eclipse.ui.handlers.RegistryToggleState;
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
import com.sun.tools.javac.util.Context;

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

        tree = new Tree(sc, SWT.MULTI);
        sc.setContent(tree);
//    	tree = (Tree)viewer.getControl();
        treeroot = new TreeItem(tree, SWT.NONE);
        tree.addSelectionListener(this);
        tree.addMouseListener(this);
        
        aListener = new IPartListener(){

            @Override
            public void partActivated(IWorkbenchPart part) {
                if(part instanceof IEditorInput){
//                    if(getCurrentFileData()) {
                        refresh();
//                    }
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
    public final static Color palered = new Color(null,255,192,192);
    public final static Color pink = new Color(null,255,128,128);
    public final static Color green = new Color(null,0,255,0);
    public final static Color palegreen = new Color(null,176,255,176);
    public final static Color orange = new Color(null,255,128,0);
    public final static Color paleorange = new Color(null,255,176,128);
    public final static Color yellow = new Color(null,255,255,0);
    public final static Color paleyellow = new Color(null,255,255,176);
    public final static Color blue = new Color(null,128,128,255);
    public final static Color paleblue = new Color(null,176,176,255);

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
    	
//    	getCurrentFileData();
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
            	refresh(currentProject,key);
            }
            treeroot.setExpanded(true);
    	}
    }
    
    public int where(TreeItem parent, String name) {
    	// FIXME - could use a binary search. This is mosre robust if the list is not sorted for some reason
    	int i = 0;
    	for (TreeItem t: parent.getItems()) {
    		if (t.getText().compareToIgnoreCase(name) >= 0) return i;
    		i++;
    	}
    	return parent.getItemCount();
    }
    
    public int where2(TreeItem parent, String name) {
    	// FIXME - could use a binary search. This is mosre robust if the list is not sorted for some reason
    	int i = 0;
    	for (TreeItem t: parent.getItems()) {
    		String s = ((Info)t.getData()).signature;
    		if (s.compareToIgnoreCase(name) >= 0) return i;
    		i++;
    	}
    	return parent.getItemCount();
    }
    
    static Date start;
    static Date end;
    public static void start() {
    	start = new Date();
    	end = null;
    }
    public static void stop() {
    	end = new Date();
    }
    
    public void refresh(IJavaProject jproject, String key) {
    	OpenJMLInterface iface = Activator.utils().getInterface(jproject);
    	if (currentProject != jproject) {
    		setProject(jproject);
    	}
    	Map<String,IProverResult> results = iface.getProofResults();
    	IProverResult result = results.get(key);
    	Symbol sym = result.methodSymbol();
    	
    	String pname, scname, cname;
    	Symbol classSym = null;
    	if (sym != null) {
    		PackageSymbol p = sym.packge();
    		pname = p.getQualifiedName().toString();
        	classSym = sym.owner;
        	scname = iface.keyForSym(classSym);
        	cname = classSym.getSimpleName().toString();
    	} else {
    		int k = key.indexOf('(');
    		k = key.lastIndexOf('.',k);
    		scname = key.substring(0,k);
    		int kk = key.lastIndexOf('.',k-1);
    		cname = key.substring(kk+1,k);
    		pname = key.substring(0, kk);
    	}
    	if (pname.isEmpty()) pname = "<default package>";
    	TreeItem ti = treeitems.get(pname);
    	if (ti == null) {
    		int index = where(treeroot,pname);
    		ti = new TreeItem(treeroot, SWT.NONE, index);
    		ti.setText(pname);
    		treeitems.put(pname, ti);
    	}

    	TreeItem tii = treeitems.get(scname);
    	if (tii == null) {
    		int index = where(ti,scname);
    		tii = new TreeItem(ti,SWT.NONE,index);
    		tii.setText(scname); // FIXME - what about nested classes
    		treeitems.put(scname, tii);
    		{
    			Info iteminfo = new Info();
    			iteminfo.key = scname;
    			iteminfo.proofResult = null;
    			iteminfo.javaElement = sym == null ? null : iface.convertType((Symbol.ClassSymbol)classSym);
    			iteminfo.signature = sym == null ? cname : classSym.getSimpleName().toString();
    			tii.setData(iteminfo);
    		}
    	}

    	String text = sym == null ? key : sym.toString();
    	TreeItem tiii = treeitems.get(key);
    	boolean tiii_isNew = tiii == null;
    	Color oldColor =null;
    	if (tiii == null) {
    		int index = where2(tii,key);
    		tiii = new TreeItem(tii,SWT.NONE,index);
    		treeitems.put(key, tiii);
    	} else {
    	    oldColor = tiii.getBackground();
    	}

    	Kind resultKind = result == null ? null : result.result();
    	String info = result == null ? "" : (" ["
    			+ (org.jmlspecs.openjml.Utils.testingMode ? "TIME" : String.format("%5.3f", result.duration())) 
    			+ " " + result.prover() + "] ");
    	tiii.removeAll();
    	String name = resultKind == null ? "" : resultKind.toString();
    	String padding = "      ";
    	padding = padding.substring(0,name.length() <= padding.length() ? padding.length()-name.length() : 0);
    	String alltext = resultKind == null ? text : ("[" + resultKind.toString() + "] " + text + info);
    	Color color = white;
    	{
    		Info iteminfo = new Info();
    		iteminfo.key = key;
    		iteminfo.proofResult = result;
    		if (sym != null) iteminfo.javaElement = iface.convertMethod((MethodSymbol)sym);
    		iteminfo.signature = key;
    		tiii.setData(iteminfo);
    	}
    	treece.remove(tiii);
    	if (resultKind == IProverResult.SAT || resultKind == IProverResult.POSSIBLY_SAT) {
    		alltext = ("[INVALID] " + text + info);
    		color = orange;
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
    			//tiii.setExpanded(true);
    		}
    	} else if (resultKind == IProverResult.UNSAT) {
    		alltext = ("[VALID]    " + text + info);
    		color = green;
    	} else if (resultKind == IProverResult.ERROR) {
    		color = red;
        } else if (resultKind == IProverResult.TIMEOUT) {
            color = pink;
    	} else if (resultKind == IProverResult.UNKNOWN) {
    		color = pink;
    	} else if (resultKind == IProverResult.INFEASIBLE) {
    		color = yellow;
    	} else if (resultKind == IProverResult.SKIPPED) {
    		color = blue;
    	} else if (resultKind == IProverResult.RUNNING) {
    		color = white;
    	} else if (resultKind == IProverResult.CANCELLED) {
    		color = blue;
    	} else if (resultKind == IProverResult.COMPLETED) {
    		return; // No change
    	} else if (resultKind == null) {
    		alltext = text;
    		color = white;
    	} else {
    		color = red;
    	}
    	tiii.setText(alltext);
    	tiii.setBackground(color);
    	
    	setSummaryColor(tii);
    	setSummaryColor(ti);
    	
    	// Show the item if (it did not exist)  
        //    || ((the user set the toggle to allow auto open) && (the color is changing on refresh))
        //    || ((the user set the toggle to allow auto open on Error) && (some sort of error occurred))
        boolean autoOpen = false;
    	if (!tiii_isNew) { // Don't bother checking the menu state if we are going to auto open anyway
    	    try {
    	        IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
    	        ICommandService csrv = (ICommandService) w.getService(ICommandService.class);
    	        Command command2 = csrv.getCommand("org.openjml.commands.ToggleAutoOpen"); //$NON-NLS-1$
                autoOpen = (Boolean) command2.getState(RegistryToggleState.STATE_ID).getValue() && !color.equals(oldColor);
//    	        Command command = csrv.getCommand("org.openjml.commands.RadioAutoOpen"); //$NON-NLS-1$
//    	        String radioState = (String) command.getState(RadioState.STATE_ID).getValue();
//                if ("Error".equals(radioState) && color != green && color != white) autoOpen = true;
//                if ("Auto".equals(radioState) && !color.equals(oldColor)) autoOpen = true;
    	    } catch (Exception e) {
    	        // Just in case something goes wrong
    	    }
    	}
        if (tiii_isNew || autoOpen) treeroot.getParent().showItem(tiii);
        if (resultKind != IProverResult.RUNNING && key.equals(Activator.utils().currentTraceViewUISignature(null))) {
            // Don't update if we are in a RUNNING state - we get spurious messages that the counterexample is out of date
            // FIXME - why is there any coujnterexample at all to update?
            updateCEView(tiii,false);
        }
    }
    
    private void setSummaryColor(TreeItem tii) {
        Color worst = palegreen;
        for (TreeItem t: tii.getItems()) {
            Color itemColor = t.getBackground();
            if (itemColor == null) continue;
            if (itemColor == red || itemColor == palered) worst = palered; 
            if (worst == palered) continue;
            if (itemColor == pink) worst = palered; 
            if (worst == palered) continue;
            if (itemColor == orange || itemColor == paleorange) worst = paleorange;
            if (worst == paleorange) continue;
            if (itemColor == yellow || itemColor == paleyellow) worst = paleyellow;
            if (worst == paleyellow) continue;
            if (itemColor == blue || itemColor == paleblue) worst = paleblue;
            if (itemColor == white) worst = white;
        }
        tii.setBackground(worst);
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

//    		IProject p = input.getFile().getProject();
//    		currentProject = p.hasNature(JavaCore.NATURE_ID) ? JavaCore.create(p) : null;

    		return true;
    	} catch (Exception e) {
    		return false;
    	}
    }
    
    public void toggleAutoOpen(boolean newValue) {
    }

    public void clearProofResults() {
    	if (currentProject != null) {
    		OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
        	if (iface != null) iface.clearProofResults(currentProject);
    	}
    	setProject(null);
    }
    
    public void setProject(IJavaProject jproject) {
    	if (currentProject == jproject && jproject != null) return;
    	currentProject = jproject;
    	treeitems.clear();
    	treece.clear();
    	treeroot.removeAll();
    	refresh();
    	selected = null;
    	selectedList.clear();
    }
    
    static Map<String,String> userText = new HashMap<>();
    {
    	userText.put("UNSAT", "VALID [UNSAT]");
    	userText.put("POSSIBLY_SAT", "INVALID [POSSIBLY_SAT]");
    }
    
    static String userText(String n) {
    	String r = userText.get(n);
    	return r == null ? n : r;
    }
    
    static public String exportProofResults(/*@ nullable */FileWriter output) {
    	try {
    		StringBuilder summary = new StringBuilder();
    		String spaces = "                                        "; //$NON-NLS-1$
    		final OpenJMLView view = Utils.findView();
    		if (view == null) return null;
    		if (output == null && view.currentProject == null) return null;
    		Map<String,Integer> counts = new HashMap<String,Integer>();
    		OpenJMLInterface iface = Activator.utils().getInterface(view.currentProject);
    		Map<String,IProverResult> proofResults = iface.getProofResults();
    		TreeSet<String> t = new TreeSet<String>(proofResults.keySet());
    		for (String s: t) {
    			String result = proofResults.get(s).result().toString();
    			String user = userText(result);
    			if (output != null) output.append(user + spaces.substring(0,25-user.length()) + s + Strings.eol);
    			Integer i = counts.get(result);
    			if (i == null) i = 1; else i = i + 1;
    			counts.put(result, i);
    		}
    		if (output != null) output.append(Strings.eol);
    		int total = 0;
    		
    		for (String result: new TreeSet<>(counts.keySet())) {
    			Integer k = counts.get(result);
    			total += k;
    			String number = k.toString();
    			summary.append(number + spaces.substring(0,5-number.length()) + Strings.space + userText(result) + Strings.eol);
    		}
    		if (t.size() != total) {
    			int diff = t.size()-total;
    			summary.append(diff + "    ?????" + Strings.eol);
    		}
    		
    		summary.append(t.size() + spaces.substring(0,5-Integer.toString(counts.size()).length()) + "  TOTAL" + Strings.eol); //$NON-NLS-1$
    		if (output != null) output.append(summary);

    		String timeSinceStartInSeconds = start == null ? null : String.format("%10.2f",((end != null ? end : new Date()).getTime() - start.getTime())/1000.0);
    		if (output != null && timeSinceStartInSeconds != null) output.append("TOTAL WALL CLOCK TIME = " + timeSinceStartInSeconds + " seconds").append(Strings.eol);
    		if (timeSinceStartInSeconds != null) summary.append("TOTAL TIME = " + timeSinceStartInSeconds + " seconds").append(Strings.eol);
    		
    		if (output != null) Activator.utils().showMessageInUI(null,"Proof results summary",summary.toString());

    		StringBuilder brief = new StringBuilder();
    		brief.append(t.size() - zeroifnull(counts.get("RUNNING")) - zeroifnull(counts.get("CANCELLED")));
    		brief.append(" [").append("VAL=").append(zeroifnull(counts.get("UNSAT")));
    		brief.append(" ").append("ERR=").append(zeroifnull(counts.get("ERROR")));
    		brief.append(" ").append("INV=").append(zeroifnull(counts.get("POSSIBLY_SAT")));
    		brief.append(" ").append("TIM=").append(zeroifnull(counts.get("TIMEOUT")));
    		brief.append(" ").append("INF=").append(zeroifnull(counts.get("INFEASIBLE")));
    		brief.append(" ").append("SKI=").append(zeroifnull(counts.get("SKIPPED")));
    		brief.append("] ");
    		if (timeSinceStartInSeconds != null) brief.append(timeSinceStartInSeconds + " sec");
    		return brief.toString();
    	} catch (IOException e) {
    		return null;
    	}
    }
    
    static public void importProofResults(/*@ nullable */FileReader input) {
    	try ( BufferedReader br = new BufferedReader(input)){
    		final OpenJMLView view = Utils.findView();
    		if (view == null) return ;
    		if (input == null && view.currentProject == null) return ;
    		OpenJMLInterface iface = Activator.utils().getInterface(view.currentProject);
    		Map<String,IProverResult> proofResults = iface.getProofResults();
    		String line = null;
    		String unknowns = "";
    		while ((line = br.readLine()) != null) {
    			String[] tokens = line.trim().split("[ ]+");
    			String t = tokens[0].replace("[","").replace("]","");
    			IProverResult pr;
    			switch (t) {
    			case "VALID": proofResults.put(tokens[2], new ProverResult(null,IProverResult.UNSAT,null)); break;
    			case "INVALID": proofResults.put(tokens[2], new ProverResult(null,IProverResult.SAT,null)); break;
    			case "TIMEOUT": proofResults.put(tokens[1], new ProverResult(null,IProverResult.TIMEOUT,null)); break;
    			case "SKIPPED": proofResults.put(tokens[1], new ProverResult(null,IProverResult.SKIPPED,null)); break;
    			case "ERROR": proofResults.put(tokens[1], new ProverResult(null,IProverResult.ERROR,null)); break;
    			case "RUNNING": proofResults.put(tokens[1], new ProverResult(null,IProverResult.RUNNING,null)); break;
    			case "CANCELLED": proofResults.put(tokens[1], new ProverResult(null,IProverResult.CANCELLED,null)); break;
    			case "INFEASIBLE": proofResults.put(tokens[1], new ProverResult(null,IProverResult.INFEASIBLE,null)); break;
//    			default:
//    				unknowns = unknowns + " " + tokens[0];
    			}
    		}
			view.refresh();
    	} catch (IOException e) {
    		return ;
    	}
    }
    
    static public Integer zeroifnull(Integer n) {
    	return n == null ? 0 : n;
    }
    
    public void clearSelectedProofResults() {
		OpenJMLInterface iface = Activator.utils().getInterface(currentProject);
    	for (TreeItem ti: selectedList) {
    		clearResults(iface,ti);
    	}
		treeroot.removeAll();
		treeitems.clear();
		treece.clear();
		refresh();
    	//selectedList.clear();
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
    java.util.List<TreeItem> selectedList = new java.util.ArrayList<>(10);

	@Override
	public void widgetSelected(SelectionEvent e) {
		TreeItem ti = selected = (TreeItem)e.item;
		boolean multi = (e.stateMask & SWT.MOD1) != 0;
		if (!multi) selectedList.clear();
		selectedList.add(ti);
		if (ti == null) return;
		updateCEView(ti,true);
	}
	
	public void updateCEView(TreeItem ti, boolean show) {
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
				if (ce instanceof Counterexample ) {
					String text = ((Counterexample)ce).traceText; // FIXME - change to method on interface
					Activator.utils().setTraceViewUI(null,info.signature,text,show);
					if (info.javaElement instanceof IMethod) {
						iface.highlightCounterexamplePath((IMethod)info.javaElement,info.proofResult,ce);
					}
					if (pi != ti) treece.put(pi, ce);
				} else {
					Kind k = pr.result();
					String desc = k == IProverResult.UNSAT ? "consistent" 
							: k == IProverResult.SAT ? "inconsistent"
							: k == IProverResult.POSSIBLY_SAT ? "probably inconsistent"
							: k.toString().toLowerCase();
					String text = (k == IProverResult.ERROR ? "Error occurred while checking method: "
	                         : "Method and its specifications are " + desc + ": ") 
								+ info.key;
					Object extra = pr.otherInfo();
					if (extra != null) text = text + Strings.eol + extra.toString();
					Activator.utils().setTraceViewUI(null, info.signature, text, show);
					treece.remove(pi);
				}
			}
		}
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) {
		widgetSelected(e);
	}

	/** Launches a Java editor for the method or class that was clicked */
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
