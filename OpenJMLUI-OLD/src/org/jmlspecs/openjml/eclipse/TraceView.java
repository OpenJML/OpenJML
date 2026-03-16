package org.jmlspecs.openjml.eclipse;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;
import org.eclipse.ui.part.ViewPart;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;

// FIXME - needs scrollbars
public class TraceView extends ViewPart {

    public static final String ID = "org.openjml.traceview"; //$NON-NLS-1$
    
//    Document doc;
    
//    String currentFileName;
//    String currentFilePath;
//    IProject project;
    IPartListener aListener;
//    Label lblFileName;
    
    MessageConsole speedyConsole;
    MessageConsoleStream msgOut;
    
//    private Action updateExpressionsAll;
//    private Action updateExpressionsCS;
//    private Action updateExpressionsDaikon;
//    private Action clearExpressions;
//    private Action reloadExpressions;
//    private Action processExpressions;
//    private Action processExpressionsWP;
//    private Action saveExpressions;
    
    public String signature;
    Text text;
    
    public TraceView() {
    }
    

    /**
     * Create contents of the view part.
     * @param parent
     */
    @Override
    public void createPartControl(Composite parent) {
        
        this.setPartName("OpenJML Trace");
        Composite container = new Composite(parent, SWT.NONE);
        GridLayout gridLayout = new GridLayout(1, true);
        gridLayout.marginWidth = 0;
        gridLayout.marginHeight = 0;
        container.setLayout(gridLayout);
        
        text = new Text(container, SWT.MULTI|SWT.V_SCROLL|SWT.H_SCROLL|SWT.BORDER|SWT.READ_ONLY);
        GridData gridData = new GridData(GridData.FILL, GridData.FILL, true, true);
        text.setLayoutData(gridData);
        text.setText("<no data>");
        
        refresh();
        
//        aListener = new IPartListener(){
//
//            @Override
//            public void partActivated(IWorkbenchPart part) {
//                if(part instanceof IEditorInput){
////                    if(getCurrentFileData()) {
////                        populateTable();
////                    }
//                }
//            }
//
//            @Override
//            public void partBroughtToTop(IWorkbenchPart part) {
//                if(part instanceof IEditorInput){
////                    if(getCurrentFileData()) {
////                        populateTable();
////                    }
//                }
//            }
//
//            @Override
//            public void partClosed(IWorkbenchPart part) {}
//
//            @Override
//            public void partDeactivated(IWorkbenchPart part) {}
//
//            @Override
//            public void partOpened(IWorkbenchPart part) {}
//        };
//        PlatformUI.getWorkbench().getActiveWorkbenchWindow().getPartService().addPartListener(aListener);
//        
        createActions();
        initializeToolBar();
    }
    
    /** Refreshes the view - must be called from the UI thread */
    public void refresh() {
    	OpenJMLView view =  Activator.utils().showView();
    	if (view == null) {
    		Activator.utils().showMessageInUI(null,"OpenJML","Could not locate view");
    		return;
    	}
        IJavaProject p = view.currentProject;
        if (p != null) Activator.utils().setTraceViewUI(this,p);
    }
    
    
    /**
     * Create the actions.
     */
    private void createActions() {
//        updateExpressionsCS = new Action("Get From CodeSonar"){
//            public void run(){
//                String hub = Preferences.getHubUrl(project);
//                Integer aid = ProjectData.getAnalysisId(project);
//                if (aid != null) {
//                	String[] args = {
//                        "-codesonar",
//                        "-hub",
//                        hub,
//                        "-id",
//                        aid.toString(),
//                        "-fetch",
//                        currentFilePath};
//                	updateExpressions(args);
//                } else {
//                	String[] args = {
//                        "-codesonar",
//                        "-hub",
//                        hub,
//                        "-fetch",
//                        currentFilePath};
//                	updateExpressions(args);
//                }
//            }
//        };
    }

    /**
     * Initialize the toolbar.
     */
    private void initializeToolBar() { // FIXME - does this really do anything?
        getViewSite().getActionBars().getToolBarManager();
    }


//    public void dispose(){
//        PlatformUI.getWorkbench()
//                  .getActiveWorkbenchWindow()
//                  .getPartService()
//                  .removePartListener(aListener);
//    }
    
    // Required method
    @Override
    public void setFocus() {
    }
    
    public void setText(String methodName, String t) {
        signature = methodName;
    	if (methodName == null) {
            this.setPartName("OpenJML Trace");
            text.setText("<no method specified>");
    	} else {
    		this.setPartName("Trace: " + methodName);
    		text.setText(t == null ? "<no trace information>" : t);
    	}
    	text.update();
    	this.setFocus();
    }

}
