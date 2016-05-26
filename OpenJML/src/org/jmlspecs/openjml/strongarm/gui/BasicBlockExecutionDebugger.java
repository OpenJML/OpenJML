package org.jmlspecs.openjml.strongarm.gui;

import java.awt.BorderLayout;
import java.awt.FlowLayout;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.border.EmptyBorder;
import javax.swing.JTextField;
import javax.swing.JSplitPane;
import javax.swing.JScrollPane;
import javax.swing.JTextPane;
import javax.swing.border.TitledBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Document;
import javax.swing.text.Highlighter;
import javax.swing.text.Style;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import javax.swing.JOptionPane;

import org.jmlspecs.openjml.JmlTree.JmlMethodSpecs;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;
import org.jmlspecs.openjml.strongarm.TraceElement;

import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;

import java.awt.Dimension;
import java.awt.Font;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.DefaultListModel;
import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.LayoutStyle.ComponentPlacement;
import javax.swing.JTextArea;
import javax.swing.JList;
import javax.swing.border.EtchedBorder;
import java.awt.Color;
import javax.swing.JComboBox;
import javax.swing.JLabel;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.ListSelectionEvent;
import java.awt.event.ItemListener;
import java.awt.event.ItemEvent;

public class BasicBlockExecutionDebugger extends JDialog {

    private final JPanel contentPanel = new JPanel();
    private JTextPane basicBlocks;
    private JTextPane ast;
    private JTextArea log;
    private JComboBox currentLabel;
    private JList executionPlan;
    private List<TraceElement> traceData;

    /**
     * Launch the application.
     */
    public static void main(String[] args) {
        try {
            

            
            BasicBlockExecutionDebugger dialog = new BasicBlockExecutionDebugger();
            dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
            dialog.setModal(true);
            dialog.setVisible(true);

        } catch (Exception e) {
            e.printStackTrace();
        }
    }
    
    
    public static void trace(JCBlock transformedAST, BasicProgram blockForm, List<BasicBlock> allBlocks, List<TraceElement> trace, JmlMethodSpecs specs, String oldContract){
        
        BasicBlockExecutionDebugger dialog = new BasicBlockExecutionDebugger();
        
        dialog.loadTrace(transformedAST, blockForm, allBlocks, trace, specs, oldContract);
        
        dialog.setModal(true);
        dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
        dialog.setVisible(true);
        
    }

    public void loadTrace(JCBlock transformedAST, BasicProgram blockForm, List<BasicBlock> allBlocks, List<TraceElement> trace, JmlMethodSpecs specs, String oldContract){
        
        traceData = trace;
        
        getAst().setText(transformedAST.toString());
        getBasicBlocks().setText(blockForm.toString());

        // the execution plan
        
        DefaultListModel listModel = new DefaultListModel();
        

        for(BasicBlock b : allBlocks){
            currentLabel.addItem(b.id().toString());
        }

        // walk through the execution plan
        for(TraceElement e : trace){
            listModel.addElement(e.getBlock().id().toString());    
        }
        
        
        // a list of all blocks.
        getExecutionPlan().setModel(listModel);
        
        
        Style style = getBasicBlocks().addStyle("Red", null);
        StyleConstants.setForeground(style, Color.RED);
        StyleConstants.setBold(style, true);
        
        Style style2 = getBasicBlocks().addStyle("Blue", null);
        StyleConstants.setForeground(style2, Color.BLUE);
        StyleConstants.setBold(style2, true);
        

        highlightRegex("BL_.*:", blockForm.toString(), "Red");
        highlightRegex("assert", blockForm.toString(), "Blue");
        highlightRegex("assume", blockForm.toString(), "Blue");
        highlightRegex("goto", blockForm.toString(), "Blue");
        highlightRegex("follows", blockForm.toString(), "Blue");
        
        
        getContract().setText(oldContract + "\n\n-----------\n\n\n" + specs.toString());
        
        
        
    }
    static Color highlightColor = new Color(255,255,0,150);

    static DefaultHighlighter.DefaultHighlightPainter painter = new DefaultHighlighter.DefaultHighlightPainter(highlightColor);
    private JTextArea contract;

    private void setSelectedLabel(String l){

        // find the start of the label
        Pattern pattern = Pattern.compile("BL_.*:");
        Matcher matcher = pattern.matcher(getBasicBlocks().getText());

        Highlighter hilite = getBasicBlocks().getHighlighter();
        
        int start = -1;
        int end   = -1;
        
        Highlighter.Highlight[] hilites = hilite.getHighlights();

        for (int i = 0; i < hilites.length; i++) {
            if (hilites[i].getPainter() instanceof DefaultHighlighter.DefaultHighlightPainter) {
                hilite.removeHighlight(hilites[i]);
            }
        }
        
        while (matcher.find()) {            

            
            
            if(start!=-1){
                end = matcher.start()-1;
                break;
            }else{
                if(matcher.group().equals(l + ":")){
                    start = matcher.start();
                }
            }
                
        }
        try {
            if(end==-1){
                end = getBasicBlocks().getText().length();
            }
            hilite.addHighlight(start,  end, painter);
            
            getBasicBlocks().setCaretPosition(start);
        } catch (BadLocationException e) {
            //e.printStackTrace();
        }
    }
    
    private void highlightRegex(String regex, String text, String color){

        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(text);

        StyledDocument doc = (StyledDocument) getBasicBlocks().getDocument();
        
        while (matcher.find()) {            
            doc.setCharacterAttributes(matcher.start(), matcher.end()- matcher.start(), getBasicBlocks().getStyle(color), true);
        }
    }
    
    private void updateExecutionResult(){
        
        int idx = getExecutionPlan().getSelectedIndex();
        
        TraceElement traceElement = traceData.get(idx);
        
        StringBuffer buff = new StringBuffer();
        
        for(JCExpression e : traceElement.getExprs()){
            buff.append("Added Expression: " + e.toString() + "\n");
        }
        
        log.setText(buff.toString());
        
    }
    /**
     * Create the dialog.
     */
    public BasicBlockExecutionDebugger() {
        setBounds(100, 100, 834, 547);
        getContentPane().setLayout(new BorderLayout());
        contentPanel.setBorder(new EmptyBorder(5, 5, 5, 5));
        getContentPane().add(contentPanel, BorderLayout.CENTER);
        
        JSplitPane splitPane_3 = new JSplitPane();
        splitPane_3.setResizeWeight(1.0);
        
        JPanel panel_1 = new JPanel();
        splitPane_3.setRightComponent(panel_1);
        panel_1.setPreferredSize(new Dimension(500, 10));
        
        JLabel lblExecutionPlan = new JLabel("Execution Plan");
        
        JSplitPane splitPane_2 = new JSplitPane();
        splitPane_2.setBorder(null);
        splitPane_2.setOrientation(JSplitPane.VERTICAL_SPLIT);
        GroupLayout gl_panel_1 = new GroupLayout(panel_1);
        gl_panel_1.setHorizontalGroup(
            gl_panel_1.createParallelGroup(Alignment.LEADING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addGroup(gl_panel_1.createParallelGroup(Alignment.LEADING)
                        .addComponent(splitPane_2, GroupLayout.DEFAULT_SIZE, 294, Short.MAX_VALUE)
                        .addGroup(gl_panel_1.createSequentialGroup()
                            .addComponent(lblExecutionPlan)
                            .addContainerGap(202, Short.MAX_VALUE))))
        );
        gl_panel_1.setVerticalGroup(
            gl_panel_1.createParallelGroup(Alignment.LEADING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addComponent(lblExecutionPlan)
                    .addPreferredGap(ComponentPlacement.RELATED)
                    .addComponent(splitPane_2, GroupLayout.DEFAULT_SIZE, 487, Short.MAX_VALUE))
        );
        
        JScrollPane scrollPane_2 = new JScrollPane();
        splitPane_2.setLeftComponent(scrollPane_2);
        
        executionPlan = new JList();
        scrollPane_2.setViewportView(executionPlan);
        
        contract = new JTextArea();
        contract.setFont(new Font("Courier", Font.PLAIN, 13));
        splitPane_2.setRightComponent(contract);
        executionPlan.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                setSelectedLabel(executionPlan.getSelectedValue().toString());
                
                updateExecutionResult();
            }
        });
        splitPane_2.setDividerLocation(200);
        
        panel_1.setLayout(gl_panel_1);
        
        JSplitPane splitPane = new JSplitPane();
        splitPane.setResizeWeight(1.0);
        splitPane_3.setLeftComponent(splitPane);
        splitPane.setBorder(null);
        splitPane.setOrientation(JSplitPane.VERTICAL_SPLIT);
        
        JPanel panel = new JPanel();
        panel.setBorder(null);
        splitPane.setLeftComponent(panel);
        panel.setLayout(new BorderLayout(0, 0));
        
        JSplitPane splitPane_1 = new JSplitPane();
        splitPane_1.setBorder(null);
        panel.add(splitPane_1, BorderLayout.CENTER);
        
        JScrollPane scrollPane = new JScrollPane();
        splitPane_1.setLeftComponent(scrollPane);
        
        ast = new JTextPane();
        ast.setFont(new Font("Courier", Font.PLAIN, 13));
        scrollPane.setViewportView(ast);
        
        JScrollPane scrollPane_1 = new JScrollPane();
        splitPane_1.setRightComponent(scrollPane_1);
        
        basicBlocks = new JTextPane();
        basicBlocks.setFont(new Font("Courier", Font.PLAIN, 13));
        scrollPane_1.setViewportView(basicBlocks);
        splitPane_1.setDividerLocation(200);
        
        currentLabel = new JComboBox();
        currentLabel.addItemListener(new ItemListener() {
            public void itemStateChanged(ItemEvent e) {
                setSelectedLabel(currentLabel.getSelectedItem().toString());
            }
        });
        contentPanel.setLayout(new BorderLayout(0, 0));
        panel.add(currentLabel, BorderLayout.NORTH);
        
        log = new JTextArea();
        log.setFont(new Font("Courier", Font.PLAIN, 13));
        splitPane.setRightComponent(log);
        splitPane.setDividerLocation(400);
        contentPanel.add(splitPane_3);
        splitPane_3.setDividerLocation(500);
    }
    public JTextPane getBasicBlocks() {
        return basicBlocks;
    }
    public JTextPane getAst() {
        return ast;
    }
    public JTextArea getLog() {
        return log;
    }
    public JComboBox getCurrentLabel() {
        return currentLabel;
    }
    public JList getExecutionPlan() {
        return executionPlan;
    }
    public JTextArea getContract() {
        return contract;
    }
}
