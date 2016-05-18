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
import javax.swing.JOptionPane;
import org.jmlspecs.openjml.esc.BasicProgram;
import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;

import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCExpression;

import java.awt.Dimension;
import java.awt.Font;
import java.util.ArrayList;
import java.util.List;

import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.LayoutStyle.ComponentPlacement;
import javax.swing.JTextArea;
import javax.swing.JList;
import javax.swing.border.EtchedBorder;
import java.awt.Color;
import javax.swing.JComboBox;
import javax.swing.JLabel;

public class BasicBlockExecutionDebugger extends JDialog {

    private final JPanel contentPanel = new JPanel();
    private JTextPane basicBlocks;
    private JTextPane ast;
    private JTextArea log;
    private JScrollPane executionPlan;
    private JComboBox currentLabel;

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
    
    class TraceElement {
        private List<JCExpression> exprs = new ArrayList<JCExpression>();
        private BasicBlock block;
        public TraceElement(BasicBlock block){
            this.block = block;
        }
        
        public void addExpr(JCExpression expr){
            exprs.add(expr);
        }
        
        public BasicBlock getBlock(){
            return this.block;
        }
        public List<JCExpression> getExprs(){
            return this.exprs;
        }
    }
    
    public static void trace(JCBlock transformedAST, BasicProgram blockForm, List<BasicBlock> allBlocks, List<TraceElement> trace){
        new BasicBlockExecutionDebugger().loadTrace(transformedAST, blockForm, allBlocks, trace);
    }

    public void loadTrace(JCBlock transformedAST, BasicProgram blockForm, List<BasicBlock> allBlocks, List<TraceElement> trace){
        
        // TODO - update the AST
        
        // Update the block program.
        //getBasicBlocks().setText(blockForm.toString());
        
        
        
         BasicBlockExecutionDebugger dialog = new BasicBlockExecutionDebugger();
         dialog.setModal(true);
         dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
         dialog.setVisible(true);
        
    }
    
    /**
     * Create the dialog.
     */
    public BasicBlockExecutionDebugger() {
        setBounds(100, 100, 834, 547);
        getContentPane().setLayout(new BorderLayout());
        contentPanel.setBorder(new EmptyBorder(5, 5, 5, 5));
        getContentPane().add(contentPanel, BorderLayout.CENTER);
        contentPanel.setLayout(new BorderLayout(0, 0));
        
        JSplitPane splitPane = new JSplitPane();
        splitPane.setOrientation(JSplitPane.VERTICAL_SPLIT);
        contentPanel.add(splitPane, BorderLayout.CENTER);
        
        JPanel panel = new JPanel();
        splitPane.setLeftComponent(panel);
        panel.setLayout(new BorderLayout(0, 0));
        
        JSplitPane splitPane_1 = new JSplitPane();
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
        panel.add(currentLabel, BorderLayout.NORTH);
        
        log = new JTextArea();
        log.setFont(new Font("Courier", Font.PLAIN, 13));
        splitPane.setRightComponent(log);
        splitPane.setDividerLocation(400);
        
        JPanel panel_1 = new JPanel();
        panel_1.setPreferredSize(new Dimension(300, 10));
        contentPanel.add(panel_1, BorderLayout.EAST);
        
        JLabel lblExecutionPlan = new JLabel("Execution Plan");
        
        executionPlan =  new JScrollPane();
        GroupLayout gl_panel_1 = new GroupLayout(panel_1);
        gl_panel_1.setHorizontalGroup(
            gl_panel_1.createParallelGroup(Alignment.TRAILING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addComponent(lblExecutionPlan)
                    .addContainerGap(202, Short.MAX_VALUE))
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                    .addComponent(executionPlan, GroupLayout.PREFERRED_SIZE, 288, GroupLayout.PREFERRED_SIZE)
                    .addContainerGap())
        );
        gl_panel_1.setVerticalGroup(
            gl_panel_1.createParallelGroup(Alignment.LEADING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addComponent(lblExecutionPlan)
                    .addPreferredGap(ComponentPlacement.RELATED)
                    .addComponent(executionPlan, GroupLayout.DEFAULT_SIZE, 481, Short.MAX_VALUE)
                    .addContainerGap())
        );
        panel_1.setLayout(gl_panel_1);
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
    public JScrollPane getExecutionPlan() {
        return executionPlan;
    }
    public JComboBox getCurrentLabel() {
        return currentLabel;
    }
}
