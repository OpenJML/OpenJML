package org.jmlspecs.openjml.utils.ui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import com.sun.tools.javac.tree.JCTree;


public class ASTView extends JPanel {
	public ASTView() {
		initComponents();
	}

	private void initComponents() {
	    astPanel = new ASTPanel(this.root); 
		panel3 = new JPanel();
		label1 = new JLabel();
		splaySlider = new JSlider();
		showExtended = new JCheckBox();
		splitPane1 = new JSplitPane();
		panel7 = new JPanel();
		panel8 = new JPanel();
		label4 = new JLabel();
		astTitle = new JLabel();
		panel9 = new JPanel();
		label2 = new JLabel();
		filterText = new JTextField();
		popOut = new JButton();
		separator1 = new JSeparator();
		astPane = new JScrollPane();
		panel4 = new JPanel();
		panel5 = new JPanel();
		label3 = new JLabel();
		panel6 = new JPanel();
		button2 = new JButton();
		scrollPane4 = new JScrollPane();
		astSource = new JTextPane();

		//======== this ========

		
		setLayout(new BorderLayout());

		//======== panel3 ========
		{
			panel3.setLayout(new FlowLayout(FlowLayout.LEFT));

			//---- label1 ----
			label1.setText("Tree Splay");
			label1.setHorizontalAlignment(SwingConstants.CENTER);
			panel3.add(label1);
			panel3.add(splaySlider);

			//---- showExtended ----
			showExtended.setText("Show Extended Properties?");
			panel3.add(showExtended);
		}
		add(panel3, BorderLayout.SOUTH);

		//======== splitPane1 ========
		{
			splitPane1.setOrientation(JSplitPane.VERTICAL_SPLIT);
			splitPane1.setDividerLocation(200);
			splitPane1.setLastDividerLocation(200);

			//======== panel7 ========
			{
				panel7.setLayout(new BoxLayout(panel7, BoxLayout.Y_AXIS));

				//======== panel8 ========
				{
					panel8.setBorder(null);
					panel8.setMaximumSize(new Dimension(2147483647, 16));
					panel8.setLayout(new GridBagLayout());
					((GridBagLayout)panel8.getLayout()).columnWidths = new int[] {0, 0, 0, 0};
					((GridBagLayout)panel8.getLayout()).rowHeights = new int[] {0, 0};
					((GridBagLayout)panel8.getLayout()).columnWeights = new double[] {0.0, 0.0, 0.0, 1.0E-4};
					((GridBagLayout)panel8.getLayout()).rowWeights = new double[] {0.0, 1.0E-4};

					//---- label4 ----
					label4.setText("AST View");
					panel8.add(label4, new GridBagConstraints(0, 0, 1, 1, 0.0, 0.0,
						GridBagConstraints.CENTER, GridBagConstraints.BOTH,
						new Insets(0, 0, 0, 5), 0, 0));

					//---- astTitle ----
					astTitle.setText("text");
					astTitle.setForeground(Color.red);
					panel8.add(astTitle, new GridBagConstraints(1, 0, 1, 1, 0.0, 0.0,
						GridBagConstraints.CENTER, GridBagConstraints.BOTH,
						new Insets(0, 0, 0, 5), 0, 0));

					//======== panel9 ========
					{
						panel9.setLayout(new FlowLayout(FlowLayout.RIGHT));

						//---- label2 ----
						label2.setText("Filter:");
						panel9.add(label2);

						//---- filterText ----
						filterText.setMinimumSize(new Dimension(200, 20));
						filterText.setPreferredSize(new Dimension(200, 20));
						panel9.add(filterText);

						//---- popOut ----
						popOut.setText("Pop Out");
						panel9.add(popOut);
					}
					panel8.add(panel9, new GridBagConstraints(2, 0, 1, 1, 1.0, 0.0,
						GridBagConstraints.CENTER, GridBagConstraints.BOTH,
						new Insets(0, 0, 0, 0), 0, 0));
				}
				panel7.add(panel8);
				panel7.add(separator1);
				panel7.add(astPane);
			}
			splitPane1.setTopComponent(panel7);

			//======== panel4 ========
			{
				panel4.setLayout(new BoxLayout(panel4, BoxLayout.Y_AXIS));

				//======== panel5 ========
				{
					panel5.setBorder(new SoftBevelBorder(SoftBevelBorder.LOWERED));
					panel5.setMaximumSize(new Dimension(2147483647, 16));
					panel5.setLayout(new GridBagLayout());
					((GridBagLayout)panel5.getLayout()).columnWidths = new int[] {0, 0, 0};
					((GridBagLayout)panel5.getLayout()).rowHeights = new int[] {0, 0};
					((GridBagLayout)panel5.getLayout()).columnWeights = new double[] {0.0, 0.0, 1.0E-4};
					((GridBagLayout)panel5.getLayout()).rowWeights = new double[] {0.0, 1.0E-4};

					//---- label3 ----
					label3.setText("AST Source");
					panel5.add(label3, new GridBagConstraints(0, 0, 1, 1, 0.0, 0.0,
						GridBagConstraints.CENTER, GridBagConstraints.BOTH,
						new Insets(0, 0, 0, 5), 0, 0));

					//======== panel6 ========
					{
						panel6.setLayout(new FlowLayout(FlowLayout.RIGHT));

						//---- button2 ----
						button2.setText("Help");
						panel6.add(button2);
					}
					panel5.add(panel6, new GridBagConstraints(1, 0, 1, 1, 1.0, 0.0,
						GridBagConstraints.CENTER, GridBagConstraints.BOTH,
						new Insets(0, 0, 0, 0), 0, 0));
				}
				panel4.add(panel5);

				//======== scrollPane4 ========
				{
					scrollPane4.setViewportView(astSource);
				}
				panel4.add(scrollPane4);
			}
			splitPane1.setBottomComponent(panel4);
		}
		add(splitPane1, BorderLayout.CENTER);
		
		astSource.setText(root.children.get(0).data.get(0).toString());

        astPane.setViewportView(astPanel);
        splaySlider.setMaximum(5000);
        splaySlider.setMinimum(10);
        splaySlider.setValue(astPanel.getSpan());
        splaySlider.addChangeListener(new ChangeListener(){

            @Override
            public void stateChanged(ChangeEvent arg0) {
                
                astPanel.setSplay(splaySlider.getValue());
            }
            
        });
        
        showExtended.addChangeListener(new ChangeListener(){

            @Override
            public void stateChanged(ChangeEvent arg0) {
                astPanel.setShowExtended(showExtended.isSelected());
            }
            
        });
        
        filterText.addKeyListener(new KeyListener(){

            @Override
            public void keyPressed(KeyEvent arg0) {
            }

            @Override
            public void keyReleased(KeyEvent arg0) {
                astPanel.setFilter(filterText.getText());
            }

            @Override
            public void keyTyped(KeyEvent arg0) {
            }
            
        });
        
        popOut.addActionListener(new ActionListener(){

            @Override
            public void actionPerformed(ActionEvent arg0) {
                JFrame c = new JFrame();
                
                c.setTitle(title);
                c.setLayout(new BorderLayout());
                
                ASTView v = new ASTView(title, astRoot);
                
                c.getContentPane().add(v, BorderLayout.CENTER);
                
                c.pack();
                c.setVisible(true);
            }
            
        });
		
	}

	private JPanel panel3;
	private JLabel label1;
	private JSlider splaySlider;
	private JCheckBox showExtended;
	private JSplitPane splitPane1;
	private JPanel panel7;
	private JPanel panel8;
	private JLabel label4;
	private JLabel astTitle;
	private JPanel panel9;
	private JLabel label2;
	private JTextField filterText;
	private JButton popOut;
	private JSeparator separator1;
	private JScrollPane astPane;
	private JPanel panel4;
	private JPanel panel5;
	private JLabel label3;
	private JPanel panel6;
	private JButton button2;
	private JScrollPane scrollPane4;
	private JTextPane astSource;
	private ASTPanel astPanel;
    private ASTTreeNode root;
    
    private String title;
    private JCTree astRoot;
	
    public ASTView(String title, JCTree root) {
        ASTVisitor v = new ASTVisitor();
        v.scan(root);
       
        this.root = v.root;
        initComponents();
        astTitle.setText("(" + title + ")");
        
        this.title = title;
        this.astRoot = root;
    }

}
