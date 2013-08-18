package org.jmlspecs.openjml.utils.ui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FileDialog;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.ButtonGroup;
import javax.swing.DefaultComboBoxModel;
import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JSeparator;
import javax.swing.JTextField;
import javax.swing.LayoutStyle.ComponentPlacement;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;
import javax.swing.border.EmptyBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import org.jmlspecs.openjml.utils.Prover;
import org.jmlspecs.openjml.utils.ProverValidator;
import org.jmlspecs.openjml.utils.ui.res.ApplicationMessages.ApplicationMessageKey;
import javax.swing.SwingConstants;
import java.awt.GridLayout;
import java.awt.GridBagLayout;
import java.awt.GridBagConstraints;
import java.awt.Insets;
import javax.swing.border.BevelBorder;
import javax.swing.border.EtchedBorder;
import com.jgoodies.forms.layout.FormLayout;
import com.jgoodies.forms.layout.ColumnSpec;
import com.jgoodies.forms.layout.RowSpec;
import com.jgoodies.forms.factories.FormFactory;
import javax.swing.BoxLayout;


public class ConfigureSMTProversDialog extends JDialog {
    
    static {
        //
        // The JDK on OS X will automatically set this up. On other platforms we do it explicitly.
        //
        try {
           if(System.getProperty("os.name").contains("OS X")==false){
               UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
           }
        } catch (Exception e) {
            // Not worth reporting this.
        }
    }
    
    public enum SMTPersistenceSetting {
        USER, PROJECT;
    }


    private final JPanel contentPanel = new JPanel();

    private JTextField   textFieldProverPath;

    private JButton      okButton;

    private JButton      cancelButton;

    private JLabel       statusMsg;

    private JComboBox    comboProver;
    private final ButtonGroup persistenceMode = new ButtonGroup();
    private JRadioButton setForUserRadioButton;
    private JRadioButton setForProjectRadioButton;
    


    /**
     * Launch the application.
     */
    public static void main(String[] args) {
        try {
            ConfigureSMTProversDialog dialog = new ConfigureSMTProversDialog();
            dialog.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
            dialog.setLocationRelativeTo(null);
            dialog.setVisible(true);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    /**
     * Create the dialog.
     */
    public ConfigureSMTProversDialog() {
        setResizable(false);
        
        setModal(true);
        
        setBounds(100, 100, 746, 451);
        getContentPane().setLayout(new BorderLayout());
        
                JPanel panel = new JPanel();
                getContentPane().add(panel, BorderLayout.NORTH);
                panel.setPreferredSize(new Dimension(10, 80));
                panel.setMinimumSize(new Dimension(10, 80));
                panel.setBackground(Color.WHITE);
                
                        JLabel lblConfigureOpenjml = new JLabel("Configure OpenJML");
                        lblConfigureOpenjml.setFont(new Font("Lucida Grande", Font.PLAIN, 25));
                        
                                JLabel lblNewLabel = new JLabel("");
                                lblNewLabel
                                        .setIcon(new ImageIcon(
                                                ConfigureSMTProversDialog.class
                                                        .getResource("/org/jmlspecs/openjml/utils/ui/res/jml-logo-small64.png")));
                                GroupLayout gl_panel = new GroupLayout(panel);
                                gl_panel.setHorizontalGroup(
                                    gl_panel.createParallelGroup(Alignment.LEADING)
                                        .addGroup(gl_panel.createSequentialGroup()
                                            .addContainerGap()
                                            .addComponent(lblConfigureOpenjml)
                                            .addPreferredGap(ComponentPlacement.RELATED, 450, Short.MAX_VALUE)
                                            .addComponent(lblNewLabel)
                                            .addContainerGap())
                                );
                                gl_panel.setVerticalGroup(
                                    gl_panel.createParallelGroup(Alignment.LEADING)
                                        .addGroup(gl_panel.createSequentialGroup()
                                            .addGroup(gl_panel.createParallelGroup(Alignment.LEADING)
                                                .addGroup(gl_panel.createSequentialGroup()
                                                    .addGap(24)
                                                    .addComponent(lblConfigureOpenjml))
                                                .addGroup(gl_panel.createSequentialGroup()
                                                    .addGap(8)
                                                    .addComponent(lblNewLabel)))
                                            .addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
                                );
                                panel.setLayout(gl_panel);
        contentPanel.setBorder(new EmptyBorder(5, 5, 5, 5));
        getContentPane().add(contentPanel, BorderLayout.CENTER);
        contentPanel.setLayout(new BorderLayout(0, 0));

        JPanel panel_1 = new JPanel();
        contentPanel.add(panel_1, BorderLayout.CENTER);

        JLabel lblNewLabel_1 = new JLabel(MessageUtil.getMessage(ApplicationMessageKey.MsgInvalidProverConfiguration));
        lblNewLabel_1.setHorizontalTextPosition(SwingConstants.LEADING);
        JLabel lblNewLabel_2 = new JLabel("Default Prover:");

        comboProver = new JComboBox();
        comboProver.setModel(new DefaultComboBoxModel(new String[] { "Z3 (version 4.3+)",
                "CVC4 (version 1.1+)", "Yices (version 2.1+)" }));

        final JLabel lblExecutable = new JLabel("Z3 Executable:");
        lblExecutable.setMaximumSize(new Dimension(110, 16));
        lblExecutable.setMinimumSize(new Dimension(110, 16));
        lblExecutable.setPreferredSize(new Dimension(110, 16));

        //
        // Updates the text of the executable label
        //
        comboProver.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {

                JComboBox c = ((JComboBox) e.getSource());

                // update the label
                lblExecutable.setText(String.format(MessageUtil
                        .getMessage(ApplicationMessageKey.MsgProverExecutable),
                        c.getSelectedItem().toString().split(" ")[0]));

                // clear the file
                textFieldProverPath.setText("");
                setErrorState();
            }
        });

        textFieldProverPath = new JTextField();
        
        textFieldProverPath.getDocument().addDocumentListener(new DocumentListener(){

            @Override
            public void insertUpdate(DocumentEvent e) { 
                validateProver();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                setErrorState();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                
            }
            
        });
        
        textFieldProverPath.setEditable(false);
        textFieldProverPath.setColumns(10);

        JButton btnBrowse = new JButton("Browse");

        //
        // Grab the correct path to the executable, perhaps try to validate it.
        //
        btnBrowse.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {

                // OS X requires special treatment to enable it to work like a
                // native application
                if (System.getProperty("os.name").contains("OS X")) {

                    JFrame frame = new JFrame();
                    System.setProperty("apple.awt.fileDialogForDirectories",
                            "true");
                    FileDialog d = new FileDialog(frame);
                    d.setVisible(true);
                    

                    if (d.getFile()!=null) {
                        String file = d.getFile();
                        String dir  = d.getDirectory();

                        textFieldProverPath.setText(dir + file);
                    } 
                    
                    

                } else {
                    final JFileChooser picker = new JFileChooser();
                    int result = picker
                            .showOpenDialog(ConfigureSMTProversDialog.this);

                    if (result == JFileChooser.APPROVE_OPTION) {
                        File f = picker.getSelectedFile();

                        textFieldProverPath.setText(f.getAbsolutePath());
                    } 
                }

            }
        });
        
        
        JSeparator separator = new JSeparator();

        statusMsg = new JLabel();
        
        setForProjectRadioButton = new JRadioButton("Set for this project only");
        persistenceMode.add(setForProjectRadioButton);
        
        setForUserRadioButton = new JRadioButton("Set as user default");
        persistenceMode.add(setForUserRadioButton);
        setForUserRadioButton.setSelected(true);
        GroupLayout gl_panel_1 = new GroupLayout(panel_1);
        gl_panel_1.setHorizontalGroup(
            gl_panel_1.createParallelGroup(Alignment.TRAILING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addGroup(gl_panel_1.createParallelGroup(Alignment.LEADING)
                        .addComponent(lblNewLabel_1, GroupLayout.DEFAULT_SIZE, 582, Short.MAX_VALUE)
                        .addGroup(gl_panel_1.createSequentialGroup()
                            .addComponent(lblNewLabel_2)
                            .addGap(40)
                            .addGroup(gl_panel_1.createParallelGroup(Alignment.LEADING)
                                .addComponent(comboProver, GroupLayout.PREFERRED_SIZE, 204, GroupLayout.PREFERRED_SIZE)
                                .addComponent(setForUserRadioButton)
                                .addComponent(setForProjectRadioButton)))
                        .addGroup(gl_panel_1.createSequentialGroup()
                            .addComponent(lblExecutable, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
                            .addGap(23)
                            .addGroup(gl_panel_1.createParallelGroup(Alignment.LEADING)
                                .addComponent(textFieldProverPath, GroupLayout.DEFAULT_SIZE, 367, Short.MAX_VALUE)
                                .addComponent(statusMsg))
                            .addPreferredGap(ComponentPlacement.RELATED)
                            .addComponent(btnBrowse))
                        .addComponent(separator, GroupLayout.DEFAULT_SIZE, 582, Short.MAX_VALUE))
                    .addGap(12))
        );
        gl_panel_1.setVerticalGroup(
            gl_panel_1.createParallelGroup(Alignment.LEADING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addComponent(lblNewLabel_1, GroupLayout.PREFERRED_SIZE, 82, GroupLayout.PREFERRED_SIZE)
                    .addPreferredGap(ComponentPlacement.RELATED)
                    .addGroup(gl_panel_1.createParallelGroup(Alignment.BASELINE)
                        .addComponent(lblNewLabel_2)
                        .addComponent(comboProver, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE))
                    .addPreferredGap(ComponentPlacement.RELATED)
                    .addComponent(setForUserRadioButton)
                    .addPreferredGap(ComponentPlacement.RELATED)
                    .addComponent(setForProjectRadioButton)
                    .addGap(18)
                    .addComponent(separator, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
                    .addGap(18)
                    .addGroup(gl_panel_1.createParallelGroup(Alignment.BASELINE)
                        .addComponent(lblExecutable, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
                        .addComponent(textFieldProverPath, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
                        .addComponent(btnBrowse))
                    .addPreferredGap(ComponentPlacement.RELATED)
                    .addComponent(statusMsg)
                    .addContainerGap(21, Short.MAX_VALUE))
        );
        panel_1.setLayout(gl_panel_1);
        {
            JPanel buttonPane = new JPanel();
            getContentPane().add(buttonPane, BorderLayout.SOUTH);
            buttonPane.setLayout(new BoxLayout(buttonPane, BoxLayout.Y_AXIS));
            
            JSeparator separator_1 = new JSeparator();
            separator_1.setSize(new Dimension(0, 2));
            separator_1.setMinimumSize(new Dimension(0, 2));
            separator_1.setMaximumSize(new Dimension(32767, 2));
            buttonPane.add(separator_1);
            {
                
                JPanel panel_2 = new JPanel();
                FlowLayout flowLayout = (FlowLayout) panel_2.getLayout();
                flowLayout.setAlignment(FlowLayout.RIGHT);
                buttonPane.add(panel_2);
                cancelButton = new JButton("Exit");
                panel_2.add(cancelButton);
                cancelButton.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        System.exit(1);
                    }
                });
                cancelButton.setActionCommand("Cancel");
                {
                    okButton = new JButton("Continue");
                    panel_2.add(okButton);
                    okButton.setEnabled(false);
                    okButton.addActionListener(new ActionListener() {
                        // continue, and optionally save the settings.
                        public void actionPerformed(ActionEvent e) {
                            dispose();
                        }
                    });
                    okButton.setActionCommand("OK");
                    getRootPane().setDefaultButton(okButton);
                }
            }
        }
        
        // start in the error state
        setErrorState();
    }
    
    public Prover getProver(){
        return Prover.getProver(comboProver.getSelectedItem().toString().split(" ")[0], textFieldProverPath.getText());
    }
    
    public SMTPersistenceSetting getPersistenceType(){
        
        if(getSetForUserRadioButton().isSelected()){
            return SMTPersistenceSetting.USER;
        }
        
        return SMTPersistenceSetting.PROJECT;
    }

    private void validateProver(){
        
        if(ProverValidator.proverValid(Prover.getProver(comboProver.getSelectedItem().toString().split(" ")[0], textFieldProverPath.getText()))){
            setSuccessState();
        }else{
            setErrorState();
        }
        
    }

    private void setErrorState() {
        statusMsg.setText(String.format(MessageUtil
                .getMessage(ApplicationMessageKey.MsgInvalidProverExecutable),
                comboProver.getSelectedItem().toString().split(" ")[0]));
        statusMsg.setForeground(Color.RED);
        okButton.setEnabled(false);

    }

    private void setSuccessState() {
        statusMsg.setText(String.format(MessageUtil
                .getMessage(ApplicationMessageKey.MsgValidProverExecutable),
                comboProver.getSelectedItem().toString().split(" ")[0]));
        statusMsg.setForeground(Color.GREEN);
        okButton.setEnabled(true);

    }
    public JRadioButton getSetForUserRadioButton() {
        return setForUserRadioButton;
    }
    public JRadioButton getSetForProjectRadioButton() {
        return setForProjectRadioButton;
    }
}
