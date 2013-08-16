package org.jmlspecs.openjml.utils.ui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dialog;
import java.awt.Dimension;
import java.awt.FileDialog;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;

import javax.swing.DefaultComboBoxModel;
import javax.swing.GroupLayout;
import javax.swing.GroupLayout.Alignment;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSeparator;
import javax.swing.JTextField;
import javax.swing.LayoutStyle.ComponentPlacement;
import javax.swing.border.EmptyBorder;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

import org.jmlspecs.openjml.utils.Prover;
import org.jmlspecs.openjml.utils.ProverValidator;
import org.jmlspecs.openjml.utils.ui.res.ApplicationMessages.ApplicationMessageKey;
import javax.swing.JRadioButton;
import javax.swing.ButtonGroup;


public class ConfigureSMTProversDialog extends JDialog {
    
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
        
        setModal(true);
        
        setBounds(100, 100, 616, 444);
        getContentPane().setLayout(new BorderLayout());
        contentPanel.setBorder(new EmptyBorder(5, 5, 5, 5));
        getContentPane().add(contentPanel, BorderLayout.CENTER);
        contentPanel.setLayout(new BorderLayout(0, 0));

        JPanel panel = new JPanel();
        panel.setPreferredSize(new Dimension(10, 80));
        panel.setMinimumSize(new Dimension(10, 80));
        panel.setBackground(Color.WHITE);
        contentPanel.add(panel, BorderLayout.NORTH);

        JLabel lblConfigureOpenjml = new JLabel("Configure OpenJML");
        lblConfigureOpenjml.setFont(new Font("Lucida Grande", Font.PLAIN, 25));

        JLabel lblNewLabel = new JLabel("");
        lblNewLabel
                .setIcon(new ImageIcon(
                        ConfigureSMTProversDialog.class
                                .getResource("/org/jmlspecs/openjml/utils/ui/res/jml-logo-small64.png")));
        GroupLayout gl_panel = new GroupLayout(panel);
        gl_panel.setHorizontalGroup(gl_panel.createParallelGroup(
                Alignment.LEADING).addGroup(
                Alignment.TRAILING,
                gl_panel.createSequentialGroup()
                        .addContainerGap()
                        .addComponent(lblConfigureOpenjml)
                        .addPreferredGap(ComponentPlacement.RELATED, 235,
                                Short.MAX_VALUE).addComponent(lblNewLabel)
                        .addContainerGap()));
        gl_panel.setVerticalGroup(gl_panel
                .createParallelGroup(Alignment.LEADING)
                .addGroup(
                        gl_panel.createSequentialGroup()
                                .addGroup(
                                        gl_panel.createParallelGroup(
                                                Alignment.LEADING)
                                                .addGroup(
                                                        gl_panel.createSequentialGroup()
                                                                .addContainerGap()
                                                                .addComponent(
                                                                        lblNewLabel))
                                                .addGroup(
                                                        gl_panel.createSequentialGroup()
                                                                .addGap(25)
                                                                .addComponent(
                                                                        lblConfigureOpenjml)))
                                .addContainerGap(10, Short.MAX_VALUE)));
        panel.setLayout(gl_panel);

        JPanel panel_1 = new JPanel();
        contentPanel.add(panel_1, BorderLayout.WEST);

        JLabel lblNewLabel_1 = new JLabel(MessageUtil.getMessage(ApplicationMessageKey.MsgInvalidProverConfiguration));
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
            gl_panel_1.createParallelGroup(Alignment.LEADING)
                .addGroup(gl_panel_1.createSequentialGroup()
                    .addContainerGap()
                    .addGroup(gl_panel_1.createParallelGroup(Alignment.LEADING)
                        .addComponent(lblNewLabel_1, GroupLayout.DEFAULT_SIZE, 594, Short.MAX_VALUE)
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
                        .addComponent(separator, GroupLayout.DEFAULT_SIZE, 594, Short.MAX_VALUE))
                    .addContainerGap())
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
                    .addContainerGap(349, Short.MAX_VALUE))
        );
        panel_1.setLayout(gl_panel_1);
        {
            JPanel buttonPane = new JPanel();
            buttonPane.setLayout(new FlowLayout(FlowLayout.RIGHT));
            getContentPane().add(buttonPane, BorderLayout.SOUTH);
            {
                cancelButton = new JButton("Exit");
                cancelButton.addActionListener(new ActionListener() {
                    public void actionPerformed(ActionEvent e) {
                        System.exit(1);
                    }
                });
                cancelButton.setActionCommand("Cancel");
                buttonPane.add(cancelButton);
            }
            {
                okButton = new JButton("Continue");
                okButton.setEnabled(false);
                okButton.addActionListener(new ActionListener() {
                    // continue, and optionally save the settings.
                    public void actionPerformed(ActionEvent e) {
                        dispose();
                    }
                });
                okButton.setActionCommand("OK");
                buttonPane.add(okButton);
                getRootPane().setDefaultButton(okButton);
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
