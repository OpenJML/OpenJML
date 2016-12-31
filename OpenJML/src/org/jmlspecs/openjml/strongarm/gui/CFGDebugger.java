package org.jmlspecs.openjml.strongarm.gui;

import java.awt.EventQueue;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;

import org.jmlspecs.openjml.esc.BasicProgram.BasicBlock;

import java.awt.BorderLayout;
import java.awt.Dimension;

public class CFGDebugger {

    private JFrame frame;
    final protected List<BasicBlock>       blocks;
    

    class CFGPanel extends JPanel {
        
        public CFGPanel(){
            
            
            
        }
        public Dimension getPreferredSize() {
            return new Dimension(250,200);
        }

        public void paintComponent(Graphics g) {
            super.paintComponent(g);       

            Graphics2D g2 = (Graphics2D) g;

            
        
        } 
    }
    
    
    
    /**
     * Launch the application.
     */
    public static void main(String[] args) {
        EventQueue.invokeLater(new Runnable() {
            public void run() {
                try {
                    CFGDebugger window = new CFGDebugger(null);
                    window.frame.setVisible(true);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        });
    }

    /**
     * Create the application.
     */
    public CFGDebugger(List<BasicBlock> blocks) {
        this.blocks = blocks;

        initialize();
        
    }
    
    private String getDot(){

        StringBuffer buff = new StringBuffer();
        
        buff.append("digraph BST {\n");
        
        for(int i=0; i < blocks.size(); i++){
            BasicBlock b = blocks.get(i);
            for(BasicBlock f : b.followers()){
                buff.append(String.format("%s -> %s [label %s];\n", b.id().toString(), f.id().toString(), "x"));
            }
        }
        
        buff.append("\n}");
        
        return buff.toString();
    }
    
    private String getPositionData(String dot){
        try {
            File f = File.createTempFile("sample", ".dot");
            File d = File.createTempFile("position", ".dot");
            PrintWriter out = new PrintWriter(f);

            out.write(dot);
            out.close();
            
            Runtime r = Runtime.getRuntime();            
                       
            r.exec(String.format("/usr/local/bin/dot -Tdot %s -o %s", f.getAbsolutePath(), d.getAbsolutePath())).waitFor();
            
            // read in the graph data 
            
            String dotData  = new String(Files.readAllBytes(Paths.get(d.toURI())));


            return dotData;
            
        } catch (Exception e) {
            e.printStackTrace();
        }
        
        return null;
        
    }
    
    public List<Shape> render(){
        
        // step # 1 - convert to DOT.
        String dot = getDot();
        
        String positionData = getPositionData(dot);
        
        // parse this to get the shape data.
        
        
        
        return null;
    }

    /**
     * Initialize the contents of the frame.
     */
    private void initialize() {
        frame = new JFrame();
        frame.setBounds(100, 100, 450, 300);
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        
        JScrollPane scrollPane = new JScrollPane();
        frame.getContentPane().add(scrollPane, BorderLayout.CENTER);
        
        
        // compute all the shapes
        List<Shape> toDraw = render();
        
        
        
    }

}
