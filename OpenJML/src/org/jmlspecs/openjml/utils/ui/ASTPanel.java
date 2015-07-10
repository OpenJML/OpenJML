package org.jmlspecs.openjml.utils.ui;

import java.awt.Color;
import java.awt.Cursor;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.RenderingHints;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionListener;
import java.awt.geom.Line2D;
import java.util.HashMap;
import java.util.Map;

import javax.swing.JButton;
import javax.swing.JPanel;

import com.sun.source.tree.ClassTree;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.util.List;

public class ASTPanel extends JPanel {

    private ASTTreeNode root;
        
    private Map<Point,ASTTreeNode> vertexMap = new HashMap<Point,ASTTreeNode>();
    
    private int SPAN = 100;
    private boolean detail = false;
    private int YSPAN = 50;
    private int YPAD  = 20;
    private int RADIUS = 20;
    private int originX = -1;
    private int originY = -1;
    
    private int clickOriginX = 0;
    private int clickOriginY = 0;
    
    public ASTPanel(ASTTreeNode root){
        super();
        this.root = root;
        
        initComponents();
        
    }
    
    public int getOriginX(){
        if(originX==-1)
            return (this.getWidth()==0 ? this.getPreferredSize().width/2 : this.getWidth()/2);
        
        return originX;
    }
    
    public int getOriginY(){
        if(originY==-1)
            return YPAD;
        return originY;
    }
    
    public int getSpan(){
        return this.SPAN;
    }
    
    
    
    // handles drawing the AST
    public void initComponents(){
        this.removeAll();
        this.setFocusable(true);
        
        // this.setLayout(null);
        setPreferredSize(new Dimension(800,800));
        
        this.setCursor(Cursor.getPredefinedCursor(Cursor.MOVE_CURSOR));
        
        
        this.addMouseMotionListener(new MouseMotionListener(){

            @Override
            public void mouseDragged(MouseEvent arg0) {
                originX = getOriginX() + (arg0.getX() -clickOriginX);
                originY = getOriginY() + (arg0.getY()- clickOriginY);
                
                clickOriginX = arg0.getX();
                clickOriginY = arg0.getY();
                
                repaint();
            }

            @Override
            public void mouseMoved(MouseEvent arg0) {
            }
            
        });
        this.addMouseListener(new MouseAdapter (){
            
            
            @Override
            public void mouseClicked(MouseEvent e){

                // was it a vertex
                for(Point p : vertexMap.keySet()){
                    
                    double distance = Math.sqrt(Math.pow(e.getX()-p.getX(), 2) + Math.pow(e.getY()-p.getY(), 2));
                    
                    if(distance <= RADIUS*1.1){
                        ASTTreeNode node = vertexMap.get(p);
                        selectedNode = node;
                        repaint();
                    }
                    
                }
                
            }
         
            @Override
            public void mousePressed(MouseEvent e){
                clickOriginX = e.getX();
                clickOriginY = e.getY();
            }
            
            public void mouseReleased(MouseEvent e){
            }
        });
    }
    
    
    @Override
    public void paintComponent(Graphics g) {
        super.paintComponent(g);
        vertexMap.clear();
        
        Graphics2D g2 = (Graphics2D) g;
        g2.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,
        RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
        g2.setRenderingHint(RenderingHints.KEY_RENDERING,
        RenderingHints.VALUE_RENDER_QUALITY);
        
        
        paintTree(root, g2, getOriginX(), getOriginY());
        
    }   
    
    float alpha = 1.0F;
   
    private Color getColor(Color c){
        return new Color(c.getRed(), c.getBlue(), c.getGreen(), (int)((alpha*255.0F)));
    }
    
    private Color colorForInstance(JCTree tree){
        if(tree instanceof JCClassDecl){
            return getColor(Color.RED);
        }else if(tree instanceof JCMethodDecl){
            return getColor(Color.GREEN);
        }
        
        return getColor(Color.BLACK);
    }
    
    public void drawCircle(Color c, Graphics2D g, int x, int y, int r) {
        g.setColor(c);
        
        x = x-(r/2);
        y = y-(r/2);
        g.fillOval(x,y,r,r);
        g.setColor(getColor(Color.BLACK));
    }
    
    public void setSplay(int splay){
        this.SPAN = splay;
        repaint();
    }
    
    public void setShowExtended(boolean showExtended){
        this.detail = showExtended;
        repaint();
    }
    
    public void setFilter(String filter){
        this.filter = filter;
        repaint();
        selectedNode = null;
    }
    ASTTreeNode selectedNode;
    
    public void setSelectedNode(ASTTreeNode n){
        selectedNode = n;
        setFilter("");
        repaint();
    }
    
    // if this node is or has a parent that matches the filter
    String filter = "";
    
    
    private void setAlphaForFilter(ASTTreeNode n){
        
        if(filter.trim().equals("")){
            alpha = 1.0F;
            
            if(selectedNode!=null){
                
                // see if this is the node or if it is a child of the selected node.
                if(selectedNode==n || isChildOf(n,selectedNode) || childIsSelected(n,selectedNode)){
                    alpha = 1.0F;
                }else{
                    alpha = .01F;
                }
            }
            
        }else{
        
           if(nodeMatches(n)){
               alpha = 1.0F;
           }else{
               alpha = .3F;
           }
        }
    }
    
 private boolean childIsSelected(ASTTreeNode what, ASTTreeNode parent){
        
     for(ASTTreeNode n : what.children){
         if(n==parent){
             return true;
         }
     }
     return false;
    }
    
    private boolean isChildOf(ASTTreeNode what, ASTTreeNode parent){
        
        if(what==null || what.data==null){
            return false;
        }
        
       
        if(what==parent){
            return true;
        }
        
        return isChildOf(what.getRoot(), parent);
    }

    private boolean nodeMatches(ASTTreeNode n){
        if(n == null || n.data==null){
            return false;
        }
        
        if(n.getNodeRep(true).contains(filter)){
            return true;
        }else{
            return nodeMatches(n.getRoot());
        }
    }
    private void renderSubgraph(Graphics2D g2, int startX, int startY, int x, int y){
        
        g2.setColor(getColor(Color.BLACK));
        g2.draw(new Line2D.Double(startX, startY, x, y));
    }
    private void renderNode(ASTTreeNode n, int x, int y, Graphics g){
        setAlphaForFilter(n);
        vertexMap.put(new Point(x,y),n);
        Color c = colorForInstance(n.data.get(0));
        drawCircle(c, (Graphics2D)g, x, y, RADIUS);
        g.drawString(n.getNodeRep(detail), x,y-10);
    }
    
    private void paintTree(ASTTreeNode n, Graphics g, int startX, int startY){
        Graphics2D g2 = (Graphics2D) g;
        
        int savedRootX = startX;
        int savedRootY = startY;
        
        
        
        // save the root
        int x = startX;
        int y = startY;
        
        // calculate the n lines of the tree to draw
        int deltaX = 0;
        
        if(n.children.size() > 1){
            deltaX = SPAN/(n.children.size()-1);
        }        
        
        // move to the base of the next tree
        if(n.data!=null){
            y = startY+YSPAN;
            x = startX-(SPAN/2);
                 
        }
        
        for(int c = 0; c < n.children.size(); c++){
            // connect the dots
            setAlphaForFilter(n.children.get(c));
            renderSubgraph(g2, startX, startY, x, y+(c*YSPAN));
            // move to next base;
            x = x+deltaX;
        }
        
        // reset root
        if(n.data!=null){
            y = startY+YSPAN;
            x = startX-(SPAN/2);
        }
        
        // recurr into each of the children
        for(int c = 0; c < n.children.size(); c++){
            ASTTreeNode child = n.children.get(c);
            
            paintTree(child, g, x, y+(c*YSPAN));
            x = x+deltaX;
        }
        
        if(n.data!=null){
            renderNode(n,savedRootX,savedRootY, g);
        }
    }
    
}
