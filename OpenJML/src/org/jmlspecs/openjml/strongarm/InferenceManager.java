package org.jmlspecs.openjml.strongarm;

import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import org.jmlspecs.openjml.utils.MD5Checksum;

public class InferenceManager {
    
    class History {
        public String checksum;
        public String file;
        
        public History(String checksum, String file){
            this.checksum = checksum;
            this.file     = file;
        }
    }
    
    public int exit;
    
    private static InferenceManager instance;
    public int round;
    private Map<Integer,List<History>> history = new HashMap<Integer,List<History>>();
    
    private InferenceManager(){}
    
    public synchronized static InferenceManager getInstance(){
        
        if(instance==null){
            instance = new InferenceManager();
        }
        
        return instance;
    }
    
    
    private History findInList(String file, List<History> history){
        for(History h : history){
            if(h.file.equals(file)){
                return h;
            }
        }
        
        return null;
    }
    
    private History findInList(String file, Integer round){        
        return findInList(file, history.get(round));
    }
    
    public boolean sanityCheck(List<History> h1, List<History> h2){
        
        if(h1.size()!=h2.size()){
            return false;
        }
        
        for(History h : h1){
            if(findInList(h.file, h2)==null){
                return false;
            }
        }
        
        for(History h : h2){
            if(findInList(h.file, h1)==null){
                return false;
            }
        }

        return true;
    }


    public List<History> filesChanged(int whichRound){
        // easy case -- everything changed
        if(whichRound==1){
            List<History> files = new ArrayList<History>();
            
            for(History h : history.get(whichRound)){
                files.add(h);
            }
            
            return files;
        }
        
        // sanity check 
        if(sanityCheck(history.get(whichRound), history.get(whichRound-1))==false){
            System.out.println("Sanity Check Failed!");
        }

        List<History> changed = new ArrayList<History>();
        
        List<History> h1 = history.get(whichRound-1);
        List<History> h2 = history.get(whichRound);
        
        
        for(History h : h1){
            if(h.checksum.equals(findInList(h.file, h2).checksum)==false){
                changed.add(h);
            }
        }
        return changed;        
        
    }
    
    public List<History> filesChanged(){
        return filesChanged(this.round);
    }
    
    public void logInference(String file) {
                
        // compute the checksum
        String checksum;

        try {
            checksum = MD5Checksum.getMD5Checksum(file);
            history.get(this.round).add(new History(checksum, file));
        } catch (Exception e) {
            e.printStackTrace();
        }
        
    }
    
    public int newRound(){
        this.round = round + 1;
        
        
        history.put(this.round, new ArrayList<History>());
        
        
        
        return this.round;
        
    }
    
    
    

}
