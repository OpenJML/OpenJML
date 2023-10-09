package org.jmlspecs.openjml.esc;

import java.util.Map;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.ArrayList;

import org.jmlspecs.openjml.JmlOption;
import org.jmlspecs.openjml.JmlTree.JmlMethodDecl;
import org.jmlspecs.openjml.Strings;

import com.sun.tools.javac.util.Context;

public class Translations {
    
    public Context context;
    
    public Translations(Context context) {
        this.context = context;
    }
    
    public Translations(JmlMethodDecl d) {
        addFirstTranslation(d);
    }

    public Map<String,JmlMethodDecl> splits = new HashMap<>();
    
    public List<String> keys() {
        ArrayList<String> list = new ArrayList<String>(splits.keySet());
        if (list.isEmpty()) { 
            list.add("");
        } else {
            Collections.sort(list);
        }
        return list;        
    }
    
    public void addFirstTranslation(JmlMethodDecl value) {
        splits.put("", value);
    }
    
    public void addTranslation(String key, JmlMethodDecl value) {
        splits.put(key, value);
    }
    
    public JmlMethodDecl getTranslation(String key) {
        return splits.get(key);
    }
    
    public void addSplit(String key, int num) {
        splits.remove(key);
        for (int i=0; i<num; i++) addTranslation(key + (char)('A' + i), null);
    }
    
    public String nextToDo() {
        for (String k: keys()) {
            if (splits.get(k) == null) return k;
        }
        return null;
    }
}
