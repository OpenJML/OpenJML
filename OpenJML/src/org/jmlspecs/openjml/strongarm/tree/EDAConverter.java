package org.jmlspecs.openjml.strongarm.tree;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

public class EDAConverter {

    private Map<String, String> map          = new HashMap<String, String>();

    private String              alphabet     = "abcdefghijklmnopqrstuvwxyz";

    private String              lastVariable = null;

    private int                 index;

    private final int           max;

    public EDAConverter() {
        index = 0;
        max = alphabet.length();
    }

    /**
     * We take a really simple approach to generating these things.
     * 
     * A, B, C, AA, BB, CC, DD, AAA, BBB
     */

    public String next() {

        if (lastVariable == null) {
            lastVariable = Character.toString(alphabet.charAt(index));
            index++;
        } else {

            //
            // get the character to operate on
            //
            int eIdx = index % max;
            int repeat = 1 + (int) (index / max);

            String s = Character.toString(alphabet.charAt(eIdx));

            lastVariable = new String(new char[repeat]).replace("\0", s);

            index++;
        }

        return lastVariable;
    }

    public String get(String t) {
        String m = map.get(t);

        if (m == null) {
            String n = next();
            map.put(t, n);
            return n;
        }

        return m;
    }

    public static void main(String args[]) {

        EDAConverter e = new EDAConverter();

        for (int i = 0; i < 100; i++) {
            System.out.println(e.next());
        }

    }
    
    private String getProgram(String eda){
        

        StringBuffer buff = new StringBuffer();
        
        List<String> vars = new LinkedList(map.values());
        
        
        buff.append("from pyeda.inter import *\n\n\n");
        
        {
            StringBuffer lhs = new StringBuffer();

            String delim = "";
            for (String i : vars) {
                lhs.append(delim).append(i);
                delim = ", ";
            }
            
            StringBuffer rhsL = new StringBuffer();
            rhsL.append("[");
            


            delim = "";
            for (String i : vars) {
                rhsL.append(delim).append(String.format("\"%s\"", i));
                delim = ", ";
            }
            
            rhsL.append("]");

            buff.append(String.format("%s = map(exprvar, %s)\n", lhs.toString(), rhsL.toString()));
        }

        
        // the expression 
        buff.append(String.format("f1 = %s\n", eda));
        buff.append("f1m = espresso_exprs(f1.to_dnf())\n");
        buff.append("print(f1m)");
        
        return buff.toString();
    }

    public boolean convert(String eda) {

        try {
            File temp = File.createTempFile("eda", ".py");
            BufferedWriter out = new BufferedWriter(new FileWriter(temp));

            String prg = getProgram(eda);
            out.write(prg);
            out.close();

            ProcessBuilder pb = new ProcessBuilder(System.getenv("STRONGARM_PYTHON"), temp.getAbsolutePath());
            Process p = pb.start();

            int returnValue = p.waitFor();
            
            if(returnValue!=0){
                return false;
            }
            
            BufferedReader in = new BufferedReader(
                    new InputStreamReader(p.getInputStream()));
            
            StringBuffer response = new StringBuffer();
            
            String line;
            while((line = in.readLine())!=null){
                response.append(line);
            }
            
            int ret = new Integer(in.readLine()).intValue();
        } catch (Exception e) {

            e.printStackTrace();
            return false;
        }
        
        return true;
    }
}