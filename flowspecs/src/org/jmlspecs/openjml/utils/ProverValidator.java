package org.jmlspecs.openjml.utils;

import java.io.InputStream;
import java.io.InputStreamReader;

public class ProverValidator {
    
   
    public static boolean proverValid(Prover prover) {

        try {

            StringBuffer buffer = new StringBuffer();
            
            Process p = new ProcessBuilder(prover.getExecutable(), prover.versionArgument())
                    .redirectErrorStream(true).start();

            InputStream is = p.getInputStream(); 

            InputStreamReader isr = new InputStreamReader(is);

            int c = isr.read();

            while (c != -1) {
                buffer.append((char)c);
                c = isr.read();
            }

            is.close();

            int exitStatus = p.waitFor();

            
             if (exitStatus != 0) {
                 return false;
             }
             
             // check output
             return prover.isValid(buffer.toString());

        } catch (Exception e) {
            return false;
        }

    }

}
