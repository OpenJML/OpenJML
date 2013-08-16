package org.jmlspecs.openjml.utils.ui.res;

import java.util.ListResourceBundle;

public class ApplicationMessages extends ListResourceBundle {
    
    private static String proverConfigurationHelper;
    
    
    static {
        
        String os = System.getProperty("os.name");
        
        if (os.contains("OS X")) {
            proverConfigurationHelper =  String.format("<html>OpenJML requires a SMT prover in order to perform static analysis, however your prover configuration is either missing or invalid. " +
                    "On your platform (%s) the OpenJML team recommends Z3, and to a lesser extent, Yices. Please configure one of these provers using the form below.</html>", os);
            
            
            
        }else if(os.indexOf("nux") >=0){
            proverConfigurationHelper =  String.format("<html>OpenJML requires a SMT prover in order to perform static analysis, however your prover configuration is either missing or invalid. " +
                    "On your platform (%s) the OpenJML team recommends Z3, and to a lesser extent, Yices. Please configure one of these provers using the form below.</html>", os);
            
            
        }else if(os.indexOf("Windows") >=0){
            proverConfigurationHelper =  String.format("<html>OpenJML requires a SMT prover in order to perform static analysis, however your prover configuration is either missing or invalid. " +
                    "On your platform (%s) the OpenJML team recommends Z3, and to a lesser extend, CVC4 and Yices. Please configure one of these provers using the form below.</html>", os);
            
        }else{
            // can't detect the OS.            
            proverConfigurationHelper = "<html>OpenJML requires a SMT prover in order to perform static analysis, however your prover configuration is either missing or invalid. " +
                    "Please configure a prover using the form below. </html>";
        }
                
        
    }

    public enum ApplicationMessageKey {
        MsgProverExecutable, MsgInvalidProverExecutable, MsgValidProverExecutable, MsgInvalidProverConfiguration, MsgCantReadPropertiesFile;
    }

    @Override
    protected Object[][] getContents() {
        return new Object[][]{
                {ApplicationMessageKey.MsgProverExecutable.toString(), "%s Executable:"},
                {ApplicationMessageKey.MsgInvalidProverExecutable.toString(), "The specified path is not a valid %s prover"},
                {ApplicationMessageKey.MsgValidProverExecutable.toString(), "The specified path is a valid %s prover"},
                {ApplicationMessageKey.MsgInvalidProverConfiguration.toString(), proverConfigurationHelper},
                {ApplicationMessageKey.MsgCantReadPropertiesFile.toString(), "Can't read the properties file %s because it may not exist or this is the first time running OpenJML. Please configure your prover settings now."}





        };
    }
}
