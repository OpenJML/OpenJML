package org.jmlspecs.openjml.jmldoc;


import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;

import com.sun.tools.doclets.formats.html.ConfigurationImpl;
import com.sun.tools.doclets.internal.toolkit.Configuration;
import com.sun.tools.doclets.internal.toolkit.WriterFactory;


/** This class is needed so that the configuration used by the doclet contains
 * the factory that writes JML information.
 * 
 * @author David Cok
 *
 */
public class ConfigurationJml extends ConfigurationImpl {
    
    static {
        instance = new ConfigurationJml(); // overwrites the ConfigurationImpl instance
        System.out.println("Initialized ConfigurationJML");
    }
    
//    public ConfigurationJml() {
//        //builderXMLPath = "org/jmlspecs/openjml/jmldoc/resources/doclet.xml";
//    }
//
//    public InputStream getBuilderXML() throws FileNotFoundException {
//        return builderXMLPath == null ?
//            ConfigurationJml.class.getResourceAsStream("resources/doclet.xml") :
//            new FileInputStream(new File(builderXMLPath));
//    }


    public WriterFactory getWriterFactory() {
        return WriterFactoryJml.getInstance();
    }

    /**
     * Return the build date for the doclet.
     */
    public String getDocletSpecificBuildDate() {
        return "OpenJMLDoc: " + "DATE-VERSION";
    }

}
