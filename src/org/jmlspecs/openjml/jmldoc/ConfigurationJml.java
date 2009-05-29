package org.jmlspecs.openjml.jmldoc;


import com.sun.tools.doclets.formats.html.ConfigurationImpl;
import com.sun.tools.doclets.internal.toolkit.WriterFactory;

import org.jmlspecs.annotations.NonNull;

/**
 * This class extends the ConfigurationImpl class that is part of the javadoc
 * tool; the extension is needed so that the configuration used by the doclet
 * contains the factory that writes JML information.
 * 
 * @author David R. Cok
 */
public class ConfigurationJml extends ConfigurationImpl {
    
    static {
        // overwrites the instance created by ConfigurationImpl
        instance = new ConfigurationJml(); 
    }

// Use something like this if we adopt a design that needs a modified xml layout
// description
//    public ConfigurationJml() {
//        //builderXMLPath = "org/jmlspecs/openjml/jmldoc/resources/doclet.xml";
//    }
//
//    public InputStream getBuilderXML() throws FileNotFoundException {
//        return builderXMLPath == null ?
//            ConfigurationJml.class.getResourceAsStream("resources/doclet.xml") :
//            new FileInputStream(new File(builderXMLPath));
//    }


    /** This method overrides the parent class to return a JML-specific writer
     * factory
     * @return a JML-specific factory that produces JML-aware writers
     */
    @NonNull
    public WriterFactory getWriterFactory() {
        return WriterFactoryJml.getInstance();
    }

    /**
     * Return the build date for the doclet.
     * @return an identification string with the build date
     */
    @NonNull
    public String getDocletSpecificBuildDate() {
        return "OpenJMLDoc: " + "DATE-VERSION";    // FIXME
    }

}
