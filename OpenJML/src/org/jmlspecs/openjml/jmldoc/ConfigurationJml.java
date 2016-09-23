package org.jmlspecs.openjml.jmldoc;


import java.text.SimpleDateFormat;
import java.util.Date;

import com.sun.tools.doclets.formats.html.ConfigurationImpl;
import com.sun.tools.doclets.internal.toolkit.WriterFactory;

import org.jmlspecs.annotation.NonNull;

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
        // instance should always be a ConfigurationJml object in jmldoc
        instance = new ConfigurationJml(); 
    }
    
    /** Returns the current singleton instance of the configuration object */
    static public ConfigurationJml getInstance() {
        return (ConfigurationJml)instance;
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
    @NonNull @Override
    public WriterFactory getWriterFactory() {
        return new WriterFactoryJml(this);
    }

    /**
     * Return the build date for the doclet.
     * @return an identification string with the build date
     */
    @NonNull
    public String getDocletSpecificBuildDate() {
        String s = new SimpleDateFormat("yyyymmdd").format(new Date());
        if (notimestamp) s = "DATE-VERSION";
        return "OpenJMLDoc: " + s;
    }

}
