package org.smtlib;

import java.util.ResourceBundle;


public class Version {
    private static final String versionRBName = "org.smtlib.resources.version";
    private static ResourceBundle versionRB;

    public static String version() throws RuntimeException {
    	String key = "release";
    	if (versionRB == null) {
    		versionRB = ResourceBundle.getBundle(versionRBName);
    	}
    	return versionRB.getString(key);
    }

}
