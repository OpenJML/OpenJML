package org.jmlspecs.openjml.utils.ui;

import java.util.Locale;
import java.util.ResourceBundle;

import org.jmlspecs.openjml.utils.ui.res.ApplicationMessages.ApplicationMessageKey;

public class MessageUtil {
    
    
    
    private static final ResourceBundle msgResources;


    static {
        msgResources = ResourceBundle.getBundle("org.jmlspecs.openjml.utils.ui.res.ApplicationMessages", Locale.getDefault());
    }

    public static String getMessage(ApplicationMessageKey key) {
        return msgResources.getString(key.toString());
    }


}
