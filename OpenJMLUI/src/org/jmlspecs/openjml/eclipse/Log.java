package org.jmlspecs.openjml.eclipse;

import javax.tools.Diagnostic;
import javax.tools.DiagnosticListener;


public class Log {

    public static Log log = new Log();
    
        static public void log(String s) { 
            if (log.listener != null) log.listener.log(s);
            else System.out.println(s); 
        }
        
        static public void errorlog(String s, Throwable e) { // FIXME - record the exception
            if (log.listener != null) log.listener.log(s);
            else System.out.println(s); 
        }
        
        public static interface IListener {
            public void log(String msg);
        }
        
        public IListener listener = null;
        
        public void setListener(IListener l) {
            listener = l;
        }
        
        //context.put(DiagnosticListener.class, new UIListener<JavaFileObject>() );
        
        final static public class UIListener<S> implements DiagnosticListener<S> {
            public UIListener() {
            }
            
            public void report(Diagnostic<? extends S> diagnostic) {
                diagnostic.getClass(); // null check
                if (log.listener != null) log.listener.log(diagnostic.toString());
                else System.out.println(diagnostic.toString());
            }

        }

}
