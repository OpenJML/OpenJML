package java.io;

import java.nio.channels.FileChannel;

public class FileOutputStream extends OutputStream {

    // CLASS SPECIFICATIONS

    /*@
      @ 
      @*/

    // FIELDS - FIXME these rename private fields
    // @ private model FileDescriptor fd;
    // @ private model FileChannel channel;
    // @ initially channel == null;
    // @ private model boolean append;
    // @ initially append == false;

    // METHODS AND CONSTRUCTORS

    /*@
      @ public normal_behavior
      @   requires name != null;
      @   assignable \nothing;
      @   ensures !wasClosed && isOpen && outputBytes.length == 0 
      @           && append == false;
      @ also
      @ public exceptional_behavior
      @   signals_only NullPointerException, FileNotFoundException;
      @   signals (NullPointerException) name == null;
      @   signals (FileNotFoundException) (* not found by JNI invocation *);
      @*/
    public FileOutputStream(String name) throws FileNotFoundException;

    /*@
      @ public normal_behavior
      @   requires name != null;
      @   assignable \not_specified;
      @   ensures !wasClosed && isOpen && outputBytes.length == 0 
      @           && this.append == append;
      @ also
      @ public exceptional_behavior
      @   signals_only NullPointerException, FileNotFoundException;
      @   signals (NullPointerException) name == null;
      @   signals (FileNotFoundException) (* not found by JNI invocation *);
      @*/
    public FileOutputStream(String name, boolean append) throws FileNotFoundException;

    /*@
      @ public normal_behavior
      @   requires file != null;
      @   assignable \not_specified;
      @   ensures !wasClosed && isOpen && outputBytes.length == 0 
      @           && this.append == false;
      @ also
      @ public exceptional_behavior
      @   signals_only NullPointerException, FileNotFoundException;
      @   signals (NullPointerException) file == null;
      @   signals (FileNotFoundException) (* not found by JNI invocation *);
      @*/    
    public FileOutputStream(File file) throws FileNotFoundException;

    /*@
      @ public normal_behavior
      @   requires file != null;
      @   assignable \not_specified;
      @   ensures !wasClosed && isOpen && outputBytes.length == 0 
      @           && this.append == append;
      @ also
      @ public exceptional_behavior
      @   signals_only NullPointerException, FileNotFoundException;
      @   signals (NullPointerException) file == null;
      @   signals (FileNotFoundException) (* not found by JNI invocation *);
      @*/
    public FileOutputStream(File file, boolean append) throws FileNotFoundException;

    /*@
      @ public normal_behavior
      @   assignable \not_specified;
      @   ensures !wasClosed && isOpen && outputBytes.length == 0 
      @           && this.append == false && fd == fdObj;
      @ also
      @ public exceptional_behavior
      @   signals_only NullPointerException;
      @   signals (NullPointerException) fdObj == null;
      @
      @*/
    public FileOutputStream(FileDescriptor fdObj);

    /*@
      @ 
      @*/
    public void write(int b) throws IOException;

    /*@
      @ 
      @*/
    public void write(byte[] b) throws IOException;

    /*@
      @ 
      @*/
    public void write(byte[] b, int off, int len) throws IOException;

    /*@
      @ 
      @*/
    public void close() throws IOException;

    /*@
      @ 
      @*/
    public final FileDescriptor getFD() throws IOException;

    /*@
      @ 
      @*/
    public FileChannel getChannel();

    /*@
      @ 
      @*/
    protected void finalize() throws IOException;

}

