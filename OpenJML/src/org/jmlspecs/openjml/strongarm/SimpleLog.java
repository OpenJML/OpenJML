package org.jmlspecs.openjml.strongarm;

public class SimpleLog {

    public enum Level {
        INFO, // 0
        DEBUG,// 1
        ERROR;// 2
    }
    
    private final Level level;
    
    public SimpleLog(Level level){
        this.level = level;
    }

    public void write(String msg, Object...args){
        System.out.println("[INFER] " + String.format(msg, args));
    }
    
    public void error(String msg, Object... args){
        
        if(this.level.ordinal() <= Level.ERROR.ordinal() == false)
            return;
        
        write(msg, args);
        
    }
    
    public void info(String msg, Object... args){
        if(this.level.ordinal() <= Level.INFO.ordinal() == false)
            return;

        write(msg, args);
        
        
    }
    
    public void debug(String msg, Object... args){
        if(this.level.ordinal() <= Level.DEBUG.ordinal() == false)
            return;
        
        write(msg, args);

    }
    
}
