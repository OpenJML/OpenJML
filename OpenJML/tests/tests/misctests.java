package tests;

import org.jmlspecs.models.JMLByte;

import junit.framework.TestCase;

// Tests that the models are present
// TODO : lots more tests of models

public class misctests extends TestCase {

    public void test1() {
        JMLByte b = new JMLByte((byte)1);
    }
    
    public void test2() {
        JMLByte b = new JMLByte((byte)1);
        Object bb = b.clone();
    }
    
}
