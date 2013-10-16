/**
 * 
 */
package tests.org.jmlspecs.openjml.flowspecs.channelmappings;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.LinkedList;

import org.jmlspecs.openjml.flowspecs.AdjacencyMatrix;
import org.jmlspecs.openjml.flowspecs.Lattice;
import org.jmlspecs.openjml.flowspecs.SecurityType;
import org.jmlspecs.openjml.flowspecs.channelmappings.ChannelSpec;
import org.jmlspecs.openjml.flowspecs.channelmappings.LevelDoesNotExistException;
import org.junit.BeforeClass;
import org.junit.Test;

/**
 * @author Toby Tobkin
 *
 */
public class ChannelSpecTest {
    
    /**A lattice containing the levels "private" and "public"*/
    private static Lattice<SecurityType> testLattice;

    /**
     * @throws java.lang.Exception
     */
    @BeforeClass
    public static void setUpBeforeClass() throws Exception {
        //Create a lattice
        LinkedList<SecurityType> levels = new LinkedList<SecurityType>();
        levels.add(new SecurityType("private"));
        levels.add(new SecurityType("public"));
        
        AdjacencyMatrix<SecurityType> backingMatrix = new AdjacencyMatrix<SecurityType>(levels);
        
        testLattice = new Lattice<SecurityType>(backingMatrix);
    }
    
    /**
     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelSpec#ChannelSpec(java.lang.String, java.lang.String, org.jmlspecs.openjml.flowspecs.Lattice)}.
     */
    @Test
    public void ChannelSpec_ValidParamsGiven_ParamsStored(){
        try {
            ChannelSpec c = new ChannelSpec("private", "public", testLattice);
            assertTrue(c.getInputLevel().compareTo("private") == 0);
            assertTrue(c.getOutputLevel().compareTo("public") == 0);
        } catch (LevelDoesNotExistException e) {
            fail("Exception should not have been thrown.");
        }
    }
    
    /**
     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelSpec#ChannelSpec(java.lang.String, java.lang.String, org.jmlspecs.openjml.flowspecs.Lattice)}.
     */
    @Test
    public void ChannelSpec_InvalidParamGiven_LevelDoesNotExistExceptionThrown(){
            try {
                ChannelSpec c = new ChannelSpec("private", "invalid level", testLattice);
                fail("Expected LevelDoesNotExistException");
            } catch (LevelDoesNotExistException e) {
                //Pass
                return;
            } catch (Exception e){
                fail("Expected LevelDoesNotExistException");
            }
            fail();
    }
}
