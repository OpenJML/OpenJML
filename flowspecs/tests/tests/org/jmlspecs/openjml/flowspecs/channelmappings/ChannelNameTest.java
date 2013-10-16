package tests.org.jmlspecs.openjml.flowspecs.channelmappings;

import static org.junit.Assert.assertTrue;

import org.jmlspecs.openjml.flowspecs.channelmappings.ChannelName;
import org.junit.Test;

/**
 * @author <a href="mailto:toby.tobkin@gmail.com">Toby Tobkin</a>
 *
 */
public class ChannelNameTest {

    /**
     * Test method for {@link org.jmlspecs.openjml.flowspecs.channelmappings.ChannelName}.
     */
    @Test
    public void Equals_VariousParamsGiven_ProperResults() {
        ChannelName cn1 = new ChannelName("aaaa");
        ChannelName cn2 = new ChannelName("bbbb");
        ChannelName cn3 = new ChannelName("aaaa");
        assertTrue(cn1.equals(cn2) == false);
        assertTrue(cn1.equals(cn3) == true);
        assertTrue(cn1.equals(cn1) == true);
    }

}
