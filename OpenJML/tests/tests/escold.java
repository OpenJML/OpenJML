package tests;

public class escold extends escnew {

    protected void setUp() throws Exception {
        super.setUp();
        options.put("-newesc",null);
        options.put("-nullableByDefault",null);
        options.put("-nonnullByDefault","");
    }

}
