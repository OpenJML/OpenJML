interface X
{
    X m();
}

public class Main
{
    public static void main(String[] args)
    {
        // Do something that forces the inner class to be loaded
        new C();
        System.out.println("Done!");
    }

    public static class C implements X
    {
        @Override
        public C m()
        {
            return null;
        }
    }
}