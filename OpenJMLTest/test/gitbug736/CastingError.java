public class CastingError {

    public static void castingError() {
        double b = (int)(-4.5);
        //@ show b;
        //@ assert b + 4.5 > 0;
        float a = (int)(-4.5);
        //@ assert a + 4.5 > 0;
   }

}
