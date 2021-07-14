public class CastingError {

public static void castingError()
   {
        float a = (int)(-4.5);
        double b = (int)(-4.5);
        //@ assert a + 4.5 > 0 && b + 4.5 > 0;
   }

}
