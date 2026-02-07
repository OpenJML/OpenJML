    public class XYZ {
        //@ private exceptional_behavior
        //@     signals_only IndexOutOfBoundsException;
        private static void callMe() {
            throw new IndexOutOfBoundsException();
        }
        //@ private behavior
        //@     ensures true;
        private static boolean convertException() {
            try {
                callMe();
            } catch (IndexOutOfBoundsException ex) {
                Object obj = ex;
                String s = obj.toString();
                Throwable th = ex;
                s = th.toString();
                throw new ArrayIndexOutOfBoundsException(s);
            }
            return true;
        }
    }
