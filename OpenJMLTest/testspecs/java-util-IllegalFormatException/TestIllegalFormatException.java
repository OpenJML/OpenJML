import java.util.*;

public class TestIllegalFormatException {

    @org.jmlspecs.annotation.SkipEsc
    public static void main(String... args) {
        stringValued();
        intValued();
        charValued();
        nullArguments();
        others();
        System.out.println("DONE");
    }

    public static void stringValued() {
        String f = "-#";
        DuplicateFormatFlagsException e1 = new DuplicateFormatFlagsException(f);
        //@ assert e1.getFlags() == f;
        //@ assert e1.getCause() == null;
        IllegalFormatFlagsException e2 = new IllegalFormatFlagsException(f);
        //@ assert e2.getFlags() == f;
        UnknownFormatFlagsException e3 = new UnknownFormatFlagsException(f);
        //@ assert e3.getFlags() == f;
        MissingFormatArgumentException e4 = new MissingFormatArgumentException(f);
        //@ assert e4.getFormatSpecifier() == f;
        MissingFormatWidthException e5 = new MissingFormatWidthException(f);
        //@ assert e5.getFormatSpecifier() == f;
        UnknownFormatConversionException e6 = new UnknownFormatConversionException(f);
        //@ assert e6.getConversion() == f;
        String m = e6.getMessage();
        //@ assert m != null;
        IllegalArgumentException ia = e1;
    }

    public static void intValued() {
        IllegalFormatCodePointException e1 = new IllegalFormatCodePointException(0x110000);
        //@ assert e1.getCodePoint() == 0x110000;
        IllegalFormatPrecisionException e2 = new IllegalFormatPrecisionException(-3);
        //@ assert e2.getPrecision() == -3;
        IllegalFormatWidthException e3 = new IllegalFormatWidthException(7);
        //@ assert e3.getWidth() == 7;
        String m = e3.getMessage();
        //@ assert m != null;
    }

    public static void charValued() {
        FormatFlagsConversionMismatchException e1 = new FormatFlagsConversionMismatchException("#", 'd');
        //@ assert e1.getConversion() == 'd';
        //@ assert e1.getFlags().equals("#");
        IllegalFormatConversionException e2 = new IllegalFormatConversionException('d', String.class);
        //@ assert e2.getConversion() == 'd';
        //@ assert e2.getArgumentClass() == String.class;
    }

    public static void nullArguments() {
        try {
            new DuplicateFormatFlagsException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
        try {
            new FormatFlagsConversionMismatchException(null, 'x');
            //@ unreachable;
        } catch (NullPointerException e) {
        }
        try {
            new IllegalFormatConversionException('x', null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
        try {
            new MissingFormatArgumentException(null);
            //@ unreachable;
        } catch (NullPointerException e) {
        }
    }

    public static void others() {
        IllformedLocaleException e1 = new IllformedLocaleException("bad", 3);
        //@ assert e1.getErrorIndex() == 3;
        IllformedLocaleException e2 = new IllformedLocaleException("bad");
        //@ assert e2.getErrorIndex() == -1;
        //@ assert e2.getMessage() == "bad";
        IllformedLocaleException e3 = new IllformedLocaleException();
        //@ assert e3.getErrorIndex() == -1;
        //@ assert e3.getMessage() == null;
        InputMismatchException e4 = new InputMismatchException("x");
        //@ assert e4.getMessage() == "x";
        NoSuchElementException ns = e4;
        FormatterClosedException e5 = new FormatterClosedException();
        //@ assert e5.getMessage() == null;
        InvalidPropertiesFormatException e6 = new InvalidPropertiesFormatException("p");
        //@ assert e6.getMessage() == "p";
        RuntimeException r = new RuntimeException();
        ServiceConfigurationError e7 = new ServiceConfigurationError("s", r);
        //@ assert e7.getMessage() == "s";
        //@ assert e7.getCause() == r;
    }
}
