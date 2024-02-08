import org.jmlspecs.annotation.*;
public final class StorageParameters 
{

    private long[] configurationSizes; // nullable in .jml

    public StorageParameters( long[] sizes) {  // argument nullable in .jml
        this.configurationSizes = sizes;
    }


    long[] getConfigurationSizes() {  // result nullable in .jml
        return configurationSizes;
    }

    public static void main(String... args) {
        StorageParameters a = new StorageParameters(null);
//        long @Nullable [] b = a.getConfigurationSizes(); // OK - lhs and rhs are nullable
//        //@ assert b == a.getConfigurationSizes(); // OK
        long[] c = a.getConfigurationSizes();  // Error - c is non_null by default
    }
}
