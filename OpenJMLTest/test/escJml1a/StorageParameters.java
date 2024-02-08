import org.jmlspecs.annotation.*;
public final class StorageParameters 
{

    private long[] configurationSizes; // nullable in .jml

    public StorageParameters( long[] sizes) { // argument nullable in .jml
        this.configurationSizes = sizes;
    }


    //@ ensures \fresh(\result);  // clause not seen because specs are in .jml
    long[] getConfigurationSizes() { // nullable in .jml
        return configurationSizes;
    }

    public static void main(String... args) {
        StorageParameters a = new StorageParameters(null);
        @Nullable long[] b = a.getConfigurationSizes();
        //@ assert b == a.getConfigurationSizes(); // OK
        long[] c = a.getConfigurationSizes();  // OK - c is nullable by default
	}
}
