import org.jmlspecs.annotation.*;
public final class StorageParameters 
{
	//@ spec_public // FIXME - should not need
	private long[] configurationSizes;
	
	public StorageParameters( long[] sizes) {
		this.configurationSizes = sizes;
	}
	
	//@ pure spec_public //FIXME - should not need
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		StorageParameters a = new StorageParameters(null);
		@Nullable long[] b = a.getConfigurationSizes();
		//@ assert b == a.getConfigurationSizes();
		long[] c = a.getConfigurationSizes();  // Error - c is non_null by default
	}
}
