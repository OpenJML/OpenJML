
public final class StorageParameters 
{
	//@ spec_public  // FIXME - should be able to get rid of this
	private long[] configurationSizes;
	
	public StorageParameters(/*@ nullable */ long[] sizes) {  // FIXME - should be able to get rid of nullable
		this.configurationSizes = sizes;
	}
	
	// @ pure // FIXME - should be able to get rid of nullable
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		StorageParameters a = new StorageParameters(null);
		/*@ nullable */ long[] b = a.getConfigurationSizes();
		//@ assert b == a.getConfigurationSizes();
		long[] c = a.getConfigurationSizes();  // Error - c is non_null by default
	}
}
