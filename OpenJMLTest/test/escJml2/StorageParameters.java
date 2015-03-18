
//@ nullable_by_default   // FIXME - should be able to get rid of this
public final class StorageParameters 
{
	//@ spec_public  // FIXME - should be able to get rid of this
	private long[] configurationSizes;
	
	//@ pure  // FIXME - should be able to get rid of this
	public StorageParameters(/*@ nullable */ long[] sizes) {

		this.configurationSizes = sizes;
	}
	
	
	long[] getConfigurationSizes() {
		return configurationSizes;
	}
	
	public static void main(String... args) {
		StorageParameters a = new StorageParameters(null);
		/*@ nullable */ long[] b = a.getConfigurationSizes();
		long[] c = a.getConfigurationSizes();  // OK - c is nullable by default
	}
}
