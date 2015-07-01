package test;

import icecaptools.IcecapProgressMonitor;
import icecaptools.launching.ShellCommand;

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.lang.reflect.Constructor;
import java.util.Arrays;
import java.util.Iterator;

import main.TestAll;

public class TestJML extends TestAll {

	private StringBuffer workspace;

	private String location;

	@Override
	protected String getInputFolder(StringBuffer path) {
		location = path.toString();
		String[] elements = path.toString().split("" + File.separatorChar);
		workspace = new StringBuffer();
		for (int i = 0; i < elements.length - 1; i++) {
			if (elements[i].trim().length() > 0) {
				workspace.append(File.separatorChar);
				workspace.append(elements[i]);
			}
		}
		return path.toString() + "bin";
	}

	@Override
	protected Iterator<File> getTestDirectories(StringBuffer path) {
		StringBuffer javax_safetycritical_test = new StringBuffer();
		StringBuffer javax_realtime_test = new StringBuffer();

		javax_safetycritical_test.append(path);
		javax_safetycritical_test.append("src");
		javax_safetycritical_test.append(File.separatorChar);
		javax_safetycritical_test.append("javax");
		javax_safetycritical_test.append(File.separatorChar);
		javax_safetycritical_test.append("safetycritical");
		javax_safetycritical_test.append(File.separatorChar);
		javax_safetycritical_test.append("test");

		javax_realtime_test.append(path);
		javax_realtime_test.append("src");
		javax_realtime_test.append(File.separatorChar);
		javax_realtime_test.append("javax");
		javax_realtime_test.append(File.separatorChar);
		javax_realtime_test.append("realtime");
		javax_realtime_test.append(File.separatorChar);
		javax_realtime_test.append("test");

		return Arrays
				.asList(new File[] { new File(javax_safetycritical_test.toString()),
						new File(javax_realtime_test.toString()) }).iterator();
	}

	@Override
	protected String getInputPackage(File testsDirectory) {
		if (testsDirectory.getAbsolutePath().contains("realtime")) {
			return "javax.realtime.test";
		} else {
			return "javax.safetycritical.test";
		}
	}

	@Override
	protected String getVMSource(StringBuffer path) {
		StringBuffer vmSource = new StringBuffer();
		vmSource.append(System.getProperty("user.home"));
		vmSource.append(File.separatorChar);
		vmSource.append("git");
		vmSource.append(File.separatorChar);
		vmSource.append("hvm-scj");
		vmSource.append(File.separatorChar);
		vmSource.append("icecapvm");
		vmSource.append(File.separatorChar);
		return vmSource.toString();
	}

	@Override
	protected void preCompile(String testPackage, String testClass) throws Exception {
		String elements[] = testClass.split("\\.");
		String className = elements[0];

		Class<?> cls = Class.forName(testPackage + "." + className);

		@SuppressWarnings("rawtypes")
		Constructor constructor = cls.getConstructor(new Class[0]);

		BasicJMLTest test = (BasicJMLTest) constructor.newInstance(new Object[0]);

		String command = test.getJMLAnnotationCommand();

		StringBuffer icecapsdk = new StringBuffer();
		icecapsdk.append(System.getProperty("user.home"));
		icecapsdk.append(File.separatorChar);
		icecapsdk.append("git");
		icecapsdk.append(File.separatorChar);
		icecapsdk.append("hvm-scj");
		icecapsdk.append(File.separatorChar);
		icecapsdk.append("icecapSDK");

		command = command.replace("WORKSPACE", workspace);
		command = command.replace("ICECAPSDK", icecapsdk);

		ShellCommand.executeCommand(command, System.out, true, location, null, 0, new IcecapProgressMonitor() {

			@Override
			public void worked(String string) {
			}

			@Override
			public boolean isCanceled() {
				return false;
			}

			@Override
			public void worked(int i) {
			}

			@Override
			public void subTask(String string) {
			}

		});
	}
		
	public static void main(String[] args) throws Throwable {
		new TestJML().performTest();
	}
}
