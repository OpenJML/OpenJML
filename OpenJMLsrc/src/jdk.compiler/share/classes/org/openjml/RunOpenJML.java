// This class is used to run openjml programmatically, in particular to run it when there are JVM options to set (such as profiling or coverage)
package org.openjml;

public class RunOpenJML {
    
  private RunOpenJML() {}

  public static void main(String... args) {
    int x = org.openjml.IAPI.openjml(args);
    System.exit(x);
  }
}
