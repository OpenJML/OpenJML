module java.base {

    requires transitive java.logging;
    requires java.xml;
    
    opens java.io;
    exports java.lang;


    exports jdk.internal.javac to
        java.compiler,
        jdk.compiler,
        jdk.incubator.vector,
        jdk.jshell;

    uses java.lang.System.LoggerFinder;

    provides java.nio.file.spi.FileSystemProvider with
        jdk.internal.jrtfs.JrtFileSystemProvider;

    provides java.util.random.RandomGenerator with
        java.security.SecureRandom,
        java.util.Random,
        java.util.SplittableRandom;

}
