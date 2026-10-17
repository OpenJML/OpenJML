import java.io.Reader;
import java.math.BigDecimal;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Properties;
import java.util.StringTokenizer;

/** Checks the JAVA_VERSION entry of the release file of the JDK that runs this program (#1012), the way
 * tools that identify a JDK without running it do: the file is <java.home>/release, read as a Java properties
 * file; the value has its quotes removed and is parsed as maven-surefire does (its leading major[.minor]
 * numbers, as a BigDecimal) and as the JDK itself does (Runtime.Version.parse). Its feature (major) version
 * must equal the JVM's own java.specification.version.
 */
public class CheckJavaVersion {
    public static void main(String... args) throws Exception {
        Path release = Path.of(System.getProperty("java.home"), "release");
        Properties props = new Properties();
        try (Reader r = Files.newBufferedReader(release)) {
            props.load(r);
        }
        String raw = props.getProperty("JAVA_VERSION");
        if (raw == null) {
            fail("no JAVA_VERSION key in " + release);
        }
        String version = raw.replace("\"", "");

        // As maven-surefire does: the leading major[.minor] numbers of the version, as a number
        StringTokenizer tokens = new StringTokenizer(version, "._");
        String majorMinor = null;
        if (tokens.countTokens() == 1) {
            majorMinor = tokens.nextToken();
        } else if (tokens.countTokens() >= 2) {
            String major = tokens.nextToken();
            String minor = tokens.nextToken();
            majorMinor = minor.chars().allMatch(Character::isDigit) ? major + "." + minor : major;
        }
        BigDecimal surefire;
        try {
            surefire = new BigDecimal(majorMinor);
        } catch (RuntimeException e) {
            fail("JAVA_VERSION \"" + version + "\" does not parse as a number the way maven-surefire reads it");
            return;
        }

        // As the JDK parses a version string
        Runtime.Version parsed;
        try {
            parsed = Runtime.Version.parse(version);
        } catch (RuntimeException e) {
            fail("JAVA_VERSION \"" + version + "\" is not a valid Java version string: " + e.getMessage());
            return;
        }

        String spec = System.getProperty("java.specification.version");
        if (parsed.feature() != Integer.parseInt(spec) || surefire.intValue() != parsed.feature()) {
            fail("JAVA_VERSION \"" + version + "\" does not match the JVM's java.specification.version " + spec);
        }
        System.out.println("JAVA_VERSION is present, parses, and matches the JVM's java.specification.version");
    }

    static void fail(String message) {
        System.out.println("FAIL: " + message);
        System.exit(1);
    }
}
