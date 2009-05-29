package org.jmlspecs.openjml.jmldoc;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A Java annotation used to indicate the subjective quality of a JML
 * specification. These annotations are included in generated documentation and
 * are stored in classfiles.
 * 
 * @author Joseph Kiniry
 */
@Retention(RetentionPolicy.CLASS)
@Documented
public @interface Quality {
  /**
   * Specifications range in quality from POOR to EXCELLENT. If a specification
   * has not yet been written at all, then it is MISSING.
   * 
   * @author Joseph Kiniry
   */
  public enum SpecQuality {
    // A specification does not exist and has never been written.
    MISSING,
    // The specification exists, but is...
    /** ... very poor. */
    POOR,
    /** ... just ok. */
    OK,
    /** ... quite good and usable in several tools. */
    GOOD,
    /** ... very good and essentially complete. */
    EXCELLENT
  }
  SpecQuality quality() default SpecQuality.MISSING;
  String author() default "";
  String changed() default "";
}
