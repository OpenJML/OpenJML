package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface Also {
  /** tag format: (('+'|'-')? JavaId) (',' ('+'|'-') JavaId)*)? */
  String tag() default "";
  SpecCase[] value() default {};
}
