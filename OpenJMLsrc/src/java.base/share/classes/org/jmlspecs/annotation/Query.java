package org.jmlspecs.annotation;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Documented;

/** Defines the 'query' JML annotation */

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface Query {
    String value() default "";
}
