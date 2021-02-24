package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

// This annotation is advice to OpenJML to inline the associated method
@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface Inline {
}
