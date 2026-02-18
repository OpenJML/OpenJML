package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface Ghost {
	// The default is temporary. It allows us to use @Ghost
	// as a simple modifier in the context of JML4.
	String value() default "";
}
