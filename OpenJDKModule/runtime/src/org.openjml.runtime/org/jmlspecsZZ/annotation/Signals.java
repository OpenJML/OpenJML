package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface Signals {

	boolean redundantly() default false;
	String value()        default "true";

}
