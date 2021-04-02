package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(value=RetentionPolicy.RUNTIME)
@Documented
@Target(value={ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface Nullable {}