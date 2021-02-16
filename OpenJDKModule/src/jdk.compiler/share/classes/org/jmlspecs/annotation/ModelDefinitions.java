package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
@Documented
public @interface ModelDefinitions {
  Model[] value() default {};
  ModelField[] fields() default {};
  ModelMethod[] methods() default {};
  ModelType[] types() default {};
}
