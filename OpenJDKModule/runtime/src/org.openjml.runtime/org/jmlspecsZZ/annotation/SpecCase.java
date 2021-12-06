package org.jmlspecs.annotation;

import java.lang.annotation.Documented;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
@Documented
public @interface SpecCase {
  /** tag format: (('+'|'-')? JavaId) (',' ('+'|'-') JavaId)*)? */
  String tag()				       default "";
  String header()			       default "";
  String forall()				   default "$not_specified";
  String old()					   default "$not_specified";
  String requires()                default "$not_specified";
  String requiresRedundantly()     default "$not_specified";
  String ensures()                 default "$not_specified";
  String ensuresRedundantly()      default "$not_specified";
  String signals()                 default "$not_specified";
  String signalsRedundantly()      default "$not_specified";
  String signalsOnly()             default "$not_specified";
  String signalsOnlyRedundantly()  default "$not_specified";
  String diverges()				   default "$not_specified";
  String divergesRedundantly()	   default "$not_specified";
  String when()				  	   default "$not_specified";
  String whenRedundantly()	  	   default "$not_specified";
  String assignable()              default "$not_specified";
  String assignableRedundantly()   default "$not_specified";
  String accessible()              default "$not_specified";
  String accessibleRedundantly()   default "$not_specified";
  String callable()                default "$not_specified";
  String callableRedundantly()     default "$not_specified";
  String measuredBy()              default "$not_specified";
  String measuredByRedundantly()   default "$not_specified";
  String captures()                default "$not_specified";
  String capturesRedundantly()     default "$not_specified";
  String workingSpace()            default "$not_specified";
  String workingSpaceRedundantly() default "$not_specified";
  String duration()            	   default "$not_specified";
  String durationRedundantly() 	   default "$not_specified";
  
  String modelProgram()			   default "$not_specified";
}
