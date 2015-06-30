This is the generic interface for a visitor that can return
a value. As a convenience, the object is also deconstructed
in the class. The original object is sent nevertheless because
we may want to use it.

TODO: Consider having a base class for this which is parametrized
by the return type for each type of node.

\file{Evaluator.java}
/** 
  This file is generated from evaluator.tpl. Do not edit.
*/
package freeboogie.ast;
import java.math.BigInteger;

/**
  Use as a base class when you want to compute a value of type
  {@code R} for each node. An example is the typechecker.
 */
public class Evaluator<R> {
\normal_classes{
  public R eval(\ClassName \className, 
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      \memberName
    }
  ) {
    \children{if (\memberName != null) \memberName.eval(this);}
    return null;
  }
}
}
