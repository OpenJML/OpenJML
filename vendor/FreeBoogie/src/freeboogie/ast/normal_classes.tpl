This template generates java classes for the normal classes.

\normal_classes{\file{\ClassName.java}
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package freeboogie.ast;
import java.math.BigInteger; // for AtomNum

public final class \ClassName extends \BaseName {
\enums{  public enum \EnumName {\values[, ]{
    \VALUE_NAME}
  }}
\invariants{  //@ invariant \inv_text;
}
\children{  private final \MemberType \memberName;
}
\primitives{  private final \Membertype \memberName;
}

  // === Constructors and Factories ===
  private \ClassName(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}) {
    this.location = AstLocation.unknown();
\members{    this.\memberName = \memberName; \if_nonnull{assert \memberName != null;}{}
}  }

  private \ClassName(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}, AstLocation location) {
    this(\members[,]{\memberName});
    assert location != null;
    this.location = location;
  }
  
  public static \ClassName mk(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}) {
    return new \ClassName(\members[, ]{\memberName});
  }

  public static \ClassName mk(\members[, ]{\if_primitive{\Membertype}{\MemberType} \memberName}, AstLocation location) {
    return new \ClassName(\members[, ]{\memberName}, location);
  }

  // === Accessors ===
\members{
  public \if_primitive{\Membertype}{\MemberType} get\MemberName() { return \memberName; }}

  // R is the type of the result
  @Override
  public <R> R eval(Evaluator<R> evaluator) { 
    return evaluator.eval(this, \members[,]{\memberName}); 
  }
}
