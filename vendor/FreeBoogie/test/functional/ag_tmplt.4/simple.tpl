This should output very simple AST classes in the subdirectory ast.

\normal_classes{
\file{ast/\ClassName.java}
/**
  Public domain.
  This class is generated automatically from simple.tpl. Do not edit.
 */
package freeboogie.ast;

public class \ClassName extends \BaseName {
\enums{  public enum \EnumName {\values[, ]{
    \VALUE_NAME}
  }}
\invariants{  //@ invariant \inv_text;
}
\children{  private \MemberType \memberName;
}
\primitives{  private \Membertype \memberName;
}

  public \ClassName(\members[, ]{\if_primitive{\Membertype}{\MemberType} \member_name}) {
\members{    this.\member_name = \member_name; \if_nonnull{assert \member_name != null;}{}
}  }

\members{
  public get\MemberName() { return \member_name; }}
}
}
\abstract_classes{
\file{ast/\ClassName.java}
/**
  Public domain.
  This class is generated automatically from simple.tpl. Do not edit.
 */
package freeboogie.ast;

public abstract class \ClassName extends \BaseName {}
}
\file{/dev/stdout}Done!
