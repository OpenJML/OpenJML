\file{Transformer.java}
/**
  This file was generated from transformer.tpl. Do not edit.
 */
package freeboogie.ast;
import java.math.BigInteger;

/**
  Intended to be used as a base class by visitors that either only inspect
  the AST or transform the AST. If you want to inspect nodes of type X into
  something else then you should override {@code see(X x, ...)}. (Most of
  the time you also need to code visiting of the children.) If you want to
  replace (some) nodes of type X by something you should override
  {@code eval(X x, ...)} and return the substitution. This class will take
  care of path compression.
  
  @see freeboogie.ast.Evaluator
 */
public class Transformer extends Evaluator<Ast> {
\normal_classes{  private \ClassName result\ClassName;
}
\normal_classes{

  public void see(
    \ClassName \className,
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} 
      \memberName
    }
  ) {
    boolean sameChildren = true;
    \members{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}
      new\MemberName = 
        \if_primitive{\memberName}{
          \memberName == null ? null :(\MemberType)\memberName.eval(this)
        };
      \if_primitive{}{sameChildren &= new\MemberName == \memberName;}
    }

    // TODO: explain why this works and a stack is not needed, in case it works :)
    result\ClassName = sameChildren? 
      \className : \ClassName.mk(\members[,]{new\MemberName});
  }
  
  @Override
  public \ClassName eval(
    \ClassName \className,
    \members[,]{
      \if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} 
      \memberName
    }
  ) {
    result\ClassName = \className;
    see(\className,\members[,]{\memberName});
    return result\ClassName;
  }
}
}

\file{visitor.skeleton}
// You can copy and paste the text below when you define a visitor that
// needs to override most functions on the base class.

\normal_classes{  @Override
  public void see(\ClassName \className, \members[, ]{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName}) {
    assert false; // TODO: Implement.
  }
  
}

// *********

\normal_classes{  @Override
  public \ClassName eval(\ClassName \className, \members[, ]{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType} \memberName}) {
    assert false; // TODO: Implement.
    return null;
  }

}

