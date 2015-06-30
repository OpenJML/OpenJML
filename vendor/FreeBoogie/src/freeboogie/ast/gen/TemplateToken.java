package freeboogie.ast.gen;

/**
 * Represents a token in a template file.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TemplateToken extends Token {
  
  /** Token types */
  public enum Type {
    /** \file */ FILE,
    /** \classes */ CLASSES,
    /** \is_abstract */ IF_ABSTRACT,
    /** \abstract_classes */ ABSTRACT_CLASSES,
    /** \normal_classes */ NORMAL_CLASSES,
    /** \class_name */ CLASS_NAME,
    /** \base_name */ BASE_NAME,
    /** \members */ MEMBERS,
    /** \member_type */ MEMBER_TYPE,
    /** \member_name */ MEMBER_NAME,
    /** \if_primitive */ IF_PRIMITIVE,
    /** \if_nonnull */ IF_NONNULL,
    /** \if_enum */ IF_ENUM,
    /** \children */ CHILDREN,
    /** \primitives */ PRIMITIVES,
    /** \enums */ ENUMS,
    /** \enum_name */ ENUM_NAME,
    /** \values */ VALUES,
    /** \value_name */ VALUE_NAME,
    /** \invariants */ INVARIANTS,
    /** \inv */ INV,
    /** [ */ LB,
    /** ] */ RB,
    /** { */ LC,
    /** } */ RC,
    /** some text to be copied verbatim */ OTHER
  }

  /** Identifier case styles */
  public enum Case {
    /** camelCase */ CAMEL_CASE,
    /** PascalCase */ PASCAL_CASE,
    /** lower_case */ LOWER_CASE,
    /** UPPER_CASE */ UPPER_CASE,
    /** as it appears in the abstract grammar */ ORIGINAL_CASE
  }

  /** The type of this token. */
  public Type type;
  
  /** 
   * The case of the last macro. 
   * Set and used for CLASS_NAME, BASE_NAME, MEMBER_TYPE, MEMBER_NAME,
   * ENUM_NAME, VALUE_NAME. Otherwise is meaningless.  
   */
  public Case idCase;
  
  /**
   * Initializes a token.
   * @param type the token type
   * @param rep the token representation
   * @param idCase the case convention of the token and of the represented id
   */
  public TemplateToken(Type type, String rep, Case idCase) {
    super(rep);
    this.type = type;
    this.idCase = idCase;
  }
}
