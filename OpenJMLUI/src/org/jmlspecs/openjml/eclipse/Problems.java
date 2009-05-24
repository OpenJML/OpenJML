/**
 * Copyright (c) 2005 David R. Cok
 * @author David R. Cok
 * Created Jul 14, 2005
 */
package org.jmlspecs.openjml.eclipse;

import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.text.MessageFormat;

/**
 * This class is an enum containing all the error and warning messages produced 
 * by the tool (that are not already part of the regular Eclipse & JDT messages).
 * Each item of the enum is a combination of int identifier and
 * java.text.MessageFormat style formatted message, into which substitutions
 * are made at the point of use.  Thus the same message can be reused with 
 * slightly different content.
 * 
 * TODO - to do proper localization, all the message format strings should be
 * in a localizable bundle somewhere.
 */
public enum Problems implements IProblems {
  
  /** Used for situations where unexpected inconsistency arises in the code,
   *  or some point or condition is reached in the code that should not -
   *  indicates a bug somewhere. */
  INTERNAL_ERROR(3000,ERROR,"INTERNAL ERROR: {0}"),
  INTERNAL_WARNING(3001,WARN,"INTERNAL WARNING: {0}"),

  // Java parsing errors
  
  EXPECTED_EXPRESSION(3002,ERROR,"Expected an expression here after the {0} token"),
  EXPECTED_SEMICOLON_IN_ONDEMAND_IMPORT(3003,ERROR,"Expected a semicolon here, after the * in an on-demand import declaration"),
  EXPECTED_SEMICOLON_IN_IMPORT(3004,ERROR,"Expected a semicolon or . here, after an identifier in an import declaration"),
  JML_BAD_TYPE(3005,ERROR,"A JML {0} must contain a {1} expression, not {2}"),          
  EXPECTED_SEMICOLON_AFTER_EXPRESSION(3006,ERROR,"Expected a semicolon here to end the expression"),
  INVALID_EXPRESSION_OR_MISSING_SEMICOLON(3007,ERROR,"Either a semicolon is missing here or the expression is ill-formed"),
  INVALID_EXPRESSION(3008,ERROR,"Expression is invalid near here"),
  UNEXPECTED_END(3009,ERROR,"Expression is incomplete here"),
  UNEXPECTED_END_OR_INVALID(3010,ERROR,"Incomplete or invalid expression here"),
  NO_MATCHING_RBRACKET(3011,ERROR,"Expected a right bracket (]) to match a previous left bracket"),
  INCOMPLETE_EXPRESSION_AT_SEMICOLON(3012,ERROR,"Expression is incomplete at the semicolon here"),
  NO_MATCHING_RPAREN(3013,ERROR,"Expected a right parenthesis to match a previous left parenthesis"),
  INVALID_INPUT(3014,ERROR,"Seriously mal-formed input near here: {0}"),
  EXPECTED_LP_LB_DOT(3015,ERROR,"Expected a left bracket,left parenthesis, or dot after the preceeding identifier"),
  INVALID_TYPE(3016,ERROR,"Expected a type beginning here"),
  EXPECTED_IDENTIFIER_AFTER_DOT(3017,ERROR,"Expected an identifier after the DOT in a qualified name"),
  EXPECTED_SEMICOLON_AFTER_EXPR_OR_DECL(3018,ERROR,"Invalid expression or missing semicolon in declaration"),
  EXPECTED_NAME_IN_DECL(3019,ERROR,"Expected a name here in a declaration"),
  INVALID_LEFT_HAND_SIDE(3020,ERROR,"Left-hand sides of assignment statements must be names, array accesses or field accesses"),
  NO_CLASS_TOKEN(3021,ERROR,"Expected .class after a name or type"),
  BAD_THIS(3022,ERROR,"A this token must follow a name, not an expression"),
  NO_MATCHING_RANGLE(3023,ERROR,"Expected a > token to match a previous < token"),
  EXPECTED(3024,ERROR,"Expected {0} here"),
  BAD_BOUND(3025,ERROR,"A Wildcard type must be bounded using the keywords extends or super"),
  EXPECTED_COMMA_OR_RBRACE(3026,ERROR,"Expected a valid expression terminated by a comma or right brace (})"),
  NO_DIMS_FOR_VOID(3027,ERROR,"A void type literal may not be given any array dimensions"),
  TYPES_BUT_NO_LP(3028,ERROR,"If there are explicit type arguments, there must also be a method argument list"),
  BAD_TYPE_OR_ARRAY_ACCESS(3029,ERROR,"If this is an array access, there should not be type qualifiers; if it is a Type.class literal there should be no array indices"),
  NO_ARRAY_ACCESS_ON_ARRAY_CREATION(3030,WARN,
          "The JLS does not allow an array access expression on an array creation expression, although javac parses it"),
  NO_ARRAY_INIT(3031,ERROR,"The JLS does not allow an array initalizer when some dimensions are specified"),
  DUPLICATED_MODIFIER(3032,ERROR,"Java does not allow modifiers to be duplicated"),
  INVALID_PACKAGE(3033,ERROR,"An invalid package declaration or missing semicolon here"),
  EXPECTED_END_OF_FILE(3034,ERROR,"Expected an end of file here"),
  VARARGS_MUST_BE_LAST(3035,ERROR,"Formal parameters allowing a variable number of arguments are permitted only as the last parameter"),
  NO_MATCHING_RBRACE(3036,ERROR,"Expected a right brace to match a previous left brace (or the code near here is ill-formed)"),
  BAD_MODIFIER(3037,ERROR,"A {0} modifier is not allowed on a {1} declaration"),
  MULTIPLE_ACCESS_MODIFIERS(3038,ERROR,"Only one modifier of public, protected, private is allowed"),
  BAD_MODIFIER_COMBINATION(3039,ERROR,"A {0} may not be declared both {1} and {2}"),        
  NO_MODIFIERS_IN_FOR(3040,ERROR,"No modifiers are allowed in a traditional for statement"),        
  BAD_STATEMENT_EXPRESSION(3041,ERROR,"A Statement Expression is required here - increment, decrement, assignment, method call, or new instance creation expressions"),
  NO_METHOD_NAME(3042,ERROR,"A declaration has no type or no method name or the constructor name does not match the type"),
  NO_REQUIRED_MODIFIER(3042,ERROR,"A {0} is required to be declared {1}"),
  BAD_NUMBER_OF_ARGS(3043,ERROR,"The {0} function has the wrong number of arguments: has {2}, expects {1}"),
  INVALID_EXPRESSION_OR_MISSING_RPAREN(3044,ERROR,"Expression is invalid or right parenthesis is missing near here"),
  DEPRECATED_ARRAY_BRACKETS(3045,WARN,"Placing array type bracket pairs for the return type after the formal argument list is unusual, error-prone and deprecated"),
  NO_PARAMETERIZED_EXCEPTIONS(3046,ERROR,"Exceptions may not be parameterized types"),
  NO_MATCHING_SUPER_CONSTRUCTOR(3047,ERROR,"There is no matching constructor declaration for this super constructor call in {0}"),
  NO_MATCHING_CONSTRUCTOR(3048,ERROR,"There is no matching constructor declaration for this constructor invocation for type {0}"),
  EXPECTED_IN_IMPORT(3049,ERROR,"Expected {0} here, after an import or static keyword in an import declaration"),
  IGNORED_SPECSPATH_ELEMENT(3050,WARN,"Ignoring specspath element that could not be found: {0}"),
  UNEXPECTED_TOKEN(3051,ERROR,"Recognition error in the parser"),
  
  
  // JML parsing errors
  
  MISSING_SEMICOLON_IN_SPECIFICATION(3500,WARN,"A semicolon is expected before the end of the annotation comment"),
  IMPORT_NOT_MODEL(3501,ERROR,"An import statement in an annotation must be a model import"),
  IMPORT_ONLY_MODEL(3502,ERROR,"A model import statement may not have any modifiers other than model"),
  NO_GHOST_AND_MODEL(3503,ERROR,"A declaration may not be declared both ghost and model"),
  NEITHER_GHOST_NOR_MODEL(3504,ERROR,"A JML declaration must be declared either model or ghost"),
  BAD_DECL_LOCATION(3505,ERROR,"A JML specification {1} must be a {0}"),
  UNTERMINATED_JML_INFORMAL_SPEC(3506,ERROR,"A JML informal specification was not terminated with *) before the end of input or end of the JML comment"),
  NOT_REDUNDANT(3507,ERROR,"This keyword does not have a _redundantly version"),
  MISPLACED_METHOD_SPEC_CLAUSES(3508,ERROR,"Method specification clauses must directly precede a method declaration"),
  MISPLACED_SPEC_CLAUSE(3509,ERROR,"This specification clause is misplaced within the body of the type declaration"),
  MISPLACED_JML_DECL(3510,ERROR,"This {0} is misplaced; it should be {1}."),
  MISPLACED_MODIFIERS(3511,ERROR,"This modifier is not placed just prior to an appropriate declaration"),
  MISPLACED_IN_MAPS_CLAUSE(3512,ERROR,"An in or maps clause must immediately follow a field declaration"),
  MISPLACED_METHOD_SPECS(3513,ERROR,"Method specification clauses must immediately precede a method declaration"),
  MISPLACED_REFINE(3514,ERROR,"A refines specification must follow any package declaration and precede any imports"),
  MISPLACED_MODEL_IMPORT(3515,ERROR,"A model import declaration must follow any package and refine declarations and precede any type declarations"),
  MULTIPLE_REFINE(3516,ERROR,"At most one refine declaration is allowed per compilation unit"),
  INVALID_INITIALIZER(3517,ERROR,"No initializers are allowed in a quantified expression"),
  NO_RANGE_EXPRESSION(3518,ERROR,"A {0} quantified expression must have a range predicate"),
  MISSING_END_SPEC_GROUP(3519,ERROR,"There is no |} to match this specification group beginning"),
  EXTRA_END_SPEC_GROUP(3520,ERROR,"There is no beginning {| to match this specification group ending"),
  BAD_SPEC_GROUP(3521,ERROR,"A {| may not immediately follow a closing |}"),
  MISPLACED_MODEL_PROGRAM(3522,ERROR,"A model_program may not be in a nested specification case nor may it follow other specification clauses"),
  ALSO_AFTER_MODEL_PROGRAM(3523,ERROR,"A model_program must be followed by an also or the end of the specifications"),
  MULTIPLE_BEHAVIOR_KEYWORDS(3524,ERROR,"Each behavior keyword must begin a top-level specification case"), 
  FORALL_HAS_INIT(3525,ERROR,"A forall declaration may not have an initializer"),
  OLD_HAS_NO_INIT(3526,ERROR,"An old declaration must have an initializer"),
  OUT_OF_ORDER_CLAUSE(3527,ERROR,"This method specification clause is out of order and is ignored"),
  OUT_OF_ORDER_WARNING(3528,WARN,"This method specification clause is out of order"),
  NO_EXAMPLE_NESTING(3529,WARN,"Nesting of specifications is not allowed in examples"),
  DUPLICATE_KEYWORD(3530,WARN,"JML only allows one {0} section per method specification; use also to join multiple sections"),
  OUT_OF_ORDER_EXAMPLE(3531,WARN,"JML requires implies_that sections to preceded for_example sections"),
  SUPERFLUOUS_SIGNALS_CLAUSE(3532,WARN,"This signals clause is superfluous, since it does not restrict the postcondition at all"),
  MISPLACED_MODEL_TYPEDECL(3533,ERROR,"A model type declaration must follow any package, refine, and import declarations"),
  NO_SUCH_METHOD(3534,ERROR,"No method with this signature found"),
  
  // Java type checking errors
  
  BAD_INFIX_TYPES(3600,ERROR,"Infix operator {0} is not defined for operand types {1} and {2}"),
  BAD_PREFIX_TYPES(3601,ERROR,"Prefix operator {0} is not defined for operand type {1}"),
  BAD_POSTFIX_TYPES(3602,ERROR,"Postfix operator {0} is not defined for operand type {1}"),
  BAD_INIT_TYPE(3603,ERROR,"A value of type {0} cannot be used to initialize a variable of type {1}"),
  BAD_ASSIGNMENT_TYPES(3604,ERROR,"Assignment operator {0} is not defined for operand types {1} and {2}"),
  CONDITIONAL_TYPE(3605,ERROR,"The types in a conditional expression are mismatched: {0} and {1}"),
  BAD_TYPE(3606,ERROR,"The {0} has type {1} instead of {2}"),
  BAD_LABEL(3607,ERROR,"The label of the {0} statement does not match the label of any enclosing statement"),
  RETURN_TYPE_NOT_VOID(3608,ERROR,"This method has a void return type and does not expect an expression in the return statement"),
  BAD_RETURN_TYPE(3609,ERROR,"The return statement expression has type {0}, which is not assignable to the method''s declared return type, {1}"),
  RETURN_TYPE_SHOULD_NOT_BE_VOID(3610,ERROR,"The return statement must contain an expression of type {0}"),
  UNDEFINED_NAME(3611,ERROR,"The variable or field name {0} cannot be found"),
  NO_SUCH_TYPE(3612,ERROR,"No type with this name could be found: {0}"),
  NO_SUCH_TYPE_OR_PACKAGE(3613,ERROR,"No type or package with this name could be found: {0}"),
  DUPLICATE_IMPORT(3614,ERROR,"The type {0} is imported through multiple import declarations: {1} and {2}"),
  BAD_ABSTRACT(3615,ERROR,"A method may not be declared abstract if it\'s containing class is not abstract"),
  BAD_ABSTRACT_CONSTRUCTOR(3616,ERROR,"A constructor may not be declared abstract"),
  DUPLICATE_STATIC_IMPORT(3614,ERROR,"The name {0} is imported through multiple static import declarations: {1} and {2}"),
  BAD_LOOKUP(3615,ERROR,"Could not find {0} as a member of type {1}"),
  DUPLICATE_FIELD_REFERENCE(3616,ERROR,"Field reference {0} is ambiguous between declarations in types {1} and {2}"),
  DUPLICATE_TYPE_REFERENCE(3617,ERROR,"Type reference {0} is ambiguous between types {1} and {2}"),
  BAD_CAST(3618,ERROR,"Cannot cast an expression of type {0} to type {1}"),
  UNDEFINED_NAME_IN_TYPE(3619,ERROR,"The variable or field name {0} cannot be found in type {1}"),
  
  
  
  
  // JML type checking errors
  BAD_SET_STATEMENT(3700,ERROR,"A JML set statement must contain an assignment statement"),
  INTERNAL_EXCEPTION(3701,ERROR,"An internal error occurred during {0}: {1}\n{2}"),
  DUPLICATE_DECLARATION(3702,ERROR,"The variable {0} is declared more than once"),
  BAD_SIGNALS_EXCEPTION_TYPE(3703,ERROR,"The Exception type is {0}, but is supposed to be a subtype of java.lang.Exception"),
  CIRCULAR_REFINEMENT(3704,ERROR,"Illegal circular refinement sequence containing {0} beginning with {1}"),
  MISSING_REFINEMENT(3705,ERROR,"Refinement sequence beginning with {0} leads to {1}, which refines {2}, which does not exist - check the specs path for package {3}"),
  NOT_IN_REFINEMENT_SEQUENCE(3706,WARN,"The file {0} is not in its own refinement sequence{1}"),
  
  // Other miscellaneous errors
  /** An input file or directory specified by the user (on the command line) does not exist. */
  UNKNOWN_INPUT(3900,WARN,"An input element could not be found in the file system: {0}"),
  /** An element of the classpath specified by the user (on the command line) does not exist. */
  UNKNOWN_CLASSPATH(3901,WARN,"An element of the classpath could not be found: {0}"),
  /** The user-specified classpath is empty. */
  ZERO_LENGTH_CLASSPATH(3902,WARN,"The classpath is empty (except the JRE library)"),
  /** No files found */
  NO_INPUTS(3903,ERROR,"There were no files specified on the command-line"),
  /** An error, such as an io error, occurred on handling this input */
  ERROR_INPUT(3904,ERROR,"An error occurred on finding this input: {0}; {1}"),
  /** An element of the classpath specified by the user (on the command line) does not exist. */
  DUPLICATE_CLASSPATH(3905,WARN,"Duplicate classpath element: {0}"),
  /** Some error occurred in loading an element of the classpath. */
  ERROR_IN_CLASSPATH(3906,WARN,"Failed to load a classpath element: {0}; {1}"),
  /** Generic unexpected problem, but recoverable */
  UNEXPECTED_RECOVERABLE_PROBLEM(3907,WARN,"{0}"),
  /** Errors when parsing the command line arguments */
  COMMAND_LINE_ERRORS(3908,ERROR,"{0}"),
  /** An element of the specspath specified by the user (on the command line) does not exist. */
  DUPLICATE_SPECSPATH(3909,WARN,"Duplicate specspath element: {0}"),
  /** The internal specification libaray could not be read */
  NOINTERNALSPECS(3910,WARN,"Could not locate the internal specification library: {0}"),
  
  /** Used when an unexpected exception occurs */
  UNEXPECTED_EXCEPTION(3996,ERROR,"Unexpected Exception - see console or error log: {0}"),        
  /** Used when an anomalous situation is encountered, worthy of reporting, but is recoverable */
  RECOVERABLE(3997,WARN,"Recoverable error:"),
  /** Used when a call to Eclipse functionality fails,e.g. JavaModelException or CoreException */
  ECLIPSE(3998,ERROR,"ECLIPSE ENVIRONMENT FAILURE: {0}"),  
  /** Use to note to the user that some feature is not completely handled. */
  NOT_IMPLEMENTED(3999,ERROR,"Grammar feature is not yet implemented: {0}"),


  ;
  
  
  
  /**
   * An integer id that uniquely identifies the message
   */
  private int id;
  
  /**
   * A template in java.text.MessageFormat style
   */
  private String template;
  
  /**
   * An int that indicates the default severity of the problem
   */
  private int severity;
  
  /**
   * Constructor for an enum constant of this class
   * @param id The unique int identifier
   * @param severity the severity (IGNORE, WARNING, ERROR) of the problem
   * @param template The MessageFormat style message
   */
  private Problems(int id, int severity, String template) {
    this.id = id;
    this.severity = severity;
    this.template = template;
  }
  
  /**
   * Returns the template for the Problems object
   */
  public String toString() {
    return template;
  }
  
  /**
   * Returns the message consisting of the template with the arguments
   * substituted.
   * @param messageArgs The arguments to substitute in the template
   * @return The resulting String
   */
  public String toString(Object... messageArgs) {
    return MessageFormat.format(template,messageArgs);
  }
  
  /** Returns the unique identifier of the message
   * @return The unique identifier of the message
   */
  public int id() {
    return id;
  }
  
  /** Returns the default severity of the problem, consistent with the
   * use of severity by the IProblem interface
   * @return The default severity of the problem
   */
  public int severity() {
    return severity;
  }
  
  /** Sets the severity of the problem
   * @param severity the severity (IGNORE, WARNING, ERROR) of the problem
   */
  public void setSeverity(int severity) {
    this.severity = severity;
  }

  /** A utility function to convert an exception stack to a String
   * @param e the exception
   * @return a String containing the stack trace
   */
  public static String exceptionStack(Throwable e) {
    ByteArrayOutputStream b = new ByteArrayOutputStream();
    PrintWriter pw = new PrintWriter(b);
    e.printStackTrace(pw);
    pw.close();
    return b.toString();
  }
}

