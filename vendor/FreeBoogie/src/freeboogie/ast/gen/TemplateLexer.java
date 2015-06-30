package freeboogie.ast.gen;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import freeboogie.util.Err;

/**
 * Lexer for template files. The macros and teh delimiters they use 
 * are recognized; everything inbetween is considered as the token
 * `other' and will be later copied verabtim to the output. 
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TemplateLexer extends PeekStream<TemplateToken> {
  
  private CharStream stream;
  private Character lastChar;
  private StringBuilder sb;
  
  private static final Map<String, TemplateToken.Type> macros =
    new HashMap<String, TemplateToken.Type>(101);
  private static final Map<Character, TemplateToken.Type> oneCharTokens =
    new HashMap<Character, TemplateToken.Type>(11);
  private static int maxMacroLen;
  private static final Map<String, TemplateToken.Case> idCases =
    new HashMap<String, TemplateToken.Case>(7);
  
  static {
    macros.put("\\file", TemplateToken.Type.FILE);
    macros.put("\\classes", TemplateToken.Type.CLASSES);
    macros.put("\\if_abstract", TemplateToken.Type.IF_ABSTRACT);
    macros.put("\\abstract_classes", TemplateToken.Type.ABSTRACT_CLASSES);
    macros.put("\\normal_classes", TemplateToken.Type.NORMAL_CLASSES);
    macros.put("\\class_name", TemplateToken.Type.CLASS_NAME);
    macros.put("\\className", TemplateToken.Type.CLASS_NAME);
    macros.put("\\ClassName", TemplateToken.Type.CLASS_NAME);
    macros.put("\\CLASS_NAME", TemplateToken.Type.CLASS_NAME);
    macros.put("\\Classname", TemplateToken.Type.CLASS_NAME);
    macros.put("\\base_name", TemplateToken.Type.BASE_NAME);
    macros.put("\\baseName", TemplateToken.Type.BASE_NAME);
    macros.put("\\BaseName", TemplateToken.Type.BASE_NAME);
    macros.put("\\BASE_NAME", TemplateToken.Type.BASE_NAME);
    macros.put("\\Basename", TemplateToken.Type.BASE_NAME);
    macros.put("\\members", TemplateToken.Type.MEMBERS);
    macros.put("\\member_type", TemplateToken.Type.MEMBER_TYPE);
    macros.put("\\memberType", TemplateToken.Type.MEMBER_TYPE);
    macros.put("\\MemberType", TemplateToken.Type.MEMBER_TYPE);
    macros.put("\\MEMBER_TYPE", TemplateToken.Type.MEMBER_TYPE);
    macros.put("\\Membertype", TemplateToken.Type.MEMBER_TYPE);
    macros.put("\\member_name", TemplateToken.Type.MEMBER_NAME);
    macros.put("\\memberName", TemplateToken.Type.MEMBER_NAME);
    macros.put("\\MemberName", TemplateToken.Type.MEMBER_NAME);
    macros.put("\\MEMBER_NAME", TemplateToken.Type.MEMBER_NAME);
    macros.put("\\Membername", TemplateToken.Type.MEMBER_NAME);
    macros.put("\\if_primitive", TemplateToken.Type.IF_PRIMITIVE);
    macros.put("\\if_nonnull", TemplateToken.Type.IF_NONNULL);
    macros.put("\\if_enum", TemplateToken.Type.IF_ENUM);
    macros.put("\\children", TemplateToken.Type.CHILDREN);
    macros.put("\\primitives", TemplateToken.Type.PRIMITIVES);
    macros.put("\\enums", TemplateToken.Type.ENUMS);
    macros.put("\\enum_name", TemplateToken.Type.ENUM_NAME);
    macros.put("\\enumName", TemplateToken.Type.ENUM_NAME);
    macros.put("\\EnumName", TemplateToken.Type.ENUM_NAME);
    macros.put("\\ENUM_NAME", TemplateToken.Type.ENUM_NAME);
    macros.put("\\Enumname", TemplateToken.Type.ENUM_NAME);
    macros.put("\\values", TemplateToken.Type.VALUES);
    macros.put("\\value_name", TemplateToken.Type.VALUE_NAME);
    macros.put("\\valueName", TemplateToken.Type.VALUE_NAME);
    macros.put("\\ValueName", TemplateToken.Type.VALUE_NAME);
    macros.put("\\VALUE_NAME", TemplateToken.Type.VALUE_NAME);
    macros.put("\\Valuename", TemplateToken.Type.VALUE_NAME);
    macros.put("\\invariants", TemplateToken.Type.INVARIANTS);
    macros.put("\\inv_text", TemplateToken.Type.INV);
    
    idCases.put("\\class_name", TemplateToken.Case.LOWER_CASE);
    idCases.put("\\className", TemplateToken.Case.CAMEL_CASE);
    idCases.put("\\ClassName", TemplateToken.Case.PASCAL_CASE);
    idCases.put("\\CLASS_NAME", TemplateToken.Case.UPPER_CASE);
    idCases.put("\\Classname", TemplateToken.Case.ORIGINAL_CASE);
    idCases.put("\\base_name", TemplateToken.Case.LOWER_CASE);
    idCases.put("\\baseName", TemplateToken.Case.CAMEL_CASE);
    idCases.put("\\BaseName", TemplateToken.Case.PASCAL_CASE);
    idCases.put("\\BASE_NAME", TemplateToken.Case.UPPER_CASE);
    idCases.put("\\Basename", TemplateToken.Case.ORIGINAL_CASE);
    idCases.put("\\member_type", TemplateToken.Case.LOWER_CASE);
    idCases.put("\\memberType", TemplateToken.Case.CAMEL_CASE);
    idCases.put("\\MemberType", TemplateToken.Case.PASCAL_CASE);
    idCases.put("\\MEMBER_TYPE", TemplateToken.Case.UPPER_CASE);
    idCases.put("\\Membertype", TemplateToken.Case.ORIGINAL_CASE);
    idCases.put("\\member_name", TemplateToken.Case.LOWER_CASE);
    idCases.put("\\memberName", TemplateToken.Case.CAMEL_CASE);
    idCases.put("\\MemberName", TemplateToken.Case.PASCAL_CASE);
    idCases.put("\\MEMBER_NAME", TemplateToken.Case.UPPER_CASE);
    idCases.put("\\Membername", TemplateToken.Case.ORIGINAL_CASE);
    idCases.put("\\enum_name", TemplateToken.Case.LOWER_CASE);
    idCases.put("\\enumName", TemplateToken.Case.CAMEL_CASE);
    idCases.put("\\EnumName", TemplateToken.Case.PASCAL_CASE);
    idCases.put("\\ENUM_NAME", TemplateToken.Case.UPPER_CASE);
    idCases.put("\\Enumname", TemplateToken.Case.ORIGINAL_CASE);
    idCases.put("\\value_name", TemplateToken.Case.LOWER_CASE);
    idCases.put("\\valueName", TemplateToken.Case.CAMEL_CASE);
    idCases.put("\\ValueName", TemplateToken.Case.PASCAL_CASE);
    idCases.put("\\VALUE_NAME", TemplateToken.Case.UPPER_CASE);
    idCases.put("\\Valuename", TemplateToken.Case.ORIGINAL_CASE);
    
    
    oneCharTokens.put('[', TemplateToken.Type.LB);
    oneCharTokens.put(']', TemplateToken.Type.RB);
    oneCharTokens.put('{', TemplateToken.Type.LC);
    oneCharTokens.put('}', TemplateToken.Type.RC);
    
    maxMacroLen = 0;
    for (String s : macros.keySet())
      maxMacroLen = Math.max(maxMacroLen, s.length());
  }

  /** 
   * Initialize a lexer. 
   * @param stream the underlying character stream
   */
  public TemplateLexer(CharStream stream) {
    super(new TokenLocation<TemplateToken>());
    this.stream = stream;
    lastChar = null;
  }
  
  @Override
  public String getName() {
    return stream.getName();
  }
  
  /*
   * This method always read ahead one character.
   *  
   * @see freeboogie.ast.gen.PeekStream#read() 
   * @see freeboogie.ast.gen.AgLexer#read()
   */
  @Override
  protected TemplateToken read() throws IOException {
    if (lastChar == null) lastChar = stream.next();
    if (lastChar == null) return null;
    
    TemplateToken.Type type = oneCharTokens.get(lastChar);
    TemplateToken.Case idCase = null;
    sb = new StringBuilder();
    sb.append(lastChar);
    
    if (type != null) {
      lastChar = stream.next();
    } else if (lastChar == '\\') {
      stream.mark();
      // read the macro
      while (sb.length() <= maxMacroLen && !macros.containsKey(sb.toString())) {
        lastChar = stream.next();
        sb.append(lastChar);
      }
      if (sb.length() > maxMacroLen) {
        err("Please don't use '\\' outside macro names.");
        sb.setLength(0);
        sb.append('\\');
        stream.rewind();
        lastChar = null;
        type = TemplateToken.Type.OTHER;
      } else if (lastChar == null) {
        err("The template ends abruptly while I was reading a macro: " + sb);
        type = TemplateToken.Type.OTHER;
      } else {
        lastChar = stream.next();
        type = macros.get(sb.toString());
        idCase = idCases.get(sb.toString());
      }
    } else {
      // read in plain text
      type = TemplateToken.Type.OTHER;
      lastChar = stream.next();
      while (lastChar != null && lastChar != '\\' && !oneCharTokens.containsKey(lastChar)) {
        sb.append(lastChar);
        lastChar = stream.next();
      }
    }
    
    stream.eat();
    return new TemplateToken(type, sb.toString(), idCase);
  }
  
  private void err(String e) {
    Err.error(getName() + stream.getLoc() + ": " + e);
  }
}
