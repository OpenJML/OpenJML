package freeboogie.ast.gen;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import java.util.logging.Logger;

import freeboogie.util.Err;

/**
 * The template parser. This is where the output is produced.
 * By default the output is set to {@code null} which means that
 * the beginning of a template can contain arbitrary comments.
 * The <tt>\file</tt> macro switches the output to another
 * destination. (A common trick is to use /dev/stdout as a sink
 * to inform the user about the progress of the template processing.)
 * 
 * Some macros must be nested in others. For example \class_name
 * must be nested in \classes or \normal_classes or \abstract_classes.
 * If the nesting is incorrect a warning is printed on the console
 * and <WRONG_MACRO> goes to the output. If there are nested \classes
 * macros then only the innermost one is considered. (In most
 * applications nested list macros should not be needed.)
 * 
 * TODO: consider adding an optional parameter for macros that indicates
 *       a nesting level such that, for example, the following is legal
 *          \classes{(\classes{\ClassName[0],\ClassName[1]})}
 *       and prints all pairs of class names.
 * 
 * TODO If nested list macros are deemed unnecessary then switch the
 *      context stacks to single (nullable) elements.
 *      
 * TODO The duplicated code is a bit too much for my taste.
 * 
 * TODO I may want to add macro definitions such as
 *      \def\Type{\if_primitive{\if_enum{\ClassName.}{}\Membertype}{\MemberType}}
 *      It gets tedious to write it.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class TemplateParser {
  /*
   * The function |processTop| is the main loop. It reads a
   * token and distributes the work to various |process*| methods.
   * It is also responsible for stopping when a certain closing
   * } or ] is met (and it reads it). The variables |curlyCnt|
   * and |bracketCnt| count the nesting (since the beginning
   * of the template) and are used to identify on which ] or }
   * we should stop. Notice that the user shouldn't use unbalanaced
   * paranthesis in the template for this scheme to work.
   * 
   * The stacks |*Context| contain information about the nested
   * macros seen in the input.
   */

  private static final Logger log = Logger.getLogger("freeboogie.ast.gen");
  
  private TemplateLexer lexer;
  private Grammar grammar;
  
  private Stack<AgClass> classContext;
  private Stack<AgMember> memberContext;
  private Stack<AgEnum> enumContext;
  private Stack<String> valueContext;
  private Stack<String> invariantContext;
  
  private Writer output;
  
  private int curlyCnt; // counts {} nesting
  private int bracketCnt; // counts [] nesting
  
  private TemplateToken lastToken;
  
  private boolean balancedWarning = true;

  // classes are processed in alphabetical order
  private Set<AgClass> orderedClasses;
  private Set<AgClass> abstractClasses;
  private Set<AgClass> normalClasses;
  
  /**
   * @param fileName the name of the template file
   * @throws FileNotFoundException if the template file is not found
   */
  public TemplateParser(String fileName) throws FileNotFoundException {
    FileInputStream fis = new FileInputStream(fileName);
    CharStream cs = new CharStream(fis, fileName);
    lexer = new TemplateLexer(cs);
    output = null;
    lastToken = null;
    
    classContext = new Stack<AgClass>();
    memberContext = new Stack<AgMember>();
    enumContext = new Stack<AgEnum>();
    valueContext = new Stack<String>();
    invariantContext = new Stack<String>();

    orderedClasses = null;
    abstractClasses = null;
    normalClasses = null;
  }

  /**
   * Processes the current template using grammar {@code g}.
   * @param g the grammar
   * @throws IOException 
   */
  public void process(Grammar g) throws IOException {
    grammar = g;
    processTop(Integer.MAX_VALUE, Integer.MAX_VALUE);
    if (output != null) output.flush();
  }

  /*
   * For now I will enforce {} and [] to be balanced pretty much 
   * everywhere.
   * 
   * The function dispatches the work to the appropriate worker.
   * It also takes care of stoping when a } or a ] with a given
   * nesting level is seen.
   */
  private void processTop(int curlyStop, int bracketStop) throws IOException {
    readToken();
    while (lastToken != null) {
      switch (lastToken.type) {
      case FILE:
        processFile(); break;
      case CLASSES:
        processClasses(); break;
      case IF_ABSTRACT:
        processIsAbstract(); break;
      case ABSTRACT_CLASSES:
        processAbstractClasses(); break;
      case NORMAL_CLASSES:
        processNormalClasses(); break;
      case CLASS_NAME:
        processClassName(); break;
      case BASE_NAME:
        processBaseName(); break;
      case MEMBERS:
        processMembers(); break;
      case MEMBER_TYPE:
        processMemberType(); break;
      case MEMBER_NAME:
        processMemberName(); break;
      case IF_PRIMITIVE:
        processIfPrimitive(); break;
      case IF_NONNULL:
        processIfNonnull(); break;
      case IF_ENUM:
        processIfEnum(); break;
      case CHILDREN:
        processChildren(); break;
      case PRIMITIVES:
        processPrimitives(); break;
      case ENUMS:
        processEnums(); break;
      case ENUM_NAME:
        processEnumName(); break;
      case VALUES:
        processValues(); break;
      case VALUE_NAME:
        processValueName(); break;
      case INVARIANTS:
        processInvariants(); break;
      case INV:
        processInv(); break;
      default:
        if (curlyStop == curlyCnt || bracketStop == bracketCnt) return;
        write(lastToken.rep);
      }
      if (curlyCnt == 0 && bracketCnt == 0) lexer.eat();
      readToken();
    }
  }
  
  /*
   * Reads { file_name } and makes output point to file_name.
   * If the file cannot be open then switch to a null output
   * and give a warning.
   */
  private void processFile() throws IOException {
    readToken();
    if (lastToken.type != TemplateToken.Type.LC) {
      err("Hey, \\file should be followed by {");
      Err.help("I'm gonna stop producing output.");
      switchOutput(null);
      skipToRc(curlyCnt, true);
      return;
    }
    StringWriter sw = new StringWriter();
    switchOutput(sw);
    processTop(curlyCnt - 1, Integer.MAX_VALUE);
    String fn = sw.toString().replaceAll("\\s+", "_");
    try {
      FileWriter fw = new FileWriter(fn);
      switchOutput(fw);
      log.info("The output goes to the file " + fn);
    } catch (IOException e) {
      err("Cannot write to file " + fn);
      Err.help("I'm gonna stop producing output.");
      switchOutput(null);
    }
  }
  
  private <T> void processList(Collection<T> set, Stack<T> stack) throws IOException {
    readToken();
    String separator = "";
    if (lastToken.type == TemplateToken.Type.LB) {
      readToken();
      if (lastToken.type != TemplateToken.Type.OTHER) {
         err("Sorry, you can't use any funny stuff as a separator.");
        skipToRc(curlyCnt, true);
        return;
      }
      separator = lastToken.rep;
      readToken();
      if (lastToken.type != TemplateToken.Type.RB) {
        err("The separator is not properly closed by ].");
        skipToRb(bracketCnt - 1, true);
      }
      if (lastToken.type != TemplateToken.Type.LC)
        readToken();
    }
    if (lastToken.type != TemplateToken.Type.LC) {
      err("There should be a { after a list macro.");
      skipToRc(curlyCnt - 1, true);
      return;
    }
    if (set.isEmpty()) skipToRc(curlyCnt - 1, false);
    int i = 0; // TODO is there another way to check if I'm looking at the last?
    for (T el : set) {
      if (i != 0) {
        lexer.rewind();
        write(separator);
        ++curlyCnt;
      }
      if (++i != set.size()) lexer.mark();
        
      stack.add(el);
      processTop(curlyCnt - 1, Integer.MAX_VALUE);
      stack.pop();
    }
  }
  
  private void processClasses() throws IOException {
    splitClasses();
    processList(orderedClasses, classContext);
  }
  
  private void processYesNo(boolean yes) throws IOException {
    if (!yes) skipToRc(curlyCnt, false);
    readToken();
    if (lastToken.type != TemplateToken.Type.LC) {
      err("An if macro should be followed by {yes}{no}.");
      Err.help("I'll act as if <" + lastToken.rep + "> was {.");
    }
    processTop(curlyCnt - 1, Integer.MAX_VALUE);
    if (yes) skipToRc(curlyCnt, false);
  }
  
  private void processIsAbstract() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(classContext.peek().members.isEmpty());
  }
  
  private void splitClasses() {
    if (abstractClasses != null) return;
    orderedClasses = new TreeSet<AgClass>();
    abstractClasses = new TreeSet<AgClass>();
    normalClasses = new TreeSet<AgClass>();
    for (AgClass c: grammar.classes.values()) {
      orderedClasses.add(c);
      if (c.members.isEmpty())
        abstractClasses.add(c);
      else
        normalClasses.add(c);
    }
  }
  
  private void processAbstractClasses() throws IOException {
    splitClasses();
    processList(abstractClasses, classContext);
  }
  
  private void processNormalClasses() throws IOException {
    splitClasses();
    processList(normalClasses, classContext);
  }
  
  private <T> boolean checkContext(Stack<T> context) throws IOException {
    if (context.isEmpty()) {
      err("Macro used in a wrong context.");
      write("<WRONG_MACRO>");
      return false;
    }
    return true;
  }
  
  private void processClassName() throws IOException {
    if (checkContext(classContext)) 
      writeId(classContext.peek().name, lastToken.idCase);
  }
  
  private void processBaseName() throws IOException {
    if (checkContext(classContext))  
      writeId(classContext.peek().base, lastToken.idCase);
  }
  
  private void processMembers() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().members, memberContext);
  }
  
  private void processMemberType() throws IOException {
    if (checkContext(memberContext))
      writeId(memberContext.peek().type, lastToken.idCase);
  }
  
  private void processMemberName() throws IOException {
    if (checkContext(memberContext))
      writeId(memberContext.peek().name, lastToken.idCase);
  }
  
  private void processIfPrimitive() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(memberContext.peek().primitive);
  }
  
  private void processIfNonnull() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(memberContext.peek().nonNull);
  }
  
  private void processIfEnum() throws IOException {
    if (!checkContext(memberContext)) {
      skipToRc(curlyCnt, true);
      skipToRc(curlyCnt, true);
      return;
    }
    processYesNo(memberContext.peek().isenum);
  }

  private void processChildren() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    List<AgMember> children = new ArrayList<AgMember>(23);
    for (AgMember m : classContext.peek().members)
      if (!m.primitive) children.add(m);
    processList(children, memberContext);
  }
  
  private void processPrimitives() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    List<AgMember> primitives = new ArrayList<AgMember>(23);
    for (AgMember m : classContext.peek().members)
      if (m.primitive) primitives.add(m);
    processList(primitives, memberContext);
  }
  
  private void processEnums() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().enums, enumContext);
  }
  
  private void processEnumName() throws IOException {
    if (checkContext(enumContext))
      writeId(enumContext.peek().name, lastToken.idCase);
  }
  
  private void processValues() throws IOException {
    if (!checkContext(enumContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(enumContext.peek().values, valueContext);
  }
  
  private void processValueName() throws IOException {
    if (checkContext(valueContext))
      writeId(valueContext.peek(), lastToken.idCase);
  }
  
  private void processInvariants() throws IOException {
    if (!checkContext(classContext)) {
      skipToRc(curlyCnt, true);
      return;
    }
    processList(classContext.peek().invariants, invariantContext);
  }
  
  private void processInv() throws IOException {
    if (checkContext(invariantContext))
      write(invariantContext.peek());
  }
  
  private void skipToRc(int cnt, boolean warn) throws IOException {
    skipToR(cnt, Integer.MAX_VALUE, warn);
  }
  
  private void skipToRb(int cnt, boolean warn) throws IOException {
    skipToR(Integer.MAX_VALUE, cnt, warn);
  }
  
  /*
   * This reads the input until either it finishes or the } or ]
   * with the specified nesting level is encountered. 
   */
  private void skipToR(int curlyStop, int bracketStop, boolean w) throws IOException {
    StringBuilder sb = new StringBuilder();
    while (true) {
      readToken();
      if (lastToken == null) break;
      sb.append(lastToken.rep);
      if (lastToken.type == TemplateToken.Type.RC 
        && curlyStop == curlyCnt) break;
      if (lastToken.type == TemplateToken.Type.RB 
        && bracketStop == bracketCnt) break;
    } 
    if (w) Err.help("I'm skipping: " + sb);
  }
  
  private void readToken() throws IOException {
    lastToken = lexer.next();
    if (lastToken == null) return;
    log.finer("read token <" + lastToken.rep + "> of type " + lastToken.type);
    if (lastToken.type == TemplateToken.Type.LB) ++bracketCnt;
    if (lastToken.type == TemplateToken.Type.RB) --bracketCnt;
    if (lastToken.type == TemplateToken.Type.LC) ++curlyCnt;
    if (lastToken.type == TemplateToken.Type.RC) --curlyCnt;
    if (balancedWarning && (curlyCnt < 0 || bracketCnt < 0)) {
      err("You are on thin ice.");
      Err.help("I don't guarantee what happens if you use unbalaced [] or {}.");
      balancedWarning = false;
    }
  }
  
  private void switchOutput(Writer newOutput) throws IOException {
    if (output != null) output.flush();
    output = newOutput;
    if (output == null) 
      log.fine("Output is turned off.");
  }

  /*
   * Writes |id| using the case convention |cs|.
   */
  // candidate for memoization
  private void writeId(String id, TemplateToken.Case cs) throws IOException {
    if (cs == TemplateToken.Case.ORIGINAL_CASE) {
      write(id);
      return;
    }
    StringBuilder res = new StringBuilder(id.length());
    boolean first = true;
    boolean prevIs_ = true;
    boolean prevIsUpper = false;
    for (int i = 0; i < id.length(); ++i) {
      char c = id.charAt(i);
      if (c == '_') prevIs_ = true;
      else {
        boolean thisIsUpper = Character.isUpperCase(c);
        if (prevIs_ || (thisIsUpper && !prevIsUpper)) {
          // beginning of word
          switch (cs) {
          case CAMEL_CASE:
            if (first) res.append(Character.toLowerCase(c));
            else res.append(Character.toUpperCase(c));
            break;
          case PASCAL_CASE:
            res.append(Character.toUpperCase(c));
            break;
          case LOWER_CASE:
            if (!first) res.append('_');
            res.append(Character.toLowerCase(c));
            break;
          case UPPER_CASE:
            if (!first) res.append('_');
            res.append(Character.toUpperCase(c));
            break;
          default:
            Err.fatal("Don't know which case to use for " + id);
          }
        } else {
          // the rest of letters
          switch (cs) {
          case UPPER_CASE:
            res.append(Character.toUpperCase(c));
            break;
          default:
            res.append(Character.toLowerCase(c));
          }
        }
        first = false;
        prevIs_ = false;
        prevIsUpper = thisIsUpper;
      }
    }
    write(res.toString());
  }
  
  /*
   * Sends |s| to the |output|.
   */
  private void write(String s) throws IOException {
    if (output != null) {
      output.write(s);
    }
  }
  
  private void err(String e) {
    Err.error(lexer.getName() + lexer.getLoc() + ": " + e);
  }
}
