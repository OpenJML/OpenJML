import java.nio.CharBuffer;
import java.io.*;

public class Transform {

static final String s1 = "span class=\"textboxed\"";
static final String r1 = "div class=\"textboxed\"";


static final String s2 = "</span></span><span class=\"textboxed\"><span style=\"font-family:monospace\">";

static final String s3 = "nowrap\" ><div class=\"textboxed\">";
static final String r3 = "nowrap\" >";

static final String s4 = "</div>";

public static void main(String ... args) {

try{
    File f = new File(args[0]);
    Reader r = new FileReader(f);
    CharBuffer c = CharBuffer.allocate(1000000);
    r.read(c);
    r.close();
    c.limit(c.position());
    c.rewind();
    String input = c.toString();


    StringBuilder output = new StringBuilder();
    String rest = input;
    while (!rest.isEmpty()) {
      
      int k = rest.indexOf(s1);
      if (k >= 0)  {
          output.append(rest.substring(0,k));
       	  output.append(r1);
          rest = rest.substring(k + s1.length());
          int count = 0;
          int pos = 0;
          do {
          k = rest.indexOf("span",pos);
          if (rest.charAt(k-1) == '<') count++;
          else if (rest.charAt(k-1) == '/') {
            if (rest.substring(k-2).startsWith(s2)) {
                output.append(rest.substring(0,k-2)); 
                rest = rest.substring(k-2 + s2.length());
                pos = 0; k = -4;
            } else {
                count--;
            }
          }
          pos = k + 4;
          } while (count >= 0);
          output.append(rest.substring(0,k));
          output.append("div");
          rest = rest.substring(k+4);

      } else {
          output.append(rest);
          rest = "";
      }
      
    }

    rest = output.toString();
    output.setLength(0);

    for (int kk = 0; kk<10; kk++) {
        int k = rest.indexOf(s3);
        output.append(rest.substring(0,k));
        output.append(r3);
        rest = rest.substring(k+s3.length());
        k = rest.indexOf(s4);
        output.append(rest.substring(0,k));
        rest = rest.substring(k+s4.length());
    }
    output.append(rest);

    f.renameTo(new File(args[0] + ".backup"));

    Writer w = new FileWriter(f);
    w.append(output);
    w.close();



} catch (Exception e) {
  System.out.println(e);
}

}
}
