public class TRY {

  public static class CL implements AutoCloseable {
    String id;
    public CL(String id) { this.id = id; }
    public void close() throws RuntimeException {
        System.out.println("Closing " + id);
       throw new RuntimeException(id);
    }
  }
  public static void main(String ... args) {
    try {
      try ( var a = new CL("A"); var b = new CL("B") ) {
      }
    } catch (Exception e) {
      System.out.println(e.getMessage());
      for (var ee: e.getSuppressed()) {
        System.out.println("SUPPRESSED " + ee);
      }
    }
  }
}
    
