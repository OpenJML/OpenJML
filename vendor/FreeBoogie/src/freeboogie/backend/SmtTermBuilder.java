package freeboogie.backend;

/**
 * Builds a term tree, which looks like an S-expression.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SmtTermBuilder extends TermBuilder {

  /* @see freeboogie.backend.TermBuilder#reallyMk(java.lang.String, java.lang.Object) */
  @Override
  protected Term reallyMk(Sort sort, String termId, Object a) {
    return new SmtTerm(sort, termId, a);
  }

  /* @see freeboogie.backend.TermBuilder#reallyMk(java.lang.String, freeboogie.backend.Term[]) */
  @Override
  protected Term reallyMk(Sort sort, String termId, Term[] a) {
    return new SmtTerm(sort, termId, a);
  }

  /* @see freeboogie.backend.TermBuilder#reallyMkNary(java.lang.String, freeboogie.backend.Term[]) */
  @Override
  protected Term reallyMkNary(Sort sort, String termId, Term[] a) {
    return new SmtTerm(sort, termId, a);
  }

}
