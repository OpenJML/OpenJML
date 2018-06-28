import com.google.common.base.Function;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;

import java.util.Collection;
import java.util.Set;


public class Test {

  public void blah(Collection<String> tagNames) {
    final Set<String> lowerTagNames = Sets.newHashSet(Iterables.transform(tagNames, new Function<String, String>() {
      @Override
      public String apply(String s) {
        return s.toLowerCase();
      }
    }));
  }

}