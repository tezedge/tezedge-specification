import tlc2.value.impl.IntValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;

import java.util.*;

public class Samples {
    
  public static Value Samples(IntValue good_node, TupleValue hash_seq) {
    int x = (int) Math.pow(2, good_node.val);
    Random rng = new Random(x);
    List<IntValue> values = new ArrayList<>();
    values.add((IntValue) hash_seq.getElem(0));
    int n = hash_seq.size();
    for (int i = 1; i < n; i++) {
      boolean keep = rng.nextBoolean();
      if (keep) {
        values.add((IntValue) hash_seq.getElem(i));
      }
    };
    return new TupleValue(values.toArray(new Value[0]));
  }
}
