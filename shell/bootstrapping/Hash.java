import tlc2.value.impl.IntValue;
import tlc2.value.impl.Value;

public class Hash {
    
    public static Value Hash(Value v) {
        return IntValue.gen(v.hashCode());
    }
}
