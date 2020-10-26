package il.ac.bgu.cs.formalmethodsintro.base.fairness;

import java.util.Set;

public class FairnessCondition <T>{
    private Set<Set<T>> unconditional;
    private Set<Set<T>> strong;
    private Set<Set<T>> weak;

    public FairnessCondition(Set<Set<T>> unconditional, Set<Set<T>> strong, Set<Set<T>> weak) {
        this.unconditional = unconditional;
        this.strong = strong;
        this.weak = weak;
    }

    public Set<Set<T>> getUnconditional() {
        return unconditional;
    }

    public Set<Set<T>> getStrong() {
        return strong;
    }

    public Set<Set<T>> getWeak() {
        return weak;
    }
}
