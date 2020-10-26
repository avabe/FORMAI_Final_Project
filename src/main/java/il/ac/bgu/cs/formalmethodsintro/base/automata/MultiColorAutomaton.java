package il.ac.bgu.cs.formalmethodsintro.base.automata;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class MultiColorAutomaton<State, L> {

    private final Set<State> initial;
    private final Map<Integer, Set<State>> accepting;
    private final Map<State, Map<Set<L>, Set<State>>> transitions;

    public MultiColorAutomaton() {
        transitions = new HashMap<>();
        initial = new HashSet<>();
        accepting = new HashMap<>();
    }

    public void addState(State s) {
        if (!transitions.containsKey(s)) {
            transitions.put(s, new HashMap<>());
        }
    }

    public void addTransition(State source, Set<L> symbol, State destination) {
        if (!transitions.containsKey(source)) {
            addState(source);
        }

        if (!transitions.containsKey(destination)) {
            addState(destination);
        }

        Set<State> set = transitions.get(source).get(symbol);
        if (set == null) {
            set = new HashSet<>();
            transitions.get(source).put(symbol, set);
        }
        set.add(destination);
    }

    public Set<State> getAcceptingStates(int color) {
        Set<State> acc = accepting.get(color);

        if (acc == null) {
            acc = new HashSet<>();
            accepting.put(color, acc);
        }

        return acc;
    }

    public Set<State> getInitialStates() {
        return initial;
    }

    public Map<State, Map<Set<L>, Set<State>>> getTransitions() {
        return transitions;
    }

    public Set<State> nextStates(State source, Set<L> symbol) {
        if (!transitions.containsKey(source)) {
            throw new IllegalArgumentException();
        } else {
            return transitions.get(source).get(symbol);
        }
    }

    public void setAccepting(State s, int color) {
        Set<State> acc = accepting.get(color);

        if (acc == null) {
            acc = new HashSet<>();
            accepting.put(color, acc);
        }

        addState(s);
        acc.add(s);
    }

    public void setInitial(State s) {
        addState(s);
        initial.add(s);
    }

    public Set<Integer> getColors() {
        return accepting.keySet();
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 53 * hash + Objects.hashCode(this.initial);
        hash = 53 * hash + Objects.hashCode(this.accepting);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final MultiColorAutomaton<?, ?> other = (MultiColorAutomaton<?, ?>) obj;
        if (!Objects.equals(this.initial, other.initial)) {
            return false;
        }
        if (!Objects.equals(this.accepting, other.accepting)) {
            return false;
        }
        return Objects.equals(this.transitions, other.transitions);
    }

}
