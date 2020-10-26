package il.ac.bgu.cs.formalmethodsintro.base.programgraph;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * A data structure for program graphs.
 *
 * @param <L> Type of the locations.
 * @param <A> Type of the actions.
 */
public class ProgramGraph<L, A> {

    /**
     * The set of initial locations of the program graph.
     */
    private final Set<L> initLocations = new HashSet<>();

    /**
     * The set of locations (nodes) of the program graph.
     */
    private final Set<L> locations = new HashSet<>();

    /**
     * The set of transitions (edges) in the program graph.
     */
    private final Set<PGTransition<L, A>> transitions = new HashSet<>();

    /**
     * Initializations for the program.
     */
    private final Set<List<String>> initializations = new HashSet<>();

    /**
     * The name of the program graph.
     */
    private String name;

    /**
     * Add an option for the initial value of the variables. The format of the
     * initialization is a list of actions. For example the initialization
     * {@code asList("x := 15", "y:=9")} says that the initial value of x is 15
     * and that the initial value of y is 9.
     * <p>
     * Note that this method can be called several times with different
     * parameters to allow for nondeterministic initialization.
     *
     * @param init A list of initialization actions.
     */
    public void addInitalization(List<String> init) {
        initializations.add(init);
    }

    /**
     * @return The set of initialization lists.
     */
    public Set<List<String>> getInitalizations() {
        return initializations;
    }

    /**
     * Add an initial state.
     *
     * @param location An location already in the graph
     * @param isInitial whether {@code location} should be an initial location
     * in {@code this}.
     * @throws IllegalArgumentException, if {@code location} is not a location
     * in {@code this}.
     */
    public void setInitial(L location, boolean isInitial) {
        if (isInitial) {
            addLocation(location);
            initLocations.add(location);
        } else {
            initLocations.remove(location);
        }
    }

    /**
     * Ann a new location (node) to the program graph.
     *
     * @param l The name of the new location.
     */
    public void addLocation(L l) {
        locations.add(l);
    }

    /**
     * Add a transition to the program graph.
     *
     * @param t A transition to add.
     */
    public void addTransition(PGTransition<L, A> t) {
        addLocation(t.getFrom());
        addLocation(t.getTo());
        transitions.add(t);
    }

    /**
     * @return The set of initial locations.
     */
    public Set<L> getInitialLocations() {
        return Collections.unmodifiableSet(initLocations);
    }

    /**
     * @return The set of locations.
     */
    public Set<L> getLocations() {
        return Collections.unmodifiableSet(locations);
    }

    /**
     * @return the transitions
     */
    public Set<PGTransition<L, A>> getTransitions() {
        return Collections.unmodifiableSet(transitions);
    }

    /**
     * Removes a location from the program graph.
     *
     * @param l A location to remove.
     */
    public void removeLocation(L l) {
        locations.remove(l);
    }

    /**
     * Remove a transition.
     *
     * @param t A transition to remove.
     */
    public void removeTransition(PGTransition<L, A> t) {
        transitions.remove(t);
    }

    /**
     * @return The name of the program graph.
     */
    public String getName() {
        return name;
    }

    /**
     * Set the name of the program graph.
     *
     * @param name The new name.
     */
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 61 * hash + Objects.hashCode(this.locations);
        hash = 61 * hash + Objects.hashCode(this.transitions);
        hash = 61 * hash + Objects.hashCode(this.name);
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
        if (!(obj instanceof ProgramGraph)) {
            return false;
        }
        final ProgramGraph<?, ?> other = (ProgramGraph<?, ?>) obj;
        if (!Objects.equals(this.name, other.name)) {
            return false;
        }
        if (!Objects.equals(this.initLocations, other.initLocations)) {
            return false;
        }
        if (!Objects.equals(this.locations, other.locations)) {
            return false;
        }
        if (!Objects.equals(this.transitions, other.transitions)) {
            return false;
        }
        return Objects.equals(this.initializations, other.initializations);
    }

    @Override
    public String toString() {
        return String.format("[ProgamGraph name:%s locations:%d transitions:%d]",
                getName(), getLocations().size(), getTransitions().size());
    }

}
