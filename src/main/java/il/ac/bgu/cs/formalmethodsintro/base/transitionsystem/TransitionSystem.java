package il.ac.bgu.cs.formalmethodsintro.base.transitionsystem;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;

import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedActionException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedAtomicPropositionException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedStateException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.FVMException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.TransitionSystemPart;

/**
 * Interface of a transition system, as defined in page 20 of the book.
 *
 * <strong>Important Note to Students</strong>
 * When implementing this interface, you <em>must</em> implement
 * {@code euqals()} and {@code hashCode()}. The equality tests should match any
 * object whose class implements this interface. This is similar to the fact
 * that a {@link TreeSet} and a {@link HashSet} can be equal, even though they
 * do not have the same concrete class.
 *
 * @param <STATE> Type of the states in the system.
 * @param <ACTION> Type of the actions in the system.
 * @param <ATOMIC_PROPOSITION> Type of the atomic propositions in the system.
 */
public class TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> {

    private String name;

    private final Set<STATE> states = new HashSet<>();
    private final Set<ACTION> actions = new HashSet<>();
    private final Set<TSTransition<STATE, ACTION>> transitions = new HashSet<>();
    private final Set<STATE> initialStates = new HashSet<>();
    private final Set<ATOMIC_PROPOSITION> atomicPropositions = new HashSet<>();
    private final HashMap<STATE, Set<ATOMIC_PROPOSITION>> labelingFunction = new HashMap<>();

    /**
     * Get the name of the transitions system.
     *
     * @return The name of the transition system.
     */
    public String getName() {
        return name;
    }

    /**
     * Set the name of the transition system.
     *
     * @param name A new for the transition system.
     */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * Add an action. Note: This method must be idempotent.
     *
     * @param anAction A name for the new action.
     */
    public void addAction(ACTION anAction) {
        actions.add(anAction);
    }

    /**
     * Remove an action.
     *
     * @param action The name of the action to remove.
     * @throws FVMException If the action in use by a transition.
     */
    public void removeAction(ACTION action) throws FVMException {
        for (var t : transitions) {
            if (t.getAction().equals(action)) {
                throw new DeletionOfAttachedActionException(action, TransitionSystemPart.TRANSITIONS);
            }
        }

        actions.remove(action);
    }

    /**
     * Add a state. Note: This method must be idempotent.
     *
     * @param state A name for the new state.
     *
     */
    public void addState(STATE state) {
        if (state == null) {
            throw new IllegalArgumentException("Cannot add a null state");
        }
        states.add(state);
    }

    /**
     * Add {@code aState} as an initial state of {@code this} transition system.
     * {@code aState} can already be a part of {@code this}, but this is not
     * mandatory - it is added to the system it not.
     *
     * @param aState A state to add to the set of initial states.
     * @param isInitial Whether {@code state} should be an initial state of
     * {@code this}.
     */
    public void addInitialState(STATE aState) {
        addState(aState);
        initialStates.add(aState);
    }

    /**
     * Removes {@code aState} from the initial state set.
     *
     * @param aState the state that no longer will be a starting state.
     */
    public void removeInitialState(STATE aState) {
        initialStates.remove(aState);
    }

    /**
     * Gets the states.
     *
     * Note: the returned collection is unmodifiable, to prevent non-validated
     * changes being made.
     *
     * @return The set of states.
     */
    public Set<STATE> getStates() {
        return Collections.unmodifiableSet(states);
    }

    /**
     * Gets the initial states.
     *
     * Note: the returned collection is unmodifiable, to prevent non-validated
     * changes being made.
     *
     * @return The set of initial states.
     */
    public Set<STATE> getInitialStates() {
        return Collections.unmodifiableSet(initialStates);
    }

    /**
     * Remove a state.
     *
     * @param state The name of the state to remove.
     * @throws FVMException If the state is in use by a transition.
     */
    public void removeState(STATE state) throws FVMException {
        transitions.stream()
                .filter((t) -> (t.getFrom().equals(state) || t.getTo().equals(state)))
                .findFirst().map(t -> {
                    throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
                });

        states.remove(state);
        initialStates.remove(state);
        labelingFunction.remove(state);
    }

    /**
     * Add a transition. The action and states are added automatically, if they
     * are not already a part of {@code this} transition system.
     *
     * @param t The transition to add.
     * @throws FVMException If the states or the action does not exist.
     */
    public void addTransition(TSTransition<STATE, ACTION> t) throws FVMException {
        addState(t.getFrom());
        addState(t.getTo());
        addAction(t.getAction());

        transitions.add(t);
    }

    /**
     * Removes a transition. States and actions remain in {@code this} system.
     *
     * @param t The transition to remove.
     */
    public void removeTransition(TSTransition<STATE, ACTION> t) {
        transitions.remove(t);
    }

    /**
     * Get the transitions.
     *
     * Note: The returned collection is unmodifiable, to protect the consistency
     * of {@code this}' internal state.
     *
     * @return The set of the transitions.
     */
    public Set<TSTransition<STATE, ACTION>> getTransitions() {
        return Collections.unmodifiableSet(transitions);
    }

    /**
     * Get the actions.
     *
     * Note: The returned set is unmodifiable, to prevent {@code this} from
     * getting into an inconsistent state.
     *
     * @return A copy of the set of actions.
     */
    public Set<ACTION> getActions() {
        return Collections.unmodifiableSet(actions);
    }

    /**
     * Add an atomic proposition. Has no effect if the proposition already
     * exists.
     *
     * @param p The name of the new atomic proposition.
     */
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        if (p == null) {
            throw new IllegalArgumentException("Cannot add a null proposition");
        }
        atomicPropositions.add(p);
    }

    /**
     * Get the the atomic propositions.
     *
     * @return The set of atomic propositions.
     */
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        return Collections.unmodifiableSet(atomicPropositions);
    }

    /**
     * Remove an atomic proposition.
     *
     * @param p The name of the proposition to remove.
     * @throws FVMException If the proposition is used as label of a state.
     */
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        labelingFunction.values().stream().flatMap(s -> s.stream())
                .filter(ap -> ap.equals(p))
                .findFirst().ifPresent(ap -> {
                    throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.LABELING_FUNCTION);
                });

        atomicPropositions.remove(p);
    }

    /**
     * Label a state by an atomic proposition. Adds the label and the state to
     * {@code this}, if they are not already part of it.
     *
     * @param s A state
     * @param l An atomic proposition.
     */
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) {
        addState(s);
        addAtomicProposition(l);
        Set<ATOMIC_PROPOSITION> labelSet = labelingFunction.get(s);

        if (labelSet == null) {
            labelSet = new HashSet<>();
            labelingFunction.put(s, labelSet);
        }

        labelSet.add(l);
    }

    /**
     * Returns the label of state {@code s}. Result is never {@code null}, but
     * might be an empty set.
     *
     * @param aState The state whose label we request.
     * @return {@code s}'s label.
     * @throws StateNotFoundException if {@code s} is not a member of
     * {@code this}' state set.
     */
    public Set<ATOMIC_PROPOSITION> getLabel(STATE aState) {
        if (states.contains(aState)) {
            return labelingFunction.getOrDefault(aState, Collections.emptySet());
        } else {
            throw new StateNotFoundException("State " + aState + " not found");
        }
    }

    /**
     * Get the labeling function.
     *
     * @return The set of maps representing the labeling function.
     */
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        return labelingFunction;
    }

    /**
     * atomic proposition, the method returns without changing anything.
     *
     * @param s A state.
     * @param l An atomic proposition
     */
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        Set<ATOMIC_PROPOSITION> labelSet = labelingFunction.get(s);

        if (labelSet != null) {
            labelSet.remove(l);
            if (labelSet.isEmpty()) {
                labelingFunction.remove(s);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    /// Overriding java.lang.Object essentials
    @Override
    public int hashCode() {
        int hash = 7;
        hash = 41 * hash + Objects.hashCode(this.name);
        hash = 41 * hash + Objects.hashCode(this.initialStates);
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
        if (!(obj instanceof TransitionSystem)) {
            return false;
        }
        @SuppressWarnings("rawtypes")
        final TransitionSystem other = (TransitionSystem) obj;
        if (!Objects.equals(getName(), other.getName())) {
            return false;
        }
        if (!Objects.equals(getStates(), other.getStates())) {
            return false;
        }
        if (!Objects.equals(getActions(), other.getActions())) {
            return false;
        }
        if (!Objects.equals(getTransitions(), other.getTransitions())) {
            return false;
        }
        if (!Objects.equals(getInitialStates(), other.getInitialStates())) {
            return false;
        }
        if (!Objects.equals(getAtomicPropositions(), other.getAtomicPropositions())) {
            return false;
        }
        return Objects.equals(getLabelingFunction(), other.getLabelingFunction());
    }

    @Override
    public String toString() {
        return String.format(
                "[TransitionSystem name=" + name + " %d states (%d initial), %d actions, %d transitions, %d atomicPropositions]",
                states.size(), initialStates.size(), actions.size(), transitions.size(), atomicPropositions.size()
        );
    }

    /// 
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    /// Convenience methods for less painful system creation.
    @SuppressWarnings("unchecked")
    public void addStates(STATE... states) {
        for (STATE s : states) {
            addState(s);
        }
    }

    public void addAllStates(STATE states[]) {
        for (STATE s : states) {
            addState(s);
        }
    }

    public void addAllStates(Iterable<STATE> states) {
        for (STATE s : states) {
            addState(s);
        }
    }

    @SuppressWarnings("unchecked")
    public void addActions(ACTION... actions) {
        for (ACTION a : actions) {
            addAction(a);
        }
    }

    public void addAllActions(ACTION actions[]) {
        for (ACTION a : actions) {
            addAction(a);
        }
    }

    public void addAllActions(Iterable<ACTION> actions) {
        for (ACTION a : actions) {
            addAction(a);
        }
    }

    @SuppressWarnings("unchecked")
    public void addAtomicPropositions(ATOMIC_PROPOSITION... aps) {
        for (ATOMIC_PROPOSITION ap : aps) {
            addAtomicProposition(ap);
        }
    }

    public void addAllAtomicPropositions(ATOMIC_PROPOSITION aps[]) {
        for (ATOMIC_PROPOSITION ap : aps) {
            addAtomicProposition(ap);
        }
    }

    public void addAllAtomicPropositions(Iterable<ATOMIC_PROPOSITION> aps) {
        for (ATOMIC_PROPOSITION ap : aps) {
            addAtomicProposition(ap);
        }
    }

    // / convenience methods
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    /// These are builder methods and classes, supporting an internal DSL approach.
    /// This approach makes manual building of transition systems less painful.
    /**
     * An internal DSL method making manual addition of transitions easier.
     * Usage: {@code ts.addTransitionFrom(a).action(alpha).to(b);}
     *
     * <em>NOTE:</em> These methods have default implementation, no need to
     * implement it yourself. But you might want to look at the mechanism, if
     * you're into internal DSLs.
     *
     * @param s The starting point of this transition.
     * @return A phase 1 transition builder.
     */
    public TransitionBuilder_1<STATE, ACTION, ATOMIC_PROPOSITION> addTransitionFrom(STATE s) {
        return new TransitionBuilder_1<>(this, s);
    }

    @SuppressWarnings("hiding")
    public class TransitionBuilder_1<STATE, ACTION, ATOMIC_PROPOSITION> {

        final TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> ts;
        final STATE from;

        TransitionBuilder_1(TransitionSystem<STATE, ACTION, ATOMIC_PROPOSITION> aTs, STATE startingPoint) {
            ts = aTs;
            from = startingPoint;
        }

        public TransitionBuilder_2<STATE, ACTION, ATOMIC_PROPOSITION> action(ACTION a) {
            return new TransitionBuilder_2<>(this, a);
        }
    }

    @SuppressWarnings("hiding")
    public class TransitionBuilder_2<STATE, ACTION, ATOMIC_PROPOSITION> {

        final TransitionBuilder_1<STATE, ACTION, ATOMIC_PROPOSITION> prev;
        final ACTION action;

        public TransitionBuilder_2(TransitionBuilder_1<STATE, ACTION, ATOMIC_PROPOSITION> prev, ACTION action) {
            this.prev = prev;
            this.action = action;
        }

        public void to(STATE to) {
            prev.ts.addTransition(new TSTransition<>(prev.from, action, to));
        }
    }

    // / builder classes
    ////////////////////////////////////////////////////////////////////////////
}
