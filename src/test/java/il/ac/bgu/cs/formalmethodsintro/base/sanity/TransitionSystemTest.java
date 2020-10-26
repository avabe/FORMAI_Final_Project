package il.ac.bgu.cs.formalmethodsintro.base.sanity;

import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.AP.P;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.AP.Q;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.Actions.A1;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.Actions.A3;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.States.S1;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.States.S2;
import static il.ac.bgu.cs.formalmethodsintro.base.sanity.TransitionSystemTest.States.S3;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedActionException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedAtomicPropositionException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.DeletionOfAttachedStateException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;

/**
 * Set of basic tests for {@link TransitionSystem} implementation.
 */
public class TransitionSystemTest {

    public static enum States {
        S1, S2, S3
    }

    public static enum AP {
        P, Q
    }

    public static enum Actions {
        A1, A2, A3
    }

    TransitionSystem<States, Actions, AP> ts;

    @Before
    public void before() {
        ts = new TransitionSystem<>();
    }

    @Test(timeout = 2000)
    public void initialStateMustBeInStates() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addInitialState(S3);

        assertEquals(Set.of(S1, S2, S3), ts.getStates());
    }

    @Test(timeout = 2000)
    public void initialStateCanBeRemoved() throws Exception {
        ts.addStates(S1, S2);
        ts.addInitialState(S1);
        ts.removeState(S1);

        assertEquals(Set.of(S2), ts.getStates());
    }

    @Test(timeout = 2000)
    public void initialStateCanBeRemovedAfterCleaning() throws Exception {
        ts.addState(S1);
        ts.addInitialState(S1);
        ts.removeInitialState(S1);
        ts.removeState(S1);
    }

    @Test(expected = DeletionOfAttachedAtomicPropositionException.class, timeout = 2000)
    public void usedLabelCantBeRemoved() throws Exception {
        ts.addState(S1);
        ts.addAtomicProposition(Q);
        ts.addToLabel(S1, Q);
        ts.removeAtomicProposition(Q);
    }

    @Test(timeout = 2000)
    public void labeledStateLabelWorks() throws Exception {
        ts.addState(S1);
        ts.addAtomicPropositions(Q, P);
        ts.addToLabel(S1, Q);
        assertEquals(Set.of(Q), ts.getLabel(S1));
        ts.addToLabel(S1, P);
        assertEquals(Set.of(Q, P), ts.getLabel(S1));
    }

    @Test(timeout = 2000)
    public void labeledStateLabelWorks_emptysetLabel() throws Exception {
        ts.addState(S1);
        ts.addAtomicProposition(Q);
        assertEquals(Set.of(), ts.getLabel(S1));
    }

    @Test(expected = StateNotFoundException.class, timeout = 2000)
    public void labeledStateInvalidStateError() throws Exception {
        ts.addState(S1);
        ts.getLabel(S3);
        fail("When asked about the label of a nonexistent state, the transition system should throw a StateNotFoundException");
    }

    @Test(timeout = 2000)
    public void addValidTransition() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S2));
    }

    @Test(timeout = 2000)
    public void addInvalidTransition_fromState() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S3, A1, S2));
        assertEquals(Set.of(S1, S2, S3), ts.getStates());
    }

    @Test(timeout = 2000)
    public void addInvalidTransition_toState() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S3));
        assertEquals(Set.of(S1, S2, S3), ts.getStates());
    }

    @Test(timeout = 2000)
    public void addInvalidTransition_action() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A3, S2));
    }

    @Test(expected = DeletionOfAttachedStateException.class, timeout = 2000)
    public void cannotRemoveStateInTransition_from() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S2));
        ts.removeState(S1);
    }

    @Test(expected = DeletionOfAttachedStateException.class, timeout = 2000)
    public void cannotRemoveStateInTransition_to() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S2));
        ts.removeState(S2);
    }

    @Test(expected = DeletionOfAttachedActionException.class, timeout = 2000)
    public void cannotRemoveActionInTransition() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S2));
        ts.removeAction(A1);
    }

}
