package il.ac.bgu.cs.formalmethodsintro.base.sanity;

import static il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.makeLinearTs;
import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import java.util.Set;
import static org.junit.Assert.assertEquals;

/**
 * Testing the consistency of a transition system implementation.
 *
 * @author michael
 */
public class TransitionSystemConsistencyTest {

    @Test(timeout = 2000)
    public void transitionToNonexistentState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addTransition(new TSTransition<>(1, "a2", 700));
        assertEquals("Destination state should be added",
                Set.of(1, 2, 3, 4, 5, 700), ts.getStates());
    }

    @Test(timeout = 2000)
    public void transitionFromNonexistentState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addTransition(new TSTransition<>(700, "a2", 1));
        assertEquals("Source set should be added",
                Set.of(1, 2, 3, 4, 5, 700), ts.getStates());
    }

    @Test(timeout = 2000)
    public void transitionWithNonexistentAction() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addTransition(new TSTransition<>(1, "not-an-action", 2));
        assertEquals("transition action should be added",
                Set.of("a1", "a2", "a3", "a4", "not-an-action"), ts.getActions());
    }

    @Test(timeout = 2000)
    public void nonexistentInitialState() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(5);
        ts.addInitialState(700);
        assertEquals("Initial state should be added",
                Set.of(1, 2, 3, 4, 5, 700), ts.getStates());
    }

    @Test(timeout = 2000)
    public void illegalLabel() {
        TransitionSystem<Integer, String, String> ts = makeLinearTs(4);
        ts.addAtomicProposition("g");
        ts.addToLabel(1, "not-there");
        assertEquals(Set.of("g", "not-there"), ts.getAtomicPropositions());
    }

}
