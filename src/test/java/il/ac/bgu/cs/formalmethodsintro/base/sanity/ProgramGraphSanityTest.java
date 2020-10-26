package il.ac.bgu.cs.formalmethodsintro.base.sanity;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import java.util.Set;
import org.junit.Test;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 *
 * Sanity test for the provided {@link ProgramGraph}.
 *
 * @author michael
 */
public class ProgramGraphSanityTest {

    @Test
    public void consistencyChecks() {
        ProgramGraph<String, String> sut = FvmFacade.get().createProgramGraph();
        sut.addTransition(new PGTransition<>("from", "true", "act", "to"));
        assertEquals(Set.of("from", "to"), sut.getLocations());

        sut.setInitial("newLocation", true);
        assertEquals(Set.of("from", "to", "newLocation"), sut.getLocations());
        assertEquals(Set.of("newLocation"), sut.getInitialLocations());

        sut.setInitial("from", true);
        assertEquals(Set.of("from", "newLocation"), sut.getInitialLocations());

        sut.setInitial("newLocation", false);
        assertEquals(Set.of("from"), sut.getInitialLocations());
    }

    @Test
    public void testEqualities() {
        ProgramGraph<String, String> sut1 = FvmFacade.get().createProgramGraph();
        ProgramGraph<String, String> sut2 = FvmFacade.get().createProgramGraph();

        assertEquals(sut1, sut2);

        sut1.setName("sut1");
        assertNotEquals(sut1, sut2);

        sut1.setName(null);

        sut1.addTransition(new PGTransition<>("from", "true", "act", "to"));
        sut2.addTransition(new PGTransition<>("from", "true", "act", "to"));
        sut1.addTransition(new PGTransition<>("fromA", "true", "act", "toA"));
        sut2.addTransition(new PGTransition<>("fromA", "true", "act", "toA"));
        assertEquals(sut1, sut2);

        sut2.addTransition(new PGTransition<>("fromA", "true", "act", "toA"));
        assertEquals(sut1, sut2);

        sut2.addTransition(new PGTransition<>("fromA", "true", "actX", "toA"));
        assertNotEquals(sut1, sut2);
    }

}
