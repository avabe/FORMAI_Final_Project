package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;
import java.util.stream.Collectors;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.InterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.fairness.FairnessCondition;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.*;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.DostmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.IfstmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationFailed;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationSucceeded;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * More about facade: {@linkplain http://www.vincehuston.org/dp/facade.html}.
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;

    /**
     * @return an instance of this class.
     */
    public static FvmFacade get() {
        if (INSTANCE == null) {
            INSTANCE = new FvmFacade();
        }
        return INSTANCE;
    }

    /**
     * Checks whether a transition system is action deterministic. I.e., if for
     * any given p and α there exists only a single tuple (p,α,q) in →. Note
     * that this must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        for (var tr : ts.getTransitions()) {
            if (post(ts, tr.getFrom(), tr.getAction()).size() > 1)
                return false;
        }
        return ts.getInitialStates().size() <= 1;
    }

    /**
     * Checks whether an action is ap-deterministic (as defined in class), in
     * the context of a given {@link TransitionSystem}.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        for (var state : ts.getStates()) {
            Set<S> post_s = post(ts, state);
            for (var it = post_s.iterator(); it.hasNext(); ) {
                var curr = it.next();
                for (var it2 = post_s.iterator(); it2.hasNext(); ) {
                    var next = it2.next();
                    if (!curr.equals(next)) {
                        if (ts.getLabel(curr).equals(ts.getLabel(next)))
                            return false;
                    }
                }
            }
        }
        return ts.getInitialStates().size() <= 1;
    }

    /**
     * Checks whether an alternating sequence is an execution of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution of {@code ts}.
     * @return {@code true} iff {@code e} is an execution of {@code ts}.
     */
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is an execution fragment of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution fragment of
     *            {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> restS = e;
        while (restS.size() > 1) {
            AlternatingSequence<A, S> restA = restS.tail();
            S currS = restS.head();
            A currA = restA.head();
            if (restA.size() <= 1) return false;
            restS = restA.tail();
            if (!ts.getStates().contains(currS)) return false;
            if (!ts.getActions().contains(currA)) return false;
            if (!post(ts, currS, currA).contains(restS.head())) return false;
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an initial execution fragment
     * of a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an initial execution
     *            fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!isExecutionFragment(ts, e))
            return false;
        return ts.getInitialStates().contains(e.head());
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be a maximal execution fragment
     *            of {@code ts}.
     * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
     */
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if (!isExecutionFragment(ts, e))
            return false;
        return isStateTerminal(ts, e.last());
    }


    public <S> void checkState(Set<S> states, S s) {
        if (!states.contains(s))
            throw new StateNotFoundException("State " + s + " not found");
    }

    /**
     * Checks whether a state in {@code ts} is terminal.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        checkState(ts.getStates(), s);

        return post(ts, s).size() == 0;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        checkState(ts.getStates(), s);
        Set<S> p = new HashSet<>();
        for (var t : ts.getTransitions()) {
            if (t.getFrom().equals(s)) {
                p.add(t.getTo());
            }
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> p = new HashSet<>();
        for (var s : c) {
            p.addAll(post(ts, s));
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        checkState(ts.getStates(), s);
        Set<TSTransition<S, A>> trans = ts.getTransitions();
        Set<S> p = new HashSet<>();
        for (var t : trans) {
            if (t.getFrom().equals(s) && t.getAction().equals(a)) {
                p.add(t.getTo());
            }
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> p = new HashSet<>();
        for (var s : c) {
            p.addAll(post(ts, s, a));
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        checkState(ts.getStates(), s);
        Set<S> p = new HashSet<>();
        for (var t : ts.getTransitions()) {
            if (t.getTo().equals(s)) {
                p.add(t.getFrom());
            }
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> p = new HashSet<>();
        for (var s : c) {
            p.addAll(pre(ts, s));
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        checkState(ts.getStates(), s);
        Set<S> p = new HashSet<>();
        for (var t : ts.getTransitions()) {
            if (t.getTo().equals(s) && t.getAction().equals(a)) {
                p.add(t.getFrom());
            }
        }
        return p;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> p = new HashSet<>();
        for (var s : c) {
            p.addAll(pre(ts, s, a));
        }
        return p;
    }

    /**
     * Implements the {@code reach(TS)} function.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> r = new HashSet<>();
        r.addAll(ts.getInitialStates());
        LinkedList<S> q = new LinkedList<>();
        q.addAll(ts.getInitialStates());
        while (q.size() > 0) {
            S curr = q.poll();
            Set<S> neighbors = post(ts, curr);
            for (S s : neighbors) {
                if (!r.contains(s)) {
                    q.add(s);
                }
            }
            r.addAll(neighbors);
        }
        return r;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A>  Type of actions (in both systems).
     * @param <P>  Type of atomic propositions (in both systems).
     * @param ts1  The first transition system.
     * @param ts2  The second transition system.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<A>());
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1>               Type of states in the first system.
     * @param <S2>               Type of states in the first system.
     * @param <A>                Type of actions (in both systems).
     * @param <P>                Type of atomic propositions (in both systems).
     * @param ts1                The first transition system.
     * @param ts2                The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        Set<Pair<S1, S2>> states = new HashSet<>();
        TransitionSystem<Pair<S1, S2>, A, P> ret = new TransitionSystem<>();
        // make TS1XTS2 states
        for (var s1 : ts1.getStates()) {
            for (var s2 : ts2.getStates()) {
                Pair<S1, S2> curr = new Pair<>(s1, s2);
                // add labeling for the new state
                Set<P> s1_labels = ts1.getLabel(s1);
                Set<P> s2_labels = ts2.getLabel(s2);
                for (var l : s1_labels)
                    ret.addToLabel(curr, l);
                for (var l : s2_labels)
                    ret.addToLabel(curr, l);
                // end labeling
                if (ts1.getInitialStates().contains(s1) && ts2.getInitialStates().contains(s2))
                    ret.addInitialState(curr);
                states.add(curr);
            }
        }
        Set<TSTransition<S1, A>> trns1 = ts1.getTransitions();
        Set<TSTransition<S2, A>> trns2 = ts2.getTransitions();
        Set<TSTransition<S1, A>> trns1_hs = new HashSet<>();
        Set<TSTransition<S2, A>> trns2_hs = new HashSet<>();
        Queue<Pair<S1, S2>> queue = new LinkedList<>(ret.getInitialStates());
        while (!queue.isEmpty()) {
            Pair<S1, S2> curr = queue.poll();
            for (var t : trns1) {
                if (handShakingActions.contains(t.getAction())) {
                    for (var t2 : trns2) {
                        if (t2.getAction().equals(t.getAction()) && curr.first.equals(t.getFrom()) && curr.second.equals(t2.getFrom())) {
                            Pair<S1, S2> newState = new Pair<S1, S2>(t.getTo(), t2.getTo());
                            TSTransition newTrns = new TSTransition<>(curr, t.getAction(), newState);
                            if (!tsAlreadyExists(ret.getTransitions(), newTrns)) {
                                ret.addTransition(newTrns);
                                queue.add(newState);
                            }
                        }
                    }
                    //trns1_hs.add(t);
                    //trns1.remove(t);
                } else {
                    if (curr.first.equals(t.getFrom())) {
                        Pair<S1, S2> newState = new Pair<S1, S2>(t.getTo(), curr.second);
                        TSTransition newTrns = new TSTransition<>(curr, t.getAction(), newState);
                        if (!tsAlreadyExists(ret.getTransitions(), newTrns)) {
                            ret.addTransition(newTrns);
                            queue.add(newState);
                        }
                    }
                }
            }
            for (var t : trns2) {
                if (handShakingActions.contains(t.getAction())) {
                    continue;
                    //trns2_hs.add(t);
                    //trns2.remove(t);
                } else {
                    if (curr.second.equals(t.getFrom())) {
                        Pair<S1, S2> newState = new Pair<S1, S2>(curr.first, t.getTo());
                        TSTransition newTrns = new TSTransition<>(curr, t.getAction(), newState);
                        if (!tsAlreadyExists(ret.getTransitions(), newTrns)) {
                            ret.addTransition(newTrns);
                            queue.add(newState);
                        }
                        //ret.addTransition(new TSTransition<>(curr, t.getAction(), new Pair<S1, S2>(curr.first, t.getTo())));
                        //trns2.remove(t);
                    }
                }
            }
        }
        for (var t1 : trns1_hs) {
            for (var t2 : trns2_hs) {
                if (t1.getAction().equals(t2.getAction()))
                    ret.addTransition(new TSTransition<>(new Pair<S1, S2>(t1.getFrom(), t2.getFrom()), t1.getAction(), new Pair<S1, S2>(t1.getTo(), t2.getTo())));
            }
        }
        ret.addAllActions(ts1.getActions());
        ret.addAllActions(ts2.getActions());
        return ret;
    }

    /**
     * Creates a new {@link ProgramGraph} object.
     *
     * @param <L> Type of locations in the graph.
     * @param <A> Type of actions of the graph.
     * @return A new program graph instance.
     */
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraph<>();
    }

    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A>  Type of actions in BOTH GRAPHS.
     * @param pg1  The first program graph.
     * @param pg2  The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> pg = new ProgramGraph<>();
        // create locations
        for (L1 l1 : pg1.getLocations()) {
            for (L2 l2 : pg2.getLocations()) {
                Pair<L1, L2> l = new Pair<>(l1, l2);
                pg.addLocation(l);
                if (pg1.getInitialLocations().contains(l1) && pg2.getInitialLocations().contains(l2)) {
                    pg.setInitial(l, true);
                }
            }
        }
        //create initializations
        for (List<String> init1 : pg1.getInitalizations()) {
            for (List<String> init2 : pg2.getInitalizations()) {
                List<String> init = new LinkedList<>();
                init.addAll(init1);
                init.addAll(init2);
                pg.addInitalization(init);
            }
        }
        //create transitions
        for (PGTransition<L1, A> trans1 : pg1.getTransitions()) {
            L1 l1 = trans1.getFrom();
            L1 l1_to = trans1.getTo();
            for (L2 l2 : pg2.getLocations()) {
                PGTransition<Pair<L1, L2>, A> trans = new PGTransition<>(new Pair<>(l1, l2), trans1.getCondition(),
                        trans1.getAction(), new Pair<>(l1_to, l2));
                pg.addTransition(trans);
            }
        }
        for (PGTransition<L2, A> trans2 : pg2.getTransitions()) {
            L2 l2 = trans2.getFrom();
            L2 l2_to = trans2.getTo();
            for (L1 l1 : pg1.getLocations()) {
                PGTransition<Pair<L1, L2>, A> trans = new PGTransition<>(new Pair<>(l1, l2), trans2.getCondition(),
                        trans2.getAction(), new Pair<>(l1, l2_to));
                pg.addTransition(trans);
            }
        }

        return pg;
    }

    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(
            Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ret = new TransitionSystem<>();
        Set<String> inputs = c.getInputPortNames();
        Set<String> registers = c.getRegisterNames();
        //States
        for (int i = 0; i < Math.pow(2, inputs.size()); i++) {
            Map<String, Boolean> inputMap = convertToBoolMap(inputs, i);
            ret.addAction(inputMap);//Actions
            for (int j = 0; j < Math.pow(2, registers.size()); j++) {
                Map<String, Boolean> regMap = convertToBoolMap(registers, j);
                Pair<Map<String, Boolean>, Map<String, Boolean>> newState = new Pair<Map<String, Boolean>, Map<String, Boolean>>(inputMap, regMap);
                ret.addState(newState);
                //Initial states
                if (j == 0)
                    ret.addInitialState(new Pair<>(inputMap, regMap));
                //Labeling
                for (var in : inputs)
                    if (inputMap.get(in))
                        ret.addToLabel(newState, in);
                for (var reg : registers)
                    if (regMap.get(reg))
                        ret.addToLabel(newState, reg);
                var outputSet = c.computeOutputs(inputMap, regMap);
                for (var out : outputSet.keySet())
                    if (outputSet.get(out))
                        ret.addToLabel(newState, out);
            }
        }
        //Transitions
        for (var s : ret.getStates()) {
            for (var a : ret.getActions()) {
                Pair<Map<String, Boolean>, Map<String, Boolean>> tstate = null;
                for (var ts : ret.getStates()) {
                    if (ts.first.equals(a) && ts.second.equals(c.updateRegisters(s.first, s.second)))
                        tstate = ts;
                }
                if (tstate != null)
                    ret.addTransition(new TSTransition<>(s, a, tstate));
            }
        }
        //END Transitions
        return ret;
    }

    private Map<String, Boolean> convertToBoolMap(Set<String> names, int n) {
        Map<String, Boolean> ret = new HashMap<>();
        int i = 0;
        for (var na : names) {
            int c = n % 2;
            n = n / 2;
            ret.put(na, c == 1);
        }
        return ret;
    }

    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L>           Type of program graph locations.
     * @param <A>           Type of program graph actions.
     * @param pg            The program graph to be translated into a transition system.
     * @param actionDefs    Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     *                      graph.
     * @return A transition system representing {@code pg}.
     */
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ts = new TransitionSystem<>();
        //create initial states
        for (L l0 : pg.getInitialLocations()) {
            Set<List<String>> inits = pg.getInitalizations();
            if (inits.size() <= 0) {
                Pair<L, Map<String, Object>> newstate = new Pair<>(l0, new HashMap<>());
                ts.addInitialState(newstate);
            } else {
                for (List<String> i : inits) {
                    Map<String, Object> vars = new HashMap<>();
                    for (String exp : i) {
                        vars = ActionDef.effect(actionDefs, vars, exp);
                    }
                    Pair<L, Map<String, Object>> new_initial = new Pair<>(l0, vars);
                    ts.addInitialState(new_initial);
                    ts.addToLabel(new_initial, new_initial.first.toString());
                }
            }
        }
        //create transitions
        List<Pair<L, Map<String, Object>>> ts_states = new ArrayList<>(ts.getStates());
        for (int i = 0; i < ts_states.size(); i++) {
            Pair<L, Map<String, Object>> curr = ts_states.get(i);
            Map<String, Object> curr_vars = curr.second;
            //add AP
            ts.addAtomicPropositions(curr.first.toString());
            for (PGTransition<L, A> trans : pg.getTransitions()) {
                String cond = "";
                if (trans.getFrom().equals(curr.first)) {
                    if (ConditionDef.evaluate(conditionDefs, curr_vars, trans.getCondition())) {
                        Map<String, Object> new_vars = ActionDef.effect(actionDefs, curr_vars, trans.getAction());
                        Pair<L, Map<String, Object>> new_state = new Pair<>(trans.getTo(), new_vars);
                        ts.addTransition(new TSTransition<>(curr, trans.getAction(), new_state));
                        if (!ts_states.contains(new_state))
                            ts_states.add(new_state);
                        ts.addToLabel(curr, curr.first.toString());
                        if (!(trans.getCondition().equals("true") || trans.getCondition().equals(""))) {
                            ts.addToLabel(curr, trans.getCondition());
                        }
                    }
                }
                if (!(trans.getCondition().equals("true") || trans.getCondition().equals("")))
                    ts.addAtomicProposition(trans.getCondition());
            }
        }
        return ts;
    }

    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs  The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {

        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret = new TransitionSystem<>();
        List<ProgramGraph<L, A>> programGraphs = cs.getProgramGraphs();
        Set<List<L>> inits_locations = getPermotations(programGraphs);
        Set<List<String>> initials = getPermotationsVars(programGraphs);
        ParserBasedActDef pb = new ParserBasedActDef();
        ParserBasedCondDef condDef = new ParserBasedCondDef();
        InterleavingActDef interleavingActDef = new ParserBasedInterleavingActDef();
        Set<ActionDef> actionDefs = new HashSet<>();
        Set<InterleavingActDef> interleavingActDefHashSet = new HashSet<>();
        interleavingActDefHashSet.add(interleavingActDef);
        Set<ConditionDef> conditionDefs = new HashSet<>();
        conditionDefs.add(condDef);
        actionDefs.add(pb);
        for (var l : inits_locations) {
            for (var initList : initials) {
                Map<String, Object> vars = new HashMap();
                for (var initVar : initList)
                    vars = ActionDef.effect(actionDefs, vars, initVar);
                Pair<List<L>, Map<String, Object>> newstate = new Pair<>(l, vars);
                ret.addState(newstate);
                ret.addInitialState(newstate);
            }
        }

        Queue<Pair<List<L>, Map<String, Object>>> queue = new LinkedList<>(ret.getStates());
        boolean canGoInside = false;
        while (!queue.isEmpty()) {
            var state = queue.poll();
            int locIndex = 0;
            for (var loc : state.first) {
                for (var ts : programGraphs.get(locIndex).getTransitions()) {
                    canGoInside = false;
                    if (ts.getFrom().equals(loc) && ConditionDef.evaluate(conditionDefs, state.second, ts.getCondition())) {
                        Map<String, Object> tmpVars = new HashMap<String, Object>();
                        List<L> newLocsForNewState = new LinkedList<>(state.first);
                        Pair<List<L>, Map<String, Object>> newstate = null;
                        TSTransition newTrans;
                        if (!interleavingActDef.isOneSidedAction((String) ts.getAction())) { // NonEmptyChannel
                            if (channelIsEmpty(state.second, ts.getAction())) continue;
                            tmpVars = ActionDef.effect(actionDefs, state.second, ts.getAction());
                            newLocsForNewState.remove(locIndex);
                            newLocsForNewState.add(locIndex, ts.getTo());
                            newstate = new Pair<>(newLocsForNewState, tmpVars);
                            newTrans = new TSTransition(state, ts.getAction(), newstate);
                            if (!tsAlreadyExists(ret.getTransitions(), newTrans)) {
                                ret.addTransition(newTrans);
                                canGoInside = true;
                            }
                        } else {
                            for (int j = 0; j < state.first.size(); j++) {
                                if (j == locIndex) continue;
                                var buddyloc = state.first.get(j);
                                for (var ts2 : programGraphs.get(j).getTransitions()) {
                                    if (ts2.getFrom().equals(buddyloc) && isMathAction(ts.getAction(), ts2.getAction())) {
                                        String cond1 = ts.getCondition().equals("") ? "true" : "(" + ts.getCondition() + ")";
                                        String cond2 = ts2.getCondition().equals("") ? "true" : "(" + ts2.getCondition() + ")";
                                        String condition = cond1 + "&&" + cond2;
                                        A interAction = j > locIndex ? (A) ((String) ts.getAction() + " | " + (String) ts2.getAction()) : (A) ((String) ts2.getAction() + "|" + (String) ts.getAction());
                                        boolean condSat = ConditionDef.evaluate(conditionDefs, state.second, condition);
                                        tmpVars = interleavingActDef.effect(state.getSecond(), interAction);
                                        if (condSat && tmpVars != null) {
                                            newLocsForNewState.remove(locIndex);
                                            newLocsForNewState.add(locIndex, ts.getTo());
                                            newLocsForNewState.remove(j);
                                            newLocsForNewState.add(j, ts2.getTo());
                                            newstate = new Pair<>(newLocsForNewState, tmpVars);
                                            newTrans = new TSTransition(state, null, newstate);
                                            if (!tsAlreadyExists(ret.getTransitions(), newTrans)) {
                                                ret.addTransition(newTrans);
                                                queue.add(newstate);

                                            }
                                        }
                                    }
                                }
                            }
                        }
                        if (canGoInside)
                            queue.add(newstate);
                    }
                }
                locIndex++;
            }
        }

        for (var s : ret.getStates()) {
            Set<String> labels = new HashSet<>();
            for (var loc : s.first)
                labels.add(loc.toString());
            for (var v : s.getSecond().keySet()) {
                labels.add(v + " = " + s.getSecond().get(v));
            }
            for (var l : labels)
                ret.addToLabel(s, l);
        }
        return ret;
    }

    private <STATE, ACTION> boolean tsAlreadyExists(Set<TSTransition<STATE, ACTION>> l, TSTransition t) {
        for (var ts : l) {
            if (ts.getAction() == null && t.getAction() == null) {
                if (ts.getFrom().equals(t.getFrom()) && ts.getTo().equals(t.getTo()))
                    return true;
            } else {
                if (ts.getFrom().equals(t.getFrom()) && ts.getAction().equals(t.getAction()) && ts.getTo().equals(t.getTo()))
                    return true;
            }
        }
        return false;
    }

    private <A> boolean isMathAction(A act1, A act2) {
        if (((String) act1).contains("?") && ((String) act2).contains("!")) {
            return ((String) act1).split("\\?")[0].equals(((String) act2).split("!")[0]);
        }
        if (((String) act1).contains("!") && ((String) act2).contains("?")) {
            return ((String) act1).split("!")[0].equals(((String) act2).split("\\?")[0]);
        }
        return false;
    }

    private <A> boolean channelIsEmpty(Map<String, Object> vars, A action) {
        if (!((String) action).contains("?"))
            return false;
        String ch = ((String) action).split("\\?")[0];
        if (!vars.containsKey(ch)) return true;
        return ((Vector) vars.get(ch)).size() <= 0;
    }

    public <L, A> Set<List<L>> getPermotations(List<ProgramGraph<L, A>> l) {
        if (l.isEmpty())
            return new HashSet<>();
        Set<List<L>> ret = new HashSet<>();
        List<L> x = new LinkedList<>();
        for (var i : l.get(0).getInitialLocations())
            x.add(i);
        var xs = l.size() > 1 ? l.subList(1, l.size()) : new LinkedList();
        Set<List<L>> xs_per = getPermotations(xs);
        if (xs_per.isEmpty()) {
            ret.add(x);
        } else {
            for (var loc : x) {
                for (var xs_loc : xs_per) {
                    List<L> state = new LinkedList<>();
                    state.add(loc);
                    state.addAll(xs_loc);
                    ret.add(state);
                }
            }
        }
        return ret;
    }

    public <L, A> Set<List<String>> getPermotationsVars(List<ProgramGraph<L, A>> l) {
        if (l.isEmpty())
            return new HashSet<>();
        Set<List<String>> ret = new HashSet<>();
        Set<List<String>> x = new HashSet<>();
        for (var i : l.get(0).getInitalizations())
            x.add(i);
        var xs = l.size() > 1 ? l.subList(1, l.size()) : new LinkedList();
        Set<List<String>> xs_per = getPermotationsVars(xs);
        if (xs_per.isEmpty()) {
            ret.addAll(x);
        } else {
            if (x.isEmpty())
                ret.addAll(xs_per);
            else
                for (var varList : x) {
                    for (var xs_vars : xs_per) {
                        List<String> vars = new LinkedList<>();
                        vars.addAll(varList);
                        vars.addAll(xs_vars);
                        ret.add(vars);
                    }
                }
        }
        return ret;
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        StmtContext exp = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        return nanoPromelaPG(exp);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext exp = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        return nanoPromelaPG(exp);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext exp = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        return nanoPromelaPG(exp);
    }

    private Set<PGTransition<String, String>> final_transitions = new HashSet<>();

    private ProgramGraph<String, String> nanoPromelaPG(StmtContext exp) throws Exception {
        ProgramGraph<String, String> pg = createProgramGraph();
        pg.setInitial(exp.getText().replaceAll("\\s+", ""), true);

        recursiveNanoPromelaPG(exp);
        for (PGTransition<String, String> trans : final_transitions) {
            PGTransition<String, String> new_trans = new PGTransition<>(trans.getFrom().replaceAll("\\s+", ""),
                    trans.getCondition().replaceAll("\\s+", ""), trans.getAction().replaceAll("\\s+", ""),
                    trans.getTo().replaceAll("\\s+", ""));
            pg.addTransition(new_trans);
        }
        final_transitions = new HashSet<>();

        return pg;
    }

    private Set<PGTransition<String, String>> recursiveNanoPromelaPG(StmtContext exp) throws Exception {
        Set<PGTransition<String, String>> transitions = new HashSet<>();
        String sexp = exp.getText();
        //////////Parse simple statement/////////
        if (exp.assstmt() != null || exp.chanreadstmt() != null || exp.chanwritestmt() != null ||
                exp.atomicstmt() != null || exp.skipstmt() != null) {
            String simpleStmt = exp.getText();
            PGTransition<String, String> trans = new PGTransition<>(simpleStmt, "true", simpleStmt, "exit");
            transitions.add(trans);
            final_transitions.add(trans);
        }//////////Parse if statement/////////////
        else if (exp.ifstmt() != null) {
            IfstmtContext if_stmt = exp.ifstmt();
            for (OptionContext opt : if_stmt.option()) {
                //get the transitions of the sub expressions of if_stmt
                String sopt = opt.getText();
                Set<PGTransition<String, String>> opts_transitions = recursiveNanoPromelaPG(opt.stmt());
                if (opts_transitions.isEmpty())
                    throw new Exception("Invalid Nano Promela code");
                for (PGTransition<String, String> opt_trans : opts_transitions) {
                    PGTransition<String, String> new_trans;
                    if (!(opt_trans.getCondition().equals("") || opt_trans.getCondition().equals("true"))) {
                        String cond = "(" + opt.boolexpr().getText() + ") && (" + opt_trans.getCondition() + ")";
                        new_trans = new PGTransition<>(exp.getText(), cond,
                                opt_trans.getAction(), opt_trans.getTo());
                    } else {
                        new_trans = new PGTransition<>(exp.getText(),
                                opt.boolexpr().getText(),
                                opt_trans.getAction(), opt_trans.getTo());
                    }
                    transitions.add(new_trans);
                    final_transitions.add(new_trans);
                }
                final_transitions.addAll(opts_transitions);
            }
            if (transitions.isEmpty())
                throw new Exception("Invalid Nano Promela code");
        }////////////Parse do statement///////////
        else if (exp.dostmt() != null) {
            DostmtContext do_stmt = exp.dostmt();
            String exit_cond = "";
            for (OptionContext opt : do_stmt.option()) {
                exit_cond += "!(" + opt.boolexpr().getText() + ") && ";
                Set<PGTransition<String, String>> opts_transitions = recursiveNanoPromelaPG(opt.stmt());
                if (opts_transitions.isEmpty())
                    throw new Exception("Invalid Nano Promela code");
                for (PGTransition<String, String> opt_trans : opts_transitions) {
                    String trans_to;
                    if (opt_trans.getTo().equals("exit"))//sub expr transitions to exit
                        trans_to = exp.getText();
                    else trans_to = opt_trans.getTo() + ";" + exp.getText();

                    PGTransition<String, String> new_trans;
                    if (!(opt_trans.getCondition().equals("") || opt_trans.getCondition().equals("true"))) { //sub expr has its own condition
                        String cond = "(" + opt.boolexpr().getText() + ") && (" + opt_trans.getCondition() + ")";
                        new_trans = new PGTransition<>(exp.getText(), cond,
                                opt_trans.getAction(), trans_to);
                    } else { //sub expr has no condition
                        new_trans = new PGTransition<>(exp.getText(),
                                opt.boolexpr().getText(),
                                opt_trans.getAction(), trans_to);
                    }
                    transitions.add(new_trans);
                    final_transitions.add(new_trans);
                }
                final_transitions.addAll(opts_transitions);
            }
            if (transitions.isEmpty())
                throw new Exception("Invalid Nano Promela code");
            //add exit transition
            exit_cond = exit_cond.substring(0, exit_cond.length() - 4);
            PGTransition<String, String> exit_trans = new PGTransition<>(exp.getText(),
                    exit_cond, "", "exit");
            transitions.add(exit_trans);
            final_transitions.add(exit_trans);
        }/////////Parse concatenation statement//////////
        else {
            List<StmtContext> stmts = exp.stmt();
            StmtContext first = stmts.get(0);
            StmtContext second = stmts.get(1);
            StmtContext next;
            Set<PGTransition<String, String>> first_transitions = recursiveNanoPromelaPG(first);
            if (first_transitions.isEmpty())
                throw new Exception("Invalid Nano Promela code");
            for (PGTransition<String, String> trans : first_transitions) {
                String trans_to;
                if (trans.getTo().equals("exit"))
                    trans_to = second.getText();
                else trans_to = trans.getTo() + ";" + second.getText();
                String trans_from = first.getText() + ";" + second.getText();
                PGTransition<String, String> new_trans = new PGTransition<>(trans_from,
                        trans.getCondition(), trans.getAction(), trans_to);
                transitions.add(new_trans);
                final_transitions.add(new_trans);
                next = NanoPromelaFileReader.pareseNanoPromelaString(trans_to);
                String snext = next.getText();
                snext = snext + "";
                boolean add_next = true;
                for (PGTransition<String, String> final_trans : final_transitions) {
                    if (final_trans.getFrom().replaceAll("\\s+", "").equals(next.getText().replaceAll("\\s+", ""))) {
                        add_next = false;
                    }
                }
                if (add_next) {
                    Set<PGTransition<String, String>> next_trans = recursiveNanoPromelaPG(next);
                    transitions.addAll(next_trans);
                    final_transitions.addAll(next_trans);
                }
            }
            if (transitions.isEmpty()) {
                throw new Exception("Invalid Nano Promela code");
            }
        }
        return transitions;
    }

    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts>  Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
                                                                                Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> ret = new TransitionSystem<>();
        //// create initial states
        for (Sts s0 : ts.getInitialStates()){
            for (Saut q0: aut.getInitialStates()){
                Set<Saut> next_states = aut.nextStates(q0, ts.getLabel(s0));
                if(next_states!=null)
                    for (Saut q : next_states){
                        Pair<Sts, Saut> new_state = new Pair<>(s0, q);
                        ret.addInitialState(new_state);
                        ret.addToLabel(new_state, q);
                    }
            }
        }

        List<Pair<Sts, Saut>> states = new ArrayList<>(ret.getInitialStates());
        for (int i = 0; i < states.size(); i++){
            Pair<Sts, Saut> curr = states.get(i);
            //// AP = Q
            ret.addAtomicProposition(curr.second);
            //// create transitions (and states)
            for (TSTransition<Sts, A> trans : ts.getTransitions()){
                if (trans.getFrom().equals(curr.first)){
                    Sts t = trans.getTo();
                    Set<Saut> next_states = aut.nextStates(curr.second, ts.getLabel(t));
                    if (next_states == null)
                        continue;
                    for (Saut p : next_states){
                        Pair<Sts, Saut> new_state = new Pair<>(t, p);
                        ret.addTransition(new TSTransition<>(curr, trans.getAction(), new_state));
                        ret.addToLabel(new_state, p);
                        if (!states.contains(new_state))
                            states.add(new_state);
                    }
                }
            }
        }

        return ret;
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S>    Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    A Büchi automaton for the words that do not satisfy the
     *               property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
                                                                              Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> prod = product(ts,aut);

        for (Pair<S, Saut> s0 : prod.getInitialStates()){
            // reachable states that don't fulfill FI
            Set<Pair<S, Saut>> reach_prod = nested_dfs(s0, prod, aut);
            for (Pair<S, Saut> s: reach_prod){
                // check cycle
                Set<Pair<S, Saut>> reach2_prod = nested_dfs(s, prod, aut);
                if (reach2_prod.contains(s)){
                    VerificationFailed<S> vFailed = new VerificationFailed<>();
                    List<S> prefix = reverse(s0, s, prod);
                    List<S> cycle = reverse(s, s, prod);
                    vFailed.setPrefix(prefix);
                    vFailed.setCycle(cycle);
                    return vFailed;
                }
            }
        }
        return new VerificationSucceeded<>();
    }

    private <S, A, P, Saut> Set<Pair<S, Saut>> nested_dfs(Pair<S, Saut> s, TransitionSystem<Pair<S, Saut>, A, Saut> prod,
                                               Automaton<Saut, P> aut){
        Set<Pair<S, Saut>> ret = new HashSet<>();
        Set<Saut> accepting = aut.getAcceptingStates();
        Stack<Pair<S, Saut>> stack = new Stack<>();
        stack.push(s);
        Set<Pair<S, Saut>> visited = new HashSet<>();

//        if (accepting.contains(s.second))
//            ret.add(s);

        while(!stack.empty()){
            Pair<S, Saut> curr = stack.pop();
            visited.add(curr);
            for (Pair<S, Saut> neighbor : post(prod, curr)){
                if (accepting.contains(neighbor.second))
                    ret.add(neighbor);
                if (!stack.contains(neighbor) && !visited.contains(neighbor))
                    stack.push(neighbor);
            }
        }
        return ret;
    }

    private <S, A, Saut> List<S> reverse(Pair<S, Saut> first, Pair<S, Saut> last, TransitionSystem<Pair<S, Saut>, A, Saut> prod){
        List<S> ret = new ArrayList<>();
        Node<Pair<S, Saut>> start = new Node<>(first, null);
        Stack<Node<Pair<S, Saut>>> stack = new Stack<>();
        Set<Pair<S, Saut>> visited = new HashSet<>();
        stack.push(start);

        int iteration = 0;
        while (!stack.empty()){
            Node<Pair<S, Saut>> curr_node = stack.pop();
            Pair<S, Saut> curr = curr_node._state;
            if (iteration > 0){
                if (curr.equals(last)){
                    while (curr_node._parent != null){
                        ret.add(0, curr_node._state.first);
                        curr_node = curr_node._parent;
                    }
                    if (!first.equals(last))
                        ret.add(0, curr_node._state.first);
                    break;
                }
                visited.add(curr);
            }
            for (Pair<S, Saut> neighbor : post(prod, curr)){
                Node<Pair<S, Saut>> neighbor_node = new Node<>(neighbor, curr_node);
                if (!stack.contains(neighbor_node) && !visited.contains(neighbor)){
                    stack.push(neighbor_node);
                }
            }
            iteration++;
        }
        return ret;
    }

    private static class Node<S>{
        S _state;
        Node<S> _parent;

        public Node(S state, Node<S> parent){
            _state = state;
            _parent = parent;
        }

        @Override
        public boolean equals(Object obj){
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (!(obj instanceof Node)) {
                return false;
            }
            @SuppressWarnings("rawtypes")
            final Node other = (Node) obj;
            if (this._parent == null && ((Node) obj)._parent == null)
                return true;
            if (this._parent == null || ((Node) obj)._parent == null)
                return false;
            if (!Objects.equals(this._parent, ((Node) obj)._parent))
                return false;
            return Objects.equals(this._state, ((Node) obj)._state);
        }
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        MultiColorAutomaton automaton = new MultiColorAutomaton();
        Set<LTL<L>> expressions = new HashSet<>();
        Queue<LTL<L>> queue = new LinkedList<>();
        queue.add(ltl);
        //preparing to create sub_ltl
        while(!queue.isEmpty()) {
            LTL<L> curr = queue.poll();
            if (curr instanceof Not) {
                queue.add(((Not<L>) curr).getInner());
            } else {
                if (curr instanceof And) {
                    queue.add(((And<L>) curr).getLeft());
                    queue.add(((And<L>) curr).getRight());
                }
                else if (curr instanceof Next) {
                    queue.add(((Next<L>) curr).getInner());
                    expressions.add(curr);
                } else if (curr instanceof Until) {
                    queue.add(((Until<L>) curr).getLeft());
                    queue.add(((Until<L>) curr).getRight());
                }
                if(!expressions.contains(curr))
                    expressions.add(curr);
            }
        }
        Set<Set<LTL<L>>> states = new HashSet<>();
        // sublist
        Set<Set<LTL<L>>> subList = getLTLPermotations(expressions);
        Set<LTL<L>> AllExpressions = new HashSet<>(expressions);
        expressions.forEach(e -> AllExpressions.add(new Not(e)));
        List<Set<LTL<L>>> list = new ArrayList<>(subList);
        Set<Until<L>> untilExp = AllExpressions.stream().filter(exp -> exp instanceof Until).map(exp -> (Until<L>) exp).collect(Collectors.toSet());
        Set<LTL<L>> nextExp = new HashSet<>();
        for(var s:AllExpressions){
            if(s instanceof Next)
                nextExp.add(s);
            else if (s instanceof Not && ((Not<L>) s).getInner() instanceof Next)
                nextExp.add(s);
        }
        // filtering the states : add to states list just the states that are correct
        for (var sub: subList) {
            Boolean toAdd=true;
            for(var e:untilExp){
                if(sub.contains(e.getRight()))
                    toAdd = toAdd && sub.contains(e);
            }
            for (LTL<L> element: sub) {
                if (!toAdd) break;
                toAdd = !sub.contains(LTL.not(new TRUE<L>()));
                if (!toAdd) break;
                if (element instanceof And)
                    toAdd = sub.contains(((And<L>) element).getLeft()) && sub.contains(((And<L>) element).getRight());
                else if (element instanceof Until)
                    toAdd = sub.contains(((Until<L>) element).getLeft()) || sub.contains(((Until<L>) element).getRight());
                else if (element instanceof Not) {
                    LTL<L> elementIn = ((Not<L>) element).getInner();
                    if(elementIn instanceof And){
                        toAdd = !(sub.contains(((And<L>) elementIn).getLeft()) && sub.contains(((And<L>) elementIn).getRight()));
                    }
                    else if (elementIn instanceof Until)
                        toAdd = !(sub.contains(((Until<L>) elementIn).getRight()));
                }
            }
            if(toAdd)
                states.add(sub);
        }

        //setting accepting states in the automation
        int c = 0;
        for (Until<L> until : untilExp) {
            for (Set<LTL<L>> state : states) {
                if(!state.contains(until) || state.contains(until.getRight()))
                    automaton.setAccepting(state,c);
            }
            c++;
        }
        //creating to transmition
        for (Set<LTL<L>> stateFrom: states) {
            Set<L> action = stateFrom.stream().filter(exp -> exp instanceof AP).map(exp -> ((AP<L>) exp).getName()).collect(Collectors.toSet());
            for (Set<LTL<L>> stateTo: states) {
                boolean flag=true;
                for(var u:untilExp){
                    if(stateFrom.contains(u) && !stateFrom.contains(u.getRight())) {
                        flag = flag && stateTo.contains(u);
                    }
                    if(!stateFrom.contains(u) && stateFrom.contains(u.getLeft()))
                        flag = flag && !stateTo.contains(u);
                }
                for(var n:nextExp){
                    if(stateFrom.contains(n)){
                        if(n instanceof Next)
                            flag=flag && stateTo.contains(((Next<L>) n).getInner());
                        else if(n instanceof Not)
                            flag=flag && stateTo.contains(new Not<>(((Next<L>)(((Not<L>) n).getInner())).getInner()));
                    }
                }
                if(flag)
                    automaton.addTransition(stateFrom,action,stateTo);
            }
        }

        if (automaton.getColors().isEmpty()) {
            for (var state:states) {
                automaton.setAccepting(state,0);
            }
        }
        // set initial states
        for(var s:states){
            automaton.addState(s);
            if(s.contains(ltl))
                automaton.setInitial(s);
        }
        return GNBA2NBA(automaton);
    }

    public <L> Set<Set<LTL<L>>> getLTLPermotations(Set<LTL<L>> list) {
        Set<Set<LTL<L>>> ret = new HashSet<>();
        if (list.isEmpty()) {
            return new HashSet<>();
        }
        List<LTL<L>> l = new ArrayList(list);
        LTL<L> x = l.get(0);
        var xs = l.size() > 1 ? new HashSet(l.subList(1, l.size())) : new HashSet<LTL<L>>();
        Set<Set<LTL<L>>> xs_per = getLTLPermotations(xs);
        if (xs_per.isEmpty()) {
            ret.add(new HashSet<>(Arrays.asList(x)));
            ret.add(new HashSet<>(Arrays.asList(LTL.not(l.get(0)))));
        } else {
            for (Set<LTL<L>> sub : xs_per) {
                Set<LTL<L>> newsubX = new HashSet<LTL<L>>(sub);
                Set<LTL<L>> newsubNotX = new HashSet<LTL<L>>(sub);
                newsubX.add(x);
                newsubNotX.add(LTL.not(x));
                ret.add(newsubX);
                ret.add(newsubNotX);
            }
        }
        return ret;
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L>    Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        Automaton<Pair<?,Integer>,L> ret = new Automaton<>();
        List<Integer> colors = new LinkedList<>(mulAut.getColors());

        colors.stream().sorted();
        Integer first_color = colors.get(0);
        // duplicate the GNBA k times - adding all states to the NBA
        for(Integer color : colors){
            for(var state : mulAut.getTransitions().keySet()){
                ret.addState(new Pair<>(state,color));
            }
        }
        // setting initials states
        for(var initial : mulAut.getInitialStates()){
            Pair<?,Integer> state = new Pair<>(initial,first_color);
            ret.setInitial(state);
        }

        for (Integer color:colors){
            for(var state_from : mulAut.getTransitions().keySet()){
                for (var action : mulAut.getTransitions().get(state_from).keySet()){
                    for (var state_to:mulAut.getTransitions().get(state_from).get(action)){
                        if(mulAut.getAcceptingStates(color).contains(state_from)){
                            ret.addTransition(new Pair<>(state_from,color),action,new Pair<>(state_to,(colors.get((colors.indexOf(color)+1)%colors.size()))));
                        }
                        else{
                            ret.addTransition(new Pair<>(state_from,color),action,new Pair<>(state_to,color));
                        }
                    }

                }
            }
        }

        //set accepting states
        for(var accepting_state:mulAut.getAcceptingStates(first_color)){
            ret.setAccepting(new Pair<>(accepting_state,first_color));
        }
        return ret;
    }

    /**
     * Verify that a system satisfies an LTL formula under fairness conditions.
     * @param ts Transition system
     * @param fc Fairness condition
     * @param ltl An LTL formula
     * @param <S>  Type of states in the transition system
     * @param <A> Type of actions in the transition system
     * @param <P> Type of atomic propositions in the transition system
     * @return a VerificationSucceeded object or a VerificationFailed object with a counterexample.
     */
    public <S, A, P> VerificationResult<S> verifyFairLTLFormula(TransitionSystem<S, A, P> ts, FairnessCondition<A> fc, LTL<P> ltl){

        //F_uncond
        List<LTL<String>> uncond = new LinkedList<>();
        for( Set<A> s_exp : fc.getUnconditional()){
            LTL<String> ltl_or_aplha = always(eventually(concateltl("or",new ArrayList<>(s_exp),"t",0)));
            uncond.add(ltl_or_aplha);
        }
        LTL<String> ltl_uncond = concateltl("and",uncond,"",0);

        //F_strong
        List<LTL<String>> strong = new LinkedList<>();
        for( Set<A> s_exp : fc.getStrong()){
            LTL<String> ltl_enabled_aplha = always(eventually(concateltl("or",new ArrayList<>(s_exp),"e",0)));
            LTL<String> ltl_triggered_aplha = always(eventually(concateltl("or",new ArrayList<>(s_exp),"t",0)));
            strong.add(ifthen(ltl_enabled_aplha,ltl_triggered_aplha));
        }
        LTL<String> ltl_strong = concateltl("and",strong,"",0);

        //F_weak
        List<LTL<String>> weak = new LinkedList<>();
        for( Set<A> s_exp : fc.getWeak()){
            LTL<String> ltl_enabled_aplha = eventually(always(concateltl("or",new ArrayList<>(s_exp),"e",0)));
            LTL<String> ltl_triggered_aplha = always(eventually(concateltl("or",new ArrayList<>(s_exp),"t",0)));
            weak.add(ifthen(ltl_enabled_aplha,ltl_triggered_aplha));
        }
        LTL<String> ltl_weak = concateltl("and",weak,"",0);

        LTL<String> final_ltl_f = LTL.and(LTL.and(ltl_uncond,ltl_strong),ltl_weak);
        LTL<String> final_ltl_f_string = cleanUp(ifthen(final_ltl_f,translate(ltl)));
        //Automaton<?,String> aut = LTL2NBA(cleanUp(final_ltl_f_string));
        Automaton<?,String> aut = LTL2NBA(cleanUp(new Not<>(final_ltl_f_string)));
        TransitionSystem<Pair<S,A>,A,String> fairTs = Fairness_TransitionSystem(ts,fc);
        VerificationResult<Pair<S, A>> result = verifyAnOmegaRegularProperty(fairTs, aut);
        if (result instanceof VerificationSucceeded)
            return new VerificationSucceeded<>();
        else if (result instanceof VerificationFailed){
            VerificationFailed<Pair<S, A>> originalResult = (VerificationFailed)result;
            VerificationFailed<S> newFailedResult = new VerificationFailed<>();
            newFailedResult.setPrefix(originalResult.getPrefix().stream().map(x -> x.first).collect(Collectors.toList()));
            newFailedResult.setCycle(originalResult.getCycle().stream().map(x -> x.first).collect(Collectors.toList()));

            return newFailedResult;
        }
        return null;
    }

public <S> LTL<S> cleanUp(LTL<S> src){

     LTL<S> in;
    if(src instanceof Not) {

        in = cleanUp(((Not<S>) src).getInner());

        if (in instanceof Not)

            return ((Not<S>) in).getInner();
        return new Not<>(in);
    }
    if(src instanceof Until)
        return new Until<>(cleanUp(((Until<S>) src).getLeft()), cleanUp(((Until<S>) src).getRight()));

    if(src instanceof Next)
        return new Next<>(cleanUp(((Next<S>) src).getInner()));

    if(src instanceof And){
        LTL<S> left = cleanUp(((And<S>) src).getLeft()), right = cleanUp(((And<S>) src).getRight());

        if(left instanceof TRUE)
            return right;

        if(right instanceof TRUE)
            return left;

        if(left instanceof Not){
            in = cleanUp(((Not<S>) left).getInner());
            if(in instanceof TRUE)
                return left;
        }
        if(right instanceof Not){

            in = cleanUp(((Not<S>) right).getInner());

            if(in instanceof TRUE)
                return right;
        }
        return new And<>(cleanUp(((And<S>) src).getLeft()), cleanUp(((And<S>) src).getRight()));
    }
    return src;
}


    private <P,A> LTL<String> concateltl(String op, List<A> list,String wrapper,int i){
        if(list.size()==1 && wrapper=="")
            return (LTL<String>)list.get(0);
        if(list.size()==0)
            return LTL.true_();
        if(op.equals("and")){
            if(wrapper=="t") {
                if (i == list.size() - 1)
                    return new AP<>("t(" + list.get(i).toString() + ")");
                return LTL.and(new AP<>("t(" + list.get(i).toString() + ")"), concateltl(op, list, wrapper, ++i));
                //return LTL.and(new Triggerd<P>(list.get(i).toString()).toString(),concateltl(op,list,wrapper,++i));
            }
            else if(wrapper=="e") {
                if (i == list.size() - 1)
                    return new AP<>("e(" + list.get(i).toString() + ")");
                return LTL.and(new AP<>("e(" + list.get(i).toString() + ")"), concateltl(op, list, wrapper, ++i));
                //return LTL.and(new Enabled<>(list.get(i).toString()),concateltl(op,list,wrapper,++i));
            }
            else
                return LTL.and((LTL<String>)list.get(i),concateltl(op,list,wrapper,++i));
                //return LTL.and((LTL<P>) list.get(i),concateltl(op,list,wrapper,++i));
        }
        else if(op.equals("or")){
            if(wrapper=="t") {
                if (i == list.size() - 1)
                    return new AP<>("t(" + list.get(i).toString() + ")");
                return or(new AP<>("t(" + list.get(i).toString() + ")"), concateltl(op, list, wrapper, ++i));
                //return or(new Triggerd<P>(list.get(i).toString()),concateltl(op,list,wrapper,++i));
            }
            else if(wrapper=="e") {
                if (i == list.size() - 1)
                    return new AP<>("e(" + list.get(i).toString() + ")");
                return or(new AP<>("e(" + list.get(i).toString() + ")"), concateltl(op, list, wrapper, ++i));
                //return or(new Enabled<>(list.get(i).toString()),concateltl(op,list,wrapper,++i));
            }
            else
                return or((LTL<String>)list.get(i),concateltl(op,list,wrapper,++i));
                //return or((LTL<P>) list.get(i),concateltl(op,list,wrapper,++i));
        }
        return null;
    }

    private <P> LTL<P> or(LTL<P> a,LTL<P> b){
        return LTL.not(LTL.and(LTL.not(a),LTL.not(b)));
    }
    private <P> LTL<P> eventually(LTL<P> ltl){
        return LTL.until(LTL.true_(), ltl);
    }

    private <P> LTL<P> always(LTL<P> ltl){
        return LTL.not(eventually(LTL.not(ltl)));
    }
    private <P> LTL<P> ifthen(LTL<P> ltl1,LTL<P> ltl2){
        return or(LTL.not(ltl1),ltl2);
    }
    private <P> LTL<String> translate(LTL<P> ltl){
        if (ltl instanceof TRUE)
            return LTL.true_();
        if (ltl instanceof AP)
            return new AP<String>(((AP<P>) ltl).getName().toString());
        if (ltl instanceof And)
            return LTL.and(translate(((And<P>) ltl).getLeft()), translate(((And<P>) ltl).getRight()));
        if (ltl instanceof Until)
            return LTL.until(translate(((Until<P>) ltl).getLeft()), translate(((Until<P>) ltl).getRight()));
        if (ltl instanceof Not) {
//            if(((Not<P>) ltl).getInner() instanceof Not)
//                return translate(((Not<P>) ((Not<P>) ltl).getInner()).getInner());
             return LTL.not(translate(((Not<P>) ltl).getInner()));
        }
        if (ltl instanceof Next)
            return LTL.not(translate(((Next<P>) ltl).getInner()));
        return null;
    }

    private  <T1, T2> Set<Pair<T1, T2>> getCombination(Set<T1> s1, Set<T2> s2){
        Set<Pair<T1, T2>> ret = new HashSet<>();
        for (var s : s1){
            for(var a : s2){
                ret.add(new Pair<>(s, a));
            }
        }
        return ret;
    }
    private <S, A, P> TransitionSystem<Pair<S, A>, A, String> Fairness_TransitionSystem(TransitionSystem<S, A, P> ts,FairnessCondition<A> fc) {

        TransitionSystem<Pair<S, A>, A, String> ans = new TransitionSystem<>();
        Set<Pair<S,A>> allstates = getCombination(ts.getStates(),ts.getActions());
        for (var s : allstates)
            for(var t:ts.getTransitions()){
                if(t.getTo().equals(s.first) && t.getAction().equals(s.second))
                    ans.addState(s);
            }
        Set<Pair<S,A>> allinits = getCombination(ts.getInitialStates(),ts.getActions());
        for (var s : allinits)
            ans.addInitialState(s);

        //labels
        Set<String> label_list = new LinkedHashSet<>();
        for (Set<A> c: fc.getWeak()){
            for(A a:c) {
                label_list.add("t(" + a + ")");
                label_list.add("e(" + a + ")");
            }
        }
        for (Set<A> c: fc.getStrong()){
            for(A a:c) {
                label_list.add("t(" + a + ")");
                label_list.add("e(" + a + ")");
            }
        }
        for (Set<A> c: fc.getUnconditional()){
            for(A a:c) {
                label_list.add("t(" + a + ")");
            }
        }
        for(var state:ans.getStates()){
            Set<String> labels = ts.getLabel(state.first).stream().map(l -> l.toString()).collect(Collectors.toSet());
            labels.remove("");
            String trig_state = "t("+state.second.toString()+")";
            if(label_list.contains(trig_state)){
                labels.add(trig_state);
            }
            for(var trans: ts.getTransitions()){
                if(trans.getFrom().equals(state.first)) {
                    String lbl = "e(" + trans.getAction() + ")";
                    if (label_list.contains(lbl))
                        labels.add(lbl);
                }
            }
            labels.stream().forEach(x->ans.addToLabel(state,x));
        }
        //transitions
        for(var s:ans.getStates()){
            for(var t:ts.getTransitions()){
                if(s.first.equals(t.getFrom()))
                    for(var to:ans.getStates()){
                        if(to.first.equals(t.getTo()) && to.second.equals(t.getAction()))
                            ans.addTransition(new TSTransition<>(s,t.getAction(),to));
                    }
            }
        }


        return ans;
    }

}
