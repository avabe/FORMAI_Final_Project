package il.ac.bgu.cs.formalmethodsintro.base;

import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.GraphvizPainter;

/**
 * Use {@link GraphvizPainter} to draw transition systems using Graphviz. See
 * {@linkplain http://graphviz.org} on usage etc.
 */
public class GraphvizSamples {

    static FvmFacade fvmFacadeImpl = FvmFacade.get();

    public enum STATE {
        pay, soda, beer, select
    };

    public enum ACTION {
        insertCoin, getSoda, getBeer, tau
    }

    @SuppressWarnings({"unchecked"})
    public static void main(String[] args) {
        TransitionSystem<STATE, ACTION, String> vendingMachine = new TransitionSystem<>();

        vendingMachine.addState(STATE.pay);
        vendingMachine.addState(STATE.soda);
        vendingMachine.addState(STATE.select);
        vendingMachine.addState(STATE.beer);

        vendingMachine.addInitialState(STATE.pay);

        vendingMachine.addAction(ACTION.insertCoin);
        vendingMachine.addAction(ACTION.getBeer);
        vendingMachine.addAction(ACTION.getSoda);
        vendingMachine.addAction(ACTION.tau);

        vendingMachine.addTransition(new TSTransition<>(STATE.pay, ACTION.insertCoin, STATE.select));
        vendingMachine.addTransition(new TSTransition<>(STATE.select, ACTION.tau, STATE.soda));
        vendingMachine.addTransition(new TSTransition<>(STATE.select, ACTION.tau, STATE.beer));
        vendingMachine.addTransition(new TSTransition<>(STATE.soda, ACTION.getSoda, STATE.pay));
        vendingMachine.addTransition(new TSTransition<>(STATE.beer, ACTION.getBeer, STATE.pay));

        vendingMachine.addAtomicProposition("paid");
        vendingMachine.addAtomicProposition("drink");

        vendingMachine.addToLabel(STATE.soda, "paid");
        vendingMachine.addToLabel(STATE.beer, "paid");
        vendingMachine.addToLabel(STATE.select, "paid");
        vendingMachine.addToLabel(STATE.soda, "drink");
        vendingMachine.addToLabel(STATE.beer, "drink");

        // You can copy the resulting string to, e.g., https://dreampuf.github.io/GraphvizOnline
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(vendingMachine));
    }

}
