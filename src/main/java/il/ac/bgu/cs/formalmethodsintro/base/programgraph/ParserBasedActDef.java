package il.ac.bgu.cs.formalmethodsintro.base.programgraph;

import java.util.Map;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;

import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.Evaluator;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaLexer;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.SpecContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;

/**
 * An object that identifies and interprets the actions defined in the grammar
 * nanopromela/NanoPromela.g4
 */
public class ParserBasedActDef implements ActionDef {

    /**
     * @see
     * il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef#effect(java.util.Map,
     * java.lang.String)
     */
    @Override
    public Map<String, Object> effect(Map<String, Object> eval, Object action) {
        if (action.equals("")) {
            return eval;
        }

        return new Evaluator(eval).evaluate(parseAction((String) action));
    }

    /**
     * Parse the action.
     *
     * @param action A string that represents an action
     * @return The root of the parse tree or null, if the string cannot be
     * parsed.
     */
    private StmtContext parseAction(String action) {
        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(action));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        NanoPromelaParser parser = new NanoPromelaParser(tokens);

        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowingErrorListener());

        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowingErrorListener());

        try {
            SpecContext spec = parser.spec();
            StmtContext p = spec.stmt();
            return p;
        } catch (RecognitionException ex) {
            return null;
        }
    }

    /**
     * @see
     * il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef#isMatchingAction(java.lang.String)
     */
    @Override
    public boolean isMatchingAction(Object action) {
        return action.equals("") || parseAction((String) action) != null;
    }

}
