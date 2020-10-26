package il.ac.bgu.cs.formalmethodsintro.base.programgraph;

import java.util.Map;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.Evaluator;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaLexer;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.BoolexprContext;

/**
 * An object that identifies and interprets the conditions defined in the
 * grammar nanopromela/NanoPromela.g4
 */
public class ParserBasedCondDef implements ConditionDef {

    /**
     * @see
     * il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef#evaluate(java.util.Map,
     * java.lang.String)
     */
    @Override
    public boolean evaluate(Map<String, Object> eval, String condition) {
        if (condition.equals("")) {
            return true;
        }

        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(condition));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        NanoPromelaParser parser = new NanoPromelaParser(tokens);

        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowingErrorListener());

        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowingErrorListener());

        BoolexprContext context = parser.boolexpr();

        return new Evaluator(eval).evaluate(context);
    }

}
