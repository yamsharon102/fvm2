package il.ac.bgu.cs.formalmethodsintro.base.ex2;

import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.Actions.Switch;
import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.AutomatonStates.Q0;
import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.AutomatonStates.Q1;
import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.AutomatonStates.Q2;
import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.Lights.Green;
import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.Lights.Off;
import static il.ac.bgu.cs.formalmethodsintro.base.ex2.AutTsProductTests.Lights.Red;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.p;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class AutTsProductTests {

    public enum Lights {
        Off, Green, Red
    }

    public enum Actions {
        Switch
    }

    public enum AutomatonStates {
        Q0, Q1, Q2
    }



    FvmFacade fvmFacadeImpl = FvmFacade.get();

    @SuppressWarnings("unchecked")
    @Test
    public void autTimesTs() {
        TransitionSystem<Lights, Actions, String> ts1 = buildTransitionSystem1();
        TransitionSystem<Lights, Actions, String> ts2 = buildTransitionSystem2();
        Automaton<AutomatonStates, String> aut = buildAutomaton();

        TransitionSystem<Pair<Lights, AutomatonStates>, Actions, AutomatonStates> comb1 = fvmFacadeImpl.product(ts1, aut);
//        System.out.println(comb1.getStates().containsAll());
//        System.out.println(aut.getTransitions());
        assertTrue(comb1.getStates().containsAll(set(p(Green, Q0), p(Red, Q1), p(Red, Q2), p(Green, Q2), p(Red, Q0))));
        assertEquals(set(p(Red, Q1), p(Red, Q0)), comb1.getInitialStates());
        assertEquals(set(Switch), comb1.getActions());
        assertEquals(set(Q2, Q0, Q1), comb1.getAtomicPropositions());
        assertTrue(comb1.getTransitions().containsAll(
                set(transition(p(Green, Q0), Switch, p(Red, Q0)), transition(p(Green, Q0), Switch, p(Red, Q1)), transition(p(Red, Q2), Switch, p(Green, Q2)), transition(p(Green, Q2), Switch, p(Red, Q2)), transition(p(Red, Q1), Switch, p(Green, Q2)), transition(p(Red, Q0), Switch, p(Green, Q0)))));
        assertEquals(set(Q0), comb1.getLabel(p(Green, Q0)));
        assertEquals(set(Q1), comb1.getLabel(p(Red, Q1)));
        assertEquals(set(Q2), comb1.getLabel(p(Red, Q2)));
        assertEquals(set(Q2), comb1.getLabel(p(Green, Q2)));
        assertEquals(set(Q0), comb1.getLabel(p(Red, Q0)));

        TransitionSystem<Pair<Lights, AutomatonStates>, Actions, AutomatonStates> ts = fvmFacadeImpl.product(ts2, aut);

        assertTrue(ts.getStates().containsAll(set(p(Green, Q0), p(Off, Q2), p(Off, Q0), p(Red, Q1), p(Red, Q2), p(Green, Q2), p(Red, Q0), p(Off, Q1))));
        assertEquals(set(p(Red, Q1), p(Red, Q0)), ts.getInitialStates());
        assertEquals(set(Switch), ts.getActions());
        assertEquals(set(Q2, Q0, Q1), ts.getAtomicPropositions());
        assertTrue(ts.getTransitions().containsAll(set(transition(p(Off, Q1), Switch, p(Red, Q1)), transition(p(Green, Q0), Switch, p(Red, Q1)), transition(p(Off, Q0), Switch, p(Red, Q1)), transition(p(Red, Q2), Switch, p(Green, Q2)), transition(p(Green, Q2), Switch, p(Red, Q2)), transition(p(Red, Q1), Switch, p(Green, Q2)),
                transition(p(Red, Q2), Switch, p(Off, Q2)), transition(p(Red, Q1), Switch, p(Off, Q1)), transition(p(Off, Q2), Switch, p(Red, Q2)), transition(p(Green, Q0), Switch, p(Red, Q0)), transition(p(Red, Q0), Switch, p(Green, Q0)), transition(p(Red, Q0), Switch, p(Off, Q0)),
                transition(p(Off, Q0), Switch, p(Red, Q0)), transition(p(Red, Q0), Switch, p(Off, Q1)))));
        assertEquals(set(Q0), ts.getLabel(p(Green, Q0)));
        assertEquals(set(Q2), ts.getLabel(p(Off, Q2)));
        assertEquals(set(Q0), ts.getLabel(p(Off, Q0)));
        assertEquals(set(Q1), ts.getLabel(p(Red, Q1)));
        assertEquals(set(Q2), ts.getLabel(p(Red, Q2)));
        assertEquals(set(Q2), ts.getLabel(p(Green, Q2)));
        assertEquals(set(Q0), ts.getLabel(p(Red, Q0)));
        assertEquals(set(Q1), ts.getLabel(p(Off, Q1)));

    }

    private Automaton<AutomatonStates, String> buildAutomaton() {
        Automaton<AutomatonStates, String> aut = new Automaton<>();

        Set<String> notRedAndNotGreen = set();
        Set<String> redAndNotGreen = set("red");
        Set<String> greenAndNotRed = set("green");
        Set<String> redAndGreen = set("red", "green");

        aut.addTransition(Q0, notRedAndNotGreen, Q0);
        aut.addTransition(Q0, redAndNotGreen, Q0);
        aut.addTransition(Q0, greenAndNotRed, Q0);
        aut.addTransition(Q0, redAndGreen, Q0);

        aut.addTransition(Q0, notRedAndNotGreen, Q1);
        aut.addTransition(Q0, redAndNotGreen, Q1);

        aut.addTransition(Q1, notRedAndNotGreen, Q1);
        aut.addTransition(Q1, redAndNotGreen, Q1);

        aut.addTransition(Q1, greenAndNotRed, Q2);
        aut.addTransition(Q1, redAndGreen, Q2);

        aut.addTransition(Q2, notRedAndNotGreen, Q2);
        aut.addTransition(Q2, redAndNotGreen, Q2);
        aut.addTransition(Q2, greenAndNotRed, Q2);
        aut.addTransition(Q2, redAndGreen, Q2);

        aut.setInitial(Q0);
        aut.setAccepting(Q1);
        return aut;
    }

    private TransitionSystem<Lights, Actions, String> buildTransitionSystem1() {
        TransitionSystem<Lights, Actions, String> ts = new TransitionSystem<>();

        ts.addState(Green);
        ts.addState(Red);

        ts.addInitialState(Red);

        ts.addAction(Actions.Switch);

        ts.addTransitionFrom(Red).action(Switch).to(Green);
        ts.addTransitionFrom(Green).action(Switch).to(Red);

        ts.addAtomicProposition("green");
        ts.addAtomicProposition("red");

        ts.addToLabel(Green, "green");
        ts.addToLabel(Red, "red");
        return ts;
    }

    private TransitionSystem<Lights, Actions, String> buildTransitionSystem2() {
        TransitionSystem<Lights, Actions, String> ts = new TransitionSystem<>();

        ts.addStates(Off, Red, Green);
        ts.addInitialState(Red);
        ts.addAction(Switch);

        ts.addTransitionFrom(Red).action(Switch).to(Green);
        ts.addTransitionFrom(Green).action(Switch).to(Red);
        ts.addTransitionFrom(Red).action(Switch).to(Off);
        ts.addTransitionFrom(Off).action(Switch).to(Red);

        ts.addAtomicProposition("green");
        ts.addAtomicProposition("red");

        ts.addToLabel(Green, "green");
        ts.addToLabel(Red, "red");
        return ts;
    }

}