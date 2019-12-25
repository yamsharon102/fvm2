package il.ac.bgu.cs.formalmethodsintro.base.myTests.TS;

import il.ac.bgu.cs.formalmethodsintro.base.exceptions.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;

import static il.ac.bgu.cs.formalmethodsintro.base.myTests.TS.TransitionSystemTest.Actions.*;
import static il.ac.bgu.cs.formalmethodsintro.base.myTests.TS.TransitionSystemTest.States.*;
import static il.ac.bgu.cs.formalmethodsintro.base.myTests.TS.TransitionSystemTest.AP.*;

import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;

import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * Set of basic tests for {@link TransitionSystem} implementation.
 */
public class TransitionSystemTest {

    public static enum States {S1, S2, S3}

    public static enum AP {P, Q}

    public static enum Actions {A1, A2, A3}

    TransitionSystem<States, Actions, AP> ts;

    @Before
    public void before() {
        ts = new TransitionSystem<>();
    }

    @Test(expected = Exception.class, timeout = 2000)
    public void initialStateMustBeInStates() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addInitialState(S3);
    }

    @Test(timeout = 2000)
    public void initialStateMustBeInStatesValid() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addInitialState(S1);
    }

    @Test(expected = DeletionOfAttachedStateException.class, timeout = 2000)
    public void initialStateCantBeRemoved() throws Exception {
        ts.addState(S1);
        ts.addInitialState(S1);
        ts.removeState(S1);
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
    public void usedLabelCanBeRemovedAfterCleaning() throws Exception {
        ts.addState(S1);
        ts.addAtomicProposition(Q);
        ts.addToLabel(S1, Q);
        ts.removeLabel(S1, Q);
        ts.removeAtomicProposition(Q);
    }

    @Test(timeout = 2000)
    public void labeledStateLabelWorks() throws Exception {
        ts.addState(S1);
        ts.addAtomicPropositions(Q, P);
        ts.addToLabel(S1, Q);
        assertEquals(set(Q), ts.getLabel(S1));
        ts.addToLabel(S1, P);
        assertEquals(set(Q, P), ts.getLabel(S1));
    }

    @Test(timeout = 2000)
    public void labeledStateLabelWorks_emptysetLabel() throws Exception {
        ts.addState(S1);
        ts.addAtomicProposition(Q);
        assertEquals(set(), ts.getLabel(S1));
    }

    @Test(expected = StateNotFoundException.class, timeout = 2000)
    public void labeledStateInvalidStateError() throws Exception {
        ts.addState(S1);
        ts.getLabel(S3);
        fail("When asked about the label of a nonexistent state, the transition system should throw a StateNotFoundException");
    }

    @Test(expected = DeletionOfAttachedStateException.class, timeout = 2000)
    public void labeledStateCantBeRemoved() throws Exception {
        ts.addState(S1);
        ts.addAtomicProposition(P);
        ts.addToLabel(S1, P);
        ts.removeState(S1);
    }

    @Test(timeout = 2000)
    public void labeledStateCanBeRemovedAfterCleaning() throws Exception {
        ts.addState(S1);
        ts.addAtomicProposition(P);
        ts.addToLabel(S1, P);
        ts.removeLabel(S1, P);
        ts.removeState(S1);
    }

    @Test(timeout = 2000)
    public void addValidTransition() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S2));
    }

    @Test(expected = InvalidTransitionException.class, timeout = 2000)
    public void addInvalidTransition_fromState() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S3, A1, S2));
    }

    @Test(expected = InvalidTransitionException.class, timeout = 2000)
    public void addInvalidTransition_toState() throws Exception {
        ts.addState(S1);
        ts.addState(S2);
        ts.addAction(A1);
        ts.addTransition(new TSTransition<>(S1, A1, S3));
    }

    @Test(expected = InvalidTransitionException.class, timeout = 2000)
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