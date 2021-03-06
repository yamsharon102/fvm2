package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.lang.reflect.Array;
import java.nio.charset.IllegalCharsetNameException;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.goal.GoalStructure;
import il.ac.bgu.cs.formalmethodsintro.base.fairness.FairnessCondition;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.*;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationFailed;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationSucceeded;
import org.antlr.v4.runtime.ParserRuleContext;
import org.svvrl.goal.core.util.PowerSet;

import javax.swing.plaf.nimbus.State;


/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 * <<<<<<< HEAD
 * More about facade: {@linkplain //www.vincehuston.org/dp/facade.html}.
 * =======
 * >>>>>>> master
 */
public class FvmFacade {

    private String true_stmt = "";
    private String nothing_stmt = "";
    private String exit_stmt = "";

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
        if (ts.getInitialStates().size() > 1) return false; //|I|<=1
        else {
            Set<Pair<S, A>> pair_set = new HashSet<>();
            Set<TSTransition<S, A>> ts_transition = ts.getTransitions();
            for (TSTransition<S, A> t : ts_transition) {
                Pair<S, A> p1 = new Pair<>(t.getFrom(), t.getAction());
                if (pair_set.contains(p1)) return false; //means we saw before a
                pair_set.add(p1);
            }
            return true;
        }
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
        if (ts.getInitialStates().size() > 1) return false; //|I|<=1
        else {
            Set<Pair<Pair<S, A>, Set<P>>> pair_set = new HashSet<>();
            Set<TSTransition<S, A>> ts_transition = ts.getTransitions();
            for (TSTransition<S, A> t : ts_transition) {
                Pair<S, A> p1 = new Pair<>(t.getFrom(), t.getAction());
                Pair<Pair<S, A>, Set<P>> p2 = new Pair<>(p1, ts.getLabel(t.getTo()));
                if (pair_set.contains(p2)) return false;
                pair_set.add(p2);
            }
            return true;
        }
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
        return isExecutionFragment(ts, e) && ts.getInitialStates().contains(e.head()) && isStateTerminal(ts, e.last());
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
        AlternatingSequence<S, A> curr = e;

        for (int i = 0; i < e.size(); i = i + 2) {
            if (curr.tail().isEmpty()) return true;
            S s1 = curr.head();
            if (!ts.getStates().contains(s1)) throw new StateNotFoundException("");
            A a = curr.tail().head();
            if (!ts.getActions().contains(a)) throw new ActionNotFoundException("");
            curr = curr.tail().tail();
            S s2 = curr.head();
            // Checks if <s1,a,s2> is a valid transition.
            if (!(post(ts, s1, a).contains(s2)))
                return false;
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
        return isExecutionFragment(ts, e) && ts.getInitialStates().contains(e.head());
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
        return isExecutionFragment(ts, e) && isStateTerminal(ts, e.last());
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
        if (!ts.getStates().contains(s)) throw new StateNotFoundException("");
        for (TSTransition<S, A> transition : ts.getTransitions())
            if (transition.getFrom().equals(s))
                return false;
        return true;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that is reachable from s using transition 'trans'
        for (TSTransition<S, ?> trans : transitions)
            if (trans.getFrom().equals(s))
                retSet.add(trans.getTo());
        return retSet;
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
        Set<S> retSet = new HashSet<>();
        // Got the post states for each state in c and added them in a set
        for (S s : c) {
            Set<S> gotSet = post(ts, s);
            retSet.addAll(gotSet);
        }
        return retSet;
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
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that is reachable from s using action a in transition 'trans'
        for (TSTransition<S, ?> trans : transitions)
            if (trans.getFrom().equals(s) && trans.getAction().equals(a))
                retSet.add(trans.getTo());
        return retSet;
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
        Set<S> retSet = new HashSet<>();
        // Got the post states for each state in c  using action a and added them in a set
        for (S s : c) {
            Set<S> gotSet = post(ts, s, a);
            retSet.addAll(gotSet);
        }
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that s is reachable from using transition 'trans'
        for (TSTransition<S, ?> trans : transitions)
            if (trans.getTo().equals(s))
                retSet.add(trans.getFrom());
        return retSet;
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
        Set<S> retSet = new HashSet<>();
        // Got the pre states for each state in c and added them in a set
        for (S s : c) {
            Set<S> gotSet = pre(ts, s);
            retSet.addAll(gotSet);
        }
        return retSet;
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
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that s is reachable from using action a and transition 'trans'
        for (TSTransition<S, ?> trans : transitions)
            if (trans.getTo().equals(s) && trans.getAction().equals(a))
                retSet.add(trans.getFrom());
        return retSet;
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
        Set<S> retSet = new HashSet<>();
        // Got the pre states for each state in c using action a and added them in a set
        for (S s : c) {
            Set<S> gotSet = pre(ts, s, a);
            retSet.addAll(gotSet);
        }
        return retSet;
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
        // Start with initials, get their posts and so on until dead-end.
        Set<S> retSet = new HashSet<>();
        Set<S> curr = ts.getInitialStates();
        while (!curr.isEmpty()) {
            Set<S> statsToContinue = new HashSet<>();
            for (S s : curr)
                if (!retSet.contains(s)) {
                    retSet.add(s);
                    statsToContinue.add(s);
                }
            curr = post(ts, statsToContinue);
        }
        return retSet;
    }

//    public <S, A> Set<S> getExecution(TransitionSystem<S, A, ?> ts, S s) {
//        // Start with initials, get their posts and so on until dead-end.
//        List<S> retSet = new LinkedList<>();
//        Set<S> initialStates = ts.getInitialStates();
//        for (S s1 : initialStates) {
//
//        }
//        return retSet;
//    }

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
        return interleave(ts1, ts2, new HashSet<>());
    }

    private <S1, S2, A, P> Set<TSTransition<Pair<S1, S2>, A>> getTransInterleave(TransitionSystem<S1, A, P> ts1,
                                                                                 TransitionSystem<S2, A, P> ts2,
                                                                                 Set<Pair<S1, S2>> new_states, Set<A> handShakingActions) {
        Set<TSTransition<Pair<S1, S2>, A>> ret_set = new HashSet<>();
        for (TSTransition<S1, A> transition1 : ts1.getTransitions()) {
            if (!(handShakingActions.contains(transition1.getAction()))) {
                for (Pair<S1, S2> state1 : new_states)
                    if (state1.first.equals(transition1.getFrom()))
                        ret_set.add(new TSTransition<>(state1, transition1.getAction(),
                                new Pair<>(transition1.getTo(), state1.second)));
                    else
                        for (Pair<S1, S2> state2 : new_states)
                            if (state2.first.equals(transition1.getFrom()))
                                for (TSTransition<S2, A> transition2 : ts2.getTransitions())
                                    if (transition2.getFrom().equals(state2.second) &&
                                            transition2.getAction().equals(transition1.getAction()))
                                        ret_set.add(new TSTransition<>(state1, transition1.getAction(),
                                                new Pair<>(transition1.getTo(), transition2.getTo())));
            }
            else{
                for (TSTransition<S2, A> transition2 : ts2.getTransitions()){
                    if (transition2.getAction().equals(transition1.getAction())){
                        ret_set.add(new TSTransition<>(new Pair<>(transition1.getFrom(), transition2.getFrom()),
                                transition1.getAction(),
                                new Pair<>(transition1.getTo(), transition2.getTo())));
                    }
                }
            }
        }
        for (TSTransition<S2, A> transition2 : ts2.getTransitions())
            if (!(handShakingActions.contains(transition2.getAction())))
                for (Pair<S1, S2> state1 : new_states)
                    if (state1.second.equals(transition2.getFrom()))
                        ret_set.add(new TSTransition<>(state1, transition2.getAction(),
                                new Pair<>(state1.first, transition2.getTo())));
        return ret_set;
    }

    private <S1, S2, P, A> Set<Pair<S1, S2>> getStatesInterleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        Set<Pair<S1, S2>> ret_set = new HashSet<>();
        for (S1 s1 : ts1.getStates())
            for (S2 s2 : ts2.getStates())
                ret_set.add(new Pair<>(s1, s2));
        return ret_set;
    }

    private <A, S2, P, S1> TransitionSystem<Pair<S1, S2>, A, P> createTS(Set<Pair<S1, S2>> new_states, Set<Pair<S1, S2>> initials, Set<A> new_actions,
                                                                         Set<TSTransition<Pair<S1, S2>, A>> new_transitions, Set<P> new_APs,
                                                                         Map<Pair<S1, S2>, Set<P>> L_function) {
        TransitionSystem<Pair<S1, S2>, A, P> ret_ST = new TransitionSystem<>();
        for (Pair<S1, S2> state : new_states) {
            if (initials.contains(state))
                ret_ST.addInitialState(state);
            else
                ret_ST.addState(state);
        }
        ret_ST.addAllActions(new_actions);
        for (TSTransition<Pair<S1, S2>, A> transition : new_transitions)
            ret_ST.addTransition(transition);
        ret_ST.addAllAtomicPropositions(new_APs);

        return ret_ST;
    }

    private <S2, S1, A, P> Map<Pair<S1, S2>, Set<P>> getLFunction(
            TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<Pair<S1, S2>> new_states) {
        Map<Pair<S1, S2>, Set<P>> L_function = new HashMap<>();
        for (Pair<S1, S2> state : new_states) {
            Set<P> curr_AP = new HashSet<>();
            curr_AP.addAll(ts1.getLabel(state.first));
            curr_AP.addAll(ts2.getLabel(state.second));
            L_function.put(state, curr_AP);
        }
        return L_function;
    }

    private <P, A, S2, S1> TransitionSystem<Pair<S1,S2>,A,P> setLabels(TransitionSystem<Pair<S1,S2>,A,P> ret_st, Set<Pair<S1,S2>> new_states,
                                                                       TransitionSystem<S1,A,P> ts1, TransitionSystem<S2,A,P> ts2) {
        for (Pair<S1, S2> state : new_states){
            Set<P> labels1 = ts1.getLabel(state.first);
            for (P label1: labels1)
                ret_st.addToLabel(state, label1);
            Set<P> labels2 = (ts2.getLabel(state.second));
            for (P label2: labels2)
                ret_st.addToLabel(state, label2);
        }

        return ret_st;
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


        // States
        Set<Pair<S1, S2>> new_states = getStatesInterleave(ts1, ts2);

        // Initials
        Set<Pair<S1, S2>> initials = new HashSet<>();
        for (Pair<S1, S2> pair : new_states)
            if (ts1.getInitialStates().contains(pair.first) && ts2.getInitialStates().contains(pair.second))
                initials.add(pair);

        // Transitions
        Set<TSTransition<Pair<S1, S2>, A>> new_transitions =
                getTransInterleave(ts1, ts2, new_states, handShakingActions);

        // Actions
        Set<A> new_actions = new HashSet<>();
        new_actions.addAll(ts1.getActions());
        new_actions.addAll(ts2.getActions());

        // APs
        Set<P> new_APs = new HashSet<>();
        new_APs.addAll(ts1.getAtomicPropositions());
        new_APs.addAll(ts2.getAtomicPropositions());

        // L function
        Map<Pair<S1, S2>, Set<P>> L_function = getLFunction(ts1, ts2, new_states);

        // Create Transition System
        TransitionSystem<Pair<S1, S2>, A, P> ret_ST = createTS(new_states, initials, new_actions
                , new_transitions, new_APs, L_function);

        ret_ST = setLabels(ret_ST, new_states, ts1, ts2);

        return ret_ST;
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

    public Set<List<String>> create_initialization(Set<List<String>>  init){
        Set<List<String>> retl;
        if(init.size()>0) retl=init;
        else {
            retl=new HashSet<>();
            List<String> empty=new LinkedList<>();
            empty.add("");
            retl.add(empty);
        }
        return retl;
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
        ProgramGraph<Pair<L1,L2>,A> ret_graph=createProgramGraph();
        Set<List<String>> list1=create_initialization(pg1.getInitalizations()),list2=create_initialization(pg2.getInitalizations());

        for(List<String> l1:list1){
            for(List<String> l2:list2){
                List<String> l=new LinkedList<>();
                l.addAll(l1);l.addAll(l2);
                l.remove("");
                ret_graph.addInitalization(l);
            }
        }
        for (PGTransition<L1,A> pga: pg1.getTransitions())
            for (L2 loc2:pg2.getLocations()){
                Pair<L1,L2> to=new Pair<>(pga.getTo(),loc2);
                Pair<L1,L2> from=new Pair<>(pga.getFrom(),loc2);
                A action=pga.getAction();
                String cond=pga.getCondition();
                PGTransition pgt_n=new PGTransition(from,cond,action,to);
                ret_graph.addTransition(pgt_n);
            }
        for (PGTransition<L2, A> pgb : pg2.getTransitions())
            for (L1 loc1 : pg1.getLocations()) {
                Pair<L1, L2> from = new Pair<>(loc1, pgb.getFrom());
                Pair<L1, L2> to = new Pair<>(loc1, pgb.getTo());
                A action = pgb.getAction();
                String cond = pgb.getCondition();
                PGTransition pgt_e = new PGTransition(from, cond, action, to);
                ret_graph.addTransition(pgt_e);
            }
        for (Pair<L1, L2> loc : ret_graph.getLocations())
            if (pg1.getInitialLocations().contains(loc.first) && pg2.getInitialLocations().contains(loc.second))
                ret_graph.setInitial(loc, true);
        return ret_graph;
    }


    private List<Map<String,Boolean>> get_all_combos( int index_in_list, Map<String,Boolean> ret_map,List<String> list){
        Map<String,Boolean>[] arr_ofmaps=new Map[2];
        List<Map<String,Boolean>> ret=new LinkedList<>();
        arr_ofmaps[0]=new HashMap<>(ret_map);
        arr_ofmaps[1]=new HashMap<>(ret_map);
        arr_ofmaps[0].put(list.get(index_in_list),false);
        arr_ofmaps[1].put(list.get(index_in_list),true);
        ret.addAll(get_all_combos(index_in_list+1,arr_ofmaps[0],list));
        ret.addAll(get_all_combos(index_in_list+1,arr_ofmaps[1],list));
        return ret;
    }
    private List<String> get_true(Map<String,Boolean> map){
        List<String> ret= new LinkedList<>();
        for (String s: map.keySet()){
            if(map.get(s)) ret.add(s);
        }
        return ret;
    }

    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object>
        transitionSystemFromCircuit(Circuit c) {
        List<String> tags=new LinkedList<>(); //all tags
        tags.addAll(c.getRegisterNames());
        tags.addAll(c.getInputPortNames());
        tags.addAll(c.getOutputPortNames());
        //collected all tags
       TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ret_ts=new TransitionSystem<>();
       for (String s: tags) ret_ts.addAtomicProposition(s); //added all tags
       List<Map<String,Boolean>> list_regs_combo=get_all_combos(0,new HashMap<String, Boolean>(),new LinkedList<String>(c.getRegisterNames()));
        List<Map<String,Boolean>> list_input_combos=get_all_combos(0,new HashMap<String, Boolean>(),new LinkedList<String>(c.getInputPortNames()));
        //created all possible combo's for states
        for (Map<String, Boolean> reg: list_regs_combo ){
            for (Map<String,Boolean> a:list_input_combos){
                Pair<Map<String, Boolean>, Map<String, Boolean>> p=new Pair<>(reg,a); //matched combo's
                ret_ts.addState(p); //added
                boolean isinitial=true;
                for (String r:reg.keySet()) if (reg.get(r)) isinitial=false; //all regs start with false
                if (isinitial) ret_ts.addInitialState(p); //if all is false- set as initial state
            }
        }
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state: ret_ts.getStates()){
            for (Map<String,Boolean> a:list_input_combos){
                //going over all the states with every possible input
                Map<String,Boolean> ret_c=c.updateRegisters(a,state.first); //getting new regs
                Map<String,Boolean> out_c=c.computeOutputs(a,ret_c); //getting new output
                TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>,Map<String, Boolean>> tsTransition; //declare
                Pair<Map<String, Boolean>, Map<String, Boolean>> post_state=new Pair<>(ret_c,a); //new state
                tsTransition=new TSTransition<>(state,a,post_state); //creating
                ret_ts.addTransition(tsTransition); //adding transion
                List<String> state_pros=new LinkedList<>(); //for this state tags
                state_pros.addAll(get_true(out_c));state_pros.addAll(get_true(ret_c));state_pros.addAll(get_true(a)); //finding tags
                for (String s:state_pros) ret_ts.addToLabel(state,s); //adding tags
            }
        }
       //TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>,Map<String, Boolean>> tsTransition =new TSTransition();

       return ret_ts;
    }

    private Map<String,Object> get_values(List<String> list){
        Map<String,Object> ret=new HashMap<>();int begin=0;
        for (String s: list){
            if(s.contains(":=")){
                begin=s.indexOf(":=");
                String var=s.substring(0,begin);
                String val=s.substring(begin+2);
                Integer v=new Integer(val);
                ret.put(var,v);
            }
            else{
                    if(s.contains("?")) begin=s.indexOf("?");
                    else if(s.contains("!")) begin=s.indexOf("!");
                    String var=s.substring(0,begin);
                    String val=s.substring(begin+2);
                    Integer v=new Integer(val);
                    ret.put(var,v);
            }
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
        TransitionSystem<Pair<L, Map<String, Object>>,A,String> ret_ts=new TransitionSystem<>();
        Set<Pair<L, Map<String, Object>>> init_states=new HashSet<>();
        for (L s: pg.getInitialLocations()){
            if(pg.getInitalizations().size()>0){
                for (List<String> list_s:pg.getInitalizations()){
                    Map<String, Object> evaluated=new HashMap<>();
                    evaluated=get_values(list_s);
                    Pair<L, Map<String, Object>> p_s=new Pair<L, Map<String, Object>>(s,evaluated);
                    ret_ts.addInitialState(p_s);
                    ret_ts.addToLabel(p_s,p_s.second.toString());
                    init_states.add(p_s);
                }
            }else{
                Map<String, Object> evaluated=new HashMap<>();
                Pair<L, Map<String, Object>> p_s=new Pair<L, Map<String, Object>>(s,evaluated);
                ret_ts.addState(p_s);
                ret_ts.addInitialState(p_s);
                ret_ts.addAtomicProposition(p_s.first.toString());
                ret_ts.addToLabel(p_s,p_s.first.toString());
                init_states.add(p_s);
            }
        }
            List<PGTransition<L, A>> curr_trans=new LinkedList<>(pg.getTransitions());
            Set<Pair<L, Map<String, Object>>> send_set=new HashSet<>(init_states);
            Set<Pair<L, Map<String, Object>>> got_set=new HashSet<>(init_states);
        Pair<Set<Pair<L, Map<String, Object>>>,List<PGTransition<L, A>>> pair=new Pair<>(send_set,curr_trans);
            do {
                send_set=got_set;
                pair=get_new_states(ret_ts,pg,actionDefs,conditionDefs,send_set,curr_trans);
                got_set=pair.first;
                curr_trans.removeAll(pair.second);
            }while(got_set.size()>0);

        return ret_ts;
    }

    private<L,A> List<PGTransition<L, A>> get_trans(L tofind,List<PGTransition<L, A>> trans){
        List<PGTransition<L, A>> ret=new LinkedList<>();
        for (PGTransition<L, A> t:trans) {
            if(t.getFrom().equals(tofind)) ret.add(t);
        }
        return ret;
    }
    private <L,A> void add_atomic(Pair<L, Map<String, Object>> new_loc,Map<String, Object> new_eval, TransitionSystem<Pair<L, Map<String, Object>>, A, String> ret_ts){
        if(new_eval.size()>0){
            for (String s:new_eval.keySet()){
                String toadd=s+" = "+new_eval.get(s).toString();
                ret_ts.addAtomicProposition(toadd);
                ret_ts.addToLabel(new_loc,toadd);
            }
        }
    }
    /**
     * Creates a {@link TransitionSystem} from a program graph.
     * @param <L> Type of program graph locations.
     * @param <A> Type of program graph actions.
     * @param pg The program graph to be translated into a transition system.
     * @param actionDefs Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program graph.
     * @return A transition system representing {@code pg}.
     */
    private<L,A> Pair<Set<Pair<L, Map<String, Object>>>,List<PGTransition<L, A>>> get_new_states( TransitionSystem<Pair<L, Map<String, Object>>, A, String> ret_ts,ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs, Set<Pair<L, Map<String, Object>>> init_states,List<PGTransition<L, A>> curr_trans){
        Set<Pair<L, Map<String, Object>>> ret_set=new HashSet<>();
        List<PGTransition<L, A>> valid_trans,ret_trans=new LinkedList<>();
        for(Pair<L, Map<String, Object>> p_init :init_states){
            valid_trans=get_trans(p_init.first,curr_trans);
            for (PGTransition<L, A> p:valid_trans){
                if (p.getFrom().equals(p_init.first)){
                    if(ConditionDef.evaluate(conditionDefs,p_init.second,p.getCondition())){
                        ret_trans.add(p);
                        Map<String, Object> new_eval=ActionDef.effect(actionDefs,p_init.second,p.getAction());
                        if(new_eval!=null){
                            Pair<L, Map<String, Object>> new_loc=new Pair<>(p.getTo(),new_eval);
                            TSTransition<Pair<L, Map<String, Object>>,A> new_tst=new TSTransition<>(p_init,p.getAction(),new_loc);
                            ret_ts.addTransition(new_tst);
                            //ret_ts.addToLabel(new_loc,p_init.toString());
                            ret_set.add(new_loc);
                            if(new_loc.second!=null){
                                ret_ts.addAtomicProposition(new_loc.second.toString());
                                ret_ts.addToLabel(new_loc,new_loc.second.toString());
                            }
                            if(new_eval!=null)add_atomic(new_loc,new_eval,ret_ts);
                        }
                    }
                }
            }
        }
        return new Pair<>(ret_set,ret_trans);
    }
    private <L,A> ProgramGraph<List<L>, A> get_list_pg_from_one_pg(ProgramGraph<L, A> pg_p){

        ProgramGraph<List<L>, A> ret=new ProgramGraph<>();
        for(List<String> initalization:pg_p.getInitalizations()) ret.addInitalization(initalization);
        for (L p:pg_p.getLocations()){
            List<L> list=new LinkedList<>();
            list.add(p);
            ret.addLocation(list);
            if(pg_p.getInitialLocations().contains(p)) ret.setInitial(list,true);

        }
        for(PGTransition<L,A> t:pg_p.getTransitions()){
            List<L> list_from=new LinkedList<>();
            L p=t.getFrom();
            list_from.add(p);
            List<L> list_to=new LinkedList<>();
            p=t.getFrom();
            list_to.add(p);
            PGTransition<List<L>,A> new_t=new PGTransition<>(list_from,t.getCondition(),t.getAction(),list_to);
            ret.addTransition(new_t);
        }

        return ret;
    }
    private <L,A> ProgramGraph<List<L>, A> get_list_pg_from_pair(ProgramGraph<Pair<L, L>, A> pg_p){

        ProgramGraph<List<L>, A> ret=new ProgramGraph<>();
        for(List<String> initalization:pg_p.getInitalizations()) ret.addInitalization(initalization);
        for (Pair<L,L> p:pg_p.getLocations()){
            List<L> list=new LinkedList<>();
            list.add(p.first);list.add(p.second);
            ret.addLocation(list);
            if(pg_p.getInitialLocations().contains(p)) ret.setInitial(list,true);

        }
        for(PGTransition<Pair<L,L>,A> t:pg_p.getTransitions()){
            List<L> list_from=new LinkedList<>();
            Pair<L,L> p=t.getFrom();
            list_from.add(p.first);list_from.add(p.second);
            List<L> list_to=new LinkedList<>();
            p=t.getFrom();
            list_to.add(p.first);list_to.add(p.second);
            PGTransition<List<L>,A> new_t=new PGTransition<>(list_from,t.getCondition(),t.getAction(),list_to);
            ret.addTransition(new_t);
        }

        return ret;
    }
    private <L,A> ProgramGraph<List<L>, A> get_list_pg_from_pair_with_first_list(ProgramGraph<Pair<List<L>, L>, A> pg_p){

        ProgramGraph<List<L>, A> ret=new ProgramGraph<>();
        for(List<String> initalization:pg_p.getInitalizations()) ret.addInitalization(initalization);
        for (Pair<List<L>,L> p:pg_p.getLocations()){
            List<L> list=new LinkedList<>();
            list.addAll(p.first);list.add(p.second);
            ret.addLocation(list);
            if(pg_p.getInitialLocations().contains(p)) ret.setInitial(list,true);

        }
        for(PGTransition<Pair<List<L>,L>,A> t:pg_p.getTransitions()){
            List<L> list_from=new LinkedList<>();
            Pair<List<L>,L> p=t.getFrom();
            list_from.addAll(p.first);list_from.add(p.second);
            List<L> list_to=new LinkedList<>();
            p=t.getFrom();
            list_to.addAll(p.first);list_to.add(p.second);
            PGTransition<List<L>,A> new_t=new PGTransition<>(list_from,t.getCondition(),t.getAction(),list_to);
            ret.addTransition(new_t);
        }

        return ret;
    }
    private<L,A> ProgramGraph<List<L>, A> get_pg_from_cs(ChannelSystem<L, A> cs){
        ProgramGraph<List<L>, A> ret=new ProgramGraph<>();
        List<ProgramGraph<L, A>> programGraphs=cs.getProgramGraphs();
        if(programGraphs.size()>=2){
            ProgramGraph<Pair<L, L>, A> fist_pg=interleave(programGraphs.get(0),programGraphs.get(1));
            ret=get_list_pg_from_pair(fist_pg);
            for (int i=2;i<programGraphs.size();i++){
                ProgramGraph<Pair<List<L>, L>, A> new_pg=interleave(ret,programGraphs.get(i));
                ret=get_list_pg_from_pair_with_first_list(new_pg);
            }
        }
        else ret= get_list_pg_from_one_pg(programGraphs.get(0));
        return ret;
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
            ChannelSystem<L, A> cs ) {

        Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
        Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
        return transitionSystemFromChannelSystem(cs, actions, conditions);
    }

    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ret_ts;
        ret_ts=transitionSystemFromProgramGraph(get_pg_from_cs(cs),actions,conditions);
        return ret_ts;
    }


    private List<PGTransition> sub(StmtContext stmtContext) throws Exception {
        ParserRuleContext context;
        List<PGTransition> pgTransitions = null;
        if ((context = stmtContext.dostmt()) != null)
            pgTransitions = subDo(context);
        else if ((context = stmtContext.ifstmt()) != null)
            pgTransitions = subIf(context);
        else if ((context = stmtContext.assstmt()) != null)
            pgTransitions = subAss(context);
        else if ((context = stmtContext.atomicstmt()) != null)
            pgTransitions = subAtomic(context);
        else if ((context = stmtContext.skipstmt()) != null)
            pgTransitions = subSkip(context);
        else if ((context = stmtContext.chanreadstmt()) != null)
            pgTransitions = subAss(context);
        else if ((context = stmtContext.chanwritestmt()) != null)
            pgTransitions = subAss(context);
        else if (stmtContext.stmt() != null)
            pgTransitions = subStmt(stmtContext.stmt());
        else
            throw new  Exception("Code is invalid");
        return pgTransitions;
    }

    private List<PGTransition> subDo(ParserRuleContext context) throws Exception {
        context = (NanoPromelaParser.DostmtContext) context;
        List<PGTransition> ret_set = new LinkedList<>();
        String from = context.getText();
        List<String> conds = new LinkedList<>();
        for (OptionContext option : ((NanoPromelaParser.DostmtContext) context).option()){
            List<PGTransition> stmt_tag = sub(option.stmt());
            conds.add(option.boolexpr().getText());
            for (PGTransition transition : stmt_tag){
                if (transition.getFrom().equals(option.stmt().getText())){
                    if (transition.getTo().equals(exit_stmt))
                        ret_set.add(new PGTransition(from, getCond(option, transition), transition.getAction(), from));
                    else
                        ret_set.add(new PGTransition(from, getCond(option, transition), transition.getAction(), transition.getTo()+";"+from));
                }
                else {
                    String from1 = transition.getFrom().toString().isEmpty() ? "" : transition.getFrom().toString() + ";";
                    String to1 = transition.getTo().toString().isEmpty() ? "" : transition.getTo().toString() + ";";
                    ret_set.add(new PGTransition(from1 + from, transition.getCondition(),
                            transition.getAction(), to1 + from));
//                    ret_set.add(transition);
                }
            }
        }
        StringBuilder out_conds = new StringBuilder();
        for (int i = 0; i < conds.size() - 1; i++)
            out_conds.append("!(").append(conds.get(i)).append(") && ");
        out_conds.append("!(").append(conds.get(conds.size()-1)).append(")");
        ret_set.add(new PGTransition(from, out_conds.toString(), nothing_stmt, exit_stmt));
        return ret_set;
    }

    private List<PGTransition> subAss(ParserRuleContext context) {
        return getPgTransitions(context);
    }

    private List<PGTransition> getPgTransitions(ParserRuleContext context) {
        List<PGTransition> ret_set = new LinkedList<>();
        PGTransition pgTransition = new PGTransition(context.getText(), true_stmt, context.getText(), exit_stmt);
        ret_set.add(pgTransition);
        return ret_set;
    }

    private List<PGTransition> subAtomic(ParserRuleContext context) {
        context = (NanoPromelaParser.AtomicstmtContext) context;
        return getPgTransitions(context);
    }

    private List<PGTransition> subSkip(ParserRuleContext context) {
        context = (NanoPromelaParser.SkipstmtContext) context;
        List<PGTransition> ret_set = new LinkedList<>();
        PGTransition pgTransition = new PGTransition("skip", true_stmt, "skip", exit_stmt);
        ret_set.add(pgTransition);
        return ret_set;
    }

    private List<PGTransition> subIf(ParserRuleContext context) throws Exception {
        context = ((NanoPromelaParser.IfstmtContext) context);
        List<PGTransition> ret_set = new LinkedList<>();
        String from = context.getText();
        for (OptionContext option : ((NanoPromelaParser.IfstmtContext) context).option()) {
            List<PGTransition> stmt_tag = sub(option.stmt());
            for (PGTransition transition : stmt_tag) {
                if (transition.getFrom().equals(option.stmt().getText())) {
                    String cond = getCond(option, transition);
                    PGTransition pgTransition = new PGTransition(from, cond, transition.getAction(), transition.getTo());
                    ret_set.add(pgTransition);
                    if (transition.getFrom().toString().indexOf("do") == 0)
                        ret_set.add(transition);
                } else
                    ret_set.add(transition);
            }
        }
        return ret_set;
    }

    private String getCond(OptionContext option, PGTransition stmt_tag) {
        String h = true_stmt;
        if (option.boolexpr().getText().equals(true_stmt)) h = "(true)";
        else if (!(option.boolexpr().getText().equals("true"))) h = "(" + option.boolexpr().getText() + ")";
        String cond;
        if (stmt_tag.getCondition().equals(true_stmt)) cond = h;
        else
            if (h.equals(""))
                cond = stmt_tag.getCondition();
            else
                cond = "("+h + " && " + stmt_tag.getCondition()+")";
        return cond;
    }

    private List<PGTransition> subStmt(List<StmtContext> stmt) throws Exception {
        List<PGTransition> ret_set = new LinkedList<>();
        List<PGTransition> stmt1 = sub(stmt.get(0));
        for (PGTransition transition : stmt1) {
            String from = transition.getFrom() + ";" + stmt.get(1).getText();
            if (transition.getTo().equals(exit_stmt)) {
                PGTransition to_add = new PGTransition(from, transition.getCondition(), transition.getAction(), stmt.get(1).getText());
                ret_set.add(to_add);
            } else {
                    PGTransition to_add = new PGTransition(from, transition.getCondition(), transition.getAction(), transition.getTo()+";"+stmt.get(1).getText());
                    ret_set.add(to_add);
            }
        }

        ret_set.addAll(sub(stmt.get(1)));

        return ret_set;
    }


    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        StmtContext stmtContext = NanoPromelaFileReader.pareseNanoPromelaFile(filename);
        List<PGTransition> transitions = sub(stmtContext);
        return makeGraph(stmtContext, transitions);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        StmtContext stmtContext = NanoPromelaFileReader.pareseNanoPromelaString(nanopromela);
        List<PGTransition> transitions = sub(stmtContext);
        return makeGraph(stmtContext, transitions);
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        StmtContext stmtContext = NanoPromelaFileReader.parseNanoPromelaStream(inputStream);
        List<PGTransition> transitions = sub(stmtContext);
        return makeGraph(stmtContext, transitions);
    }

    private ProgramGraph<String, String> makeGraph(StmtContext stmtContext, List<PGTransition> transitions) {
        ProgramGraph<String, String> ret_graph = createProgramGraph();
        for (PGTransition transition: transitions) {
            if (transition.getFrom().equals(stmtContext.getText()))
                ret_graph.setInitial((String)transition.getFrom(), true);
            ret_graph.addTransition(transition);
        }
        return ret_graph;
    }

    // UTNTUIL HERERERE

//    private <Saut, P> Set<Saut> automataStates(Automaton<Saut, P> aut){
//        Set<Saut> ret_set = new HashSet<>();
//        Map<Saut, Map<Set<P>, Set<Saut>>> transition = aut.getTransitions();
//        for (Saut currState : transition.keySet()){
//            ret_set.add(currState);
//            ret_set.add(transition.ge)
//        }
//    }

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

        TransitionSystem<Pair<Sts,Saut>,A,Saut> TSXA = new TransitionSystem();

        // Transitions
        Set<TSTransition<Pair<Sts,Saut>, A>> transitions = getTRANSX(ts,aut);
        for (TSTransition<Pair<Sts,Saut>, A> trans : transitions)
            TSXA.addTransition(trans);

        // Initials
        Set<Pair<Sts,Saut>> IX = getIX(ts, aut);
        for (Pair<Sts,Saut> I : IX)
            TSXA.addInitialState(I);

        // Labels
        for (Pair<Sts,Saut> Stsxa : TSXA.getStates())
            TSXA.addToLabel(Stsxa, Stsxa.second);

        return TSXA;
    }

    private <A, Saut, Sts, P> Set<TSTransition<Pair<Sts,Saut>,A>> getTRANSX(TransitionSystem<Sts,A,P> ts, Automaton<Saut,P> aut) {
        Set<TSTransition<Pair<Sts,Saut>,A>> TSXATrans = new HashSet<>();
        Set<TSTransition<Sts, A>> tsTrans = ts.getTransitions();
        Map<Saut, Map<Set<P>, Set<Saut>>> autTrans = aut.getTransitions();
        for (TSTransition<Sts, A> TStransition : tsTrans)
            for (Saut q : autTrans.keySet()){
                Set<Saut> Ps = autTrans.get(q).get(ts.getLabel(TStransition.getTo()));
                for (Saut p : Ps){
                    TSTransition<Pair<Sts,Saut>,A> toAdd = new TSTransition<>(
                            new Pair<>(TStransition.getFrom(), q),
                            TStransition.getAction(),
                            new Pair<>(TStransition.getTo(), p)
                    );
                    TSXATrans.add(toAdd);
                }
            }
        return TSXATrans;
    }

    private <A, Saut, Sts, P> Set<Pair<Sts,Saut>> getIX(TransitionSystem<Sts,A,P> ts, Automaton<Saut,P> aut) {
        Set<Pair<Sts,Saut>> IXs = new HashSet<>();
        for (Sts s0 : ts.getInitialStates())
            for (Saut q0 : aut.getInitialStates()){
                Set<Saut> nexts = aut.nextStates(q0, ts.getLabel(s0));
                for (Saut q : nexts)
                    IXs.add(new Pair<>(s0, q));
            }
        return IXs;
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
        TransitionSystem<Pair<S, Saut>, A, Saut> ProdTransitionSystem = product(ts, aut);
        Set<Pair<S, Saut>> reachableStates = reach(ProdTransitionSystem);
        Set<Pair<S, Saut>> badStates = new HashSet<>();
        for (Pair<S, Saut> Stsxa : reachableStates)
            if (aut.getAcceptingStates().contains(ProdTransitionSystem.getLabel(Stsxa)))
                badStates.add(Stsxa);

        if (badStates.size() == 0) return new VerificationSucceeded<>();

//        All Routes

        Map<Pair<S, Saut>, List> routes = getPairListMap(ProdTransitionSystem);

//        Cycles
        Map<Pair<S, Saut>, List> cycles = getPairListMap(ProdTransitionSystem, badStates);

        for (Pair<S, Saut> bad : cycles.keySet()){
            VerificationFailed VF = new VerificationFailed();
            VF.setCycle(cycles.get(bad));
            VF.setPrefix(routes.get(bad));
            return VF;
        }

        return new VerificationSucceeded<>();
    }

    private <S, A, Saut> Map<Pair<S, Saut>, List> getPairListMap(TransitionSystem<Pair<S, Saut>, A, Saut> prodTransitionSystem, Set<Pair<S, Saut>> badStates) {
        Map<Pair<S, Saut>, List> cycles = new HashMap<>();
        for (Pair<S, Saut> bad : badStates) {
            ArrayDeque<Pair<S, Saut>> startCycles = new ArrayDeque<>();
            startCycles.add(bad);

            Map<Pair<S, Saut>, List> badRoutes = new HashMap<>();
            List<Pair<S, Saut>> start = new LinkedList<>();
            start.add(bad);
            badRoutes.put(bad, start);
            boolean finished = false;

            while (!startCycles.isEmpty() && !finished) {
                Pair<S, Saut> curr = startCycles.pop();
                for (Pair<S, Saut> next : post(prodTransitionSystem, curr)){
                    if (!bad.equals(next) && badRoutes.containsKey(next)) continue;
                    List route = List.copyOf(badRoutes.get(curr));
                    route.add(next);
                    if (next.equals(bad)) {
                        cycles.put(bad, route);
                        finished = true;
                    }
                    else {
                        badRoutes.put(next, route);
                        startCycles.add(next);
                    }
                }
            }
        }
        return cycles;
    }

    private <S, A, Saut> Map<Pair<S, Saut>, List> getPairListMap(TransitionSystem<Pair<S, Saut>, A, Saut> prodTransitionSystem) {
        Map<Pair<S, Saut>, List> routes = new HashMap<>();
        ArrayDeque<Pair<S, Saut>> currStates = new ArrayDeque<>(prodTransitionSystem.getInitialStates());
        for (Pair<S, Saut> init : prodTransitionSystem.getInitialStates()) {
            List<Pair<S, Saut>> route = new LinkedList<>();
            route.add(init);
            routes.put(init, route);
        }

        while (! currStates.isEmpty()){
            Pair<S, Saut> curr = currStates.pop();
            for (Pair<S, Saut> next : post(prodTransitionSystem, curr)) {
                if (routes.containsKey(next)) continue;
                List route = List.copyOf(routes.get(curr));
                route.add(next);
                routes.put(next, route);
                currStates.add(next);

            }
        }
        return routes;
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param //ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Set<Set<LTL<L>>> get_power(Set<LTL<L>> subs){
        Set<Set<LTL<L>>> ret=new HashSet<>();
        //Todo
        return ret;
    }

    public <L> Set<Set<LTL<L>>> get_power_Set(Set<LTL<L>> given_set){
        Set<Set<LTL<L>>> retSet = new HashSet<>();
        if (given_set.isEmpty())
            retSet.add(given_set);
        else {
            for (LTL<L> element : given_set){
                given_set.remove(element);
                Set<Set<LTL<L>>> without = new HashSet<>(get_power_Set(given_set));
                for (Set<LTL<L>> notWith:without)
                    retSet.add(notWith);
                Set<Set<LTL<L>>> with = new HashSet<>();
                for (Set<LTL<L>> obj : without)
                    with.add(obj);
                for (Set<LTL<L>> inWith : with) {
                    Set<LTL<L>> toAdd = new HashSet<>(((Set) inWith));
                    toAdd.add(element);
                    retSet.add(toAdd);
                }
                break;
            }
        }
        return retSet;
    }

    public <L> boolean is_valid_B(Set<LTL<L>> b,Set<LTL<L>> clousre){
        Set<LTL<L>> notin_B=new HashSet<>();
        //if(!b.contains(LTL.true_())) return false;
        for (LTL<L> lltl:clousre){
            if(!b.contains(lltl)){
                notin_B.add(lltl);
                if(!b.contains(get_Not(lltl))) return false;
                //if(!(b.contains(get_Not(lltl)))) return false;
            }
            if(b.contains(lltl)&&b.contains(get_Not(lltl))) return false;
            if(lltl instanceof Until) {
                LTL<L> righti = ((Until<L>) lltl).getRight();
                if(b.contains(righti)) if(!b.contains(lltl)) return false;
                LTL<L> lefti=((Until<L>) lltl).getLeft();
                if((!((b.contains(lefti))||(b.contains(righti))))&&(b.contains(lltl))) return false;
            }
            if(lltl instanceof And)
            {
                if(b.contains(lltl)){
                    if((!b.contains(((And<L>) lltl).getRight()))||(!b.contains(((And<L>) lltl).getLeft()))) return false;
                }
                else {
                    if(b.contains(((And<L>) lltl).getLeft())&&b.contains(((And<L>) lltl).getRight())) return false;
                }
            }
        }
        return true;
    }
    public <L> boolean is_transtion(Set<LTL<L>> from_B,Set<LTL<L>> too_B_tag,Set<LTL<L>> A,Set<LTL<L>> subs){
        for(LTL<L> ltl_next:from_B){
            if(ltl_next instanceof Next) if(!too_B_tag.contains(((Next<L>) ltl_next).getInner())) return false;
            if(ltl_next instanceof AP) if(!A.contains(ltl_next)) return false;
        }
        for(LTL<L> a:A){ if(!from_B.contains(a)) return false; }

        for(LTL<L> ltl_too:too_B_tag){
             if(!from_B.contains(new Next<>(ltl_too))) return false; }
        for (LTL<L> ltl_from_sub:subs){
            if (ltl_from_sub instanceof Until){
                LTL<L> left2=((Until<L>) ltl_from_sub).getLeft();
                LTL<L> right1=((Until<L>) ltl_from_sub).getRight();
                if (from_B.contains(ltl_from_sub)&&(!(from_B.contains(left2)))) {
                    if(!(too_B_tag.contains(ltl_from_sub))) return false;
                }
                if ((!(from_B.contains(ltl_from_sub)))&&(from_B.contains(right1))) {
                    if(too_B_tag.contains(ltl_from_sub)) return false;
                }
            }
        }
        return true;
    }
    public <L>  Set<Pair<Set<Set<LTL<L>>>,Integer>> get_final_states(Set<LTL<L>> subs,Set<Set<LTL<L>>> B_members){
        Set<LTL<L>>until_sub=new HashSet<>();
        for(LTL<L> ltl:subs) if(subs instanceof Until) until_sub.add(ltl);
        Set<Pair<Set<Set<LTL<L>>>,Integer>> ret=new HashSet<>();
        int counter=1;
        for(Set<LTL<L>> mightB:B_members){
            Set<Set<LTL<L>>> temp=new HashSet<>();
            boolean is_good=true;
            for (LTL<L> until:until_sub){
                LTL<L> left2=((Until<L>) until).getLeft();
                if((!(B_members.contains(until_sub)))||(B_members.contains(left2))) is_good=false;
            }

            if (is_good){
                Set<Set<LTL<L>>>temp_set=new HashSet<>();
                temp_set.add(mightB);
                Pair<Set<Set<LTL<L>>>,Integer> to_add=new Pair<>(temp_set,new Integer(counter));
                counter++;
                ret.add(to_add);
            }
        }
        return ret;
    }
    public <L> Set<L> get_real_A(Set<LTL<L>> A_of_b){
        Set<L> ret=new HashSet<>();
        for (LTL<L> ltl:A_of_b) {if(ltl instanceof AP) ret.add(((AP<L>) ltl).getName());}
        return ret;
    }
    public <L> Set<LTL<L>> get_aa(Set<LTL<L>> b){
        Set<LTL<L>> ret=new HashSet<>();
        for (LTL<L> l:b) if(l instanceof AP) ret.add((AP<L>) l);
        return ret;
    }
    public <L> LTL<L>  get_Not(LTL<L> ltl){
        LTL<L> ret;
        if(ltl instanceof Not){ ret=((Not<L>) ltl).getInner(); }
        else{ ret=new Not<>(ltl); }
        return ret;
    }
    public <L> Set<LTL<L>> get_clousre(LTL<L> ltl) {
        Set<LTL<L>> ret=new HashSet<>();
        ret.add(ltl); //adding the ltl itself
        if(ltl instanceof TRUE){ret.add(get_Not(ltl)); }
        else{
            if(ltl instanceof Not){ ret.add(((Not<L>) ltl).getInner()); }
            else{
                if(ltl instanceof Next){
                    ret.add(get_Not(ltl));
                    ret.addAll(get_clousre(((Next<L>) ltl).getInner()));
                }
                else{
                    if(ltl instanceof And){
                        ret.add(get_Not(ltl));
                        ret.addAll(get_clousre(((And<L>) ltl).getRight()));
                        ret.addAll(get_clousre(((And<L>) ltl).getLeft()));
                    }
                    else{
                        if(ltl instanceof Until){
                            ret.add(get_Not(ltl));
                            ret.addAll(get_clousre(((Until<L>) ltl).getRight()));
                            ret.addAll(get_clousre(((Until<L>) ltl).getLeft()));
                        }
                    }
                }
            }
        }
        return ret;
    }

    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        Automaton<?, L> ret=new Automaton<>();
        MultiColorAutomaton<Set<LTL<L>>,L> gnba=new MultiColorAutomaton<>();
        Set<LTL<L>> subs_ltl=get_clousre(ltl);
        Set<Set<LTL<L>>> power_members=get_power_Set(get_clousre(ltl));
        Set<Set<LTL<L>>> B_members=new HashSet<>();
        for(Set<LTL<L>> b:power_members) if(is_valid_B(b,subs_ltl)) B_members.add(b);
        Set<Set<LTL<L>>> inital_states=new HashSet<>();
        for(Set<LTL<L>> b:B_members){
            if(b.contains(ltl)){
                inital_states.add(b);
                gnba.setInitial(b);
            }
            Set<LTL<L>> A_of_b=get_aa(b);
            Set<L> real_A=get_real_A(A_of_b);
            Set<Set<LTL<L>>> tempb=new HashSet<>(B_members);
            tempb.remove(b);
            for (Set<LTL<L>> b_tag:tempb){
                if(is_transtion(b,b_tag,A_of_b,subs_ltl)){
                    gnba.addTransition(b,real_A,b_tag);
                }
            }
        }
        Set<Pair<Set<Set<LTL<L>>>,Integer>> final_states=get_final_states(subs_ltl,B_members);
        for (Pair<Set<Set<LTL<L>>>,Integer> funal_st:final_states) {
            for (Set<LTL<L>> funal_state:funal_st.first) {

                gnba.setAccepting(funal_state,funal_st.second.intValue());
            }
        }
        ret=GNBA2NBA(gnba);
        return ret;
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param //<L>    Type of resultant automaton transition alphabet
     * @param //mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public Integer get_min_from_set(Set<Integer> set_int){
        Integer ret=-1;
        for (Integer x:set_int){ if(ret<x) ret=x; }
        return ret;
    }
    public <State, L> boolean isaccepting(MultiColorAutomaton<State, L> mulAut,State state){
        boolean ret=false;
        Set<Integer> colors = mulAut.getColors();
        for (Integer layer:colors) if(mulAut.getAcceptingStates(layer).contains(state)) return true;
        return ret;
    }
    public <State, L> Set<Object> run_over_layer(Set<Object> init,Integer layer_num,MultiColorAutomaton<State, L> mulAut,Automaton<Object, L> ret_NBA,int first_level_num,int next_level_num,boolean is_final_level){
        Set<Pair<Object,Integer>> ran_over=new HashSet<>();
        Set<Object> ret=new HashSet<>();
        Queue<State> queue=new ArrayDeque<>();
        for (State initial_state:(Set<State>)init){ queue.add(initial_state); }
        Map<State, Map<Set<L>, Set<State>>> transitions=mulAut.getTransitions();
        while (!queue.isEmpty()) {
            State curr_state=queue.poll();
            if(!ran_over.contains(curr_state)) {
                Map<Set<L>, Set<State>> trans_of_state = transitions.get(curr_state);
                Set<Set<L>> keyes_of_state = trans_of_state.keySet();
                for (Set<L> tran : keyes_of_state) {
                    Set<State> states_of_tran = transitions.get(curr_state).get(tran);
                    for (State s : states_of_tran) {
                        Pair<Object,Integer> ps=new Pair<>(curr_state,layer_num);
                        Pair<Object,Integer> pd;
                        if (mulAut.getAcceptingStates(layer_num).contains(s)) {
                            int new_layer_num=0;
                            if(is_final_level) new_layer_num=first_level_num;
                            else new_layer_num=next_level_num;
                        pd=new Pair<>(s,new_layer_num);
                        }
                        else pd=new Pair<>(s,layer_num);
                        ret_NBA.addTransition(ps,tran,pd);
                        ran_over.add(pd);
                        //queue.add(s);
                        ret.add(s);
                    }
                }
            }
        }
        return  ret;
    }
    public Integer get_real_num(int num,int k){
        return new Integer((num%k)+1);
    }

    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        Automaton<Object, L> ret_NBA = new Automaton<>();
        int k = mulAut.getColors().size();
        Set<Integer> colors = mulAut.getColors();
        List<Integer> color_list=new LinkedList<>(colors);
        Collections.sort(color_list);
        int index=0;
        Integer inital_level_index=color_list.get(index);
        for (Object initial_state:mulAut.getInitialStates()){ ret_NBA.setInitial(new Pair<Object,Integer>(initial_state,get_real_num(index,k))); }
        for (Object final_state:mulAut.getAcceptingStates(inital_level_index)) {ret_NBA.setAccepting(new Pair<Object,Integer>(final_state,get_real_num(index,k)));}
        Set<Object> states= (Set<Object>) mulAut.getInitialStates();
        while (index<color_list.size()-1){
           states=run_over_layer(states,new Integer(index),mulAut,ret_NBA,inital_level_index,color_list.get(index),false);
           index++;
        }
        states=run_over_layer(states,new Integer(index),mulAut,ret_NBA,inital_level_index,inital_level_index,true);
        //run_over_layer(,new Integer(index),mulAut,ret_NBA,inital_level_index,color_list.get(inital_level_index),false);
        return ret_NBA;
//        throw new java.lang.UnsupportedOperationException();
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
        return null;
    }

    public static void main(String[] args) {
        Set<Integer> check = new HashSet<>();
        check.add(1);
        check.add(2);
        System.out.println();
    }

}
