package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ActionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
<<<<<<< HEAD
 * More about facade: {@linkplain //www.vincehuston.org/dp/facade.html}.
=======
>>>>>>> master
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;

    /**
     *
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
     * @param ts The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if(ts.getInitialStates().size()>1) return false; //|I|<=1
        else{
            Set<Pair<S,A>> pair_set= new HashSet<>();
            Set<TSTransition<S, A>> ts_transition= ts.getTransitions();
            for (TSTransition<S, A> t : ts_transition){
                Pair<S,A> p1=new Pair<>(t.getFrom(),t.getAction());
                if(pair_set.contains(p1)) return false; //means we saw before a
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
     * @param ts The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if(ts.getInitialStates().size()>1) return false; //|I|<=1
        else{
            Set<Pair<Pair<S,A>,Set<P>>> pair_set= new HashSet<>();
            Set<TSTransition<S, A>> ts_transition= ts.getTransitions();
            for (TSTransition<S, A> t : ts_transition){
                Pair<S,A> p1=new Pair<>(t.getFrom(),t.getAction());
                Pair<Pair<S,A>,Set<P>> p2=new Pair<>(p1,ts.getLabel(t.getTo()));
                if(pair_set.contains(p2)) return false;
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
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be an execution of {@code ts}.
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
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be an execution fragment of
     * {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        AlternatingSequence<S, A> curr = e;
        for (int i = 0; i < e.size(); i = i + 2) {
            S s1 = curr.head();
            A a = curr.tail().head();
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
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be an initial execution
     * fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecution(ts, e) && ts.getInitialStates().contains(e.head());
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts The transition system being tested.
     * @param e The sequence that may or may not be a maximal execution fragment
     * of {@code ts}.
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
     * @param ts Transition system of {@code s}.
     * @param s The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        for (TSTransition<S, A> transition : ts.getTransitions())
            if (transition.getFrom().equals(s))
                return false;
        return true;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that is reachable from s using transition 'trans'
        for (TSTransition<S, ?> trans:transitions)
            if(trans.getFrom().equals(s))
                retSet.add(trans.getTo());
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param c States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> retSet = new HashSet<>();
        // Got the post states for each state in c and added them in a set
        for(S s : c){
            Set<S> gotSet = post(ts, s);
            retSet.addAll(gotSet);
        }
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that is reachable from s using action a in transition 'trans'
        for (TSTransition<S, ?> trans:transitions)
            if(trans.getFrom().equals(s) && trans.getAction().equals(a))
                retSet.add(trans.getTo());
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param c Set of states in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> retSet = new HashSet<>();
        // Got the post states for each state in c  using action a and added them in a set
        for(S s : c){
            Set<S> gotSet = post(ts, s, a);
            retSet.addAll(gotSet);
        }
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that s is reachable from using transition 'trans'
        for (TSTransition<S, ?> trans:transitions)
            if(trans.getTo().equals(s))
                retSet.add(trans.getFrom());
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param ts Transition system of {@code s}.
     * @param c States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        Set<S> retSet = new HashSet<>();
        // Got the pre states for each state in c and added them in a set
        for(S s : c){
            Set<S> gotSet = pre(ts, s);
            retSet.addAll(gotSet);
        }
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param s A state in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        Set<S> retSet = new HashSet<>();
        Set<? extends TSTransition<S, ?>> transitions = ts.getTransitions();
        // Added every state that s is reachable from using action a and transition 'trans'
        for (TSTransition<S, ?> trans:transitions)
            if(trans.getTo().equals(s) && trans.getAction().equals(a))
                retSet.add(trans.getFrom());
        return retSet;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts Transition system of {@code s}.
     * @param c Set of states in {@code ts}.
     * @param a An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> retSet = new HashSet<>();
        // Got the pre states for each state in c using action a and added them in a set
        for(S s : c){
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
     * @param ts Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        // Start with initials, get their posts and so on until dead-end.
        Set<S> retSet = new HashSet<>();
        Set<S> curr = ts.getInitialStates();
        while(!curr.isEmpty()){
            Set<S> statsToContinue = new HashSet<>();
            for (S s : curr)
                if (!retSet.contains(s)){
                    retSet.add(s);
                    statsToContinue.add(s);
                }
            curr = post(ts, statsToContinue);
        }
        return retSet;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A> Type of actions (in both systems).
     * @param <P> Type of atomic propositions (in both systems).
     * @param ts1 The first transition system.
     * @param ts2 The second transition system.
     *
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<>());
    }

    private <S1, S2, A, P> Set<TSTransition<Pair<S1,S2>,A>> getTransInterleave(TransitionSystem<S1, A, P> ts1,
                                                                               TransitionSystem<S2, A, P> ts2,
                                                                               Set<Pair<S1, S2>> new_states, Set<A> handShakingActions) {
        Set<TSTransition<Pair<S1,S2>,A>> ret_set = new HashSet<>();
        for (TSTransition<S1, A> transition1 : ts1.getTransitions()){
            if (!(handShakingActions.contains(transition1.getAction())))
                for (Pair<S1, S2> state1 : new_states)
                    if (state1.first.equals(transition1.getFrom()))
                        ret_set.add(new TSTransition<>(state1, transition1.getAction(),
                                new Pair<>(transition1.getTo(),state1.second)));
            else
                for (Pair<S1, S2> state2 : new_states)
                    if (state2.first.equals(transition1.getFrom()))
                        for (TSTransition<S2, A> transition2 : ts2.getTransitions())
                            if (transition2.getFrom().equals(state2.second) &&
                                    transition2.getAction().equals(transition1.getAction()))
                                ret_set.add(new TSTransition<>(state1, transition1.getAction(),
                                        new Pair<>(transition1.getTo(),transition2.getTo())));
        }
        for (TSTransition<S2, A> transition2 : ts2.getTransitions())
            if (!(handShakingActions.contains(transition2.getAction())))
                for (Pair<S1, S2> state1 : new_states)
                    if (state1.second.equals(transition2.getFrom()))
                        ret_set.add(new TSTransition<>(state1, transition2.getAction(),
                                new Pair<>(state1.first, transition2.getTo())));
        return ret_set;
    }

    private <S1, S2, P, A> Set<Pair<S1,S2>> getStatesInterleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        Set<Pair<S1, S2>> ret_set = new HashSet<>();
        for (S1 s1 : ts1.getStates())
            for (S2 s2 : ts2.getStates())
                ret_set.add(new Pair<>(s1, s2));
        return ret_set;
    }

    private <A, S2, P, S1> TransitionSystem<Pair<S1,S2>,A,P> createTS(Set<Pair<S1, S2>> new_states, Set<Pair<S1, S2>> initials, Set<A> new_actions,
                                                                      Set<TSTransition<Pair<S1, S2>, A>> new_transitions, Set<P> new_APs,
                                                                      Map<Pair<S1, S2>, Set<P>> L_function) {
        TransitionSystem<Pair<S1, S2>, A, P> ret_ST = new TransitionSystem<>();
        for (Pair<S1, S2> state : new_states){
            if (initials.contains(state))
                ret_ST.addInitialState(state);
            else
                ret_ST.addState(state);
        }
        ret_ST.addAllActions(new_actions);
        for (TSTransition<Pair<S1,S2>,A> transition : new_transitions)
            ret_ST.addTransition(transition);
        ret_ST.addAllAtomicPropositions(new_APs);
        for (Pair<S1, S2> state : L_function.keySet())
            ret_ST.addToLabel(state, (P) L_function.get(state));

        return ret_ST;
    }

    private <S2, S1, A, P> Map<Pair<S1,S2>,Set<P>> getLFunction(
            TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<Pair<S1, S2>> new_states) {
        Map<Pair<S1, S2>, Set<P>> L_function = new HashMap<>();
        for (Pair<S1, S2> state : new_states){
            Set<P> curr_AP = new HashSet<>();
            curr_AP.addAll(ts1.getLabel(state.first));
            curr_AP.addAll(ts2.getLabel(state.second));
            L_function.put(state, curr_AP);
        }
        return L_function;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A> Type of actions (in both systems).
     * @param <P> Type of atomic propositions (in both systems).
     * @param ts1 The first transition system.
     * @param ts2 The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     *
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
            TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {

        //States
        Set<Pair<S1, S2>> new_states = getStatesInterleave(ts1, ts2);

        // Initials
        Set<Pair<S1, S2>> initials = new HashSet<>();
        for (Pair<S1, S2> pair : new_states)
            if (ts1.getInitialStates().contains(pair.first) && ts2.getInitialStates().contains(pair.second))
                initials.add(pair);

        // Transitions
        Set<TSTransition<Pair<S1,S2>,A>> new_transitions =
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

    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A> Type of actions in BOTH GRAPHS.
     * @param pg1 The first program graph.
     * @param pg2 The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1,L2>,A> ret_graph=createProgramGraph();
        Set<List<String>> in_ret=new HashSet<>();
        in_ret.addAll(pg1.getInitalizations());
        in_ret.addAll(pg2.getInitalizations());
        for (PGTransition<L1,A> pga: pg1.getTransitions())
            for (L2 loc2:pg2.getLocations()){
                Pair<L1,L2> to=new Pair<>(pga.getTo(),loc2);
                Pair<L1,L2> from=new Pair<>(pga.getFrom(),loc2);
                A action=pga.getAction();
                String cond=pga.getCondition();
                PGTransition pgt_n=new PGTransition(from,cond,action,to);
                ret_graph.addTransition(pgt_n);
            }
        for (PGTransition<L2,A> pgb: pg2.getTransitions())
            for (L1 loc1:pg1.getLocations()){
                Pair<L1,L2> from=new Pair<>(loc1,pgb.getFrom());
                Pair<L1,L2> to=new Pair<>(loc1,pgb.getTo());
                A action=pgb.getAction();
                String cond=pgb.getCondition();
                PGTransition pgt_e=new PGTransition(from,cond,action,to);
                ret_graph.addTransition(pgt_e);
            }
        for (Pair<L1,L2> loc: ret_graph.getLocations())
            if(pg1.getInitialLocations().contains(loc.first)&&pg2.getInitialLocations().contains(loc.second))
                ret_graph.setInitial(loc,true);
        return ret_graph;
    }

    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object>
        transitionSystemFromCircuit(Circuit c) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L> Type of program graph locations.
     * @param <A> Type of program graph actions.
     * @param pg The program graph to be translated into a transition system.
     * @param actionDefs Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     * graph.
     * @return A transition system representing {@code pg}.
     */
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(
            ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new java.lang.UnsupportedOperationException();
    }

    // UTNTUIL HERERERE

    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts> Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A> Type of actions in the transition system.
     * @param <P> Type of atomic propositions in the transition system, which is
     * also the type of the automaton alphabet.
     * @param ts The transition system.
     * @param aut The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
            Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S> Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A> Type of actions in the transition system.
     * @param <P> Type of atomic propositions in the transition system, which is
     * also the type of the automaton alphabet.
     * @param ts The transition system.
     * @param aut A Büchi automaton for the words that do not satisfy the
     * property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
            Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
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
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new java.lang.UnsupportedOperationException();
    }

}
