package il.ac.bgu.cs.formalmethodsintro.base.PG;

import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.*;
import static org.junit.Assert.assertEquals;


import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import org.junit.Test;

import java.util.Set;

public class ProgramGraphProductTest {

    FvmFacade fvmFacadeImpl = FvmFacade.get();

    @Test
    // See Figure 2.9 and Figure 2.10
    @SuppressWarnings({"unchecked", "rawtypes"})
    public void peterson() throws Exception {
        ProgramGraph pg1 = PetersonProgramGraphBuilder.build(1);
        ProgramGraph pg2 = PetersonProgramGraphBuilder.build(2);

        ProgramGraph pg = fvmFacadeImpl.interleave(pg1, pg2);

        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        assertEquals(set(p("noncrit1", "noncrit2"), p("wait1", "noncrit2"), p("noncrit1", "crit2"), p("crit1", "crit2"),
                p("wait1", "crit2"), p("crit1", "noncrit2"), p("crit1", "wait2"), p("wait1", "wait2"),
                p("noncrit1", "wait2")), pg.getLocations());

        assertEquals(set(p("noncrit1", "noncrit2")), pg.getInitialLocations());

        assertEquals(
                set(seq("b1:=0", "x:=2", "b2:=0", "x:=2"), seq("b1:=0", "x:=1", "b2:=0", "x:=1"),
                        seq("b1:=0", "x:=1", "b2:=0", "x:=2"), seq("b1:=0", "x:=2", "b2:=0", "x:=1")),
                pg.getInitalizations());

        assertEquals(
                set(pgtransition(p("crit1", "crit2"), "true", "b1:=0", p("noncrit1", "crit2")),
                        pgtransition(p("noncrit1", "noncrit2"), "true", "atomic{b2:=1;x:=1}", p("noncrit1", "wait2")),
                        pgtransition(p("crit1", "crit2"), "true", "b2:=0", p("crit1", "noncrit2")),
                        pgtransition(p("crit1", "noncrit2"), "true", "b1:=0", p("noncrit1", "noncrit2")),
                        pgtransition(p("crit1", "noncrit2"), "true", "atomic{b2:=1;x:=1}", p("crit1", "wait2")),
                        pgtransition(p("wait1", "wait2"), "x==2 || b1==0", "", p("wait1", "crit2")),
                        pgtransition(p("noncrit1", "crit2"), "true", "b2:=0", p("noncrit1", "noncrit2")),
                        pgtransition(p("crit1", "wait2"), "true", "b1:=0", p("noncrit1", "wait2")),
                        pgtransition(p("noncrit1", "noncrit2"), "true", "atomic{b1:=1;x:=2}", p("wait1", "noncrit2")),
                        pgtransition(p("wait1", "crit2"), "true", "b2:=0", p("wait1", "noncrit2")),
                        pgtransition(p("wait1", "noncrit2"), "true", "atomic{b2:=1;x:=1}", p("wait1", "wait2")),
                        pgtransition(p("noncrit1", "crit2"), "true", "atomic{b1:=1;x:=2}", p("wait1", "crit2")),
                        pgtransition(p("noncrit1", "wait2"), "x==2 || b1==0", "", p("noncrit1", "crit2")),
                        pgtransition(p("crit1", "wait2"), "x==2 || b1==0", "", p("crit1", "crit2")),
                        pgtransition(p("wait1", "noncrit2"), "x==1 || b2==0", "", p("crit1", "noncrit2")),
                        pgtransition(p("wait1", "crit2"), "x==1 || b2==0", "", p("crit1", "crit2")),
                        pgtransition(p("wait1", "wait2"), "x==1 || b2==0", "", p("crit1", "wait2")),
                        pgtransition(p("noncrit1", "wait2"), "true", "atomic{b1:=1;x:=2}", p("wait1", "wait2"))),
                pg.getTransitions());

        TransitionSystem ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

        assertEquals(set(p(p("wait1", "wait2"), map(p("x", 2), p("b2", 1), p("b1", 1))),
                p(p("noncrit1", "noncrit2"), map(p("x", 1), p("b2", 0), p("b1", 0))),
                p(p("noncrit1", "crit2"), map(p("x", 1), p("b2", 1), p("b1", 0))),
                p(p("crit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1))),
                p(p("wait1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1))),
                p(p("wait1", "crit2"), map(p("x", 2), p("b2", 1), p("b1", 1))),
                p(p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0))),
                p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1))),
                p(p("crit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1))),
                p(p("noncrit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 0)))), ts.getStates());
        assertEquals(set(p(p("noncrit1", "noncrit2"), map(p("x", 1), p("b2", 0), p("b1", 0))),
                p(p("noncrit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 0)))), ts.getInitialStates());
        assertEquals(set("", "atomic{b2:=1;x:=1}", "b2:=0", "b1:=0", "atomic{b1:=1;x:=2}"), ts.getActions());
        assertEquals(set("b1 = 0", "b1 = 1", "<noncrit1,crit2>", "x = 1", "x = 2", "<crit1,noncrit2>", "b2 = 1",
                "<crit1,wait2>", "<wait1,crit2>", "b2 = 0", "<noncrit1,wait2>", "<wait1,wait2>", "<wait1,noncrit2>",
                "<noncrit1,noncrit2>"), ts.getAtomicPropositions());
        assertEquals(
                set(transition(p(p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0))), "",
                        p(p("noncrit1", "crit2"), map(p("x", 1), p("b2", 1), p("b1", 0)))),
                        transition(
                                p(p("wait1", "wait2"), map(p("x", 2), p("b2", 1), p("b1", 1))), "",
                                p(p("wait1", "crit2"), map(p("x", 2), p("b2", 1), p("b1", 1)))),
                        transition(p(p("crit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1))), "b1:=0",
                                p(p("noncrit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 0)))),
                        transition(
                                p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1))), "atomic{b2:=1;x:=1}",
                                p(p("wait1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1)))),
                        transition(
                                p(p("noncrit1", "noncrit2"), map(p("x", 1), p("b2", 0), p("b1", 0))),
                                "atomic{b1:=1;x:=2}",
                                p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1)))),
                        transition(p(p("noncrit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 0))),
                                "atomic{b1:=1;x:=2}",
                                p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1)))),
                        transition(p(p("noncrit1", "crit2"), map(p("x", 1), p("b2", 1), p("b1", 0))),
                                "atomic{b1:=1;x:=2}", p(p("wait1", "crit2"), map(p("x", 2), p("b2", 1), p("b1", 1)))),
                        transition(p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1))), "",
                                p(p("crit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1)))),
                        transition(p(p("crit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1))),
                                "atomic{b2:=1;x:=1}", p(p("crit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1)))),
                        transition(
                                p(p("crit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1))), "b1:=0", p(
                                        p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0)))),
                        transition(p(p("noncrit1", "crit2"), map(p("x", 1), p("b2", 1), p("b1", 0))), "b2:=0",
                                p(p("noncrit1", "noncrit2"), map(p("x", 1), p("b2", 0), p("b1", 0)))),
                        transition(p(p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0))),
                                "atomic{b1:=1;x:=2}", p(p("wait1", "wait2"), map(p("x", 2), p("b2", 1), p("b1", 1)))),
                        transition(
                                p(p("wait1", "crit2"), map(p("x", 2), p("b2", 1), p("b1", 1))), "b2:=0",
                                p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1)))),
                        transition(p(p("noncrit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 0))),
                                "atomic{b2:=1;x:=1}",
                                p(p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0)))),
                        transition(p(p("wait1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1))), "",
                                p(p("crit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1)))),
                        transition(p(p("noncrit1", "noncrit2"), map(p("x", 1), p("b2", 0), p("b1", 0))),
                                "atomic{b2:=1;x:=1}",
                                p(p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0))))),
                ts.getTransitions());
        assertEquals(set("b1 = 1", "b2 = 1", "<wait1,wait2>", "x = 2"),
                ts.getLabel(p(p("wait1", "wait2"), map(p("x", 2), p("b2", 1), p("b1", 1)))));
        assertEquals(set("b1 = 0", "b2 = 0", "x = 1", "<noncrit1,noncrit2>"),
                ts.getLabel(p(p("noncrit1", "noncrit2"), map(p("x", 1), p("b2", 0), p("b1", 0)))));
        assertEquals(set("b1 = 0", "<noncrit1,crit2>", "b2 = 1", "x = 1"),
                ts.getLabel(p(p("noncrit1", "crit2"), map(p("x", 1), p("b2", 1), p("b1", 0)))));
        assertEquals(set("b1 = 1", "b2 = 0", "x = 2", "<crit1,noncrit2>"),
                ts.getLabel(p(p("crit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1)))));
        assertEquals(set("b1 = 1", "b2 = 1", "<wait1,wait2>", "x = 1"),
                ts.getLabel(p(p("wait1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1)))));
        assertEquals(set("b1 = 1", "b2 = 1", "<wait1,crit2>", "x = 2"),
                ts.getLabel(p(p("wait1", "crit2"), map(p("x", 2), p("b2", 1), p("b1", 1)))));
        assertEquals(set("b1 = 0", "b2 = 1", "<noncrit1,wait2>", "x = 1"),
                ts.getLabel(p(p("noncrit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 0)))));
        assertEquals(set("b1 = 1", "b2 = 0", "x = 2", "<wait1,noncrit2>"),
                ts.getLabel(p(p("wait1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 1)))));
        assertEquals(set("b1 = 1", "b2 = 1", "<crit1,wait2>", "x = 1"),
                ts.getLabel(p(p("crit1", "wait2"), map(p("x", 1), p("b2", 1), p("b1", 1)))));
        assertEquals(set("b1 = 0", "b2 = 0", "x = 2", "<noncrit1,noncrit2>"),
                ts.getLabel(p(p("noncrit1", "noncrit2"), map(p("x", 2), p("b2", 0), p("b1", 0)))));

    }

    // See Page 43 Figure 2.6
    @SuppressWarnings({"rawtypes", "unchecked"})
    @Test
    public void semaphorebased() throws Exception {
        ProgramGraph pg1 = SemaphoreBasedMutualExclusionBuilder.build(1);
        ProgramGraph pg2 = SemaphoreBasedMutualExclusionBuilder.build(2);

        ProgramGraph pg = fvmFacadeImpl.interleave(pg1, pg2);

        assertEquals(set(p("noncrit1", "noncrit2"), p("wait1", "noncrit2"), p("noncrit1", "crit2"), p("crit1", "crit2"),
                p("wait1", "crit2"), p("crit1", "noncrit2"), p("crit1", "wait2"), p("wait1", "wait2"),
                p("noncrit1", "wait2")), pg.getLocations());
        assertEquals(set(p("noncrit1", "noncrit2")), pg.getInitialLocations());
        assertEquals(set(seq("y:=1", "y:=1")), pg.getInitalizations());
        assertEquals(set(pgtransition(p("crit1", "noncrit2"), "true", "y:=y+1", p("noncrit1", "noncrit2")),
                pgtransition(p("crit1", "crit2"), "true", "y:=y+1", p("noncrit1", "crit2")),
                pgtransition(p("wait1", "wait2"), "y>0", "y:=y-1", p("wait1", "crit2")),
                pgtransition(p("wait1", "noncrit2"), "true", "", p("wait1", "wait2")),
                pgtransition(p("noncrit1", "crit2"), "true", "y:=y+1", p("noncrit1", "noncrit2")),
                pgtransition(p("crit1", "crit2"), "true", "y:=y+1", p("crit1", "noncrit2")),
                pgtransition(p("crit1", "noncrit2"), "true", "", p("crit1", "wait2")),
                pgtransition(p("wait1", "crit2"), "y>0", "y:=y-1", p("crit1", "crit2")),
                pgtransition(p("wait1", "noncrit2"), "y>0", "y:=y-1", p("crit1", "noncrit2")),
                pgtransition(p("noncrit1", "noncrit2"), "true", "", p("noncrit1", "wait2")),
                pgtransition(p("noncrit1", "wait2"), "y>0", "y:=y-1", p("noncrit1", "crit2")),
                pgtransition(p("crit1", "wait2"), "y>0", "y:=y-1", p("crit1", "crit2")),
                pgtransition(p("wait1", "crit2"), "true", "y:=y+1", p("wait1", "noncrit2")),
                pgtransition(p("noncrit1", "crit2"), "true", "", p("wait1", "crit2")),
                pgtransition(p("noncrit1", "noncrit2"), "true", "", p("wait1", "noncrit2")),
                pgtransition(p("noncrit1", "wait2"), "true", "", p("wait1", "wait2")),
                pgtransition(p("crit1", "wait2"), "true", "y:=y+1", p("noncrit1", "wait2")),
                pgtransition(p("wait1", "wait2"), "y>0", "y:=y-1", p("crit1", "wait2"))), pg.getTransitions());

        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        TransitionSystem ts = fvmFacadeImpl.transitionSystemFromProgramGraph(pg, ad, cd);

        assertEquals(
                set(p(p("noncrit1", "noncrit2"), map(p("y", 1))), p(p("noncrit1", "crit2"), map(p("y", 0))),
                        p(p("crit1", "noncrit2"), map(p("y", 0))), p(p("wait1", "wait2"), map(p("y", 1))),
                        p(p("wait1", "crit2"), map(p("y", 0))), p(p("wait1", "noncrit2"), map(p("y", 1))),
                        p(p("crit1", "wait2"), map(p("y", 0))), p(p("noncrit1", "wait2"), map(p("y", 1)))),
                ts.getStates());

        assertEquals(set(p(p("noncrit1", "noncrit2"), map(p("y", 1)))), ts.getInitialStates());

        assertEquals(set("", "y:=y-1", "y:=y+1"), ts.getActions());

        assertEquals(
                set("<noncrit1,crit2>", "<wait1,crit2>", "<crit1,wait2>", "<noncrit1,wait2>", "<wait1,wait2>",
                        "<crit1,noncrit2>", "y = 0", "<wait1,noncrit2>", "y = 1", "<noncrit1,noncrit2>"),
                ts.getAtomicPropositions());

        assertEquals(set(
                transition(p(p("wait1", "noncrit2"), map(p("y", 1))), "", p(p("wait1", "wait2"), map(p("y", 1)))),
                transition(p(p("noncrit1", "noncrit2"), map(p("y", 1))), "", p(p("noncrit1", "wait2"), map(p("y", 1)))),
                transition(p(p("wait1", "crit2"), map(p("y", 0))), "y:=y+1", p(p("wait1", "noncrit2"), map(p("y", 1)))),
                transition(p(p("crit1", "wait2"), map(p("y", 0))), "y:=y+1", p(p("noncrit1", "wait2"), map(p("y", 1)))),
                transition(p(p("crit1", "noncrit2"), map(p("y", 0))), "", p(p("crit1", "wait2"), map(p("y", 0)))),
                transition(p(p("noncrit1", "crit2"), map(p("y", 0))), "y:=y+1",
                        p(p("noncrit1", "noncrit2"), map(p("y", 1)))),
                transition(p(p("wait1", "wait2"), map(p("y", 1))), "y:=y-1", p(p("crit1", "wait2"), map(p("y", 0)))),
                transition(p(p("noncrit1", "crit2"), map(p("y", 0))), "", p(p("wait1", "crit2"), map(p("y", 0)))),
                transition(p(p("noncrit1", "noncrit2"), map(p("y", 1))), "", p(p("wait1", "noncrit2"), map(p("y", 1)))),
                transition(p(p("noncrit1", "wait2"), map(p("y", 1))), "y:=y-1",
                        p(p("noncrit1", "crit2"), map(p("y", 0)))),
                transition(p(p("crit1", "noncrit2"), map(p("y", 0))), "y:=y+1",
                        p(p("noncrit1", "noncrit2"), map(p("y", 1)))),
                transition(p(p("wait1", "noncrit2"), map(p("y", 1))), "y:=y-1",
                        p(p("crit1", "noncrit2"), map(p("y", 0)))),
                transition(p(p("noncrit1", "wait2"), map(p("y", 1))), "", p(p("wait1", "wait2"), map(p("y", 1)))),
                transition(p(p("wait1", "wait2"), map(p("y", 1))), "y:=y-1", p(p("wait1", "crit2"), map(p("y", 0))))),
                ts.getTransitions());

        assertEquals(set("y = 1", "<noncrit1,noncrit2>"), ts.getLabel(p(p("noncrit1", "noncrit2"), map(p("y", 1)))));
        assertEquals(set("<noncrit1,crit2>", "y = 0"), ts.getLabel(p(p("noncrit1", "crit2"), map(p("y", 0)))));
        assertEquals(set("<crit1,noncrit2>", "y = 0"), ts.getLabel(p(p("crit1", "noncrit2"), map(p("y", 0)))));
        assertEquals(set("<wait1,wait2>", "y = 1"), ts.getLabel(p(p("wait1", "wait2"), map(p("y", 1)))));
        assertEquals(set("<wait1,crit2>", "y = 0"), ts.getLabel(p(p("wait1", "crit2"), map(p("y", 0)))));
        assertEquals(set("<wait1,noncrit2>", "y = 1"), ts.getLabel(p(p("wait1", "noncrit2"), map(p("y", 1)))));
        assertEquals(set("<crit1,wait2>", "y = 0"), ts.getLabel(p(p("crit1", "wait2"), map(p("y", 0)))));
        assertEquals(set("<noncrit1,wait2>", "y = 1"), ts.getLabel(p(p("noncrit1", "wait2"), map(p("y", 1)))));

    }

}