package il.ac.bgu.cs.formalmethodsintro.base.PG;

import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.map;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.p;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.pgtransition;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.FileInputStream;
import java.io.InputStream;
import java.io.StringBufferInputStream;
import java.util.Map;
import java.util.Set;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import org.junit.Before;
import org.junit.Test;

@SuppressWarnings("deprecation")
public class NanoPromelaTest {

    FvmFacade fvmFacadeImpl;

    @Before
    public void setup() {
        fvmFacadeImpl = FvmFacade.get();
    }

    @Test
    public void test1() throws Exception {
        try (InputStream in = new FileInputStream(System.getProperty("user.dir") + "\\src\\main\\java\\il\\ac\\bgu\\cs\\formalmethodsintro\\base\\nanopromela\\tst1.np")) {
            System.out.println(in);
            ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

            assertTrue(pg.getLocations().containsAll(set("", "do::x<3->x:=x+1od;y:=9",
                    "if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi", "y:=9")));
            assertEquals(set("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi"), pg.getInitialLocations());
            assertEquals(set(), pg.getInitalizations());
            Set<PGTransition> setToCheck = set(pgtransition("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi",
                    "(a==b) && ((x!=y) && (!((x<3))))", "", "y:=9"), pgtransition("y:=9", "", "y:=9", ""),
                    pgtransition("do::x<3->x:=x+1od;y:=9", "(x<3)", "x:=x+1", "do::x<3->x:=x+1od;y:=9"),
                    pgtransition("do::x<3->x:=x+1od;y:=9", "!((x<3))", "", "y:=9"),
                    pgtransition("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi", "(a==c)",
                            "bb:=1", ""),
                    pgtransition("if::a==c->bb:=1::a==b->if::x!=y->do::x<3->x:=x+1odfi;y:=9fi",
                            "(a==b) && ((x!=y) && ((x<3)))", "x:=x+1", "do::x<3->x:=x+1od;y:=9"));

            assertTrue(pg.getTransitions().containsAll(setToCheck));
        }
    }

    @Test
    public void test2() throws Exception {
        try (InputStream in = new FileInputStream(System.getProperty("user.dir") + "\\src\\main\\java\\il\\ac\\bgu\\cs\\formalmethodsintro\\base\\nanopromela\\tst2.np")) {

            ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

            assertTrue(pg.getLocations().containsAll(
                    set("", "ppp:=2", "do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
                            "if::x>1->C?x;D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2fi",
                            "y:=1;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
                            "D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
                            "do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
                            "D!r;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"))
                    );
            assertEquals(set("if::x>1->C?x;D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2fi"),
                    pg.getInitialLocations());
            assertEquals(set(), pg.getInitalizations());
            Set<PGTransition> setToCheck = set(pgtransition("do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "(x>1)", "C?x",
                    "y:=1;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
                    pgtransition("ppp:=2", "", "ppp:=2", ""),
                    pgtransition("do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "!((x>1))", "", "ppp:=2"),
                    pgtransition("do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "(r>3)",
                            "r:=1", "D!r;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
                    pgtransition("D!r;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "",
                            "D!r", "do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
                    pgtransition("D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "", "D!5",
                            "do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
                    pgtransition("if::x>1->C?x;D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2fi", "(x>1)",
                            "C?x", "D!5;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
                    pgtransition("y:=1;do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2", "",
                            "y:=1", "do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"),
                    pgtransition("do::r>3->r:=1;D!rod;do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2",
                            "!((r>3))", "", "do::x>1->C?x;y:=1;do::r>3->r:=1;D!rodod;ppp:=2"));



            assertTrue(pg.getTransitions().containsAll(setToCheck));
        }
    }

    @Test
    public void test3() throws Exception {
        try (InputStream in = new FileInputStream(System.getProperty("user.dir") + "\\src\\main\\java\\il\\ac\\bgu\\cs\\formalmethodsintro\\base\\nanopromela\\tst3.np")) {
            ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

            assertTrue(pg.getLocations().containsAll(set("", "do::x<4->x:=5;x:=6od;x:=7", "x:=6;do::x<4->x:=5;x:=6od;x:=7", "x:=7",
                    "if::x<3->do::x<4->x:=5;x:=6od;x:=7fi")));
            assertEquals(set("if::x<3->do::x<4->x:=5;x:=6od;x:=7fi"), pg.getInitialLocations());
            assertEquals(set(), pg.getInitalizations());
            assertTrue(pg.getTransitions().containsAll(set(
                    pgtransition("if::x<3->do::x<4->x:=5;x:=6od;x:=7fi", "(x<3) && ((x<4))", "x:=5",
                            "x:=6;do::x<4->x:=5;x:=6od;x:=7"),
                    pgtransition("x:=7", "", "x:=7", ""),
                    pgtransition("do::x<4->x:=5;x:=6od;x:=7", "(x<4)", "x:=5", "x:=6;do::x<4->x:=5;x:=6od;x:=7"),
                    pgtransition("do::x<4->x:=5;x:=6od;x:=7", "!((x<4))", "", "x:=7"),
                    pgtransition("if::x<3->do::x<4->x:=5;x:=6od;x:=7fi", "(x<3) && (!((x<4)))", "", "x:=7"),
                    pgtransition("x:=6;do::x<4->x:=5;x:=6od;x:=7", "", "x:=6", "do::x<4->x:=5;x:=6od;x:=7")))
                    );

        }
    }

    @SuppressWarnings("unchecked")
    @Test
    public void soda() throws Exception {
        ProgramGraph<String, String> pg = VendingmachineInNanopromela.build();

        assertTrue(pg.getLocations().containsAll(
                set("", "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                        "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"))
                );
        assertEquals(
                set("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                pg.getInitialLocations());
        assertEquals(set(), pg.getInitalizations());

        Set<PGTransition> setToCheck = set(pgtransition(
                        "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                        "(nbeer>0)", "nbeer:=nbeer-1",
                        "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "(true)", "skip",
                                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "!((true)||(true))", "", ""),
                        pgtransition(
                                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "(nsoda>0)", "nsoda:=nsoda-1",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "((nsoda==0)&&(nbeer==0))", "skip",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "(true)", "atomic{nbeer:=3;nsoda:=3}",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"));

        assertTrue(pg.getTransitions().containsAll(setToCheck));

        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = fvmFacadeImpl
                .transitionSystemFromProgramGraph(pg, ad, cd);

        assertTrue(pg.getLocations().containsAll(
                set("", "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                        "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"))
                );
        assertEquals(
                set("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                pg.getInitialLocations());
        assertEquals(set(), pg.getInitalizations());
        assertTrue(pg.getTransitions().containsAll(
                set(pgtransition(
                        "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                        "(true)", "skip",
                        "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "(nbeer>0)", "nbeer:=nbeer-1",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "!((true)||(true))", "", ""),
                        pgtransition(
                                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "(nsoda>0)", "nsoda:=nsoda-1",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "(true)", "atomic{nbeer:=3;nsoda:=3}",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
                        pgtransition(
                                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
                                "((nsoda==0)&&(nbeer==0))", "skip",
                                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od")))
                );

//        assertEquals(set(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                map(p("nbeer", 2), p("nsoda", 3))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map()),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 0))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0))),
//                p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map()),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 0))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2))),
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0)))),
//                ts.getStates());
//        assertEquals(
//                set(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map())),
//                ts.getInitialStates());
//        assertEquals(set("nsoda:=nsoda-1", "skip", "nbeer:=nbeer-1", "atomic{nbeer:=3;nsoda:=3}"), ts.getActions());
//        assertEquals(set("nbeer = 3", "nbeer = 2", "nbeer = 1", "nbeer = 0",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1", "nsoda = 0", "nsoda = 3", "nsoda = 2"), ts.getAtomicPropositions());
//        assertEquals(set(transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                map(p("nbeer", 3), p("nsoda", 0))),
//                "nbeer:=nbeer-1",
//                p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 2)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0))),
//                        "skip",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 0)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 0)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 2)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 1)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 1)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 0)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 2)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 1)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 2)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 0))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 2)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 1)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 0)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 2)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 1)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 0)))),
//                transition(
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map()),
//                        "skip",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map())),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 2)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 0)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 1)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 2)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 1)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 0)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 2)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 1)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 0)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 1)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map()),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0))),
//                        "nbeer:=nbeer-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 0)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3))),
//                        "atomic{nbeer:=3;nsoda:=3}",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 3)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 1)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 0)))),
//                transition(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3))),
//                        "nsoda:=nsoda-1",
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 2)))),
//                transition(
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map()),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map())),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 2), p("nsoda", 3)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 0))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 3), p("nsoda", 0)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 1), p("nsoda", 2)))),
//                transition(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1))),
//                        "skip",
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map(p("nbeer", 0), p("nsoda", 1))))),
//                ts.getTransitions());
//
//        assertEquals(set("nbeer = 2",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3)))));
//        assertEquals(
//                set("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
//                ts.getLabel(
//                        p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map())));
//        assertEquals(set("nbeer = 3",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 0)))));
//        assertEquals(set("nbeer = 1",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 0",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 3",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 1",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 2",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0)))));
//        assertEquals(set("nbeer = 0",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 3",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 2",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 0",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 3",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 2",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 1",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0)))));
//        assertEquals(set("nbeer = 1",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 0",
//                "if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0)))));
//        assertEquals(
//                set("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od"),
//                ts.getLabel(
//                        p("if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi;do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                                map())));
//        assertEquals(set("nbeer = 2",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 3",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 2",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 3",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 0)))));
//        assertEquals(set("nbeer = 1",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 0",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 1",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 0",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 0)))));
//        assertEquals(set("nbeer = 3",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 2",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 0",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 3",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 1"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 3), p("nsoda", 1)))));
//        assertEquals(set("nbeer = 1",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 3"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 3)))));
//        assertEquals(set("nbeer = 2",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 2), p("nsoda", 0)))));
//        assertEquals(set("nbeer = 0",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 2"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 0), p("nsoda", 2)))));
//        assertEquals(set("nbeer = 1",
//                "do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                "nsoda = 0"),
//                ts.getLabel(p("do::true->skip;if::nsoda>0->nsoda:=nsoda-1::nbeer>0->nbeer:=nbeer-1::(nsoda==0)&&(nbeer==0)->skipfi::true->atomic{nbeer:=3;nsoda:=3}od",
//                        map(p("nbeer", 1), p("nsoda", 0)))));

    }

    @SuppressWarnings({"unchecked"})
    @Test
    public void test10() throws Exception {
        InputStream in = new StringBufferInputStream("x:=4;\n" +
                "if :: x>3 -> do  	\n" +
                "  :: x < 5 -> x:=x+3\n" +
                "  :: x > 6 -> x:=x-4\n" +
                "   	od\n" +
                "fi\n" +
                "");

        ProgramGraph<String, String> pg = fvmFacadeImpl.programGraphFromNanoPromela(in);

        assertTrue(pg.getLocations().containsAll(set("", "do::x<5->x:=x+3::x>6->x:=x-4od", "if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi",
                "x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi")));
        assertEquals(set("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"), pg.getInitialLocations());
        assertEquals(set(), pg.getInitalizations());

        assertTrue(pg.getTransitions().containsAll(set(
                pgtransition("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "(x>3) && ((x<5))", "x:=x+3",
                        "do::x<5->x:=x+3::x>6->x:=x-4od"),
                pgtransition("do::x<5->x:=x+3::x>6->x:=x-4od", "x>=5 && x<=6", "", ""),
                pgtransition("do::x<5->x:=x+3::x>6->x:=x-4od", "(x<5)", "x:=x+3", "do::x<5->x:=x+3::x>6->x:=x-4od"),
                pgtransition("x:=4;if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "", "x:=4",
                        "if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi"),
                pgtransition("do::x<5->x:=x+3::x>6->x:=x-4od", "(x>6)", "x:=x-4", "do::x<5->x:=x+3::x>6->x:=x-4od"),
                pgtransition("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "(x>3) && (!((x<5)||(x>6)))", "", ""),
                pgtransition("if::x>3->do::x<5->x:=x+3::x>6->x:=x-4odfi", "(x>3) && ((x>6))", "x:=x-4",
                        "do::x<5->x:=x+3::x>6->x:=x-4od"))));
    }


}