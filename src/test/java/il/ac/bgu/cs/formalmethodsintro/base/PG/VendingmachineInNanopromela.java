package il.ac.bgu.cs.formalmethodsintro.base.PG;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;


public class VendingmachineInNanopromela {

    static FvmFacade fvmFacadeImpl = FvmFacade.get();

    public static ProgramGraph<String, String> build() throws Exception {
        return fvmFacadeImpl.programGraphFromNanoPromelaString(//
                "do :: true ->                                      \n" +
                        "		skip;                                       \n" +
                        "		if 	:: nsoda > 0 -> nsoda := nsoda - 1      \n" +
                        "			:: nbeer > 0 -> nbeer := nbeer - 1      \n" +
                        "			:: (nsoda == 0) && (nbeer == 0) -> skip \n" +
                        "		fi                                          \n" +
                "	:: true -> atomic{nbeer := 3; nsoda := 3}       \n" +
                "od");
    }

}