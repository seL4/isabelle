(*  Title:      HOL/Lambda/Confluence.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Basic confluence lemmas.
*)

open Confluence;

goalw Confluence.thy [confluent1_def,diamond_def]
  "!!R. confluent1(R) ==> diamond(R^*)";
by(strip_tac 1);
be rtrancl_induct 1;
by(ALLGOALS(fast_tac (trancl_cs addEs [rtrancl_trans])));
qed "confluent1_diamond";

goalw Confluence.thy [confluent1_def,confluent2_def]
  "!!R. confluent2(R) ==> confluent1(R)";
by(fast_tac (HOL_cs addIs [r_into_rtrancl]) 1);
qed "confluent2_confluent1";

goalw Confluence.thy [confluent2_def,diamond_def]
  "!!R. diamond(R) ==> confluent2(R)";
by(strip_tac 1);
be rtrancl_induct 1;
by(fast_tac trancl_cs 1);
by(fast_tac (HOL_cs addSEs [rtrancl_into_rtrancl]) 1);
qed "diamond_confluent2";

goalw Confluence.thy [confluent_def]
  "!!R.[| diamond(R); T <= R; R <= T^* |] ==> confluent(T)";
bd rtrancl_mono 1;
bd rtrancl_mono 1;
by(fast_tac (HOL_cs addIs [diamond_confluent2, confluent2_confluent1,
                           confluent1_diamond]
                    addDs [subset_antisym]
                    addss (HOL_ss addsimps [rtrancl_idemp])) 1);
qed "diamond_to_confluence";

goalw Confluence.thy [confluent_def,diamond_def,Church_Rosser_def]
  "Church_Rosser(R) = confluent(R)";
br iffI 1;
 by(safe_tac HOL_cs);
 be allE 1;
 be allE 1;
 be mp 1;
 br rtrancl_trans 1;
  br (Un_upper2 RS rtrancl_mono RS subsetD) 1;
  br rtrancl_converseI 1;
  be converseI 1;
 be (Un_upper1 RS rtrancl_mono RS subsetD) 1;
be rtrancl_induct 1;
 by(fast_tac trancl_cs 1);
 by(slow_tac (rel_cs addIs [r_into_rtrancl]
                     addEs [rtrancl_trans,r_into_rtrancl RS rtrancl_trans]) 1);
qed "Church_Rosser_confluent";
