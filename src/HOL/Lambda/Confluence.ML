(*  Title:      HOL/Lambda/Confluence.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Basic confluence lemmas.
*)

open Confluence;

goal Confluence.thy
  "!!R. [| !x y z. (x,y):R --> (x,z):S --> (? u. (y,u):S & (z,u):R); \
\          (x,y):R; (x,z):S^* |] ==> ? u. (y,u):S^* & (z,u):R";
be rtrancl_induct 1;
by(fast_tac trancl_cs 1);
by(fast_tac (HOL_cs addSEs [rtrancl_into_rtrancl]) 1);
qed "commute_rtrancl";

goal HOL.thy "!!P. ? x.P(x) & Q(x) ==> ? x. Q(x) & P(x)";
by(fast_tac HOL_cs 1);
val lemma = result();

goalw Confluence.thy [diamond_def]
  "!!R. diamond(R) ==> diamond(R^*)";
by(best_tac (HOL_cs addIs [commute_rtrancl,commute_rtrancl RS lemma]) 1);
qed "diamond_diamond_rtrancl";

goalw Confluence.thy [confluent_def]
  "!!R.[| diamond(R); T <= R; R <= T^* |] ==> confluent(T)";
bd rtrancl_mono 1;
bd rtrancl_mono 1;
by(fast_tac (HOL_cs addIs [diamond_diamond_rtrancl]
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
