(*  Title:      HOL/Lambda/Confluence.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Basic confluence lemmas.
*)

open Confluence;

goalw Confluence.thy [confluent_def,confluent1_def,diamondP_def]
  "!!R. confluent1(R) ==> diamondP(R^*)";
by(strip_tac 1);
be rtrancl_induct 1;
by(ALLGOALS(fast_tac (HOL_cs addIs [rtrancl_refl] addEs [rtrancl_comp])));
qed "confluent1";

goalw Confluence.thy [confluent_def]
  "!!R.[| diamondP(R); T <= R; R <= T^* |] ==> confluent(T)";
bd rtrancl_mono 1;
bd rtrancl_mono 1;
by(fast_tac (HOL_cs addIs [diamondP_confluent1,confluent1]
                    addDs [subset_antisym]
                    addss (HOL_ss addsimps [rtrancl_idemp])) 1);
qed "diamond_to_confluence";
