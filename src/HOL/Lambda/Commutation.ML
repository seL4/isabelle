(*  Title:      HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Basic commutation lemmas.
*)

open Commutation;

(* FIXME: move to Trancl *)
(* FIXME: add rtrancl_idemp globally *)
Addsimps [rtrancl_idemp];

goal Trancl.thy "!!R. [| R <= S; S <= R^* |] ==> S^* = R^*";
bd rtrancl_mono 1;
bd rtrancl_mono 1;
by(Asm_full_simp_tac 1);
by(fast_tac eq_cs 1);
qed "rtrancl_subset";

(* FIXME: move to Trancl *)
goal Trancl.thy "!!R. p:R ==> p:R^*";
by(res_inst_tac [("p","p")] PairE 1);
by(fast_tac (HOL_cs addIs [r_into_rtrancl]) 1);
qed "r_into_rtrancl1";

(* FIXME: move to Trancl *)
goal Trancl.thy "!!R. (R^* Un S^*)^* = (R Un S)^*";
by(best_tac (set_cs addIs [rtrancl_subset,r_into_rtrancl1,
                           rtrancl_mono RS subsetD]) 1);
qed "trancl_Un_trancl";

(* FIXME: move to Trancl *)
goal Commutation.thy "(R^=)^* = R^*";
by(fast_tac (trancl_cs addIs [rtrancl_subset,r_into_rtrancl1]) 1);
qed "rtrancl_reflcl";
Addsimps [rtrancl_reflcl];

(*** square ***)

goalw Commutation.thy [square_def] "!!R. square R S T U ==> square S R U T";
by(fast_tac HOL_cs 1);
qed "square_sym";

goalw Commutation.thy [square_def]
  "!!R. [| square R S T (R^=); S <= T |] ==> square (R^=) S T (R^=)";
by(fast_tac rel_cs 1);
qed "square_reflcl";

goalw Commutation.thy [square_def]
  "!!R. square R S S T ==> square (R^*) S S (T^*)";
by(strip_tac 1);
be rtrancl_induct 1;
by(fast_tac trancl_cs 1);
by(fast_tac (HOL_cs addSEs [rtrancl_into_rtrancl]) 1);
qed "square_rtrancl";

(* A big fast_tac runs out of store. Search space too large? *)
goalw Commutation.thy [commute_def]
 "!!R. square R S (S^*) (R^=) ==> commute (R^*) (S^*)";
bd square_reflcl 1;
br subsetI 1;
be r_into_rtrancl1 1;
bd square_sym 1;
bd square_rtrancl 1;
by(Asm_full_simp_tac 1);
bd square_sym 1;
bd square_rtrancl 1;
by(Asm_full_simp_tac 1);
qed "square_rtrancl_reflcl_commute";

(*** commute ***)

goalw Commutation.thy [commute_def] "!!R. commute R S ==> commute S R";
by(fast_tac (HOL_cs addIs [square_sym]) 1);
qed "commute_sym";

goalw Commutation.thy [commute_def] "!!R. commute R S ==> commute (R^*) (S^*)";
by(fast_tac (HOL_cs addIs [square_rtrancl,square_sym]) 1);
qed "commute_rtrancl";

goalw Commutation.thy [commute_def,square_def]
  "!!R. [| commute R T; commute S T |] ==> commute (R Un S) T";
by(fast_tac set_cs 1);
qed "commute_Un";

(*** diamond, confluence and union ***)

goalw Commutation.thy [diamond_def]
  "!!R. [| diamond R; diamond S; commute R S |] ==> diamond (R Un S)";
by(REPEAT(ares_tac [commute_Un,commute_sym] 1));
qed "diamond_Un";

goalw Commutation.thy [diamond_def] "!!R. diamond R ==> confluent (R)";
be commute_rtrancl 1;
qed "diamond_confluent";

goal Commutation.thy
 "!!R. [| confluent R; confluent S; commute (R^*) (S^*) |] \
\      ==> confluent(R Un S)";
br(trancl_Un_trancl RS subst) 1;
by(fast_tac (HOL_cs addDs [diamond_Un] addIs [diamond_confluent]) 1);
qed "confluent_Un";

goal Commutation.thy
  "!!R.[| diamond(R); T <= R; R <= T^* |] ==> confluent(T)";
by(fast_tac (HOL_cs addIs [diamond_confluent]
                    addDs [rtrancl_subset RS sym] addss HOL_ss) 1);
qed "diamond_to_confluence";

(*** Church_Rosser ***)

goalw Commutation.thy [square_def,commute_def,diamond_def,Church_Rosser_def]
  "Church_Rosser(R) = confluent(R)";
br iffI 1;
 by(fast_tac (HOL_cs addIs
      [Un_upper2 RS rtrancl_mono RS subsetD RS rtrancl_trans,
       rtrancl_converseI, converseI, Un_upper1 RS rtrancl_mono RS subsetD])1);
by(safe_tac HOL_cs);
be rtrancl_induct 1;
 by(fast_tac trancl_cs 1);
 by(slow_tac (rel_cs addIs [r_into_rtrancl]
                     addEs [rtrancl_trans,r_into_rtrancl RS rtrancl_trans]) 1);
qed "Church_Rosser_confluent";
