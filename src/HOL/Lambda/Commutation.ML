(*  Title:      HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Basic commutation lemmas.
*)

open Commutation;

(*** square ***)

Goalw [square_def] "square R S T U ==> square S R U T";
by (Blast_tac 1);
qed "square_sym";

Goalw [square_def]
  "[| square R S T U; T <= T' |] ==> square R S T' U";
by (Blast_tac 1);
qed "square_subset";

Goalw [square_def]
  "[| square R S T (R^=); S <= T |] ==> square (R^=) S T (R^=)";
by (Blast_tac 1);
qed "square_reflcl";

Goalw [square_def]
  "square R S S T ==> square (R^*) S S (T^*)";
by (strip_tac 1);
by (etac rtrancl_induct 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed "square_rtrancl";

Goalw [commute_def]
 "square R S (S^*) (R^=) ==> commute (R^*) (S^*)";
by (fast_tac (claset() addDs [square_reflcl,square_sym RS square_rtrancl]
                       addEs [r_into_rtrancl]
                       addss simpset()) 1);
qed "square_rtrancl_reflcl_commute";

(*** commute ***)

Goalw [commute_def] "commute R S ==> commute S R";
by (blast_tac (claset() addIs [square_sym]) 1);
qed "commute_sym";

Goalw [commute_def] "commute R S ==> commute (R^*) (S^*)";
by (blast_tac (claset() addIs [square_rtrancl,square_sym]) 1);
qed "commute_rtrancl";

Goalw [commute_def,square_def]
  "[| commute R T; commute S T |] ==> commute (R Un S) T";
by (Blast_tac 1);
qed "commute_Un";

(*** diamond, confluence and union ***)

Goalw [diamond_def]
  "[| diamond R; diamond S; commute R S |] ==> diamond (R Un S)";
by (REPEAT(ares_tac [commute_Un,commute_sym] 1));
qed "diamond_Un";

Goalw [diamond_def] "diamond R ==> confluent (R)";
by (etac commute_rtrancl 1);
qed "diamond_confluent";

Goalw [diamond_def]
  "square R R (R^=) (R^=) ==> confluent R";
by (fast_tac (claset() addIs [square_rtrancl_reflcl_commute, r_into_rtrancl]
                       addEs [square_subset]) 1);
qed "square_reflcl_confluent";

Goal
 "[| confluent R; confluent S; commute (R^*) (S^*) |] ==> confluent(R Un S)";
by (rtac (rtrancl_Un_rtrancl RS subst) 1);
by (blast_tac (claset() addDs [diamond_Un] addIs [diamond_confluent]) 1);
qed "confluent_Un";

Goal "[| diamond(R); T <= R; R <= T^* |] ==> confluent(T)";
by (force_tac (claset() addIs [diamond_confluent] 
                        addDs [rtrancl_subset RS sym], simpset()) 1);
qed "diamond_to_confluence";

(*** Church_Rosser ***)

Goalw [square_def,commute_def,diamond_def,Church_Rosser_def]
  "Church_Rosser(R) = confluent(R)";
by (safe_tac HOL_cs);
 by (blast_tac (HOL_cs addIs
      [Un_upper2 RS rtrancl_mono RS subsetD RS rtrancl_trans,
       rtrancl_converseI, converseI, Un_upper1 RS rtrancl_mono RS subsetD])1);
by (etac rtrancl_induct 1);
 by (Blast_tac 1);
by (blast_tac (claset() delrules [rtrancl_refl] 
                        addIs [r_into_rtrancl, rtrancl_trans]) 1);
qed "Church_Rosser_confluent";
