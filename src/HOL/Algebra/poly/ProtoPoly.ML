(*
    Prepearing definitions for polynomials
    $Id$
    Author: Clemens Ballarin, started 9 December 1996
*)

open ProtoPoly;

(* Rules for bound *)

val prem = goalw ProtoPoly.thy [bound_def]
  "[| !! m. n < m ==> f m = <0> |] ==> bound n f";
by (fast_tac (claset() addIs prem) 1);
qed "boundI";

Goalw [bound_def]
  "!! f. [| bound n f; n < m |] ==> f m = <0>";
by (Fast_tac 1);
qed "boundD";

Goalw [bound_def]
  "!! f. [| bound n f; n <= m  |] ==> bound m f";
by (fast_tac (set_cs addIs [le_less_trans]) 1);
(* Need set_cs, otherwise starts reasoning about naturals *)
qed "le_bound";

AddSIs [boundI];
AddDs [boundD];

Goal "(%x. <0>) : {f. EX n. bound n f}";
by (Blast_tac 1);
qed "UP_witness";
