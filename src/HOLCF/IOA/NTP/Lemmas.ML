(*  Title:      HOL/IOA/NTP/Lemmas.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

(* Logic *)

goal HOL.thy "(A --> B & C) = ((A --> B) & (A --> C))";
  by (Fast_tac 1);
qed "fork_lemma";

goal HOL.thy "((A --> B) & (C --> B)) = ((A | C) --> B)";
  by (Fast_tac 1);
qed "imp_or_lem";

goal HOL.thy "(X = (~ Y)) = ((~X) = Y)";
  by (Fast_tac 1);
qed "neg_flip";


(* Sets *)
val set_lemmas =
   map (fn s => prove_goal Set.thy s (fn _ => [Fast_tac 1]))
        ["f(x) : (UN x. {f(x)})",
         "f x y : (UN x y. {f x y})",
         "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})",
         "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"];


(* Arithmetic *)

goal NatArith.thy "!!x. 0<x ==> (x - 1 = y) = (x = Suc(y))";
by (asm_simp_tac (simpset() addsimps [diff_Suc] addsplits [nat.split]) 1);
qed "pred_suc";


Addsimps (hd_append :: set_lemmas);
