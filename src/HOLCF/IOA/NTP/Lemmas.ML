(*  Title:      HOL/IOA/NTP/Lemmas.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
*)

(* Logic *)

Goal "(X = (~ Y)) = ((~X) = Y)";
  by (Fast_tac 1);
qed "neg_flip";


(* Sets *)
val set_lemmas =
   map (fn s => prove_goal Main.thy s (fn _ => [Fast_tac 1]))
        ["f(x) : (UN x. {f(x)})",
         "f x y : (UN x y. {f x y})",
         "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})",
         "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"];


(* Arithmetic *)

Goal "0<x ==> (x - 1 = y) = (x = Suc(y))";
by (asm_simp_tac (simpset() addsimps [diff_Suc] addsplits [nat.split]) 1);
qed "pred_suc";


Addsimps (hd_append :: set_lemmas);
