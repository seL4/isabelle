(*  Title:      HOL/IOA/NTP/Lemmas.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

(Mostly) Arithmetic lemmas
Should realy go in Arith.ML.
Also: Get rid of all the --> in favour of ==> !!!
*)

(* Logic *)
val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by(fast_tac (!claset addDs prems) 1);
qed "imp_conj_lemma";

goal HOL.thy "(P --> (? x. Q(x))) = (? x. P --> Q(x))";
  by(Fast_tac 1);
qed "imp_ex_equiv";

goal HOL.thy "(A --> B & C) = ((A --> B) & (A --> C))";
  by (Fast_tac 1);
qed "fork_lemma";

goal HOL.thy "((A --> B) & (C --> B)) = ((A | C) --> B)";
  by (Fast_tac 1);
qed "imp_or_lem";

goal HOL.thy "(X = (~ Y)) = ((~X) = Y)";
  by (Fast_tac 1);
qed "neg_flip";

goal HOL.thy "P --> Q(M) --> Q(if P then M else N)";
  by (rtac impI 1); 
  by (rtac impI 1);
  by (rtac (expand_if RS iffD2) 1);
  by (Fast_tac 1);
qed "imp_true_decompose";

goal HOL.thy "(~P) --> Q(N) --> Q(if P then M else N)";
  by (rtac impI 1); 
  by (rtac impI 1);
  by (rtac (expand_if RS iffD2) 1);
  by (Fast_tac 1);
qed "imp_false_decompose";


(* Sets *)
val set_lemmas =
   map (fn s => prove_goal Set.thy s (fn _ => [Fast_tac 1]))
        ["f(x) : (UN x. {f(x)})",
         "f x y : (UN x y. {f x y})",
         "!!a. (!x. a ~= f(x)) ==> a ~: (UN x. {f(x)})",
         "!!a. (!x y. a ~= f x y) ==> a ~: (UN x y. {f x y})"];


(* Arithmetic *)
goal Arith.thy "n ~= 0 --> Suc(m+pred(n)) = m+n";
  by (nat_ind_tac "n" 1);
  by (REPEAT(Simp_tac 1));
val Suc_pred_lemma = store_thm("Suc_pred_lemma", result() RS mp);

goal Arith.thy "((m::nat) + n = m + p) = (n = p)";
  by (nat_ind_tac "m" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
qed "left_plus_cancel";

goal Arith.thy "((x::nat) + y = Suc(x + z)) = (y = Suc(z))";
  by (nat_ind_tac "x" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
qed "left_plus_cancel_inside_succ";

goal Arith.thy "(x ~= 0) = (? y. x = Suc(y))";
  by (nat_ind_tac "x" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
  by (Fast_tac 1);
qed "nonzero_is_succ";

goal Arith.thy "(m::nat) < n --> m + p < n + p";
  by (nat_ind_tac "p" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
qed "less_add_same_less";

goal Arith.thy "(x::nat)<= y --> x<=y+k";
  by (nat_ind_tac "k" 1);
  by (Simp_tac 1);
  by (Asm_full_simp_tac 1);
qed "leq_add_leq";

goal Arith.thy "(x::nat) + y <= z --> x <= z";
  by (nat_ind_tac "y" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
  by (rtac impI 1);
  by (dtac Suc_leD 1);
  by (Fast_tac 1);
qed "left_add_leq";

goal Arith.thy "(A::nat) < B --> C < D --> A + C < B + D";
 by (rtac impI 1);
 by (rtac impI 1);
 by (rtac less_trans 1);
 by (rtac (less_add_same_less RS mp) 1);
 by (assume_tac 1);
 by (rtac (add_commute RS ssubst)1);;
 by (res_inst_tac [("m1","B")] (add_commute RS ssubst) 1);
 by (rtac (less_add_same_less RS mp) 1);
 by (assume_tac 1);
qed "less_add_cong";

goal Arith.thy "(A::nat) <= B --> C <= D --> A + C <= B + D";
  by (rtac impI 1);
  by (rtac impI 1);
  by (asm_full_simp_tac (!simpset addsimps [le_eq_less_or_eq]) 1);
  by (safe_tac (!claset));
  by (rtac (less_add_cong RS mp RS mp) 1);
  by (assume_tac 1);
  by (assume_tac 1);
  by (rtac (less_add_same_less RS mp) 1);
  by (assume_tac 1);
  by (rtac (add_commute RS ssubst)1);;
  by (res_inst_tac [("m1","B")] (add_commute RS ssubst) 1);
  by (rtac (less_add_same_less RS mp) 1);
  by (assume_tac 1);
qed "less_eq_add_cong";

goal Arith.thy "(w <= y) --> ((x::nat) + y <= z) --> (x + w <= z)";
  by (rtac impI 1); 
  by (dtac (less_eq_add_cong RS mp) 1);
  by (cut_facts_tac [le_refl] 1);
  by (dres_inst_tac [("P","x<=x")] mp 1);by (assume_tac 1);
  by (asm_full_simp_tac (!simpset addsimps [add_commute]) 1);
  by (rtac impI 1);
  by (etac le_trans 1);
  by (assume_tac 1);
qed "leq_add_left_cong";

goal Arith.thy "(? x. y = Suc(x)) = (~(y = 0))";
  by (nat_ind_tac "y" 1);
  by (Simp_tac 1);
  by (rtac iffI 1);
  by (Asm_full_simp_tac 1);
  by (Fast_tac 1);
qed "suc_not_zero";

goal Arith.thy "Suc(x) <= y --> (? z. y = Suc(z))";
  by (rtac impI 1);
  by (asm_full_simp_tac (!simpset addsimps [le_eq_less_or_eq]) 1);
  by (safe_tac (!claset));
  by (Fast_tac 2);
  by (asm_simp_tac (!simpset addsimps [suc_not_zero]) 1);
qed "suc_leq_suc";

goal Arith.thy "~0<n --> n = 0";
  by (nat_ind_tac "n" 1);
  by (Auto_tac ());
qed "zero_eq";

goal Arith.thy "x < Suc(y) --> x<=y";
  by (nat_ind_tac "n" 1);
  by (asm_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
  by (safe_tac (!claset));
  by (etac less_imp_le 1);
qed "less_suc_imp_leq";

goal Arith.thy "0<x --> Suc(pred(x)) = x";
  by (nat_ind_tac "x" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
qed "suc_pred_id";

goal Arith.thy "0<x --> (pred(x) = y) = (x = Suc(y))";
  by (nat_ind_tac "x" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
qed "pred_suc";

goal Arith.thy "(x ~= 0) = (0<x)";
  by (nat_ind_tac "x" 1);
  by (Simp_tac 1);
  by (Asm_simp_tac 1);
qed "unzero_less";

(* Odd proof. Why do induction? *)
goal Arith.thy "((x::nat) = y + z) --> (y <= x)";
  by (nat_ind_tac "y" 1);
  by (Simp_tac 1);
  by (simp_tac (!simpset addsimps [le_refl RS (leq_add_leq RS mp)]) 1);
qed "plus_leq_lem";

(* Lists *)

val list_ss = simpset_of "List";

goal List.thy "(xs @ (y#ys)) ~= []";
  by (list.induct_tac "xs" 1);
  by (simp_tac list_ss 1);
  by (asm_simp_tac list_ss 1);
qed "append_cons";

goal List.thy "(x ~= hd(xs@ys)) = (x ~= (if xs = [] then hd ys else hd xs))";
  by (list.induct_tac "xs" 1);
  by (simp_tac list_ss 1);
  by (asm_full_simp_tac list_ss 1);
qed "not_hd_append";


Addsimps ([append_cons,not_hd_append,Suc_pred_lemma] @ set_lemmas);
