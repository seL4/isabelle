(*  Title: 	HOL/Arith.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Proofs about elementary arithmetic: addition, multiplication, etc.
Tests definitions and simplifier.
*)

open Arith;

(*** Basic rewrite rules for the arithmetic operators ***)

val [pred_0, pred_Suc] = nat_recs pred_def;
val [add_0,add_Suc] = nat_recs add_def; 
val [mult_0,mult_Suc] = nat_recs mult_def; 

(** Difference **)

val diff_0 = diff_def RS def_nat_rec_0;

qed_goalw "diff_0_eq_0" Arith.thy [diff_def, pred_def]
    "0 - n = 0"
 (fn _ => [nat_ind_tac "n" 1,  ALLGOALS(asm_simp_tac nat_ss)]);

(*Must simplify BEFORE the induction!!  (Else we get a critical pair)
  Suc(m) - Suc(n)   rewrites to   pred(Suc(m) - n)  *)
qed_goalw "diff_Suc_Suc" Arith.thy [diff_def, pred_def]
    "Suc(m) - Suc(n) = m - n"
 (fn _ =>
  [simp_tac nat_ss 1, nat_ind_tac "n" 1, ALLGOALS(asm_simp_tac nat_ss)]);

(*** Simplification over add, mult, diff ***)

val arith_simps =
 [pred_0, pred_Suc, add_0, add_Suc, mult_0, mult_Suc,
  diff_0, diff_0_eq_0, diff_Suc_Suc];

val arith_ss = nat_ss addsimps arith_simps;

(**** Inductive properties of the operators ****)

(*** Addition ***)

qed_goal "add_0_right" Arith.thy "m + 0 = m"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

qed_goal "add_Suc_right" Arith.thy "m + Suc(n) = Suc(m+n)"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

val arith_ss = arith_ss addsimps [add_0_right,add_Suc_right];

(*Associative law for addition*)
qed_goal "add_assoc" Arith.thy "(m + n) + k = m + ((n + k)::nat)"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

(*Commutative law for addition*)  
qed_goal "add_commute" Arith.thy "m + n = n + (m::nat)"
 (fn _ =>  [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

qed_goal "add_left_commute" Arith.thy "x+(y+z)=y+((x+z)::nat)"
 (fn _ => [rtac (add_commute RS trans) 1, rtac (add_assoc RS trans) 1,
           rtac (add_commute RS arg_cong) 1]);

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

goal Arith.thy "!!k::nat. (k + m = k + n) = (m=n)";
by (nat_ind_tac "k" 1);
by (simp_tac arith_ss 1);
by (asm_simp_tac arith_ss 1);
qed "add_left_cancel";

goal Arith.thy "!!k::nat. (m + k = n + k) = (m=n)";
by (nat_ind_tac "k" 1);
by (simp_tac arith_ss 1);
by (asm_simp_tac arith_ss 1);
qed "add_right_cancel";

goal Arith.thy "!!k::nat. (k + m <= k + n) = (m<=n)";
by (nat_ind_tac "k" 1);
by (simp_tac arith_ss 1);
by (asm_simp_tac (arith_ss addsimps [Suc_le_mono]) 1);
qed "add_left_cancel_le";

goal Arith.thy "!!k::nat. (k + m < k + n) = (m<n)";
by (nat_ind_tac "k" 1);
by (simp_tac arith_ss 1);
by (asm_simp_tac arith_ss 1);
qed "add_left_cancel_less";

(*** Multiplication ***)

(*right annihilation in product*)
qed_goal "mult_0_right" Arith.thy "m * 0 = 0"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

(*right Sucessor law for multiplication*)
qed_goal "mult_Suc_right" Arith.thy  "m * Suc(n) = m + (m * n)"
 (fn _ => [nat_ind_tac "m" 1,
           ALLGOALS(asm_simp_tac (arith_ss addsimps add_ac))]);

val arith_ss = arith_ss addsimps [mult_0_right,mult_Suc_right];

(*Commutative law for multiplication*)
qed_goal "mult_commute" Arith.thy "m * n = n * (m::nat)"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS (asm_simp_tac arith_ss)]);

(*addition distributes over multiplication*)
qed_goal "add_mult_distrib" Arith.thy "(m + n)*k = (m*k) + ((n*k)::nat)"
 (fn _ => [nat_ind_tac "m" 1,
           ALLGOALS(asm_simp_tac (arith_ss addsimps add_ac))]);

qed_goal "add_mult_distrib2" Arith.thy "k*(m + n) = (k*m) + ((k*n)::nat)"
 (fn _ => [nat_ind_tac "m" 1,
           ALLGOALS(asm_simp_tac (arith_ss addsimps add_ac))]);

val arith_ss = arith_ss addsimps [add_mult_distrib,add_mult_distrib2];

(*Associative law for multiplication*)
qed_goal "mult_assoc" Arith.thy "(m * n) * k = m * ((n * k)::nat)"
  (fn _ => [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

qed_goal "mult_left_commute" Arith.thy "x*(y*z) = y*((x*z)::nat)"
 (fn _ => [rtac trans 1, rtac mult_commute 1, rtac trans 1,
           rtac mult_assoc 1, rtac (mult_commute RS arg_cong) 1]);

val mult_ac = [mult_assoc,mult_commute,mult_left_commute];

(*** Difference ***)

qed_goal "diff_self_eq_0" Arith.thy "m - m = 0"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS(asm_simp_tac arith_ss)]);

(*Addition is the inverse of subtraction: if n<=m then n+(m-n) = m. *)
val [prem] = goal Arith.thy "[| ~ m<n |] ==> n+(m-n) = (m::nat)";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac arith_ss));
qed "add_diff_inverse";


(*** Remainder ***)

goal Arith.thy "m - n < Suc(m)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (etac less_SucE 3);
by (ALLGOALS(asm_simp_tac arith_ss));
qed "diff_less_Suc";

goal Arith.thy "!!m::nat. m - n <= m";
by (res_inst_tac [("m","m"), ("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac arith_ss));
by (etac le_trans 1);
by (simp_tac (HOL_ss addsimps [le_eq_less_or_eq, lessI]) 1);
qed "diff_le_self";

goal Arith.thy "!!n::nat. (n+m) - n = m";
by (nat_ind_tac "n" 1);
by (ALLGOALS (asm_simp_tac arith_ss));
qed "diff_add_inverse";

goal Arith.thy "!!n::nat. n - (n+m) = 0";
by (nat_ind_tac "n" 1);
by (ALLGOALS (asm_simp_tac arith_ss));
qed "diff_add_0";

(*In ordinary notation: if 0<n and n<=m then m-n < m *)
goal Arith.thy "!!m. [| 0<n; ~ m<n |] ==> m - n < m";
by (subgoal_tac "0<n --> ~ m<n --> m - n < m" 1);
by (fast_tac HOL_cs 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac(arith_ss addsimps [diff_less_Suc])));
qed "div_termination";

val wf_less_trans = wf_pred_nat RS wf_trancl RSN (2, def_wfrec RS trans);

goalw Nat.thy [less_def] "<m,n> : pred_nat^+ = (m<n)";
by (rtac refl 1);
qed "less_eq";

goal Arith.thy "!!m. m<n ==> m mod n = m";
by (rtac (mod_def RS wf_less_trans) 1);
by(asm_simp_tac HOL_ss 1);
qed "mod_less";

goal Arith.thy "!!m. [| 0<n;  ~m<n |] ==> m mod n = (m-n) mod n";
by (rtac (mod_def RS wf_less_trans) 1);
by(asm_simp_tac (nat_ss addsimps [div_termination, cut_apply, less_eq]) 1);
qed "mod_geq";


(*** Quotient ***)

goal Arith.thy "!!m. m<n ==> m div n = 0";
by (rtac (div_def RS wf_less_trans) 1);
by(asm_simp_tac nat_ss 1);
qed "div_less";

goal Arith.thy "!!M. [| 0<n;  ~m<n |] ==> m div n = Suc((m-n) div n)";
by (rtac (div_def RS wf_less_trans) 1);
by(asm_simp_tac (nat_ss addsimps [div_termination, cut_apply, less_eq]) 1);
qed "div_geq";

(*Main Result about quotient and remainder.*)
goal Arith.thy "!!m. 0<n ==> (m div n)*n + m mod n = m";
by (res_inst_tac [("n","m")] less_induct 1);
by (rename_tac "k" 1);    (*Variable name used in line below*)
by (case_tac "k<n" 1);
by (ALLGOALS (asm_simp_tac(arith_ss addsimps (add_ac @
                       [mod_less, mod_geq, div_less, div_geq,
	                add_diff_inverse, div_termination]))));
qed "mod_div_equality";


(*** More results about difference ***)

val [prem] = goal Arith.thy "m < Suc(n) ==> m-n = 0";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac arith_ss));
qed "less_imp_diff_is_0";

val prems = goal Arith.thy "m-n = 0  -->  n-m = 0  -->  m=n";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (REPEAT(simp_tac arith_ss 1 THEN TRY(atac 1)));
qed "diffs0_imp_equal_lemma";

(*  [| m-n = 0;  n-m = 0 |] ==> m=n  *)
bind_thm ("diffs0_imp_equal", (diffs0_imp_equal_lemma RS mp RS mp));

val [prem] = goal Arith.thy "m<n ==> 0<n-m";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac arith_ss));
qed "less_imp_diff_positive";

val [prem] = goal Arith.thy "n < Suc(m) ==> Suc(m)-n = Suc(m-n)";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac arith_ss));
qed "Suc_diff_n";

goal Arith.thy "Suc(m)-n = if (m<n) 0 (Suc m-n)";
by(simp_tac (nat_ss addsimps [less_imp_diff_is_0, not_less_eq, Suc_diff_n]
                    setloop (split_tac [expand_if])) 1);
qed "if_Suc_diff_n";

goal Arith.thy "P(k) --> (!n. P(Suc(n))--> P(n)) --> P(k-i)";
by (res_inst_tac [("m","k"),("n","i")] diff_induct 1);
by (ALLGOALS (strip_tac THEN' simp_tac arith_ss THEN' TRY o fast_tac HOL_cs));
qed "zero_induct_lemma";

val prems = goal Arith.thy "[| P(k);  !!n. P(Suc(n)) ==> P(n) |] ==> P(0)";
by (rtac (diff_self_eq_0 RS subst) 1);
by (rtac (zero_induct_lemma RS mp RS mp) 1);
by (REPEAT (ares_tac ([impI,allI]@prems) 1));
qed "zero_induct";

(*13 July 1992: loaded in 105.7s*)

(**** Additional theorems about "less than" ****)

goal Arith.thy "!!m. m<n --> (? k. n=Suc(m+k))";
by (nat_ind_tac "n" 1);
by (ALLGOALS(simp_tac arith_ss));
by (REPEAT_FIRST (ares_tac [conjI, impI]));
by (res_inst_tac [("x","0")] exI 2);
by (simp_tac arith_ss 2);
by (safe_tac HOL_cs);
by (res_inst_tac [("x","Suc(k)")] exI 1);
by (simp_tac arith_ss 1);
val less_eq_Suc_add_lemma = result();

(*"m<n ==> ? k. n = Suc(m+k)"*)
bind_thm ("less_eq_Suc_add", less_eq_Suc_add_lemma RS mp);


goal Arith.thy "n <= ((m + n)::nat)";
by (nat_ind_tac "m" 1);
by (ALLGOALS(simp_tac arith_ss));
by (etac le_trans 1);
by (rtac (lessI RS less_imp_le) 1);
qed "le_add2";

goal Arith.thy "n <= ((n + m)::nat)";
by (simp_tac (arith_ss addsimps add_ac) 1);
by (rtac le_add2 1);
qed "le_add1";

bind_thm ("less_add_Suc1", (lessI RS (le_add1 RS le_less_trans)));
bind_thm ("less_add_Suc2", (lessI RS (le_add2 RS le_less_trans)));

(*"i <= j ==> i <= j+m"*)
bind_thm ("trans_le_add1", le_add1 RSN (2,le_trans));

(*"i <= j ==> i <= m+j"*)
bind_thm ("trans_le_add2", le_add2 RSN (2,le_trans));

(*"i < j ==> i < j+m"*)
bind_thm ("trans_less_add1", le_add1 RSN (2,less_le_trans));

(*"i < j ==> i < m+j"*)
bind_thm ("trans_less_add2", le_add2 RSN (2,less_le_trans));

goal Arith.thy "!!k::nat. m <= n ==> m <= n+k";
by (eresolve_tac [le_trans] 1);
by (resolve_tac [le_add1] 1);
qed "le_imp_add_le";

goal Arith.thy "!!k::nat. m < n ==> m < n+k";
by (eresolve_tac [less_le_trans] 1);
by (resolve_tac [le_add1] 1);
qed "less_imp_add_less";

goal Arith.thy "m+k<=n --> m<=(n::nat)";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac arith_ss));
by (fast_tac (HOL_cs addDs [Suc_leD]) 1);
val add_leD1_lemma = result();
bind_thm ("add_leD1", add_leD1_lemma RS mp);;

goal Arith.thy "!!k l::nat. [| k<l; m+l = k+n |] ==> m<n";
by (safe_tac (HOL_cs addSDs [less_eq_Suc_add]));
by (asm_full_simp_tac
    (HOL_ss addsimps ([add_Suc_right RS sym, add_left_cancel] @add_ac)) 1);
by (eresolve_tac [subst] 1);
by (simp_tac (arith_ss addsimps [less_add_Suc1]) 1);
qed "less_add_eq_less";


(** Monotonicity of addition (from ZF/Arith) **)

(** Monotonicity results **)

(*strict, in 1st argument*)
goal Arith.thy "!!i j k::nat. i < j ==> i + k < j + k";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac arith_ss));
qed "add_less_mono1";

(*strict, in both arguments*)
goal Arith.thy "!!i j k::nat. [|i < j; k < l|] ==> i + k < j + l";
by (rtac (add_less_mono1 RS less_trans) 1);
by (REPEAT (etac asm_rl 1));
by (nat_ind_tac "j" 1);
by (ALLGOALS(asm_simp_tac arith_ss));
qed "add_less_mono";

(*A [clumsy] way of lifting < monotonicity to <= monotonicity *)
val [lt_mono,le] = goal Arith.thy
     "[| !!i j::nat. i<j ==> f(i) < f(j);	\
\        i <= j					\
\     |] ==> f(i) <= (f(j)::nat)";
by (cut_facts_tac [le] 1);
by (asm_full_simp_tac (HOL_ss addsimps [le_eq_less_or_eq]) 1);
by (fast_tac (HOL_cs addSIs [lt_mono]) 1);
qed "less_mono_imp_le_mono";

(*non-strict, in 1st argument*)
goal Arith.thy "!!i j k::nat. i<=j ==> i + k <= j + k";
by (res_inst_tac [("f", "%j.j+k")] less_mono_imp_le_mono 1);
by (eresolve_tac [add_less_mono1] 1);
by (assume_tac 1);
qed "add_le_mono1";

(*non-strict, in both arguments*)
goal Arith.thy "!!k l::nat. [|i<=j;  k<=l |] ==> i + k <= j + l";
by (etac (add_le_mono1 RS le_trans) 1);
by (simp_tac (HOL_ss addsimps [add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (eresolve_tac [add_le_mono1] 1);
qed "add_le_mono";
