(*  Title:      HOL/Arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Proofs about elementary arithmetic: addition, multiplication, etc.
Tests definitions and simplifier.
*)

open Arith;

(*** Basic rewrite rules for the arithmetic operators ***)

val [pred_0, pred_Suc] = nat_recs pred_def;
val [add_0,add_Suc] = nat_recs add_def; 
val [mult_0,mult_Suc] = nat_recs mult_def;
store_thm("pred_0",pred_0);
store_thm("pred_Suc",pred_Suc);
store_thm("add_0",add_0);
store_thm("add_Suc",add_Suc);
store_thm("mult_0",mult_0);
store_thm("mult_Suc",mult_Suc);
Addsimps [pred_0,pred_Suc,add_0,add_Suc,mult_0,mult_Suc];

(** pred **)

val prems = goal Arith.thy "n ~= 0 ==> Suc(pred n) = n";
by (res_inst_tac [("n","n")] natE 1);
by (cut_facts_tac prems 1);
by (ALLGOALS Asm_full_simp_tac);
qed "Suc_pred";
Addsimps [Suc_pred];

(** Difference **)

bind_thm("diff_0", diff_def RS def_nat_rec_0);

qed_goalw "diff_0_eq_0" Arith.thy [diff_def, pred_def]
    "0 - n = 0"
 (fn _ => [nat_ind_tac "n" 1,  ALLGOALS Asm_simp_tac]);

(*Must simplify BEFORE the induction!!  (Else we get a critical pair)
  Suc(m) - Suc(n)   rewrites to   pred(Suc(m) - n)  *)
qed_goalw "diff_Suc_Suc" Arith.thy [diff_def, pred_def]
    "Suc(m) - Suc(n) = m - n"
 (fn _ =>
  [Simp_tac 1, nat_ind_tac "n" 1, ALLGOALS Asm_simp_tac]);

Addsimps [diff_0, diff_0_eq_0, diff_Suc_Suc];


goal Arith.thy "!!k. 0<k ==> EX j. k = Suc(j)";
by (etac rev_mp 1);
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (Fast_tac 1);
val lemma = result();

(* [| 0 < k; !!j. [| j: nat; k = succ(j) |] ==> Q |] ==> Q *)
bind_thm ("zero_less_natE", lemma RS exE);



(**** Inductive properties of the operators ****)

(*** Addition ***)

qed_goal "add_0_right" Arith.thy "m + 0 = m"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "add_Suc_right" Arith.thy "m + Suc(n) = Suc(m+n)"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

Addsimps [add_0_right,add_Suc_right];

(*Associative law for addition*)
qed_goal "add_assoc" Arith.thy "(m + n) + k = m + ((n + k)::nat)"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*Commutative law for addition*)  
qed_goal "add_commute" Arith.thy "m + n = n + (m::nat)"
 (fn _ =>  [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "add_left_commute" Arith.thy "x+(y+z)=y+((x+z)::nat)"
 (fn _ => [rtac (add_commute RS trans) 1, rtac (add_assoc RS trans) 1,
           rtac (add_commute RS arg_cong) 1]);

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

goal Arith.thy "!!k::nat. (k + m = k + n) = (m=n)";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel";

goal Arith.thy "!!k::nat. (m + k = n + k) = (m=n)";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_right_cancel";

goal Arith.thy "!!k::nat. (k + m <= k + n) = (m<=n)";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel_le";

goal Arith.thy "!!k::nat. (k + m < k + n) = (m<n)";
by (nat_ind_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel_less";

Addsimps [add_left_cancel, add_right_cancel,
          add_left_cancel_le, add_left_cancel_less];

goal Arith.thy "(m+n = 0) = (m=0 & n=0)";
by (nat_ind_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_is_0";
Addsimps [add_is_0];

goal Arith.thy "!!n. n ~= 0 ==> m + pred n = pred(m+n)";
by (nat_ind_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_pred";
Addsimps [add_pred];

(*** Multiplication ***)

(*right annihilation in product*)
qed_goal "mult_0_right" Arith.thy "m * 0 = 0"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*right Sucessor law for multiplication*)
qed_goal "mult_Suc_right" Arith.thy  "m * Suc(n) = m + (m * n)"
 (fn _ => [nat_ind_tac "m" 1,
           ALLGOALS(asm_simp_tac (!simpset addsimps add_ac))]);

Addsimps [mult_0_right,mult_Suc_right];

(*Commutative law for multiplication*)
qed_goal "mult_commute" Arith.thy "m * n = n * (m::nat)"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*addition distributes over multiplication*)
qed_goal "add_mult_distrib" Arith.thy "(m + n)*k = (m*k) + ((n*k)::nat)"
 (fn _ => [nat_ind_tac "m" 1,
           ALLGOALS(asm_simp_tac (!simpset addsimps add_ac))]);

qed_goal "add_mult_distrib2" Arith.thy "k*(m + n) = (k*m) + ((k*n)::nat)"
 (fn _ => [nat_ind_tac "m" 1,
           ALLGOALS(asm_simp_tac (!simpset addsimps add_ac))]);

Addsimps [add_mult_distrib,add_mult_distrib2];

(*Associative law for multiplication*)
qed_goal "mult_assoc" Arith.thy "(m * n) * k = m * ((n * k)::nat)"
  (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "mult_left_commute" Arith.thy "x*(y*z) = y*((x*z)::nat)"
 (fn _ => [rtac trans 1, rtac mult_commute 1, rtac trans 1,
           rtac mult_assoc 1, rtac (mult_commute RS arg_cong) 1]);

val mult_ac = [mult_assoc,mult_commute,mult_left_commute];

(*** Difference ***)

qed_goal "diff_self_eq_0" Arith.thy "m - m = 0"
 (fn _ => [nat_ind_tac "m" 1, ALLGOALS Asm_simp_tac]);
Addsimps [diff_self_eq_0];

(*Addition is the inverse of subtraction: if n<=m then n+(m-n) = m. *)
val [prem] = goal Arith.thy "[| ~ m<n |] ==> n+(m-n) = (m::nat)";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (Asm_simp_tac));
qed "add_diff_inverse";


(*** Remainder ***)

goal Arith.thy "m - n < Suc(m)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (etac less_SucE 3);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [less_Suc_eq])));
qed "diff_less_Suc";

goal Arith.thy "!!m::nat. m - n <= m";
by (res_inst_tac [("m","m"), ("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_le_self";

goal Arith.thy "!!n::nat. (n+m) - n = m";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_inverse";

goal Arith.thy "!!n::nat.(m+n) - n = m";
by (res_inst_tac [("m1","m")] (add_commute RS ssubst) 1);
by (REPEAT (ares_tac [diff_add_inverse] 1));
qed "diff_add_inverse2";

goal Arith.thy "!!k::nat. (k+m) - (k+n) = m - n";
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_cancel";
Addsimps [diff_cancel];

goal Arith.thy "!!m::nat. (m+k) - (n+k) = m - n";
val add_commute_k = read_instantiate [("n","k")] add_commute;
by (asm_simp_tac (!simpset addsimps ([add_commute_k])) 1);
qed "diff_cancel2";
Addsimps [diff_cancel2];

goal Arith.thy "!!n::nat. n - (n+m) = 0";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_0";
Addsimps [diff_add_0];

(** Difference distributes over multiplication **)

goal Arith.thy "!!m::nat. (m - n) * k = (m * k) - (n * k)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_mult_distrib" ;

goal Arith.thy "!!m::nat. k * (m - n) = (k * m) - (k * n)";
val mult_commute_k = read_instantiate [("m","k")] mult_commute;
by (simp_tac (!simpset addsimps [diff_mult_distrib, mult_commute_k]) 1);
qed "diff_mult_distrib2" ;
(*NOT added as rewrites, since sometimes they are used from right-to-left*)


(** Less-then properties **)

(*In ordinary notation: if 0<n and n<=m then m-n < m *)
goal Arith.thy "!!m. [| 0<n; ~ m<n |] ==> m - n < m";
by (subgoal_tac "0<n --> ~ m<n --> m - n < m" 1);
by (Fast_tac 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac(!simpset addsimps [diff_less_Suc])));
qed "diff_less";

val wf_less_trans = wf_pred_nat RS wf_trancl RSN (2, def_wfrec RS trans);

goalw Nat.thy [less_def] "(m,n) : pred_nat^+ = (m<n)";
by (rtac refl 1);
qed "less_eq";

goal Arith.thy "(%m. m mod n) = wfrec (trancl pred_nat) \
             \                      (%f j. if j<n then j else f (j-n))";
by (simp_tac (HOL_ss addsimps [mod_def]) 1);
val mod_def1 = result() RS eq_reflection;

goal Arith.thy "!!m. m<n ==> m mod n = m";
by (rtac (mod_def1 RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "mod_less";

goal Arith.thy "!!m. [| 0<n;  ~m<n |] ==> m mod n = (m-n) mod n";
by (rtac (mod_def1 RS wf_less_trans) 1);
by (asm_simp_tac (!simpset addsimps [diff_less, cut_apply, less_eq]) 1);
qed "mod_geq";


(*** Quotient ***)

goal Arith.thy "(%m. m div n) = wfrec (trancl pred_nat) \
                        \            (%f j. if j<n then 0 else Suc (f (j-n)))";
by (simp_tac (HOL_ss addsimps [div_def]) 1);
val div_def1 = result() RS eq_reflection;

goal Arith.thy "!!m. m<n ==> m div n = 0";
by (rtac (div_def1 RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "div_less";

goal Arith.thy "!!M. [| 0<n;  ~m<n |] ==> m div n = Suc((m-n) div n)";
by (rtac (div_def1 RS wf_less_trans) 1);
by (asm_simp_tac (!simpset addsimps [diff_less, cut_apply, less_eq]) 1);
qed "div_geq";

(*Main Result about quotient and remainder.*)
goal Arith.thy "!!m. 0<n ==> (m div n)*n + m mod n = m";
by (res_inst_tac [("n","m")] less_induct 1);
by (rename_tac "k" 1);    (*Variable name used in line below*)
by (case_tac "k<n" 1);
by (ALLGOALS (asm_simp_tac(!simpset addsimps ([add_assoc] @
                       [mod_less, mod_geq, div_less, div_geq,
                        add_diff_inverse, diff_less]))));
qed "mod_div_equality";


(*** More results about difference ***)

val [prem] = goal Arith.thy "m < Suc(n) ==> m-n = 0";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (asm_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (ALLGOALS (Asm_simp_tac));
qed "less_imp_diff_is_0";

val prems = goal Arith.thy "m-n = 0  -->  n-m = 0  -->  m=n";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (REPEAT(Simp_tac 1 THEN TRY(atac 1)));
qed_spec_mp "diffs0_imp_equal";

val [prem] = goal Arith.thy "m<n ==> 0<n-m";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (Asm_simp_tac));
qed "less_imp_diff_positive";

val [prem] = goal Arith.thy "n < Suc(m) ==> Suc(m)-n = Suc(m-n)";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (Asm_simp_tac));
qed "Suc_diff_n";

goal Arith.thy "Suc(m)-n = (if m<n then 0 else Suc(m-n))";
by (simp_tac (!simpset addsimps [less_imp_diff_is_0, not_less_eq, Suc_diff_n]
                    setloop (split_tac [expand_if])) 1);
qed "if_Suc_diff_n";

goal Arith.thy "P(k) --> (!n. P(Suc(n))--> P(n)) --> P(k-i)";
by (res_inst_tac [("m","k"),("n","i")] diff_induct 1);
by (ALLGOALS (strip_tac THEN' Simp_tac THEN' TRY o Fast_tac));
qed "zero_induct_lemma";

val prems = goal Arith.thy "[| P(k);  !!n. P(Suc(n)) ==> P(n) |] ==> P(0)";
by (rtac (diff_self_eq_0 RS subst) 1);
by (rtac (zero_induct_lemma RS mp RS mp) 1);
by (REPEAT (ares_tac ([impI,allI]@prems) 1));
qed "zero_induct";

(*13 July 1992: loaded in 105.7s*)


(*** Further facts about mod (mainly for mutilated checkerboard ***)

goal Arith.thy
    "!!m n. 0<n ==> \
\           Suc(m) mod n = (if Suc(m mod n) = n then 0 else Suc(m mod n))";
by (res_inst_tac [("n","m")] less_induct 1);
by (excluded_middle_tac "Suc(na)<n" 1);
(* case Suc(na) < n *)
by (forward_tac [lessI RS less_trans] 2);
by (asm_simp_tac (!simpset addsimps [mod_less, less_not_refl2 RS not_sym]) 2);
(* case n <= Suc(na) *)
by (asm_full_simp_tac (!simpset addsimps [not_less_iff_le, mod_geq]) 1);
by (etac (le_imp_less_or_eq RS disjE) 1);
by (asm_simp_tac (!simpset addsimps [Suc_diff_n]) 1);
by (asm_full_simp_tac (!simpset addsimps [not_less_eq RS sym, 
                                          diff_less, mod_geq]) 1);
by (asm_simp_tac (!simpset addsimps [mod_less]) 1);
qed "mod_Suc";

goal Arith.thy "!!m n. 0<n ==> m mod n < n";
by (res_inst_tac [("n","m")] less_induct 1);
by (excluded_middle_tac "na<n" 1);
(*case na<n*)
by (asm_simp_tac (!simpset addsimps [mod_less]) 2);
(*case n le na*)
by (asm_full_simp_tac (!simpset addsimps [mod_geq, diff_less]) 1);
qed "mod_less_divisor";


(** Evens and Odds **)

val less_cs = set_cs addSEs [less_zeroE, less_SucE];

AddSEs [less_zeroE, less_SucE];

goal thy "!!k b. b<2 ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)";
by (subgoal_tac "k mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Fast_tac 1);
qed "mod2_cases";

goal thy "Suc(Suc(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (safe_tac less_cs);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mod_Suc])));
qed "mod2_Suc_Suc";
Addsimps [mod2_Suc_Suc];

goal thy "(m+m) mod 2 = 0";
by (nat_ind_tac "m" 1);
by (simp_tac (!simpset addsimps [mod_less]) 1);
by (asm_simp_tac (!simpset addsimps [mod2_Suc_Suc, add_Suc_right]) 1);
qed "mod2_add_self";
Addsimps [mod2_add_self];


(**** Additional theorems about "less than" ****)

goal Arith.thy "!!m. m<n --> (? k. n=Suc(m+k))";
by (nat_ind_tac "n" 1);
by (Simp_tac 1);
by (simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (REPEAT_FIRST (ares_tac [conjI, impI]));
by (res_inst_tac [("x","0")] exI 2);
by (Simp_tac 2);
by (safe_tac HOL_cs);
by (res_inst_tac [("x","Suc(k)")] exI 1);
by (Simp_tac 1);
qed_spec_mp "less_eq_Suc_add";

goal Arith.thy "n <= ((m + n)::nat)";
by (nat_ind_tac "m" 1);
by (ALLGOALS Simp_tac);
by (etac le_trans 1);
by (rtac (lessI RS less_imp_le) 1);
qed "le_add2";

goal Arith.thy "n <= ((n + m)::nat)";
by (simp_tac (!simpset addsimps add_ac) 1);
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

goal Arith.thy "!!i. i+j < (k::nat) ==> i<k";
by (etac rev_mp 1);
by (nat_ind_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addDs [Suc_lessD]) 1);
qed "add_lessD1";

goal Arith.thy "!!k::nat. m <= n ==> m <= n+k";
by (etac le_trans 1);
by (rtac le_add1 1);
qed "le_imp_add_le";

goal Arith.thy "!!k::nat. m < n ==> m < n+k";
by (etac less_le_trans 1);
by (rtac le_add1 1);
qed "less_imp_add_less";

goal Arith.thy "m+k<=n --> m<=(n::nat)";
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
by (fast_tac (!claset addDs [Suc_leD]) 1);
qed_spec_mp "add_leD1";

goal Arith.thy "!!k l::nat. [| k<l; m+l = k+n |] ==> m<n";
by (safe_tac (HOL_cs addSDs [less_eq_Suc_add]));
by (asm_full_simp_tac
    (!simpset delsimps [add_Suc_right]
                addsimps ([add_Suc_right RS sym, add_left_cancel] @add_ac)) 1);
by (etac subst 1);
by (simp_tac (!simpset addsimps [less_add_Suc1]) 1);
qed "less_add_eq_less";


(*** Monotonicity of Addition ***)

(*strict, in 1st argument*)
goal Arith.thy "!!i j k::nat. i < j ==> i + k < j + k";
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono1";

(*strict, in both arguments*)
goal Arith.thy "!!i j k::nat. [|i < j; k < l|] ==> i + k < j + l";
by (rtac (add_less_mono1 RS less_trans) 1);
by (REPEAT (assume_tac 1));
by (nat_ind_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono";

(*A [clumsy] way of lifting < monotonicity to <= monotonicity *)
val [lt_mono,le] = goal Arith.thy
     "[| !!i j::nat. i<j ==> f(i) < f(j);       \
\        i <= j                                 \
\     |] ==> f(i) <= (f(j)::nat)";
by (cut_facts_tac [le] 1);
by (asm_full_simp_tac (!simpset addsimps [le_eq_less_or_eq]) 1);
by (fast_tac (!claset addSIs [lt_mono]) 1);
qed "less_mono_imp_le_mono";

(*non-strict, in 1st argument*)
goal Arith.thy "!!i j k::nat. i<=j ==> i + k <= j + k";
by (res_inst_tac [("f", "%j.j+k")] less_mono_imp_le_mono 1);
by (etac add_less_mono1 1);
by (assume_tac 1);
qed "add_le_mono1";

(*non-strict, in both arguments*)
goal Arith.thy "!!k l::nat. [|i<=j;  k<=l |] ==> i + k <= j + l";
by (etac (add_le_mono1 RS le_trans) 1);
by (simp_tac (!simpset addsimps [add_commute]) 1);
(*j moves to the end because it is free while k, l are bound*)
by (etac add_le_mono1 1);
qed "add_le_mono";

(*** Monotonicity of Multiplication ***)

goal Arith.thy "!!i::nat. i<=j ==> i*k<=j*k";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [add_le_mono])));
qed "mult_le_mono1";

(*<=monotonicity, BOTH arguments*)
goal Arith.thy "!!i::nat. [| i<=j; k<=l |] ==> i*k<=j*l";
by (rtac le_trans 1);
by (ALLGOALS 
    (deepen_tac (HOL_cs addIs [mult_commute RS ssubst, mult_le_mono1]) 0));
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0*)
goal Arith.thy "!!i::nat. [| i<j; 0<k |] ==> k*i < k*j";
be zero_less_natE 1;
by (Asm_simp_tac 1);
by (nat_ind_tac "x" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [add_less_mono])));
qed "mult_less_mono2";

goal Arith.thy "(0 < m*n) = (0<m & 0<n)";
by (nat_ind_tac "m" 1);
by (nat_ind_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_mult_iff";

(*Cancellation law for division*)
goal Arith.thy "!!k. [| 0<n; 0<k |] ==> (k*m) div (k*n) = m div n";
by (res_inst_tac [("n","m")] less_induct 1);
by (case_tac "na<n" 1);
by (asm_simp_tac (!simpset addsimps [div_less, zero_less_mult_iff, 
				     mult_less_mono2]) 1);
by (subgoal_tac "~ k*na < k*n" 1);
by (asm_simp_tac
     (!simpset addsimps [zero_less_mult_iff, div_geq,
			 diff_mult_distrib2 RS sym, diff_less]) 1);
by (asm_full_simp_tac (!simpset addsimps [not_less_iff_le, 
					  le_refl RS mult_le_mono]) 1);
qed "div_cancel";

goal Arith.thy "!!k. [| 0<n; 0<k |] ==> (k*m) mod (k*n) = k * (m mod n)";
by (res_inst_tac [("n","m")] less_induct 1);
by (case_tac "na<n" 1);
by (asm_simp_tac (!simpset addsimps [mod_less, zero_less_mult_iff, 
				     mult_less_mono2]) 1);
by (subgoal_tac "~ k*na < k*n" 1);
by (asm_simp_tac
     (!simpset addsimps [zero_less_mult_iff, mod_geq,
			 diff_mult_distrib2 RS sym, diff_less]) 1);
by (asm_full_simp_tac (!simpset addsimps [not_less_iff_le, 
					  le_refl RS mult_le_mono]) 1);
qed "mult_mod_distrib";


