(*  Title:      HOL/Divides.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)


(** Less-then properties **)

(*In ordinary notation: if 0<n and n<=m then m-n < m *)
goal Arith.thy "!!m. [| 0<n; ~ m<n |] ==> m - n < m";
by (subgoal_tac "0<n --> ~ m<n --> m - n < m" 1);
by (Blast_tac 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac(simpset() addsimps [diff_less_Suc])));
qed "diff_less";

val wf_less_trans = [eq_reflection, wf_pred_nat RS wf_trancl] MRS 
                    def_wfrec RS trans;

(*** Remainder ***)

goal thy "(%m. m mod n) = wfrec (trancl pred_nat) \
             \                      (%f j. if j<n then j else f (j-n))";
by (simp_tac (simpset() addsimps [mod_def]) 1);
qed "mod_eq";

goal thy "!!m. m<n ==> m mod n = m";
by (rtac (mod_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "mod_less";

goal thy "!!m. [| 0<n;  ~m<n |] ==> m mod n = (m-n) mod n";
by (rtac (mod_eq RS wf_less_trans) 1);
by (asm_simp_tac (simpset() addsimps [diff_less, cut_apply, less_eq]) 1);
qed "mod_geq";

(*NOT suitable for rewriting: loops*)
goal thy "!!m. 0<n ==> m mod n = (if m<n then m else (m-n) mod n)";
by (asm_simp_tac (simpset() addsimps [mod_less, mod_geq]) 1);
qed "mod_if";

goal thy "m mod 1 = 0";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mod_less, mod_geq])));
qed "mod_1";
Addsimps [mod_1];

goal thy "!!n. 0<n ==> n mod n = 0";
by (asm_simp_tac (simpset() addsimps [mod_less, mod_geq]) 1);
qed "mod_self";

goal thy "!!n. 0<n ==> (m+n) mod n = m mod n";
by (subgoal_tac "(n + m) mod n = (n+m-n) mod n" 1);
by (stac (mod_geq RS sym) 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_commute])));
qed "mod_add_self2";

goal thy "!!k. 0<n ==> (n+m) mod n = m mod n";
by (asm_simp_tac (simpset() addsimps [add_commute, mod_add_self2]) 1);
qed "mod_add_self1";

goal thy "!!n. 0<n ==> (m + k*n) mod n = m mod n";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps (add_ac @ [mod_add_self1]))));
qed "mod_mult_self1";

goal thy "!!m. 0<n ==> (m + n*k) mod n = m mod n";
by (asm_simp_tac (simpset() addsimps [mult_commute, mod_mult_self1]) 1);
qed "mod_mult_self2";

Addsimps [mod_mult_self1, mod_mult_self2];

goal thy "!!k. [| 0<k; 0<n |] ==> (m mod n)*k = (m*k) mod (n*k)";
by (res_inst_tac [("n","m")] less_induct 1);
by (stac mod_if 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [mod_less, mod_geq, 
				      diff_less, diff_mult_distrib]) 1);
qed "mod_mult_distrib";

goal thy "!!k. [| 0<k; 0<n |] ==> k*(m mod n) = (k*m) mod (k*n)";
by (res_inst_tac [("n","m")] less_induct 1);
by (stac mod_if 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [mod_less, mod_geq, 
				      diff_less, diff_mult_distrib2]) 1);
qed "mod_mult_distrib2";

goal thy "!!n. 0<n ==> m*n mod n = 0";
by (induct_tac "m" 1);
by (asm_simp_tac (simpset() addsimps [mod_less]) 1);
by (dres_inst_tac [("m","m*n")] mod_add_self2 1);
by (asm_full_simp_tac (simpset() addsimps [add_commute]) 1);
qed "mod_mult_self_is_0";
Addsimps [mod_mult_self_is_0];

(*** Quotient ***)

goal thy "(%m. m div n) = wfrec (trancl pred_nat) \
                        \            (%f j. if j<n then 0 else Suc (f (j-n)))";
by (simp_tac (simpset() addsimps [div_def]) 1);
qed "div_eq";

goal thy "!!m. m<n ==> m div n = 0";
by (rtac (div_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "div_less";

goal thy "!!M. [| 0<n;  ~m<n |] ==> m div n = Suc((m-n) div n)";
by (rtac (div_eq RS wf_less_trans) 1);
by (asm_simp_tac (simpset() addsimps [diff_less, cut_apply, less_eq]) 1);
qed "div_geq";

(*NOT suitable for rewriting: loops*)
goal thy "!!m. 0<n ==> m div n = (if m<n then 0 else Suc((m-n) div n))";
by (asm_simp_tac (simpset() addsimps [div_less, div_geq]) 1);
qed "div_if";

(*Main Result about quotient and remainder.*)
goal thy "!!m. 0<n ==> (m div n)*n + m mod n = m";
by (res_inst_tac [("n","m")] less_induct 1);
by (stac mod_if 1);
by (ALLGOALS (asm_simp_tac 
	      (simpset() addsimps ([add_assoc] @
				   [div_less, div_geq,
				    add_diff_inverse, diff_less]))));
qed "mod_div_equality";

(* a simple rearrangement of mod_div_equality: *)
goal thy "!!k. 0<k ==> k*(m div k) = m - (m mod k)";
by (dres_inst_tac [("m","m")] mod_div_equality 1);
by (EVERY1[etac subst, simp_tac (simpset() addsimps mult_ac),
           K(IF_UNSOLVED no_tac)]);
qed "mult_div_cancel";

goal thy "m div 1 = m";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [div_less, div_geq])));
qed "div_1";
Addsimps [div_1];

goal thy "!!n. 0<n ==> n div n = 1";
by (asm_simp_tac (simpset() addsimps [div_less, div_geq]) 1);
qed "div_self";


goal thy "!!n. 0<n ==> (m+n) div n = Suc (m div n)";
by (subgoal_tac "(n + m) div n = Suc ((n+m-n) div n)" 1);
by (stac (div_geq RS sym) 2);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [add_commute])));
qed "div_add_self2";

goal thy "!!k. 0<n ==> (n+m) div n = Suc (m div n)";
by (asm_simp_tac (simpset() addsimps [add_commute, div_add_self2]) 1);
qed "div_add_self1";

goal thy "!!n. 0<n ==> (m + k*n) div n = k + m div n";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps (add_ac @ [div_add_self1]))));
qed "div_mult_self1";

goal thy "!!m. 0<n ==> (m + n*k) div n = k + m div n";
by (asm_simp_tac (simpset() addsimps [mult_commute, div_mult_self1]) 1);
qed "div_mult_self2";

Addsimps [div_mult_self1, div_mult_self2];


(* Monotonicity of div in first argument *)
goal thy "!!n. 0<k ==> ALL m. m <= n --> (m div k) <= (n div k)";
by (res_inst_tac [("n","n")] less_induct 1);
by (Clarify_tac 1);
by (case_tac "na<k" 1);
(* 1  case n<k *)
by (subgoal_tac "m<k" 1);
by (asm_simp_tac (simpset() addsimps [div_less]) 1);
by (trans_tac 1);
(* 2  case n >= k *)
by (case_tac "m<k" 1);
(* 2.1  case m<k *)
by (asm_simp_tac (simpset() addsimps [div_less]) 1);
(* 2.2  case m>=k *)
by (asm_simp_tac (simpset() addsimps [div_geq, diff_less, diff_le_mono]) 1);
qed_spec_mp "div_le_mono";


(* Antimonotonicity of div in second argument *)
goal thy "!!k m n. [| 0<m; m<=n |] ==> (k div n) <= (k div m)";
by (subgoal_tac "0<n" 1);
 by (trans_tac 2);
by (res_inst_tac [("n","k")] less_induct 1);
by (Simp_tac 1);
by (rename_tac "k" 1);
by (case_tac "k<n" 1);
 by (asm_simp_tac (simpset() addsimps [div_less]) 1);
by (subgoal_tac "~(k<m)" 1);
 by (trans_tac 2);
by (asm_simp_tac (simpset() addsimps [div_geq]) 1);
by (subgoal_tac "(k-n) div n <= (k-m) div n" 1);
 by (best_tac (claset() addIs [le_trans] 
                       addss (simpset() addsimps [diff_less])) 1);
by (REPEAT (eresolve_tac [div_le_mono,diff_le_mono2] 1));
qed "div_le_mono2";

goal thy "!!m n. 0<n ==> m div n <= m";
by (subgoal_tac "m div n <= m div 1" 1);
by (Asm_full_simp_tac 1);
by (rtac div_le_mono2 1);
by (ALLGOALS trans_tac);
qed "div_le_dividend";
Addsimps [div_le_dividend];

(* Similar for "less than" *)
goal thy "!!m n. 1<n ==> (0 < m) --> (m div n < m)";
by (res_inst_tac [("n","m")] less_induct 1);
by (Simp_tac 1);
by (rename_tac "m" 1);
by (case_tac "m<n" 1);
 by (asm_full_simp_tac (simpset() addsimps [div_less]) 1);
by (subgoal_tac "0<n" 1);
 by (trans_tac 2);
by (asm_full_simp_tac (simpset() addsimps [div_geq]) 1);
by (case_tac "n<m" 1);
 by (subgoal_tac "(m-n) div n < (m-n)" 1);
  by (REPEAT (ares_tac [impI,less_trans_Suc] 1));
  by (asm_full_simp_tac (simpset() addsimps [diff_less]) 1);
 by (dres_inst_tac [("m","n")] less_imp_diff_positive 1);
 by (asm_full_simp_tac (simpset() addsimps [diff_less]) 1);
(* case n=m *)
by (subgoal_tac "m=n" 1);
 by (trans_tac 2);
by (asm_simp_tac (simpset() addsimps [div_less]) 1);
qed_spec_mp "div_less_dividend";
Addsimps [div_less_dividend];

(*** Further facts about mod (mainly for the mutilated chess board ***)

goal thy
    "!!m n. 0<n ==> \
\           Suc(m) mod n = (if Suc(m mod n) = n then 0 else Suc(m mod n))";
by (res_inst_tac [("n","m")] less_induct 1);
by (excluded_middle_tac "Suc(na)<n" 1);
(* case Suc(na) < n *)
by (forward_tac [lessI RS less_trans] 2);
by (asm_simp_tac (simpset() addsimps [mod_less, less_not_refl2 RS not_sym]) 2);
(* case n <= Suc(na) *)
by (asm_full_simp_tac (simpset() addsimps [not_less_iff_le, mod_geq]) 1);
by (etac (le_imp_less_or_eq RS disjE) 1);
by (asm_simp_tac (simpset() addsimps [Suc_diff_n]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_less_eq RS sym, 
                                          diff_less, mod_geq]) 1);
by (asm_simp_tac (simpset() addsimps [mod_less]) 1);
qed "mod_Suc";

goal thy "!!m n. 0<n ==> m mod n < n";
by (res_inst_tac [("n","m")] less_induct 1);
by (excluded_middle_tac "na<n" 1);
(*case na<n*)
by (asm_simp_tac (simpset() addsimps [mod_less]) 2);
(*case n le na*)
by (asm_full_simp_tac (simpset() addsimps [mod_geq, diff_less]) 1);
qed "mod_less_divisor";


(** Evens and Odds **)

(*With less_zeroE, causes case analysis on b<2*)
AddSEs [less_SucE];

goal thy "!!k b. b<2 ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)";
by (subgoal_tac "k mod 2 < 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor]) 2);
by (Asm_simp_tac 1);
by Safe_tac;
qed "mod2_cases";

goal thy "Suc(Suc(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2 < 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor]) 2);
by Safe_tac;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mod_Suc])));
qed "mod2_Suc_Suc";
Addsimps [mod2_Suc_Suc];

goal Divides.thy "(0 < m mod 2) = (m mod 2 = 1)";
by (subgoal_tac "m mod 2 < 2" 1);
by (asm_simp_tac (simpset() addsimps [mod_less_divisor]) 2);
by Auto_tac;
qed "mod2_gr_0";
Addsimps [mod2_gr_0];

goal thy "(m+m) mod 2 = 0";
by (induct_tac "m" 1);
by (simp_tac (simpset() addsimps [mod_less]) 1);
by (Asm_simp_tac 1);
qed "mod2_add_self_eq_0";
Addsimps [mod2_add_self_eq_0];

goal thy "((m+m)+n) mod 2 = n mod 2";
by (induct_tac "m" 1);
by (simp_tac (simpset() addsimps [mod_less]) 1);
by (Asm_simp_tac 1);
qed "mod2_add_self";
Addsimps [mod2_add_self];

Delrules [less_SucE];


(*** More division laws ***)

goal thy "!!n. 0<n ==> m*n div n = m";
by (cut_inst_tac [("m", "m*n")] mod_div_equality 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [mod_mult_self_is_0]) 1);
qed "div_mult_self_is_m";
Addsimps [div_mult_self_is_m];

(*Cancellation law for division*)
goal thy "!!k. [| 0<n; 0<k |] ==> (k*m) div (k*n) = m div n";
by (res_inst_tac [("n","m")] less_induct 1);
by (case_tac "na<n" 1);
by (asm_simp_tac (simpset() addsimps [div_less, zero_less_mult_iff, 
                                     mult_less_mono2]) 1);
by (subgoal_tac "~ k*na < k*n" 1);
by (asm_simp_tac
     (simpset() addsimps [zero_less_mult_iff, div_geq,
                         diff_mult_distrib2 RS sym, diff_less]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_less_iff_le, 
                                          le_refl RS mult_le_mono]) 1);
qed "div_cancel";
Addsimps [div_cancel];

goal thy "!!k. [| 0<n; 0<k |] ==> (k*m) mod (k*n) = k * (m mod n)";
by (res_inst_tac [("n","m")] less_induct 1);
by (case_tac "na<n" 1);
by (asm_simp_tac (simpset() addsimps [mod_less, zero_less_mult_iff, 
                                     mult_less_mono2]) 1);
by (subgoal_tac "~ k*na < k*n" 1);
by (asm_simp_tac
     (simpset() addsimps [zero_less_mult_iff, mod_geq,
                         diff_mult_distrib2 RS sym, diff_less]) 1);
by (asm_full_simp_tac (simpset() addsimps [not_less_iff_le, 
                                          le_refl RS mult_le_mono]) 1);
qed "mult_mod_distrib";


(************************************************)
(** Divides Relation                           **)
(************************************************)

goalw thy [dvd_def] "m dvd 0";
by (blast_tac (claset() addIs [mult_0_right RS sym]) 1);
qed "dvd_0_right";
Addsimps [dvd_0_right];

goalw thy [dvd_def] "!!m. 0 dvd m ==> m = 0";
by (fast_tac (claset() addss simpset()) 1);
qed "dvd_0_left";

goalw thy [dvd_def] "1 dvd k";
by (Simp_tac 1);
qed "dvd_1_left";
AddIffs [dvd_1_left];

goalw thy [dvd_def] "m dvd m";
by (blast_tac (claset() addIs [mult_1_right RS sym]) 1);
qed "dvd_refl";
Addsimps [dvd_refl];

goalw thy [dvd_def] "!!m n p. [| m dvd n; n dvd p |] ==> m dvd p";
by (blast_tac (claset() addIs [mult_assoc] ) 1);
qed "dvd_trans";

goalw thy [dvd_def] "!!m n. [| m dvd n; n dvd m |] ==> m=n";
by (fast_tac (claset() addDs [mult_eq_self_implies_10]
                     addss (simpset() addsimps [mult_assoc, mult_eq_1_iff])) 1);
qed "dvd_anti_sym";

goalw thy [dvd_def] "!!k. [| k dvd m; k dvd n |] ==> k dvd (m + n)";
by (blast_tac (claset() addIs [add_mult_distrib2 RS sym]) 1);
qed "dvd_add";

goalw thy [dvd_def] "!!k. [| k dvd m; k dvd n |] ==> k dvd (m-n)";
by (blast_tac (claset() addIs [diff_mult_distrib2 RS sym]) 1);
qed "dvd_diff";

goal thy "!!k. [| k dvd (m-n); k dvd n; n<=m |] ==> k dvd m";
by (etac (not_less_iff_le RS iffD2 RS add_diff_inverse RS subst) 1);
by (blast_tac (claset() addIs [dvd_add]) 1);
qed "dvd_diffD";

goalw thy [dvd_def] "!!k. k dvd n ==> k dvd (m*n)";
by (blast_tac (claset() addIs [mult_left_commute]) 1);
qed "dvd_mult";

goal thy "!!k. k dvd m ==> k dvd (m*n)";
by (stac mult_commute 1);
by (etac dvd_mult 1);
qed "dvd_mult2";

(* k dvd (m*k) *)
AddIffs [dvd_refl RS dvd_mult, dvd_refl RS dvd_mult2];

goalw thy [dvd_def] "!!m. [| f dvd m; f dvd n; 0<n |] ==> f dvd (m mod n)";
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsimps [zero_less_mult_iff]) 1);
by (res_inst_tac 
    [("x", "(((k div ka)*ka + k mod ka) - ((f*k) div (f*ka)) * ka)")] 
    exI 1);
by (asm_simp_tac (simpset() addsimps [diff_mult_distrib2, 
                                     mult_mod_distrib, add_mult_distrib2]) 1);
qed "dvd_mod";

goal thy "!!k. [| k dvd (m mod n); k dvd n; 0<n |] ==> k dvd m";
by (subgoal_tac "k dvd ((m div n)*n + m mod n)" 1);
by (asm_simp_tac (simpset() addsimps [dvd_add, dvd_mult]) 2);
by (asm_full_simp_tac (simpset() addsimps [mod_div_equality]) 1);
qed "dvd_mod_imp_dvd";

goalw thy [dvd_def]  "!!k m n. [| (k*m) dvd (k*n); 0<k |] ==> m dvd n";
by (etac exE 1);
by (asm_full_simp_tac (simpset() addsimps mult_ac) 1);
by (Blast_tac 1);
qed "dvd_mult_cancel";

goalw thy [dvd_def] "!!i j. [| i dvd m; j dvd n|] ==> (i*j) dvd (m*n)";
by (Clarify_tac 1);
by (res_inst_tac [("x","k*ka")] exI 1);
by (asm_simp_tac (simpset() addsimps mult_ac) 1);
qed "mult_dvd_mono";

goalw thy [dvd_def] "!!c. (i*j) dvd k ==> i dvd k";
by (full_simp_tac (simpset() addsimps [mult_assoc]) 1);
by (Blast_tac 1);
qed "dvd_mult_left";

goalw thy [dvd_def] "!!n. [| k dvd n; 0 < n |] ==> k <= n";
by (Clarify_tac 1);
by (ALLGOALS (full_simp_tac (simpset() addsimps [zero_less_mult_iff])));
by (etac conjE 1);
by (rtac le_trans 1);
by (rtac (le_refl RS mult_le_mono) 2);
by (etac Suc_leI 2);
by (Simp_tac 1);
qed "dvd_imp_le";

goalw thy [dvd_def] "!!k. 0<k ==> (k dvd n) = (n mod k = 0)";
by Safe_tac;
by (stac mult_commute 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("t","n")] (mod_div_equality RS subst) 1);
by (asm_simp_tac (simpset() addsimps [mult_commute]) 1);
by (Blast_tac 1);
qed "dvd_eq_mod_eq_0";
