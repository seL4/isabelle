(*  Title:      HOL/Arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Proofs about elementary arithmetic: addition, multiplication, etc.
Some from the Hoare example from Norbert Galm
*)

open Arith;

(*** Basic rewrite rules for the arithmetic operators ***)

goalw Arith.thy [pred_def] "pred 0 = 0";
by(Simp_tac 1);
qed "pred_0";

goalw Arith.thy [pred_def] "pred(Suc n) = n";
by(Simp_tac 1);
qed "pred_Suc";

Addsimps [pred_0,pred_Suc];

(** pred **)

val prems = goal Arith.thy "n ~= 0 ==> Suc(pred n) = n";
by (res_inst_tac [("n","n")] natE 1);
by (cut_facts_tac prems 1);
by (ALLGOALS Asm_full_simp_tac);
qed "Suc_pred";
Addsimps [Suc_pred];

(** Difference **)

qed_goalw "diff_0_eq_0" Arith.thy [pred_def]
    "0 - n = 0"
 (fn _ => [induct_tac "n" 1,  ALLGOALS Asm_simp_tac]);

(*Must simplify BEFORE the induction!!  (Else we get a critical pair)
  Suc(m) - Suc(n)   rewrites to   pred(Suc(m) - n)  *)
qed_goalw "diff_Suc_Suc" Arith.thy [pred_def]
    "Suc(m) - Suc(n) = m - n"
 (fn _ =>
  [Simp_tac 1, induct_tac "n" 1, ALLGOALS Asm_simp_tac]);

Addsimps [diff_0_eq_0, diff_Suc_Suc];


(**** Inductive properties of the operators ****)

(*** Addition ***)

qed_goal "add_0_right" Arith.thy "m + 0 = m"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "add_Suc_right" Arith.thy "m + Suc(n) = Suc(m+n)"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

Addsimps [add_0_right,add_Suc_right];

(*Associative law for addition*)
qed_goal "add_assoc" Arith.thy "(m + n) + k = m + ((n + k)::nat)"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*Commutative law for addition*)  
qed_goal "add_commute" Arith.thy "m + n = n + (m::nat)"
 (fn _ =>  [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "add_left_commute" Arith.thy "x+(y+z)=y+((x+z)::nat)"
 (fn _ => [rtac (add_commute RS trans) 1, rtac (add_assoc RS trans) 1,
           rtac (add_commute RS arg_cong) 1]);

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

goal Arith.thy "!!k::nat. (k + m = k + n) = (m=n)";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel";

goal Arith.thy "!!k::nat. (m + k = n + k) = (m=n)";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_right_cancel";

goal Arith.thy "!!k::nat. (k + m <= k + n) = (m<=n)";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel_le";

goal Arith.thy "!!k::nat. (k + m < k + n) = (m<n)";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel_less";

Addsimps [add_left_cancel, add_right_cancel,
          add_left_cancel_le, add_left_cancel_less];

(** Reasoning about m+0=0, etc. **)

goal Arith.thy "(m+n = 0) = (m=0 & n=0)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_is_0";
Addsimps [add_is_0];

goal Arith.thy "(pred (m+n) = 0) = (m=0 & pred n = 0 | pred m = 0 & n=0)";
by (induct_tac "m" 1);
by (ALLGOALS (fast_tac (!claset addss (!simpset))));
qed "pred_add_is_0";
Addsimps [pred_add_is_0];

goal Arith.thy "!!n. n ~= 0 ==> m + pred n = pred(m+n)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_pred";
Addsimps [add_pred];


(**** Additional theorems about "less than" ****)

goal Arith.thy "i<j --> (EX k. j = Suc(i+k))";
by (induct_tac "j" 1);
by (Simp_tac 1);
by (blast_tac (!claset addSEs [less_SucE] 
                       addSIs [add_0_right RS sym, add_Suc_right RS sym]) 1);
val lemma = result();

(* [| i<j;  !!x. j = Suc(i+x) ==> Q |] ==> Q *)
bind_thm ("less_natE", lemma RS mp RS exE);

goal Arith.thy "!!m. m<n --> (? k. n=Suc(m+k))";
by (induct_tac "n" 1);
by (ALLGOALS (simp_tac (!simpset addsimps [less_Suc_eq])));
by (blast_tac (!claset addSEs [less_SucE] 
                       addSIs [add_0_right RS sym, add_Suc_right RS sym]) 1);
qed_spec_mp "less_eq_Suc_add";

goal Arith.thy "n <= ((m + n)::nat)";
by (induct_tac "m" 1);
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
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (!claset addDs [Suc_lessD]) 1);
qed "add_lessD1";

goal Arith.thy "!!i::nat. ~ (i+j < i)";
br notI 1;
be (add_lessD1 RS less_irrefl) 1;
qed "not_add_less1";

goal Arith.thy "!!i::nat. ~ (j+i < i)";
by (simp_tac (!simpset addsimps [add_commute, not_add_less1]) 1);
qed "not_add_less2";
AddIffs [not_add_less1, not_add_less2];

goal Arith.thy "!!k::nat. m <= n ==> m <= n+k";
by (etac le_trans 1);
by (rtac le_add1 1);
qed "le_imp_add_le";

goal Arith.thy "!!k::nat. m < n ==> m < n+k";
by (etac less_le_trans 1);
by (rtac le_add1 1);
qed "less_imp_add_less";

goal Arith.thy "m+k<=n --> m<=(n::nat)";
by (induct_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (!claset addDs [Suc_leD]) 1);
qed_spec_mp "add_leD1";

goal Arith.thy "!!n::nat. m+k<=n ==> k<=n";
by (full_simp_tac (!simpset addsimps [add_commute]) 1);
by (etac add_leD1 1);
qed_spec_mp "add_leD2";

goal Arith.thy "!!n::nat. m+k<=n ==> m<=n & k<=n";
by (blast_tac (!claset addDs [add_leD1, add_leD2]) 1);
bind_thm ("add_leE", result() RS conjE);

goal Arith.thy "!!k l::nat. [| k<l; m+l = k+n |] ==> m<n";
by (safe_tac (!claset addSDs [less_eq_Suc_add]));
by (asm_full_simp_tac
    (!simpset delsimps [add_Suc_right]
                addsimps ([add_Suc_right RS sym, add_left_cancel] @add_ac)) 1);
by (etac subst 1);
by (simp_tac (!simpset addsimps [less_add_Suc1]) 1);
qed "less_add_eq_less";


(*** Monotonicity of Addition ***)

(*strict, in 1st argument*)
goal Arith.thy "!!i j k::nat. i < j ==> i + k < j + k";
by (induct_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono1";

(*strict, in both arguments*)
goal Arith.thy "!!i j k::nat. [|i < j; k < l|] ==> i + k < j + l";
by (rtac (add_less_mono1 RS less_trans) 1);
by (REPEAT (assume_tac 1));
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono";

(*A [clumsy] way of lifting < monotonicity to <= monotonicity *)
val [lt_mono,le] = goal Arith.thy
     "[| !!i j::nat. i<j ==> f(i) < f(j);       \
\        i <= j                                 \
\     |] ==> f(i) <= (f(j)::nat)";
by (cut_facts_tac [le] 1);
by (asm_full_simp_tac (!simpset addsimps [le_eq_less_or_eq]) 1);
by (blast_tac (!claset addSIs [lt_mono]) 1);
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


(*** Multiplication ***)

(*right annihilation in product*)
qed_goal "mult_0_right" Arith.thy "m * 0 = 0"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*right successor law for multiplication*)
qed_goal "mult_Suc_right" Arith.thy  "m * Suc(n) = m + (m * n)"
 (fn _ => [induct_tac "m" 1,
           ALLGOALS(asm_simp_tac (!simpset addsimps add_ac))]);

Addsimps [mult_0_right, mult_Suc_right];

goal Arith.thy "1 * n = n";
by (Asm_simp_tac 1);
qed "mult_1";

goal Arith.thy "n * 1 = n";
by (Asm_simp_tac 1);
qed "mult_1_right";

(*Commutative law for multiplication*)
qed_goal "mult_commute" Arith.thy "m * n = n * (m::nat)"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*addition distributes over multiplication*)
qed_goal "add_mult_distrib" Arith.thy "(m + n)*k = (m*k) + ((n*k)::nat)"
 (fn _ => [induct_tac "m" 1,
           ALLGOALS(asm_simp_tac (!simpset addsimps add_ac))]);

qed_goal "add_mult_distrib2" Arith.thy "k*(m + n) = (k*m) + ((k*n)::nat)"
 (fn _ => [induct_tac "m" 1,
           ALLGOALS(asm_simp_tac (!simpset addsimps add_ac))]);

(*Associative law for multiplication*)
qed_goal "mult_assoc" Arith.thy "(m * n) * k = m * ((n * k)::nat)"
  (fn _ => [induct_tac "m" 1, 
            ALLGOALS (asm_simp_tac (!simpset addsimps [add_mult_distrib]))]);

qed_goal "mult_left_commute" Arith.thy "x*(y*z) = y*((x*z)::nat)"
 (fn _ => [rtac trans 1, rtac mult_commute 1, rtac trans 1,
           rtac mult_assoc 1, rtac (mult_commute RS arg_cong) 1]);

val mult_ac = [mult_assoc,mult_commute,mult_left_commute];

goal Arith.thy "(m*n = 0) = (m=0 | n=0)";
by (induct_tac "m" 1);
by (induct_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "mult_is_0";
Addsimps [mult_is_0];


(*** Difference ***)

qed_goal "pred_Suc_diff" Arith.thy "pred(Suc m - n) = m - n"
 (fn _ => [induct_tac "n" 1, ALLGOALS Asm_simp_tac]);
Addsimps [pred_Suc_diff];

qed_goal "diff_self_eq_0" Arith.thy "m - m = 0"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);
Addsimps [diff_self_eq_0];

(*Addition is the inverse of subtraction: if n<=m then n+(m-n) = m. *)
val [prem] = goal Arith.thy "~ m<n ==> n+(m-n) = (m::nat)";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "add_diff_inverse";

Delsimps  [diff_Suc];


(*** More results about difference ***)

val [prem] = goal Arith.thy "n < Suc(m) ==> Suc(m)-n = Suc(m-n)";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "Suc_diff_n";

goal Arith.thy "m - n < Suc(m)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (etac less_SucE 3);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [less_Suc_eq])));
qed "diff_less_Suc";

goal Arith.thy "!!m::nat. m - n <= m";
by (res_inst_tac [("m","m"), ("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_le_self";

goal Arith.thy "!!i::nat. i-j-k = i - (j+k)";
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_diff_left";

(*This and the next few suggested by Florian Kammüller*)
goal Arith.thy "!!i::nat. i-j-k = i-k-j";
by (simp_tac (!simpset addsimps [diff_diff_left, add_commute]) 1);
qed "diff_commute";

goal Arith.thy "!!i j k:: nat. k<=j --> j<=i --> i - (j - k) = i - j + k";
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
by (asm_simp_tac
    (!simpset addsimps [Suc_diff_n, le_imp_less_Suc, le_Suc_eq]) 1);
by (simp_tac
    (!simpset addsimps [add_diff_inverse, not_less_iff_le, add_commute]) 1);
qed_spec_mp "diff_diff_right";

goal Arith.thy "!!i j k:: nat. k<=j --> (i + j) - k = i + (j - k)";
by (res_inst_tac [("m","j"),("n","k")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "diff_add_assoc";

goal Arith.thy "!!n::nat. (n+m) - n = m";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_inverse";
Addsimps [diff_add_inverse];

goal Arith.thy "!!n::nat.(m+n) - n = m";
by (simp_tac (!simpset addsimps [diff_add_assoc]) 1);
qed "diff_add_inverse2";
Addsimps [diff_add_inverse2];

val [prem] = goal Arith.thy "m < Suc(n) ==> m-n = 0";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (asm_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (ALLGOALS Asm_simp_tac);
qed "less_imp_diff_is_0";

val prems = goal Arith.thy "m-n = 0  -->  n-m = 0  -->  m=n";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (REPEAT(Simp_tac 1 THEN TRY(atac 1)));
qed_spec_mp "diffs0_imp_equal";

val [prem] = goal Arith.thy "m<n ==> 0<n-m";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "less_imp_diff_positive";

goal Arith.thy "Suc(m)-n = (if m<n then 0 else Suc(m-n))";
by (simp_tac (!simpset addsimps [less_imp_diff_is_0, not_less_eq, Suc_diff_n]
                    setloop (split_tac [expand_if])) 1);
qed "if_Suc_diff_n";

goal Arith.thy "P(k) --> (!n. P(Suc(n))--> P(n)) --> P(k-i)";
by (res_inst_tac [("m","k"),("n","i")] diff_induct 1);
by (ALLGOALS (strip_tac THEN' Simp_tac THEN' TRY o Blast_tac));
qed "zero_induct_lemma";

val prems = goal Arith.thy "[| P(k);  !!n. P(Suc(n)) ==> P(n) |] ==> P(0)";
by (rtac (diff_self_eq_0 RS subst) 1);
by (rtac (zero_induct_lemma RS mp RS mp) 1);
by (REPEAT (ares_tac ([impI,allI]@prems) 1));
qed "zero_induct";

goal Arith.thy "!!k::nat. (k+m) - (k+n) = m - n";
by (induct_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_cancel";
Addsimps [diff_cancel];

goal Arith.thy "!!m::nat. (m+k) - (n+k) = m - n";
val add_commute_k = read_instantiate [("n","k")] add_commute;
by (asm_simp_tac (!simpset addsimps ([add_commute_k])) 1);
qed "diff_cancel2";
Addsimps [diff_cancel2];

(*From Clemens Ballarin*)
goal Arith.thy "!!n::nat. [| k<=n; n<=m |] ==> (m-k) - (n-k) = m-n";
by (subgoal_tac "k<=n --> n<=m --> (m-k) - (n-k) = m-n" 1);
by (Asm_full_simp_tac 1);
by (induct_tac "k" 1);
by (Simp_tac 1);
(* Induction step *)
by (subgoal_tac "Suc na <= m --> n <= m --> Suc na <= n --> \
\                Suc (m - Suc na) - Suc (n - Suc na) = m-n" 1);
by (Asm_full_simp_tac 1);
by (blast_tac (!claset addIs [le_trans]) 1);
by (auto_tac (!claset addIs [Suc_leD], !simpset delsimps [diff_Suc_Suc]));
by (asm_full_simp_tac (!simpset delsimps [Suc_less_eq] 
		       addsimps [Suc_diff_n RS sym, le_eq_less_Suc]) 1);
qed "diff_right_cancel";

goal Arith.thy "!!n::nat. n - (n+m) = 0";
by (induct_tac "n" 1);
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
by (Blast_tac 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac(!simpset addsimps [diff_less_Suc])));
qed "diff_less";

val wf_less_trans = [eq_reflection, wf_pred_nat RS wf_trancl] MRS 
                    def_wfrec RS trans;

goalw Nat.thy [less_def] "(m,n) : pred_nat^+ = (m<n)";
by (rtac refl 1);
qed "less_eq";

(*** Remainder ***)

goal Arith.thy "(%m. m mod n) = wfrec (trancl pred_nat) \
             \                      (%f j. if j<n then j else f (j-n))";
by (simp_tac (!simpset addsimps [mod_def]) 1);
qed "mod_eq";

goal Arith.thy "!!m. m<n ==> m mod n = m";
by (rtac (mod_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "mod_less";

goal Arith.thy "!!m. [| 0<n;  ~m<n |] ==> m mod n = (m-n) mod n";
by (rtac (mod_eq RS wf_less_trans) 1);
by (asm_simp_tac (!simpset addsimps [diff_less, cut_apply, less_eq]) 1);
qed "mod_geq";

goal thy "!!n. 0<n ==> n mod n = 0";
by (rtac (mod_eq RS wf_less_trans) 1);
by (asm_simp_tac (!simpset addsimps [mod_less, diff_self_eq_0,
				     cut_def, less_eq]) 1);
qed "mod_nn_is_0";

goal thy "!!n. 0<n ==> (m+n) mod n = m mod n";
by (subgoal_tac "(n + m) mod n = (n+m-n) mod n" 1);
by (stac (mod_geq RS sym) 2);
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [add_commute])));
qed "mod_eq_add";

goal thy "!!n. 0<n ==> m*n mod n = 0";
by (induct_tac "m" 1);
by (asm_simp_tac (!simpset addsimps [mod_less]) 1);
by (dres_inst_tac [("m","m*n")] mod_eq_add 1);
by (asm_full_simp_tac (!simpset addsimps [add_commute]) 1);
qed "mod_prod_nn_is_0";


(*** Quotient ***)

goal Arith.thy "(%m. m div n) = wfrec (trancl pred_nat) \
                        \            (%f j. if j<n then 0 else Suc (f (j-n)))";
by (simp_tac (!simpset addsimps [div_def]) 1);
qed "div_eq";

goal Arith.thy "!!m. m<n ==> m div n = 0";
by (rtac (div_eq RS wf_less_trans) 1);
by (Asm_simp_tac 1);
qed "div_less";

goal Arith.thy "!!M. [| 0<n;  ~m<n |] ==> m div n = Suc((m-n) div n)";
by (rtac (div_eq RS wf_less_trans) 1);
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


(*** Further facts about mod (mainly for the mutilated chess board ***)

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

(*With less_zeroE, causes case analysis on b<2*)
AddSEs [less_SucE];

goal thy "!!k b. b<2 ==> k mod 2 = b | k mod 2 = (if b=1 then 0 else 1)";
by (subgoal_tac "k mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (Blast_tac 1);
qed "mod2_cases";

goal thy "Suc(Suc(m)) mod 2 = m mod 2";
by (subgoal_tac "m mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (Step_tac 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mod_Suc])));
qed "mod2_Suc_Suc";
Addsimps [mod2_Suc_Suc];

goal Arith.thy "!!m. m mod 2 ~= 0 ==> m mod 2 = 1";
by (subgoal_tac "m mod 2 < 2" 1);
by (asm_simp_tac (!simpset addsimps [mod_less_divisor]) 2);
by (safe_tac (!claset addSEs [lessE]));
by (ALLGOALS (blast_tac (!claset addIs [sym])));
qed "mod2_neq_0";

goal thy "(m+m) mod 2 = 0";
by (induct_tac "m" 1);
by (simp_tac (!simpset addsimps [mod_less]) 1);
by (asm_simp_tac (!simpset addsimps [mod2_Suc_Suc, add_Suc_right]) 1);
qed "mod2_add_self";
Addsimps [mod2_add_self];

Delrules [less_SucE];


(*** Monotonicity of Multiplication ***)

goal Arith.thy "!!i::nat. i<=j ==> i*k<=j*k";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [add_le_mono])));
qed "mult_le_mono1";

(*<=monotonicity, BOTH arguments*)
goal Arith.thy "!!i::nat. [| i<=j; k<=l |] ==> i*k<=j*l";
by (etac (mult_le_mono1 RS le_trans) 1);
by (rtac le_trans 1);
by (stac mult_commute 2);
by (etac mult_le_mono1 2);
by (simp_tac (!simpset addsimps [mult_commute]) 1);
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0*)
goal Arith.thy "!!i::nat. [| i<j; 0<k |] ==> k*i < k*j";
by (eres_inst_tac [("i","0")] less_natE 1);
by (Asm_simp_tac 1);
by (induct_tac "x" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [add_less_mono])));
qed "mult_less_mono2";

goal Arith.thy "!!i::nat. [| i<j; 0<k |] ==> i*k < j*k";
bd mult_less_mono2 1;
by (ALLGOALS (asm_full_simp_tac (!simpset addsimps [mult_commute])));
qed "mult_less_mono1";

goal Arith.thy "(0 < m*n) = (0<m & 0<n)";
by (induct_tac "m" 1);
by (induct_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_mult_iff";

goal Arith.thy "(m*n = 1) = (m=1 & n=1)";
by (induct_tac "m" 1);
by (Simp_tac 1);
by (induct_tac "n" 1);
by (Simp_tac 1);
by (fast_tac (!claset addss !simpset) 1);
qed "mult_eq_1_iff";

goal Arith.thy "!!k. 0<k ==> (m*k < n*k) = (m<n)";
by (safe_tac (!claset addSIs [mult_less_mono1]));
by (cut_facts_tac [less_linear] 1);
by (blast_tac (!claset addDs [mult_less_mono1] addEs [less_asym]) 1);
qed "mult_less_cancel2";

goal Arith.thy "!!k. 0<k ==> (k*m < k*n) = (m<n)";
bd mult_less_cancel2 1;
by (asm_full_simp_tac (!simpset addsimps [mult_commute]) 1);
qed "mult_less_cancel1";
Addsimps [mult_less_cancel1, mult_less_cancel2];

goal Arith.thy "!!k. 0<k ==> (m*k = n*k) = (m=n)";
by (cut_facts_tac [less_linear] 1);
by(Step_tac 1);
ba 2;
by (ALLGOALS (dtac mult_less_mono1 THEN' assume_tac));
by (ALLGOALS Asm_full_simp_tac);
qed "mult_cancel2";

goal Arith.thy "!!k. 0<k ==> (k*m = k*n) = (m=n)";
bd mult_cancel2 1;
by (asm_full_simp_tac (!simpset addsimps [mult_commute]) 1);
qed "mult_cancel1";
Addsimps [mult_cancel1, mult_cancel2];


(*** More division laws ***)

goal thy "!!n. 0<n ==> m*n div n = m";
by (cut_inst_tac [("m", "m*n")] mod_div_equality 1);
ba 1;
by (asm_full_simp_tac (!simpset addsimps [mod_prod_nn_is_0]) 1);
qed "div_prod_nn_is_m";
Addsimps [div_prod_nn_is_m];

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
Addsimps [div_cancel];

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


(** Lemma for gcd **)

goal Arith.thy "!!m n. m = m*n ==> n=1 | m=0";
by (dtac sym 1);
by (rtac disjCI 1);
by (rtac nat_less_cases 1 THEN assume_tac 2);
by (fast_tac (!claset addSEs [less_SucE] addss !simpset) 1);
by (best_tac (!claset addDs [mult_less_mono2] 
                      addss (!simpset addsimps [zero_less_eq RS sym])) 1);
qed "mult_eq_self_implies_10";


(*** Subtraction laws -- from Clemens Ballarin ***)

goal Arith.thy "!! a b c::nat. [| a < b; c <= a |] ==> a-c < b-c";
by (subgoal_tac "c+(a-c) < c+(b-c)" 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "c <= b" 1);
by (blast_tac (!claset addIs [less_imp_le, le_trans]) 2);
by (asm_simp_tac (!simpset addsimps [leD RS add_diff_inverse]) 1);
qed "diff_less_mono";

goal Arith.thy "!! a b c::nat. a+b < c ==> a < c-b";
bd diff_less_mono 1;
br le_add2 1;
by (Asm_full_simp_tac 1);
qed "add_less_imp_less_diff";

goal Arith.thy "!! n. n <= m ==> Suc m - n = Suc (m - n)";
br Suc_diff_n 1;
by (asm_full_simp_tac (!simpset addsimps [le_eq_less_Suc]) 1);
qed "Suc_diff_le";

goal Arith.thy "!! n. Suc i <= n ==> Suc (n - Suc i) = n - i";
by (asm_full_simp_tac
    (!simpset addsimps [Suc_diff_n RS sym, le_eq_less_Suc]) 1);
qed "Suc_diff_Suc";

goal Arith.thy "!! i::nat. i <= n ==> n - (n - i) = i";
by (subgoal_tac "(n-i) + (n - (n-i)) = (n-i) + i" 1);
by (Asm_full_simp_tac 1);
by (asm_simp_tac (!simpset addsimps [leD RS add_diff_inverse, diff_le_self, 
				     add_commute]) 1);
qed "diff_diff_cancel";

goal Arith.thy "!!k::nat. k <= n ==> m <= n + m - k";
be rev_mp 1;
by (res_inst_tac [("m", "k"), ("n", "n")] diff_induct 1);
by (Simp_tac 1);
by (simp_tac (!simpset addsimps [less_add_Suc2, less_imp_le]) 1);
by (Simp_tac 1);
qed "le_add_diff";


