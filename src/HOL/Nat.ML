(*  Title:      HOL/Nat.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Tobias Nipkow

Proofs about natural numbers and elementary arithmetic: addition,
multiplication, etc.  Some from the Hoare example from Norbert Galm.
*)

(** conversion rules for nat_rec **)

val [nat_rec_0, nat_rec_Suc] = nat.recs;
bind_thm ("nat_rec_0", nat_rec_0);
bind_thm ("nat_rec_Suc", nat_rec_Suc);

(*These 2 rules ease the use of primitive recursion.  NOTE USE OF == *)
val prems = Goal
    "[| !!n. f(n) == nat_rec c h n |] ==> f(0) = c";
by (simp_tac (simpset() addsimps prems) 1);
qed "def_nat_rec_0";

val prems = Goal
    "[| !!n. f(n) == nat_rec c h n |] ==> f(Suc(n)) = h n (f n)";
by (simp_tac (simpset() addsimps prems) 1);
qed "def_nat_rec_Suc";

val [nat_case_0, nat_case_Suc] = nat.cases;
bind_thm ("nat_case_0", nat_case_0);
bind_thm ("nat_case_Suc", nat_case_Suc);

Goal "n ~= 0 ==> EX m. n = Suc m";
by (case_tac "n" 1);
by (REPEAT (Blast_tac 1));
qed "not0_implies_Suc";

Goal "!!n::nat. m<n ==> n ~= 0";
by (case_tac "n" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "gr_implies_not0";

Goal "!!n::nat. (n ~= 0) = (0 < n)";
by (case_tac "n" 1);
by Auto_tac;
qed "neq0_conv";
AddIffs [neq0_conv];

Goal "!!n::nat. (0 ~= n) = (0 < n)";
by (case_tac "n" 1);
by Auto_tac;
qed "zero_neq_conv";
AddIffs [zero_neq_conv];

(*This theorem is useful with blast_tac: (n=0 ==> False) ==> 0<n *)
bind_thm ("gr0I", [neq0_conv, notI] MRS iffD1);

Goal "(0<n) = (EX m. n = Suc m)";
by(fast_tac (claset() addIs [not0_implies_Suc]) 1);
qed "gr0_conv_Suc";

Goal "!!n::nat. (~(0 < n)) = (n=0)";
by (rtac iffI 1);
 by (rtac ccontr 1);
 by (ALLGOALS Asm_full_simp_tac);
qed "not_gr0";
AddIffs [not_gr0];

Goal "(Suc n <= m') --> (? m. m' = Suc m)";
by (induct_tac "m'" 1);
by  Auto_tac;
qed_spec_mp "Suc_le_D";

(*Useful in certain inductive arguments*)
Goal "(m < Suc n) = (m=0 | (EX j. m = Suc j & j < n))";
by (case_tac "m" 1);
by Auto_tac;
qed "less_Suc_eq_0_disj";

Goalw [Least_nat_def]
 "[| ? n. P(Suc n); ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P(Suc m))";
by (rtac some_equality 1);
by (fold_goals_tac [Least_nat_def]);
by (safe_tac (claset() addSEs [LeastI]));
by (rename_tac "j" 1);
by (case_tac "j" 1);
by (Blast_tac 1);
by (blast_tac (claset() addDs [Suc_less_SucD, not_less_Least]) 1);
by (rename_tac "k n" 1);
by (case_tac "k" 1);
by (Blast_tac 1);
by (hyp_subst_tac 1);
by (rewtac Least_nat_def);
by (rtac (some_equality RS arg_cong RS sym) 1);
by (blast_tac (claset() addDs [Suc_mono]) 1);
by (cut_inst_tac [("m","m")] less_linear 1);
by (blast_tac (claset() addIs [Suc_mono]) 1);
qed "Least_Suc";

val prems = Goal "[| P 0; P 1; !!k. P k ==> P (Suc (Suc k)) |] ==> P n";
by (rtac nat_less_induct 1);
by (case_tac "n" 1);
by (case_tac "nat" 2);
by (ALLGOALS (blast_tac (claset() addIs prems@[less_trans])));
qed "nat_induct2";

Goal "min 0 n = (0::nat)";
by (rtac min_leastL 1);
by (Simp_tac 1);
qed "min_0L";

Goal "min n 0 = (0::nat)";
by (rtac min_leastR 1);
by (Simp_tac 1);
qed "min_0R";

Goalw [min_def] "min (Suc m) (Suc n) = Suc(min m n)";
by (Simp_tac 1);
qed "min_Suc_Suc";

Addsimps [min_0L,min_0R,min_Suc_Suc];

Goalw [max_def] "max 0 n = (n::nat)";
by (Simp_tac 1);
qed "max_0L";

Goalw [max_def] "max n 0 = (n::nat)";
by (Simp_tac 1);
qed "max_0R";

Goalw [max_def] "max (Suc m) (Suc n) = Suc(max m n)";
by (Simp_tac 1);
qed "max_Suc_Suc";

Addsimps [max_0L,max_0R,max_Suc_Suc];


(*** Basic rewrite rules for the arithmetic operators ***)

(** Difference **)

Goal "0 - n = (0::nat)";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_0_eq_0";

(*Must simplify BEFORE the induction!  (Else we get a critical pair)
  Suc(m) - Suc(n)   rewrites to   pred(Suc(m) - n)  *)
Goal "Suc(m) - Suc(n) = m - n";
by (Simp_tac 1);
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_Suc_Suc";

Addsimps [diff_0_eq_0, diff_Suc_Suc];

(* Could be (and is, below) generalized in various ways;
   However, none of the generalizations are currently in the simpset,
   and I dread to think what happens if I put them in *)
Goal "0 < n ==> Suc(n-1) = n";
by (asm_simp_tac (simpset() addsplits [nat.split]) 1);
qed "Suc_pred";
Addsimps [Suc_pred];

Delsimps [diff_Suc];


(**** Inductive properties of the operators ****)

(*** Addition ***)

Goal "m + 0 = (m::nat)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_0_right";

Goal "m + Suc(n) = Suc(m+n)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_Suc_right";

Addsimps [add_0_right,add_Suc_right];


(*Associative law for addition*)
Goal "(m + n) + k = m + ((n + k)::nat)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_assoc";

(*Commutative law for addition*)
Goal "m + n = n + (m::nat)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_commute";

Goal "x+(y+z)=y+((x+z)::nat)";
by (rtac (add_commute RS trans) 1);
by (rtac (add_assoc RS trans) 1);
by (rtac (add_commute RS arg_cong) 1);
qed "add_left_commute";

(*Addition is an AC-operator*)
bind_thms ("add_ac", [add_assoc, add_commute, add_left_commute]);

Goal "(k + m = k + n) = (m=(n::nat))";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel";

Goal "(m + k = n + k) = (m=(n::nat))";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_right_cancel";

Goal "(k + m <= k + n) = (m<=(n::nat))";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel_le";

Goal "(k + m < k + n) = (m<(n::nat))";
by (induct_tac "k" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "add_left_cancel_less";

Addsimps [add_left_cancel, add_right_cancel,
          add_left_cancel_le, add_left_cancel_less];

(** Reasoning about m+0=0, etc. **)

Goal "!!m::nat. (m+n = 0) = (m=0 & n=0)";
by (case_tac "m" 1);
by (Auto_tac);
qed "add_is_0";
AddIffs [add_is_0];

Goal "!!m::nat. (0 = m+n) = (m=0 & n=0)";
by (case_tac "m" 1);
by (Auto_tac);
qed "zero_is_add";
AddIffs [zero_is_add];

Goal "!!m::nat. (m+n=1) = (m=1 & n=0 | m=0 & n=1)";
by (case_tac "m" 1);
by (Auto_tac);
qed "add_is_1";

Goal "!!m::nat. (1=m+n) = (m=1 & n=0 | m=0 & n=1)";
by (case_tac "m" 1);
by (Auto_tac);
qed "one_is_add";

Goal "!!m::nat. (0<m+n) = (0<m | 0<n)";
by (simp_tac (simpset() delsimps [neq0_conv] addsimps [neq0_conv RS sym]) 1);
qed "add_gr_0";
AddIffs [add_gr_0];

Goal "!!m::nat. m + n = m ==> n = 0";
by (dtac (add_0_right RS ssubst) 1);
by (asm_full_simp_tac (simpset() addsimps [add_assoc]
                                 delsimps [add_0_right]) 1);
qed "add_eq_self_zero";


(**** Additional theorems about "less than" ****)

(*Deleted less_natE; instead use less_eq_Suc_add RS exE*)
Goal "m<n --> (EX k. n=Suc(m+k))";
by (induct_tac "n" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [order_le_less])));
by (blast_tac (claset() addSEs [less_SucE]
                        addSIs [add_0_right RS sym, add_Suc_right RS sym]) 1);
qed_spec_mp "less_eq_Suc_add";

Goal "n <= ((m + n)::nat)";
by (induct_tac "m" 1);
by (ALLGOALS Simp_tac);
by (etac le_SucI 1);
qed "le_add2";

Goal "n <= ((n + m)::nat)";
by (simp_tac (simpset() addsimps add_ac) 1);
by (rtac le_add2 1);
qed "le_add1";

bind_thm ("less_add_Suc1", (lessI RS (le_add1 RS le_less_trans)));
bind_thm ("less_add_Suc2", (lessI RS (le_add2 RS le_less_trans)));

Goal "(m<n) = (EX k. n=Suc(m+k))";
by (blast_tac (claset() addSIs [less_add_Suc1, less_eq_Suc_add]) 1);
qed "less_iff_Suc_add";


(*"i <= j ==> i <= j+m"*)
bind_thm ("trans_le_add1", le_add1 RSN (2,le_trans));

(*"i <= j ==> i <= m+j"*)
bind_thm ("trans_le_add2", le_add2 RSN (2,le_trans));

(*"i < j ==> i < j+m"*)
bind_thm ("trans_less_add1", le_add1 RSN (2,less_le_trans));

(*"i < j ==> i < m+j"*)
bind_thm ("trans_less_add2", le_add2 RSN (2,less_le_trans));

Goal "i+j < (k::nat) --> i<k";
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
by (blast_tac (claset() addDs [Suc_lessD]) 1);
qed_spec_mp "add_lessD1";

Goal "~ (i+j < (i::nat))";
by (rtac notI 1);
by (etac (add_lessD1 RS less_irrefl) 1);
qed "not_add_less1";

Goal "~ (j+i < (i::nat))";
by (simp_tac (simpset() addsimps [add_commute, not_add_less1]) 1);
qed "not_add_less2";
AddIffs [not_add_less1, not_add_less2];

Goal "m+k<=n --> m<=(n::nat)";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps le_simps)));
qed_spec_mp "add_leD1";

Goal "m+k<=n ==> k<=(n::nat)";
by (full_simp_tac (simpset() addsimps [add_commute]) 1);
by (etac add_leD1 1);
qed_spec_mp "add_leD2";

Goal "m+k<=n ==> m<=n & k<=(n::nat)";
by (blast_tac (claset() addDs [add_leD1, add_leD2]) 1);
bind_thm ("add_leE", result() RS conjE);

(*needs !!k for add_ac to work*)
Goal "!!k:: nat. [| k<l;  m+l = k+n |] ==> m<n";
by (force_tac (claset(),
              simpset() delsimps [add_Suc_right]
                        addsimps [less_iff_Suc_add,
                                  add_Suc_right RS sym] @ add_ac) 1);
qed "less_add_eq_less";


(*** Monotonicity of Addition ***)

(*strict, in 1st argument*)
Goal "i < j ==> i + k < j + (k::nat)";
by (induct_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono1";

(*strict, in both arguments*)
Goal "[|i < j; k < l|] ==> i + k < j + (l::nat)";
by (rtac (add_less_mono1 RS less_trans) 1);
by (REPEAT (assume_tac 1));
by (induct_tac "j" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono";

(*A [clumsy] way of lifting < monotonicity to <= monotonicity *)
val [lt_mono,le] = Goal
     "[| !!i j::nat. i<j ==> f(i) < f(j);       \
\        i <= j                                 \
\     |] ==> f(i) <= (f(j)::nat)";
by (cut_facts_tac [le] 1);
by (asm_full_simp_tac (simpset() addsimps [order_le_less]) 1);
by (blast_tac (claset() addSIs [lt_mono]) 1);
qed "less_mono_imp_le_mono";

(*non-strict, in 1st argument*)
Goal "i<=j ==> i + k <= j + (k::nat)";
by (res_inst_tac [("f", "%j. j+k")] less_mono_imp_le_mono 1);
by (etac add_less_mono1 1);
by (assume_tac 1);
qed "add_le_mono1";

(*non-strict, in both arguments*)
Goal "[|i<=j;  k<=l |] ==> i + k <= j + (l::nat)";
by (etac (add_le_mono1 RS le_trans) 1);
by (simp_tac (simpset() addsimps [add_commute]) 1);
qed "add_le_mono";


(*** Multiplication ***)

(*right annihilation in product*)
Goal "!!m::nat. m * 0 = 0";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "mult_0_right";

(*right successor law for multiplication*)
Goal  "m * Suc(n) = m + (m * n)";
by (induct_tac "m" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps add_ac)));
qed "mult_Suc_right";

Addsimps [mult_0_right, mult_Suc_right];

Goal "1 * n = n";
by (Asm_simp_tac 1);
qed "mult_1";

Goal "n * 1 = n";
by (Asm_simp_tac 1);
qed "mult_1_right";

(*Commutative law for multiplication*)
Goal "m * n = n * (m::nat)";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "mult_commute";

(*addition distributes over multiplication*)
Goal "(m + n)*k = (m*k) + ((n*k)::nat)";
by (induct_tac "m" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps add_ac)));
qed "add_mult_distrib";

Goal "k*(m + n) = (k*m) + ((k*n)::nat)";
by (induct_tac "m" 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps add_ac)));
qed "add_mult_distrib2";

(*Associative law for multiplication*)
Goal "(m * n) * k = m * ((n * k)::nat)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_mult_distrib])));
qed "mult_assoc";

Goal "x*(y*z) = y*((x*z)::nat)";
by (rtac trans 1);
by (rtac mult_commute 1);
by (rtac trans 1);
by (rtac mult_assoc 1);
by (rtac (mult_commute RS arg_cong) 1);
qed "mult_left_commute";

bind_thms ("mult_ac", [mult_assoc,mult_commute,mult_left_commute]);

Goal "!!m::nat. (m*n = 0) = (m=0 | n=0)";
by (induct_tac "m" 1);
by (induct_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "mult_is_0";

Goal "!!m::nat. (0 = m*n) = (0=m | 0=n)";
by (stac eq_commute 1 THEN stac mult_is_0 1);
by Auto_tac;
qed "zero_is_mult";

Addsimps [mult_is_0, zero_is_mult];


(*** Difference ***)

Goal "!!m::nat. m - m = 0";
by (induct_tac "m" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_self_eq_0";

Addsimps [diff_self_eq_0];

(*Addition is the inverse of subtraction: if n<=m then n+(m-n) = m. *)
Goal "~ m<n --> n+(m-n) = (m::nat)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "add_diff_inverse";

Goal "n<=m ==> n+(m-n) = (m::nat)";
by (asm_simp_tac (simpset() addsimps [add_diff_inverse, not_less_iff_le]) 1);
qed "le_add_diff_inverse";

Goal "n<=m ==> (m-n)+n = (m::nat)";
by (asm_simp_tac (simpset() addsimps [le_add_diff_inverse, add_commute]) 1);
qed "le_add_diff_inverse2";

Addsimps  [le_add_diff_inverse, le_add_diff_inverse2];


(*** More results about difference ***)

Goal "n <= m ==> Suc(m)-n = Suc(m-n)";
by (etac rev_mp 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "Suc_diff_le";

Goal "m - n < Suc(m)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (etac less_SucE 3);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [less_Suc_eq])));
qed "diff_less_Suc";

Goal "m - n <= (m::nat)";
by (res_inst_tac [("m","m"), ("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [le_SucI])));
qed "diff_le_self";
Addsimps [diff_le_self];

(* j<k ==> j-n < k *)
bind_thm ("less_imp_diff_less", diff_le_self RS le_less_trans);

Goal "!!i::nat. i-j-k = i - (j+k)";
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_diff_left";

Goal "(Suc m - n) - Suc k = m - n - k";
by (simp_tac (simpset() addsimps [diff_diff_left]) 1);
qed "Suc_diff_diff";
Addsimps [Suc_diff_diff];

Goal "0<n ==> n - Suc i < n";
by (case_tac "n" 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps le_simps) 1);
qed "diff_Suc_less";
Addsimps [diff_Suc_less];

(*This and the next few suggested by Florian Kammueller*)
Goal "!!i::nat. i-j-k = i-k-j";
by (simp_tac (simpset() addsimps [diff_diff_left, add_commute]) 1);
qed "diff_commute";

Goal "k <= (j::nat) --> (i + j) - k = i + (j - k)";
by (res_inst_tac [("m","j"),("n","k")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "diff_add_assoc";

Goal "k <= (j::nat) --> (j + i) - k = (j - k) + i";
by (asm_simp_tac (simpset() addsimps [add_commute, diff_add_assoc]) 1);
qed_spec_mp "diff_add_assoc2";

Goal "(n+m) - n = (m::nat)";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_inverse";

Goal "(m+n) - n = (m::nat)";
by (simp_tac (simpset() addsimps [diff_add_assoc]) 1);
qed "diff_add_inverse2";

Goal "i <= (j::nat) ==> (j-i=k) = (j=k+i)";
by Safe_tac;
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_add_inverse2])));
qed "le_imp_diff_is_add";

Goal "!!m::nat. (m-n = 0) = (m <= n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_is_0_eq";

Goal "!!m::nat. (0 = m-n) = (m <= n)";
by (stac (diff_is_0_eq RS sym) 1);
by (rtac eq_sym_conv 1);
qed "zero_is_diff_eq";
Addsimps [diff_is_0_eq, zero_is_diff_eq];

Goal "!!m::nat. (0<n-m) = (m<n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_diff";
Addsimps [zero_less_diff];

Goal "i < j  ==> EX k::nat. 0<k & i+k = j";
by (res_inst_tac [("x","j - i")] exI 1);
by (asm_simp_tac (simpset() addsimps [add_diff_inverse, less_not_sym]) 1);
qed "less_imp_add_positive";

Goal "P(k) --> (ALL n. P(Suc(n))--> P(n)) --> P(k-i)";
by (res_inst_tac [("m","k"),("n","i")] diff_induct 1);
by (ALLGOALS (Clarify_tac THEN' Simp_tac THEN' TRY o Blast_tac));
qed "zero_induct_lemma";

val prems = Goal "[| P(k);  !!n. P(Suc(n)) ==> P(n) |] ==> P(0)";
by (rtac (diff_self_eq_0 RS subst) 1);
by (rtac (zero_induct_lemma RS mp RS mp) 1);
by (REPEAT (ares_tac ([impI,allI]@prems) 1));
qed "zero_induct";

Goal "(k+m) - (k+n) = m - (n::nat)";
by (induct_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_cancel";

Goal "(m+k) - (n+k) = m - (n::nat)";
by (asm_simp_tac
    (simpset() addsimps [diff_cancel, inst "n" "k" add_commute]) 1);
qed "diff_cancel2";

Goal "n - (n+m) = (0::nat)";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_0";


(** Difference distributes over multiplication **)

Goal "!!m::nat. (m - n) * k = (m * k) - (n * k)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_cancel])));
qed "diff_mult_distrib" ;

Goal "!!m::nat. k * (m - n) = (k * m) - (k * n)";
val mult_commute_k = read_instantiate [("m","k")] mult_commute;
by (simp_tac (simpset() addsimps [diff_mult_distrib, mult_commute_k]) 1);
qed "diff_mult_distrib2" ;
(*NOT added as rewrites, since sometimes they are used from right-to-left*)


(*** Monotonicity of Multiplication ***)

Goal "i <= (j::nat) ==> i*k<=j*k";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_le_mono])));
qed "mult_le_mono1";

Goal "i <= (j::nat) ==> k*i <= k*j";
by (dtac mult_le_mono1 1);
by (asm_simp_tac (simpset() addsimps [mult_commute]) 1);
qed "mult_le_mono2";

(* <= monotonicity, BOTH arguments*)
Goal "[| i <= (j::nat); k <= l |] ==> i*k <= j*l";
by (etac (mult_le_mono1 RS le_trans) 1);
by (etac mult_le_mono2 1);
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0*)
Goal "!!i::nat. [| i<j; 0<k |] ==> k*i < k*j";
by (eres_inst_tac [("m1","0")] (less_eq_Suc_add RS exE) 1);
by (Asm_simp_tac 1);
by (induct_tac "x" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_less_mono])));
qed "mult_less_mono2";

Goal "!!i::nat. [| i<j; 0<k |] ==> i*k < j*k";
by (dtac mult_less_mono2 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [mult_commute])));
qed "mult_less_mono1";

Goal "!!m::nat. (0 < m*n) = (0<m & 0<n)";
by (induct_tac "m" 1);
by (case_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_mult_iff";
Addsimps [zero_less_mult_iff];

Goal "(1 <= m*n) = (1<=m & 1<=n)";
by (induct_tac "m" 1);
by (case_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "one_le_mult_iff";
Addsimps [one_le_mult_iff];

Goal "(m*n = 1) = (m=1 & n=1)";
by (induct_tac "m" 1);
by (Simp_tac 1);
by (induct_tac "n" 1);
by (Simp_tac 1);
by (fast_tac (claset() addss simpset()) 1);
qed "mult_eq_1_iff";
Addsimps [mult_eq_1_iff];

Goal "!!m::nat. (m*k < n*k) = (0<k & m<n)";
by (safe_tac (claset() addSIs [mult_less_mono1]));
by (case_tac "k" 1);
by Auto_tac;  
by (full_simp_tac (simpset() delsimps [le_0_eq]
			     addsimps [linorder_not_le RS sym]) 1);
by (blast_tac (claset() addIs [mult_le_mono1]) 1); 
qed "mult_less_cancel2";

Goal "!!m::nat. (k*m < k*n) = (0<k & m<n)";
by (simp_tac (simpset() addsimps [mult_less_cancel2, 
                                  inst "m" "k" mult_commute]) 1);
qed "mult_less_cancel1";
Addsimps [mult_less_cancel1, mult_less_cancel2];

Goal "!!m::nat. (m*k <= n*k) = (0<k --> m<=n)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
by Auto_tac;  
qed "mult_le_cancel2";

Goal "!!m::nat. (k*m <= k*n) = (0<k --> m<=n)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
by Auto_tac;  
qed "mult_le_cancel1";
Addsimps [mult_le_cancel1, mult_le_cancel2];

Goal "(m*k = n*k) = (m=n | (k = (0::nat)))";
by (cut_facts_tac [less_linear] 1);
by Safe_tac;
by Auto_tac; 	
by (ALLGOALS (dtac mult_less_mono1 THEN' assume_tac));
by (ALLGOALS Asm_full_simp_tac);
qed "mult_cancel2";

Goal "(k*m = k*n) = (m=n | (k = (0::nat)))";
by (simp_tac (simpset() addsimps [mult_cancel2, inst "m" "k" mult_commute]) 1);
qed "mult_cancel1";
Addsimps [mult_cancel1, mult_cancel2];

Goal "(Suc k * m < Suc k * n) = (m < n)";
by (stac mult_less_cancel1 1);
by (Simp_tac 1);
qed "Suc_mult_less_cancel1";

Goal "(Suc k * m <= Suc k * n) = (m <= n)";
by (stac mult_le_cancel1 1);
by (Simp_tac 1);
qed "Suc_mult_le_cancel1";

Goal "(Suc k * m = Suc k * n) = (m = n)";
by (stac mult_cancel1 1);
by (Simp_tac 1);
qed "Suc_mult_cancel1";


(*Lemma for gcd*)
Goal "!!m::nat. m = m*n ==> n=1 | m=0";
by (dtac sym 1);
by (rtac disjCI 1);
by (rtac nat_less_cases 1 THEN assume_tac 2);
by (fast_tac (claset() addSEs [less_SucE] addss simpset()) 1);
by (best_tac (claset() addDs [mult_less_mono2] addss simpset()) 1);
qed "mult_eq_self_implies_10";
