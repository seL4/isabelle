(*  Title:      HOL/Arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Proofs about elementary arithmetic: addition, multiplication, etc.
Some from the Hoare example from Norbert Galm
*)

(*** Basic rewrite rules for the arithmetic operators ***)


(** Difference **)

qed_goal "diff_0_eq_0" thy
    "0 - n = 0"
 (fn _ => [induct_tac "n" 1,  ALLGOALS Asm_simp_tac]);

(*Must simplify BEFORE the induction!  (Else we get a critical pair)
  Suc(m) - Suc(n)   rewrites to   pred(Suc(m) - n)  *)
qed_goal "diff_Suc_Suc" thy
    "Suc(m) - Suc(n) = m - n"
 (fn _ =>
  [Simp_tac 1, induct_tac "n" 1, ALLGOALS Asm_simp_tac]);

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

qed_goal "add_0_right" thy "m + 0 = m"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "add_Suc_right" thy "m + Suc(n) = Suc(m+n)"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

Addsimps [add_0_right,add_Suc_right];

(*Associative law for addition*)
qed_goal "add_assoc" thy "(m + n) + k = m + ((n + k)::nat)"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*Commutative law for addition*)  
qed_goal "add_commute" thy "m + n = n + (m::nat)"
 (fn _ =>  [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

qed_goal "add_left_commute" thy "x+(y+z)=y+((x+z)::nat)"
 (fn _ => [rtac (add_commute RS trans) 1, rtac (add_assoc RS trans) 1,
           rtac (add_commute RS arg_cong) 1]);

(*Addition is an AC-operator*)
val add_ac = [add_assoc, add_commute, add_left_commute];

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

Goal "(m+n = 0) = (m=0 & n=0)";
by (exhaust_tac "m" 1);
by (Auto_tac);
qed "add_is_0";
AddIffs [add_is_0];

Goal "(0 = m+n) = (m=0 & n=0)";
by (exhaust_tac "m" 1);
by (Auto_tac);
qed "zero_is_add";
AddIffs [zero_is_add];

Goal "(m+n=1) = (m=1 & n=0 | m=0 & n=1)";
by(exhaust_tac "m" 1);
by(Auto_tac);
qed "add_is_1";

Goal "(1=m+n) = (m=1 & n=0 | m=0 & n=1)";
by(exhaust_tac "m" 1);
by(Auto_tac);
qed "one_is_add";

Goal "(0<m+n) = (0<m | 0<n)";
by (simp_tac (simpset() delsimps [neq0_conv] addsimps [neq0_conv RS sym]) 1);
qed "add_gr_0";
AddIffs [add_gr_0];

(* FIXME: really needed?? *)
Goal "((m+n)-1 = 0) = (m=0 & n-1 = 0 | m-1 = 0 & n=0)";
by (exhaust_tac "m" 1);
by (ALLGOALS (fast_tac (claset() addss (simpset()))));
qed "pred_add_is_0";
Addsimps [pred_add_is_0];

(* Could be generalized, eg to "k<n ==> m+(n-(Suc k)) = (m+n)-(Suc k)" *)
Goal "0<n ==> m + (n-1) = (m+n)-1";
by (exhaust_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_Suc]
                                      addsplits [nat.split])));
qed "add_pred";
Addsimps [add_pred];

Goal "m + n = m ==> n = 0";
by (dtac (add_0_right RS ssubst) 1);
by (asm_full_simp_tac (simpset() addsimps [add_assoc]
                                 delsimps [add_0_right]) 1);
qed "add_eq_self_zero";


(**** Additional theorems about "less than" ****)

(*Deleted less_natE; instead use less_eq_Suc_add RS exE*)
Goal "m<n --> (? k. n=Suc(m+k))";
by (induct_tac "n" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [order_le_less])));
by (blast_tac (claset() addSEs [less_SucE] 
                        addSIs [add_0_right RS sym, add_Suc_right RS sym]) 1);
qed_spec_mp "less_eq_Suc_add";

Goal "n <= ((m + n)::nat)";
by (induct_tac "m" 1);
by (ALLGOALS Simp_tac);
qed "le_add2";

Goal "n <= ((n + m)::nat)";
by (simp_tac (simpset() addsimps add_ac) 1);
by (rtac le_add2 1);
qed "le_add1";

bind_thm ("less_add_Suc1", (lessI RS (le_add1 RS le_less_trans)));
bind_thm ("less_add_Suc2", (lessI RS (le_add2 RS le_less_trans)));

Goal "(m<n) = (? k. n=Suc(m+k))";
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
qed_goal "mult_0_right" thy "m * 0 = 0"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*right successor law for multiplication*)
qed_goal "mult_Suc_right" thy  "m * Suc(n) = m + (m * n)"
 (fn _ => [induct_tac "m" 1,
           ALLGOALS(asm_simp_tac (simpset() addsimps add_ac))]);

Addsimps [mult_0_right, mult_Suc_right];

Goal "1 * n = n";
by (Asm_simp_tac 1);
qed "mult_1";

Goal "n * 1 = n";
by (Asm_simp_tac 1);
qed "mult_1_right";

(*Commutative law for multiplication*)
qed_goal "mult_commute" thy "m * n = n * (m::nat)"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);

(*addition distributes over multiplication*)
qed_goal "add_mult_distrib" thy "(m + n)*k = (m*k) + ((n*k)::nat)"
 (fn _ => [induct_tac "m" 1,
           ALLGOALS(asm_simp_tac (simpset() addsimps add_ac))]);

qed_goal "add_mult_distrib2" thy "k*(m + n) = (k*m) + ((k*n)::nat)"
 (fn _ => [induct_tac "m" 1,
           ALLGOALS(asm_simp_tac (simpset() addsimps add_ac))]);

(*Associative law for multiplication*)
qed_goal "mult_assoc" thy "(m * n) * k = m * ((n * k)::nat)"
  (fn _ => [induct_tac "m" 1, 
            ALLGOALS (asm_simp_tac (simpset() addsimps [add_mult_distrib]))]);

qed_goal "mult_left_commute" thy "x*(y*z) = y*((x*z)::nat)"
 (fn _ => [rtac trans 1, rtac mult_commute 1, rtac trans 1,
           rtac mult_assoc 1, rtac (mult_commute RS arg_cong) 1]);

val mult_ac = [mult_assoc,mult_commute,mult_left_commute];

Goal "(m*n = 0) = (m=0 | n=0)";
by (induct_tac "m" 1);
by (induct_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "mult_is_0";
Addsimps [mult_is_0];

Goal "m <= m*(m::nat)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_assoc RS sym])));
by (etac (le_add2 RSN (2,le_trans)) 1);
qed "le_square";


(*** Difference ***)


qed_goal "diff_self_eq_0" thy "m - m = 0"
 (fn _ => [induct_tac "m" 1, ALLGOALS Asm_simp_tac]);
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

Goal "n<=(l::nat) --> Suc l - n + m = Suc (l - n + m)";
by (res_inst_tac [("m","n"),("n","l")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "Suc_diff_add_le";

Goal "m - n < Suc(m)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (etac less_SucE 3);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [less_Suc_eq])));
qed "diff_less_Suc";

Goal "m - n <= (m::nat)";
by (res_inst_tac [("m","m"), ("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
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
by (exhaust_tac "n" 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps le_simps) 1);
qed "diff_Suc_less";
Addsimps [diff_Suc_less];

Goal "i<n ==> n - Suc i < n - i";
by (exhaust_tac "n" 1);
by (auto_tac (claset(),
	      simpset() addsimps [Suc_diff_le]@le_simps));
qed "diff_Suc_less_diff";

(*This and the next few suggested by Florian Kammueller*)
Goal "!!i::nat. i-j-k = i-k-j";
by (simp_tac (simpset() addsimps [diff_diff_left, add_commute]) 1);
qed "diff_commute";

Goal "k<=j --> j<=i --> i - (j - k) = i - j + (k::nat)";
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
by (asm_simp_tac (simpset() addsimps [Suc_diff_le, le_Suc_eq]) 1);
qed_spec_mp "diff_diff_right";

Goal "k <= (j::nat) --> (i + j) - k = i + (j - k)";
by (res_inst_tac [("m","j"),("n","k")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "diff_add_assoc";

Goal "k <= (j::nat) --> (j + i) - k = i + (j - k)";
by (asm_simp_tac (simpset() addsimps [add_commute, diff_add_assoc]) 1);
qed_spec_mp "diff_add_assoc2";

Goal "(n+m) - n = (m::nat)";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_inverse";
Addsimps [diff_add_inverse];

Goal "(m+n) - n = (m::nat)";
by (simp_tac (simpset() addsimps [diff_add_assoc]) 1);
qed "diff_add_inverse2";
Addsimps [diff_add_inverse2];

Goal "i <= (j::nat) ==> (j-i=k) = (j=k+i)";
by Safe_tac;
by (ALLGOALS Asm_simp_tac);
qed "le_imp_diff_is_add";

Goal "(m-n = 0) = (m <= n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_is_0_eq";
Addsimps [diff_is_0_eq RS iffD2];

Goal "(0<n-m) = (m<n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_diff";
Addsimps [zero_less_diff];

Goal "i < j  ==> ? k. 0<k & i+k = j";
by (res_inst_tac [("x","j - i")] exI 1);
by (asm_simp_tac (simpset() addsimps [add_diff_inverse, less_not_sym]) 1);
qed "less_imp_add_positive";

Goal "Suc(m)-n = (if m<n then 0 else Suc(m-n))";
by (simp_tac (simpset() addsimps [leI, Suc_le_eq, Suc_diff_le]) 1);
qed "if_Suc_diff_le";

Goal "Suc(m)-n <= Suc(m-n)";
by (simp_tac (simpset() addsimps [if_Suc_diff_le]) 1);
qed "diff_Suc_le_Suc_diff";

Goal "P(k) --> (!n. P(Suc(n))--> P(n)) --> P(k-i)";
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
Addsimps [diff_cancel];

Goal "(m+k) - (n+k) = m - (n::nat)";
val add_commute_k = read_instantiate [("n","k")] add_commute;
by (asm_simp_tac (simpset() addsimps [add_commute_k]) 1);
qed "diff_cancel2";
Addsimps [diff_cancel2];

(*From Clemens Ballarin, proof by lcp*)
Goal "[| k<=n; n<=m |] ==> (m-k) - (n-k) = m-(n::nat)";
by (REPEAT (etac rev_mp 1));
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
(*a confluence problem*)
by (asm_simp_tac (simpset() addsimps [Suc_diff_le, le_Suc_eq]) 1);
qed "diff_right_cancel";

Goal "n - (n+m) = 0";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_add_0";
Addsimps [diff_add_0];


(** Difference distributes over multiplication **)

Goal "!!m::nat. (m - n) * k = (m * k) - (n * k)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
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

(*<=monotonicity, BOTH arguments*)
Goal "[| i <= (j::nat); k <= l |] ==> i*k <= j*l";
by (etac (mult_le_mono1 RS le_trans) 1);
by (rtac le_trans 1);
by (stac mult_commute 2);
by (etac mult_le_mono1 2);
by (simp_tac (simpset() addsimps [mult_commute]) 1);
qed "mult_le_mono";

(*strict, in 1st argument; proof is by induction on k>0*)
Goal "[| i<j; 0<k |] ==> k*i < k*j";
by (eres_inst_tac [("m1","0")] (less_eq_Suc_add RS exE) 1);
by (Asm_simp_tac 1);
by (induct_tac "x" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_less_mono])));
qed "mult_less_mono2";

Goal "[| i<j; 0<k |] ==> i*k < j*k";
by (dtac mult_less_mono2 1);
by (ALLGOALS (asm_full_simp_tac (simpset() addsimps [mult_commute])));
qed "mult_less_mono1";

Goal "(0 < m*n) = (0<m & 0<n)";
by (induct_tac "m" 1);
by (induct_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_mult_iff";
Addsimps [zero_less_mult_iff];

Goal "(m*n = 1) = (m=1 & n=1)";
by (induct_tac "m" 1);
by (Simp_tac 1);
by (induct_tac "n" 1);
by (Simp_tac 1);
by (fast_tac (claset() addss simpset()) 1);
qed "mult_eq_1_iff";
Addsimps [mult_eq_1_iff];

Goal "0<k ==> (m*k < n*k) = (m<n)";
by (safe_tac (claset() addSIs [mult_less_mono1]));
by (cut_facts_tac [less_linear] 1);
by (blast_tac (claset() addIs [mult_less_mono1] addEs [less_asym]) 1);
qed "mult_less_cancel2";

Goal "0<k ==> (k*m < k*n) = (m<n)";
by (dtac mult_less_cancel2 1);
by (asm_full_simp_tac (simpset() addsimps [mult_commute]) 1);
qed "mult_less_cancel1";
Addsimps [mult_less_cancel1, mult_less_cancel2];

Goal "(Suc k * m < Suc k * n) = (m < n)";
by (rtac mult_less_cancel1 1);
by (Simp_tac 1);
qed "Suc_mult_less_cancel1";

Goalw [le_def] "(Suc k * m <= Suc k * n) = (m <= n)";
by (simp_tac (simpset_of HOL.thy) 1);
by (rtac Suc_mult_less_cancel1 1);
qed "Suc_mult_le_cancel1";

Goal "0<k ==> (m*k = n*k) = (m=n)";
by (cut_facts_tac [less_linear] 1);
by Safe_tac;
by (assume_tac 2);
by (ALLGOALS (dtac mult_less_mono1 THEN' assume_tac));
by (ALLGOALS Asm_full_simp_tac);
qed "mult_cancel2";

Goal "0<k ==> (k*m = k*n) = (m=n)";
by (dtac mult_cancel2 1);
by (asm_full_simp_tac (simpset() addsimps [mult_commute]) 1);
qed "mult_cancel1";
Addsimps [mult_cancel1, mult_cancel2];

Goal "(Suc k * m = Suc k * n) = (m = n)";
by (rtac mult_cancel1 1);
by (Simp_tac 1);
qed "Suc_mult_cancel1";


(** Lemma for gcd **)

Goal "m = m*n ==> n=1 | m=0";
by (dtac sym 1);
by (rtac disjCI 1);
by (rtac nat_less_cases 1 THEN assume_tac 2);
by (fast_tac (claset() addSEs [less_SucE] addss simpset()) 1);
by (best_tac (claset() addDs [mult_less_mono2] addss simpset()) 1);
qed "mult_eq_self_implies_10";


(*** Subtraction laws -- mostly from Clemens Ballarin ***)

Goal "[| a < (b::nat); c <= a |] ==> a-c < b-c";
by (subgoal_tac "c+(a-c) < c+(b-c)" 1);
by (Full_simp_tac 1);
by (subgoal_tac "c <= b" 1);
by (blast_tac (claset() addIs [less_imp_le, le_trans]) 2);
by (Asm_simp_tac 1);
qed "diff_less_mono";

Goal "a+b < (c::nat) ==> a < c-b";
by (dtac diff_less_mono 1);
by (rtac le_add2 1);
by (Asm_full_simp_tac 1);
qed "add_less_imp_less_diff";

Goal "(i < j-k) = (i+k < (j::nat))";
by (rtac iffI 1);
 by (case_tac "k <= j" 1);
  by (dtac le_add_diff_inverse2 1);
  by (dres_inst_tac [("k","k")] add_less_mono1 1);
  by (Asm_full_simp_tac 1);
 by (rotate_tac 1 1);
 by (asm_full_simp_tac (simpset() addSolver cut_trans_tac) 1);
by (etac add_less_imp_less_diff 1);
qed "less_diff_conv";

Goal "(j-k <= (i::nat)) = (j <= i+k)";
by (simp_tac (simpset() addsimps [less_diff_conv, le_def]) 1);
qed "le_diff_conv";

Goal "k <= j ==> (i <= j-k) = (i+k <= (j::nat))";
by (asm_full_simp_tac
    (simpset() delsimps [less_Suc_eq_le]
               addsimps [less_Suc_eq_le RS sym, less_diff_conv,
			 Suc_diff_le RS sym]) 1);
qed "le_diff_conv2";

Goal "Suc i <= n ==> Suc (n - Suc i) = n - i";
by (asm_full_simp_tac (simpset() addsimps [Suc_diff_le RS sym]) 1);
qed "Suc_diff_Suc";

Goal "i <= (n::nat) ==> n - (n - i) = i";
by (etac rev_mp 1);
by (res_inst_tac [("m","n"),("n","i")] diff_induct 1);
by (ALLGOALS (asm_simp_tac  (simpset() addsimps [Suc_diff_le])));
qed "diff_diff_cancel";
Addsimps [diff_diff_cancel];

Goal "k <= (n::nat) ==> m <= n + m - k";
by (etac rev_mp 1);
by (res_inst_tac [("m", "k"), ("n", "n")] diff_induct 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [le_add2, less_imp_le]) 1);
by (Simp_tac 1);
qed "le_add_diff";

Goal "0<k ==> j<i --> j+k-i < k";
by (res_inst_tac [("m","j"),("n","i")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "add_diff_less";


Goal "m-1 < n ==> m <= n";
by (exhaust_tac "m" 1);
by (auto_tac (claset(), simpset() addsimps [Suc_le_eq]));
qed "pred_less_imp_le";

Goal "j<=i ==> i - j < Suc i - j";
by (REPEAT (etac rev_mp 1));
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by Auto_tac;
qed "diff_less_Suc_diff";

Goal "i - j <= Suc i - j";
by (res_inst_tac [("m","i"),("n","j")] diff_induct 1);
by Auto_tac;
qed "diff_le_Suc_diff";
AddIffs [diff_le_Suc_diff];

Goal "n - Suc i <= n - i";
by (case_tac "i<n" 1);
by (dtac diff_Suc_less_diff 1);
by (auto_tac (claset(), simpset() addsimps [less_imp_le, leI]));
qed "diff_Suc_le_diff";
AddIffs [diff_Suc_le_diff];

Goal "0 < n ==> (m <= n-1) = (m<n)";
by (exhaust_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps le_simps));
qed "le_pred_eq";

Goal "0 < n ==> (m-1 < n) = (m<=n)";
by (exhaust_tac "m" 1);
by (auto_tac (claset(), simpset() addsimps [Suc_le_eq]));
qed "less_pred_eq";

(*In ordinary notation: if 0<n and n<=m then m-n < m *)
Goal "[| 0<n; ~ m<n |] ==> m - n < m";
by (subgoal_tac "0<n --> ~ m<n --> m - n < m" 1);
by (Blast_tac 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS(asm_simp_tac(simpset() addsimps [diff_less_Suc])));
qed "diff_less";

Goal "[| 0<n; n<=m |] ==> m - n < m";
by (asm_simp_tac (simpset() addsimps [diff_less, not_less_iff_le]) 1);
qed "le_diff_less";



(** (Anti)Monotonicity of subtraction -- by Stefan Merz **)

(* Monotonicity of subtraction in first argument *)
Goal "m <= (n::nat) --> (m-l) <= (n-l)";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [le_Suc_eq]) 1);
by (blast_tac (claset() addIs [diff_le_Suc_diff, le_trans]) 1);
qed_spec_mp "diff_le_mono";

Goal "m <= (n::nat) ==> (l-n) <= (l-m)";
by (induct_tac "l" 1);
by (Simp_tac 1);
by (case_tac "n <= na" 1);
by (subgoal_tac "m <= na" 1);
by (asm_simp_tac (simpset() addsimps [Suc_diff_le]) 1);
by (fast_tac (claset() addEs [le_trans]) 1);
by (dtac not_leE 1);
by (asm_simp_tac (simpset() addsimps [if_Suc_diff_le]) 1);
qed_spec_mp "diff_le_mono2";
