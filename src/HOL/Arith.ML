(*  Title:      HOL/Arith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Proofs about elementary arithmetic: addition, multiplication, etc.
Some from the Hoare example from Norbert Galm
*)

(*** Basic rewrite rules for the arithmetic operators ***)


(** Difference **)

Goal "0 - n = 0";
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

Goal "m + 0 = m";
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
by (exhaust_tac "m" 1);
by (Auto_tac);
qed "add_is_1";

Goal "(1=m+n) = (m=1 & n=0 | m=0 & n=1)";
by (exhaust_tac "m" 1);
by (Auto_tac);
qed "one_is_add";

Goal "(0<m+n) = (0<m | 0<n)";
by (simp_tac (simpset() delsimps [neq0_conv] addsimps [neq0_conv RS sym]) 1);
qed "add_gr_0";
AddIffs [add_gr_0];

(* Could be generalized, eg to "k<n ==> m+(n-(Suc k)) = (m+n)-(Suc k)" *)
Goal "0<n ==> m + (n-1) = (m+n)-1";
by (exhaust_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [diff_Suc, Suc_n_not_n]
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
by (etac le_SucI 1);
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
Goal "m * 0 = 0";
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

Goal "(m*n = 0) = (m=0 | n=0)";
by (induct_tac "m" 1);
by (induct_tac "n" 2);
by (ALLGOALS Asm_simp_tac);
qed "mult_is_0";

Goal "(0 = m*n) = (0=m | 0=n)";
by (cut_facts_tac [mult_is_0] 1);
by (full_simp_tac (simpset() addsimps [eq_commute]) 1);
qed "zero_is_mult";

Addsimps [mult_is_0, zero_is_mult];

Goal "m <= m*(m::nat)";
by (induct_tac "m" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [add_assoc RS sym])));
by (etac (le_add2 RSN (2,le_trans)) 1);
qed "le_square";


(*** Difference ***)

Goal "m - m = 0";
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
by (exhaust_tac "n" 1);
by Safe_tac;
by (asm_simp_tac (simpset() addsimps le_simps) 1);
qed "diff_Suc_less";
Addsimps [diff_Suc_less];

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

Goal "(0 = m-n) = (m <= n)";
by (stac (diff_is_0_eq RS sym) 1);
by (rtac eq_sym_conv 1);
qed "zero_is_diff_eq";
Addsimps [diff_is_0_eq, zero_is_diff_eq];

Goal "(0<n-m) = (m<n)";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_diff";
Addsimps [zero_less_diff];

Goal "i < j  ==> ? k. 0<k & i+k = j";
by (res_inst_tac [("x","j - i")] exI 1);
by (asm_simp_tac (simpset() addsimps [add_diff_inverse, less_not_sym]) 1);
qed "less_imp_add_positive";

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

Goal "0<k ==> (m*k <= n*k) = (m<=n)";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "mult_le_cancel2";

Goal "0<k ==> (k*m <= k*n) = (m<=n)";
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1);
qed "mult_le_cancel1";
Addsimps [mult_le_cancel1, mult_le_cancel2];

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




(*---------------------------------------------------------------------------*)
(* Various arithmetic proof procedures                                       *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* 1. Cancellation of common terms                                           *)
(*---------------------------------------------------------------------------*)

(*  Title:      HOL/arith_data.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Setup various arithmetic proof procedures.
*)

signature ARITH_DATA =
sig
  val nat_cancel_sums_add: simproc list
  val nat_cancel_sums: simproc list
  val nat_cancel_factor: simproc list
  val nat_cancel: simproc list
end;

structure ArithData: ARITH_DATA =
struct


(** abstract syntax of structure nat: 0, Suc, + **)

(* mk_sum, mk_norm_sum *)

val one = HOLogic.mk_nat 1;
val mk_plus = HOLogic.mk_binop "op +";

fun mk_sum [] = HOLogic.zero
  | mk_sum [t] = t
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*normal form of sums: Suc (... (Suc (a + (b + ...))))*)
fun mk_norm_sum ts =
  let val (ones, sums) = partition (equal one) ts in
    funpow (length ones) HOLogic.mk_Suc (mk_sum sums)
  end;


(* dest_sum *)

val dest_plus = HOLogic.dest_bin "op +" HOLogic.natT;

fun dest_sum tm =
  if HOLogic.is_zero tm then []
  else
    (case try HOLogic.dest_Suc tm of
      Some t => one :: dest_sum t
    | None =>
        (case try dest_plus tm of
          Some (t, u) => dest_sum t @ dest_sum u
        | None => [tm]));


(** generic proof tools **)

(* prove conversions *)

val mk_eqv = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun prove_conv expand_tac norm_tac sg (t, u) =
  mk_meta_eq (prove_goalw_cterm_nocheck [] (cterm_of sg (mk_eqv (t, u)))
    (K [expand_tac, norm_tac]))
  handle ERROR => error ("The error(s) above occurred while trying to prove " ^
    (string_of_cterm (cterm_of sg (mk_eqv (t, u)))));

val subst_equals = prove_goal HOL.thy "[| t = s; u = t |] ==> u = s"
  (fn prems => [cut_facts_tac prems 1, SIMPSET' asm_simp_tac 1]);


(* rewriting *)

fun simp_all rules = ALLGOALS (simp_tac (HOL_ss addsimps rules));

val add_rules = [add_Suc, add_Suc_right, add_0, add_0_right];
val mult_rules = [mult_Suc, mult_Suc_right, mult_0, mult_0_right];



(** cancel common summands **)

structure Sum =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac = simp_all add_rules THEN simp_all add_ac;
end;

fun gen_uncancel_tac rule ct =
  rtac (instantiate' [] [None, Some ct] (rule RS subst_equals)) 1;


(* nat eq *)

structure EqCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel;
end);


(* nat less *)

structure LessCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel "op <";
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel_less;
end);


(* nat le *)

structure LeCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel "op <=";
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel_le;
end);


(* nat diff *)

structure DiffCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binop "op -";
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac diff_cancel;
end);



(** cancel common factor **)

structure Factor =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac = simp_all (add_rules @ mult_rules) THEN simp_all add_ac;
end;

fun mk_cnat n = cterm_of (Theory.sign_of Nat.thy) (HOLogic.mk_nat n);

fun gen_multiply_tac rule k =
  if k > 0 then
    rtac (instantiate' [] [None, Some (mk_cnat (k - 1))] (rule RS subst_equals)) 1
  else no_tac;


(* nat eq *)

structure EqCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_cancel1;
end);


(* nat less *)

structure LessCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_binrel "op <";
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_less_cancel1;
end);


(* nat le *)

structure LeCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_binrel "op <=";
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_le_cancel1;
end);



(** prepare nat_cancel simprocs **)

fun prep_pat s = Thm.read_cterm (Theory.sign_of Arith.thy) (s, HOLogic.termT);
val prep_pats = map prep_pat;

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;

val eq_pats = prep_pats ["(l::nat) + m = n", "(l::nat) = m + n", "Suc m = n", "m = Suc n"];
val less_pats = prep_pats ["(l::nat) + m < n", "(l::nat) < m + n", "Suc m < n", "m < Suc n"];
val le_pats = prep_pats ["(l::nat) + m <= n", "(l::nat) <= m + n", "Suc m <= n", "m <= Suc n"];
val diff_pats = prep_pats ["((l::nat) + m) - n", "(l::nat) - (m + n)", "Suc m - n", "m - Suc n"];

val nat_cancel_sums_add = map prep_simproc
  [("nateq_cancel_sums", eq_pats, EqCancelSums.proc),
   ("natless_cancel_sums", less_pats, LessCancelSums.proc),
   ("natle_cancel_sums", le_pats, LeCancelSums.proc)];

val nat_cancel_sums = nat_cancel_sums_add @
  [prep_simproc("natdiff_cancel_sums", diff_pats, DiffCancelSums.proc)];

val nat_cancel_factor = map prep_simproc
  [("nateq_cancel_factor", eq_pats, EqCancelFactor.proc),
   ("natless_cancel_factor", less_pats, LessCancelFactor.proc),
   ("natle_cancel_factor", le_pats, LeCancelFactor.proc)];

val nat_cancel = nat_cancel_factor @ nat_cancel_sums;


end;

open ArithData;

Addsimprocs nat_cancel;

(*---------------------------------------------------------------------------*)
(* 2. Linear arithmetic                                                      *)
(*---------------------------------------------------------------------------*)

(* Parameters data for general linear arithmetic functor *)

structure LA_Logic: LIN_ARITH_LOGIC =
struct
val ccontr = ccontr;
val conjI = conjI;
val neqE = linorder_neqE;
val notI = notI;
val sym = sym;
val not_lessD = linorder_not_less RS iffD1;
val not_leD = linorder_not_le RS iffD1;


fun mk_Eq thm = (thm RS Eq_FalseI) handle THM _ => (thm RS Eq_TrueI);

val mk_Trueprop = HOLogic.mk_Trueprop;

fun neg_prop(TP$(Const("Not",_)$t)) = TP$t
  | neg_prop(TP$t) = TP $ (Const("Not",HOLogic.boolT-->HOLogic.boolT)$t);

fun is_False thm =
  let val _ $ t = #prop(rep_thm thm)
  in t = Const("False",HOLogic.boolT) end;

fun is_nat(t) = fastype_of1 t = HOLogic.natT;

fun mk_nat_thm sg t =
  let val ct = cterm_of sg t  and cn = cterm_of sg (Var(("n",0),HOLogic.natT))
  in instantiate ([],[(cn,ct)]) le0 end;

end;

signature LIN_ARITH_DATA2 =
sig
  include LIN_ARITH_DATA
  val discrete: (string * bool)list ref
end;

structure LA_Data_Ref: LIN_ARITH_DATA2 =
struct
  val add_mono_thms = ref ([]:thm list);
  val lessD = ref ([]:thm list);
  val ss_ref = ref HOL_basic_ss;
  val discrete = ref ([]:(string*bool)list);

(* Decomposition of terms *)

fun nT (Type("fun",[N,_])) = N = HOLogic.natT
  | nT _ = false;

fun add_atom(t,m,(p,i)) = (case assoc(p,t) of None => ((t,m)::p,i)
                           | Some n => (overwrite(p,(t,n+m:int)), i));

(* Turn term into list of summand * multiplicity plus a constant *)
fun poly(Const("op +",_) $ s $ t, m, pi) = poly(s,m,poly(t,m,pi))
  | poly(all as Const("op -",T) $ s $ t, m, pi) =
      if nT T then add_atom(all,m,pi)
      else poly(s,m,poly(t,~1*m,pi))
  | poly(Const("uminus",_) $ t, m, pi) = poly(t,~1*m,pi)
  | poly(Const("0",_), _, pi) = pi
  | poly(Const("Suc",_)$t, m, (p,i)) = poly(t, m, (p,i+m))
  | poly(all as Const("op *",_) $ (Const("Numeral.number_of",_)$c) $ t, m, pi)=
      (poly(t,m*HOLogic.dest_binum c,pi)
       handle TERM _ => add_atom(all,m,pi))
  | poly(all as Const("op *",_) $ t $ (Const("Numeral.number_of",_)$c), m, pi)=
      (poly(t,m*HOLogic.dest_binum c,pi)
       handle TERM _ => add_atom(all,m,pi))
  | poly(all as Const("Numeral.number_of",_)$t,m,(p,i)) =
     ((p,i + m*HOLogic.dest_binum t)
      handle TERM _ => add_atom(all,m,(p,i)))
  | poly x  = add_atom x;

fun decomp2(rel,lhs,rhs) =
  let val (p,i) = poly(lhs,1,([],0)) and (q,j) = poly(rhs,1,([],0))
  in case rel of
       "op <"  => Some(p,i,"<",q,j)
     | "op <=" => Some(p,i,"<=",q,j)
     | "op ="  => Some(p,i,"=",q,j)
     | _       => None
  end;

fun negate(Some(x,i,rel,y,j,d)) = Some(x,i,"~"^rel,y,j,d)
  | negate None = None;

fun decomp1 (T,xxx) =
  (case T of
     Type("fun",[Type(D,[]),_]) =>
       (case assoc(!discrete,D) of
          None => None
        | Some d => (case decomp2 xxx of
                       None => None
                     | Some(p,i,rel,q,j) => Some(p,i,rel,q,j,d)))
   | _ => None);

fun decomp (_$(Const(rel,T)$lhs$rhs)) = decomp1 (T,(rel,lhs,rhs))
  | decomp (_$(Const("Not",_)$(Const(rel,T)$lhs$rhs))) =
      negate(decomp1 (T,(rel,lhs,rhs)))
  | decomp _ = None
end;

let

(* reduce contradictory <= to False.
   Most of the work is done by the cancel tactics.
*)
val add_rules = [add_0,add_0_right,Zero_not_Suc,Suc_not_Zero,le_0_eq];

val add_mono_thms = map (fn s => prove_goal Arith.thy s
 (fn prems => [cut_facts_tac prems 1,
               blast_tac (claset() addIs [add_le_mono]) 1]))
["(i <= j) & (k <= l) ==> i + k <= j + (l::nat)",
 "(i  = j) & (k <= l) ==> i + k <= j + (l::nat)",
 "(i <= j) & (k  = l) ==> i + k <= j + (l::nat)",
 "(i  = j) & (k  = l) ==> i + k  = j + (l::nat)"
];

in
LA_Data_Ref.add_mono_thms := !LA_Data_Ref.add_mono_thms @ add_mono_thms;
LA_Data_Ref.lessD := !LA_Data_Ref.lessD @ [Suc_leI];
LA_Data_Ref.ss_ref := !LA_Data_Ref.ss_ref addsimps add_rules
                      addsimprocs nat_cancel_sums_add;
LA_Data_Ref.discrete := !LA_Data_Ref.discrete @ [("nat",true)]
end;

structure Fast_Arith =
  Fast_Lin_Arith(structure LA_Logic=LA_Logic and LA_Data=LA_Data_Ref);

val fast_arith_tac = Fast_Arith.lin_arith_tac;

let
val nat_arith_simproc_pats =
  map (fn s => Thm.read_cterm (Theory.sign_of Arith.thy) (s, HOLogic.boolT))
      ["(m::nat) < n","(m::nat) <= n", "(m::nat) = n"];

val fast_nat_arith_simproc = mk_simproc
  "fast_nat_arith" nat_arith_simproc_pats Fast_Arith.lin_arith_prover;
in
Addsimprocs [fast_nat_arith_simproc]
end;

(* Because of fast_nat_arith_simproc, the arithmetic solver is really only
useful to detect inconsistencies among the premises for subgoals which are
*not* themselves (in)equalities, because the latter activate
fast_nat_arith_simproc anyway. However, it seems cheaper to activate the
solver all the time rather than add the additional check. *)

simpset_ref () := (simpset() addSolver
   (mk_solver "lin. arith." Fast_Arith.cut_lin_arith_tac));

(*Elimination of `-' on nat due to John Harrison. *)
Goal "P(a - b::nat) = (ALL d. (b = a + d --> P 0) & (a = b + d --> P d))";
by (case_tac "a <= b" 1);
by Auto_tac;
by (eres_inst_tac [("x","b-a")] allE 1);
by (asm_simp_tac (simpset() addsimps [diff_is_0_eq RS iffD2]) 1);
qed "nat_diff_split";

(*LCP's version, replacing b=a+d by a<b, which sometimes works better*)
Goal "P(a - b::nat) = (ALL d. (a<b --> P 0) & (a = b + d --> P d))";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split]));
qed "nat_diff_split'";


(* FIXME: K true should be replaced by a sensible test to speed things up
   in case there are lots of irrelevant terms involved;
   elimination of min/max can be optimized:
   (max m n + k <= r) = (m+k <= r & n+k <= r)
   (l <= min m n + k) = (l <= m+k & l <= n+k)
*)
val arith_tac_split_thms = ref [nat_diff_split,split_min,split_max];
fun arith_tac i =
  refute_tac (K true) (REPEAT o split_tac (!arith_tac_split_thms))
             ((REPEAT_DETERM o etac linorder_neqE) THEN' fast_arith_tac) i;


(* proof method setup *)

val arith_method =
  Method.METHOD (fn facts => FIRSTGOAL (Method.insert_tac facts THEN' arith_tac));

val arith_setup =
 [Method.add_methods
  [("arith", Method.no_args arith_method, "decide linear arithmethic")]];

(*---------------------------------------------------------------------------*)
(* End of proof procedures. Now go and USE them!                             *)
(*---------------------------------------------------------------------------*)

(*** Subtraction laws -- mostly from Clemens Ballarin ***)

Goal "[| a < (b::nat); c <= a |] ==> a-c < b-c";
by (arith_tac 1);
qed "diff_less_mono";

Goal "a+b < (c::nat) ==> a < c-b";
by (arith_tac 1);
qed "add_less_imp_less_diff";

Goal "(i < j-k) = (i+k < (j::nat))";
by (arith_tac 1);
qed "less_diff_conv";

Goal "(j-k <= (i::nat)) = (j <= i+k)";
by (arith_tac 1);
qed "le_diff_conv";

Goal "k <= j ==> (i <= j-k) = (i+k <= (j::nat))";
by (arith_tac 1);
qed "le_diff_conv2";

Goal "Suc i <= n ==> Suc (n - Suc i) = n - i";
by (arith_tac 1);
qed "Suc_diff_Suc";

Goal "i <= (n::nat) ==> n - (n - i) = i";
by (arith_tac 1);
qed "diff_diff_cancel";
Addsimps [diff_diff_cancel];

Goal "k <= (n::nat) ==> m <= n + m - k";
by (arith_tac 1);
qed "le_add_diff";

Goal "[| 0<k; j<i |] ==> j+k-i < k";
by (arith_tac 1);
qed "add_diff_less";

Goal "m-1 < n ==> m <= n";
by (arith_tac 1);
qed "pred_less_imp_le";

Goal "j<=i ==> i - j < Suc i - j";
by (arith_tac 1);
qed "diff_less_Suc_diff";

Goal "i - j <= Suc i - j";
by (arith_tac 1);
qed "diff_le_Suc_diff";
AddIffs [diff_le_Suc_diff];

Goal "n - Suc i <= n - i";
by (arith_tac 1);
qed "diff_Suc_le_diff";
AddIffs [diff_Suc_le_diff];

Goal "0 < n ==> (m <= n-1) = (m<n)";
by (arith_tac 1);
qed "le_pred_eq";

Goal "0 < n ==> (m-1 < n) = (m<=n)";
by (arith_tac 1);
qed "less_pred_eq";

(*Replaces the previous diff_less and le_diff_less, which had the stronger
  second premise n<=m*)
Goal "[| 0<n; 0<m |] ==> m - n < m";
by (arith_tac 1);
qed "diff_less";


(*** Reducting subtraction to addition ***)

Goal "n<=(l::nat) --> Suc l - n + m = Suc (l - n + m)";
by (simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed_spec_mp "Suc_diff_add_le";

Goal "i<n ==> n - Suc i < n - i";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_Suc_less_diff";

Goal "Suc(m)-n = (if m<n then 0 else Suc(m-n))";
by (simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "if_Suc_diff_le";

Goal "Suc(m)-n <= Suc(m-n)";
by (simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_Suc_le_Suc_diff";

Goal "[| k<=n; n<=m |] ==> (m-k) - (n-k) = m-(n::nat)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_right_cancel";


(** (Anti)Monotonicity of subtraction -- by Stephan Merz **)

(* Monotonicity of subtraction in first argument *)
Goal "m <= (n::nat) ==> (m-l) <= (n-l)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_le_mono";

Goal "m <= (n::nat) ==> (l-n) <= (l-m)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_le_mono2";

Goal "[| m < (n::nat); m<l |] ==> (l-n) < (l-m)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_less_mono2";

Goal "[| m-n = 0; n-m = 0 |] ==>  m=n";
by (asm_full_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diffs0_imp_equal";
