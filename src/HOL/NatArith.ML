(*  Title:      HOL/NatArith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Further proofs about elementary arithmetic, using the arithmetic proof
procedures.
*)

(*legacy ...*)
structure NatArith = struct val thy = the_context () end;


Goal "m <= m*(m::nat)";
by (induct_tac "m" 1);
by Auto_tac;
qed "le_square";

Goal "(m::nat) <= m*(m*m)";
by (induct_tac "m" 1);
by Auto_tac;
qed "le_cube";


(*** Subtraction laws -- mostly from Clemens Ballarin ***)

Goal "[| a < (b::nat); c <= a |] ==> a-c < b-c";
by (arith_tac 1);
qed "diff_less_mono";

Goal "(i < j-k) = (i+k < (j::nat))";
by (arith_tac 1);
qed "less_diff_conv";

Goal "(j-k <= (i::nat)) = (j <= i+k)";
by (arith_tac 1);
qed "le_diff_conv";

Goal "k <= j ==> (i <= j-k) = (i+k <= (j::nat))";
by (arith_tac 1);
qed "le_diff_conv2";

Goal "i <= (n::nat) ==> n - (n - i) = i";
by (arith_tac 1);
qed "diff_diff_cancel";
Addsimps [diff_diff_cancel];

Goal "k <= (n::nat) ==> m <= n + m - k";
by (arith_tac 1);
qed "le_add_diff";

(*Replaces the previous diff_less and le_diff_less, which had the stronger
  second premise n<=m*)
Goal "!!m::nat. [| 0<n; 0<m |] ==> m - n < m";
by (arith_tac 1);
qed "diff_less";


(** Simplification of relational expressions involving subtraction **)

Goal "[| k <= m;  k <= (n::nat) |] ==> ((m-k) - (n-k)) = (m-n)";
by (asm_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diff_diff_eq";

Goal "[| k <= m;  k <= (n::nat) |] ==> (m-k = n-k) = (m=n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split]));
qed "eq_diff_iff";

Goal "[| k <= m;  k <= (n::nat) |] ==> (m-k < n-k) = (m<n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split]));
qed "less_diff_iff";

Goal "[| k <= m;  k <= (n::nat) |] ==> (m-k <= n-k) = (m<=n)";
by (auto_tac (claset(), simpset() addsplits [nat_diff_split]));
qed "le_diff_iff";


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

Goal "!!m::nat. [| m-n = 0; n-m = 0 |] ==>  m=n";
by (asm_full_simp_tac (simpset() addsplits [nat_diff_split]) 1);
qed "diffs0_imp_equal";

(** Lemmas for ex/Factorization **)

Goal "!!m::nat. [| 1<n; 1<m |] ==> 1<m*n";
by (case_tac "m" 1);
by Auto_tac;
qed "one_less_mult"; 

Goal "!!m::nat. [| 1<n; 1<m |] ==> n<m*n";
by (case_tac "m" 1);
by Auto_tac;
qed "n_less_m_mult_n"; 

Goal "!!m::nat. [| 1<n; 1<m |] ==> n<n*m";
by (case_tac "m" 1);
by Auto_tac;
qed "n_less_n_mult_m"; 


(** Rewriting to pull differences out **)

Goal "k<=j --> i - (j - k) = i + (k::nat) - j";
by (arith_tac 1);
qed "diff_diff_right";

Goal "k <= j ==> m - Suc (j - k) = m + k - Suc j";
by (arith_tac 1);
qed "diff_Suc_diff_eq1"; 

Goal "k <= j ==> Suc (j - k) - m = Suc j - (k + m)";
by (arith_tac 1);
qed "diff_Suc_diff_eq2"; 

(*The others are
      i - j - k = i - (j + k),
      k <= j ==> j - k + i = j + i - k,
      k <= j ==> i + (j - k) = i + j - k *)
Addsimps [diff_diff_left, diff_diff_right, diff_add_assoc2 RS sym, 
	  diff_add_assoc RS sym, diff_Suc_diff_eq1, diff_Suc_diff_eq2];



(** GREATEST theorems for type "nat": not dual to LEAST, since there is
    no greatest natural number.  [The LEAST proofs are in Nat.ML, but the
    GREATEST proofs require more infrastructure.] **)

Goal "[|P k;  ALL x. P x --> (EX y. P y & ~ ((m y::nat) <= m x))|] \
\     ==> EX y. P y & ~ (m y < m k + n)";
by (induct_tac "n" 1);
by (Force_tac 1); 
(*ind step*)
by (force_tac (claset(), simpset() addsimps [le_Suc_eq]) 1); 
qed "ex_has_greatest_nat_lemma";

Goal "[|P k;  ! y. P y --> m y < b|] \
\     ==> ? x. P x & (! y. P y --> (m y::nat) <= m x)";
by (rtac ccontr 1); 
by (cut_inst_tac [("P","P"),("n","b - m k")] ex_has_greatest_nat_lemma 1);
by (subgoal_tac "m k <= b" 3);
by Auto_tac;  
qed "ex_has_greatest_nat";

Goalw [GreatestM_def]
     "[|P k;  ! y. P y --> m y < b|] \
\     ==> P (GreatestM m P) & (!y. P y --> (m y::nat) <= m (GreatestM m P))";
by (rtac someI_ex 1);
by (etac ex_has_greatest_nat 1);
by (assume_tac 1); 
qed "GreatestM_nat_lemma";

bind_thm ("GreatestM_natI", GreatestM_nat_lemma RS conjunct1);

Goal "[|P x;  ! y. P y --> m y < b|] \
\     ==> (m x::nat) <= m (GreatestM m P)";
by (blast_tac (claset() addDs [GreatestM_nat_lemma RS conjunct2 RS spec]) 1);
qed "GreatestM_nat_le";

(** Specialization to GREATEST **)

Goalw [Greatest_def]
     "[|P (k::nat);  ! y. P y --> y < b|] ==> P (GREATEST x. P x)";
by (rtac GreatestM_natI 1); 
by Auto_tac;  
qed "GreatestI";

Goalw [Greatest_def]
     "[|P x;  ! y. P y --> y < b|] ==> (x::nat) <= (GREATEST x. P x)";
by (rtac GreatestM_nat_le 1); 
by Auto_tac;  
qed "Greatest_le";

(*No analogue of not_less_Least or Least_Suc yet, since it isn't used much*)

