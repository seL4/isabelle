(*  Title:      HOL/NatArith.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel
*)

header {*Further Arithmetic Facts Concerning the Natural Numbers*}

theory NatArith
imports Nat
files "arith_data.ML"
begin

setup arith_setup

text{*The following proofs may rely on the arithmetic proof procedures.*}

lemma pred_nat_trancl_eq_le: "((m, n) : pred_nat^*) = (m \<le> n)"
by (simp add: less_eq reflcl_trancl [symmetric]
            del: reflcl_trancl, arith)

lemma nat_diff_split:
    "P(a - b::nat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
    -- {* elimination of @{text -} on @{text nat} *}
  by (cases "a<b" rule: case_split)
     (auto simp add: diff_is_0_eq [THEN iffD2])

lemma nat_diff_split_asm:
    "P(a - b::nat) = (~ (a < b & ~ P 0 | (EX d. a = b + d & ~ P d)))"
    -- {* elimination of @{text -} on @{text nat} in assumptions *}
  by (simp split: nat_diff_split)

lemmas [arith_split] = nat_diff_split split_min split_max



lemma le_square: "m \<le> m*(m::nat)"
by (induct_tac "m", auto)

lemma le_cube: "(m::nat) \<le> m*(m*m)"
by (induct_tac "m", auto)


text{*Subtraction laws, mostly by Clemens Ballarin*}

lemma diff_less_mono: "[| a < (b::nat); c \<le> a |] ==> a-c < b-c"
by arith

lemma less_diff_conv: "(i < j-k) = (i+k < (j::nat))"
by arith

lemma le_diff_conv: "(j-k \<le> (i::nat)) = (j \<le> i+k)"
by arith

lemma le_diff_conv2: "k \<le> j ==> (i \<le> j-k) = (i+k \<le> (j::nat))"
by arith

lemma diff_diff_cancel [simp]: "i \<le> (n::nat) ==> n - (n - i) = i"
by arith

lemma le_add_diff: "k \<le> (n::nat) ==> m \<le> n + m - k"
by arith

(*Replaces the previous diff_less and le_diff_less, which had the stronger
  second premise n\<le>m*)
lemma diff_less[simp]: "!!m::nat. [| 0<n; 0<m |] ==> m - n < m"
by arith


(** Simplification of relational expressions involving subtraction **)

lemma diff_diff_eq: "[| k \<le> m;  k \<le> (n::nat) |] ==> ((m-k) - (n-k)) = (m-n)"
by (simp split add: nat_diff_split)

lemma eq_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k = n-k) = (m=n)"
by (auto split add: nat_diff_split)

lemma less_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k < n-k) = (m<n)"
by (auto split add: nat_diff_split)

lemma le_diff_iff: "[| k \<le> m;  k \<le> (n::nat) |] ==> (m-k \<le> n-k) = (m\<le>n)"
by (auto split add: nat_diff_split)


text{*(Anti)Monotonicity of subtraction -- by Stephan Merz*}

(* Monotonicity of subtraction in first argument *)
lemma diff_le_mono: "m \<le> (n::nat) ==> (m-l) \<le> (n-l)"
by (simp split add: nat_diff_split)

lemma diff_le_mono2: "m \<le> (n::nat) ==> (l-n) \<le> (l-m)"
by (simp split add: nat_diff_split)

lemma diff_less_mono2: "[| m < (n::nat); m<l |] ==> (l-n) < (l-m)"
by (simp split add: nat_diff_split)

lemma diffs0_imp_equal: "!!m::nat. [| m-n = 0; n-m = 0 |] ==>  m=n"
by (simp split add: nat_diff_split)

text{*Lemmas for ex/Factorization*}

lemma one_less_mult: "[| Suc 0 < n; Suc 0 < m |] ==> Suc 0 < m*n"
by (case_tac "m", auto)

lemma n_less_m_mult_n: "[| Suc 0 < n; Suc 0 < m |] ==> n<m*n"
by (case_tac "m", auto)

lemma n_less_n_mult_m: "[| Suc 0 < n; Suc 0 < m |] ==> n<n*m"
by (case_tac "m", auto)


text{*Rewriting to pull differences out*}

lemma diff_diff_right [simp]: "k\<le>j --> i - (j - k) = i + (k::nat) - j"
by arith

lemma diff_Suc_diff_eq1 [simp]: "k \<le> j ==> m - Suc (j - k) = m + k - Suc j"
by arith

lemma diff_Suc_diff_eq2 [simp]: "k \<le> j ==> Suc (j - k) - m = Suc j - (k + m)"
by arith

(*The others are
      i - j - k = i - (j + k),
      k \<le> j ==> j - k + i = j + i - k,
      k \<le> j ==> i + (j - k) = i + j - k *)
declare diff_diff_left [simp] 
        diff_add_assoc [symmetric, simp]
        diff_add_assoc2[symmetric, simp]

text{*At present we prove no analogue of @{text not_less_Least} or @{text
Least_Suc}, since there appears to be no need.*}

ML
{*
val pred_nat_trancl_eq_le = thm "pred_nat_trancl_eq_le";
val nat_diff_split = thm "nat_diff_split";
val nat_diff_split_asm = thm "nat_diff_split_asm";
val le_square = thm "le_square";
val le_cube = thm "le_cube";
val diff_less_mono = thm "diff_less_mono";
val less_diff_conv = thm "less_diff_conv";
val le_diff_conv = thm "le_diff_conv";
val le_diff_conv2 = thm "le_diff_conv2";
val diff_diff_cancel = thm "diff_diff_cancel";
val le_add_diff = thm "le_add_diff";
val diff_less = thm "diff_less";
val diff_diff_eq = thm "diff_diff_eq";
val eq_diff_iff = thm "eq_diff_iff";
val less_diff_iff = thm "less_diff_iff";
val le_diff_iff = thm "le_diff_iff";
val diff_le_mono = thm "diff_le_mono";
val diff_le_mono2 = thm "diff_le_mono2";
val diff_less_mono2 = thm "diff_less_mono2";
val diffs0_imp_equal = thm "diffs0_imp_equal";
val one_less_mult = thm "one_less_mult";
val n_less_m_mult_n = thm "n_less_m_mult_n";
val n_less_n_mult_m = thm "n_less_n_mult_m";
val diff_diff_right = thm "diff_diff_right";
val diff_Suc_diff_eq1 = thm "diff_Suc_diff_eq1";
val diff_Suc_diff_eq2 = thm "diff_Suc_diff_eq2";
*}

subsection{*Embedding of the Naturals into any @{text
comm_semiring_1_cancel}: @{term of_nat}*}

consts of_nat :: "nat => 'a::comm_semiring_1_cancel"

primrec
  of_nat_0:   "of_nat 0 = 0"
  of_nat_Suc: "of_nat (Suc m) = of_nat m + 1"

lemma of_nat_1 [simp]: "of_nat 1 = 1"
by simp

lemma of_nat_add [simp]: "of_nat (m+n) = of_nat m + of_nat n"
apply (induct m)
apply (simp_all add: add_ac)
done

lemma of_nat_mult [simp]: "of_nat (m*n) = of_nat m * of_nat n"
apply (induct m)
apply (simp_all add: mult_ac add_ac right_distrib)
done

lemma zero_le_imp_of_nat: "0 \<le> (of_nat m::'a::ordered_semidom)"
apply (induct m, simp_all)
apply (erule order_trans)
apply (rule less_add_one [THEN order_less_imp_le])
done

lemma less_imp_of_nat_less:
     "m < n ==> of_nat m < (of_nat n::'a::ordered_semidom)"
apply (induct m n rule: diff_induct, simp_all)
apply (insert add_le_less_mono [OF zero_le_imp_of_nat zero_less_one], force)
done

lemma of_nat_less_imp_less:
     "of_nat m < (of_nat n::'a::ordered_semidom) ==> m < n"
apply (induct m n rule: diff_induct, simp_all)
apply (insert zero_le_imp_of_nat)
apply (force simp add: linorder_not_less [symmetric])
done

lemma of_nat_less_iff [simp]:
     "(of_nat m < (of_nat n::'a::ordered_semidom)) = (m<n)"
by (blast intro: of_nat_less_imp_less less_imp_of_nat_less)

text{*Special cases where either operand is zero*}
declare of_nat_less_iff [of 0, simplified, simp]
declare of_nat_less_iff [of _ 0, simplified, simp]

lemma of_nat_le_iff [simp]:
     "(of_nat m \<le> (of_nat n::'a::ordered_semidom)) = (m \<le> n)"
by (simp add: linorder_not_less [symmetric])

text{*Special cases where either operand is zero*}
declare of_nat_le_iff [of 0, simplified, simp]
declare of_nat_le_iff [of _ 0, simplified, simp]

text{*The ordering on the @{text comm_semiring_1_cancel} is necessary
to exclude the possibility of a finite field, which indeed wraps back to
zero.*}
lemma of_nat_eq_iff [simp]:
     "(of_nat m = (of_nat n::'a::ordered_semidom)) = (m = n)"
by (simp add: order_eq_iff)

text{*Special cases where either operand is zero*}
declare of_nat_eq_iff [of 0, simplified, simp]
declare of_nat_eq_iff [of _ 0, simplified, simp]

lemma of_nat_diff [simp]:
     "n \<le> m ==> of_nat (m - n) = of_nat m - (of_nat n :: 'a::comm_ring_1)"
by (simp del: of_nat_add
	 add: compare_rls of_nat_add [symmetric] split add: nat_diff_split)


end
