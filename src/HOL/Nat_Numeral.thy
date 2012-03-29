(*  Title:      HOL/Nat_Numeral.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary numerals for the natural numbers *}

theory Nat_Numeral
imports Int
begin

subsection{*Function @{term nat}: Coercion from Type @{typ int} to @{typ nat}*}

declare nat_1 [simp]

lemma nat_neg_numeral [simp]: "nat (neg_numeral w) = 0"
  by simp

lemma numeral_1_eq_Suc_0: "Numeral1 = Suc 0"
  by simp


subsection{*Function @{term int}: Coercion from Type @{typ nat} to @{typ int}*}

lemma int_numeral: "int (numeral v) = numeral v"
  by (rule of_nat_numeral) (* already simp *)

lemma nonneg_int_cases:
  fixes k :: int assumes "0 \<le> k" obtains n where "k = of_nat n"
  using assms by (cases k, simp, simp)

subsubsection{*Successor *}

lemma Suc_nat_eq_nat_zadd1: "(0::int) <= z ==> Suc (nat z) = nat (1 + z)"
apply (rule sym)
apply (simp add: nat_eq_iff)
done

lemma Suc_nat_number_of_add:
  "Suc (numeral v + n) = numeral (v + Num.One) + n"
  by simp


subsubsection{*Subtraction *}

lemma diff_nat_eq_if:
     "nat z - nat z' =  
        (if z' < 0 then nat z   
         else let d = z-z' in     
              if d < 0 then 0 else nat d)"
by (simp add: Let_def nat_diff_distrib [symmetric])

(* Int.nat_diff_distrib has too-strong premises *)
lemma nat_diff_distrib': "\<lbrakk>0 \<le> x; 0 \<le> y\<rbrakk> \<Longrightarrow> nat (x - y) = nat x - nat y"
apply (rule int_int_eq [THEN iffD1], clarsimp)
apply (subst zdiff_int [symmetric])
apply (rule nat_mono, simp_all)
done

lemma diff_nat_numeral [simp]: 
  "(numeral v :: nat) - numeral v' = nat (numeral v - numeral v')"
  by (simp only: nat_diff_distrib' zero_le_numeral nat_numeral)

lemma nat_numeral_diff_1 [simp]:
  "numeral v - (1::nat) = nat (numeral v - 1)"
  using diff_nat_numeral [of v Num.One] by simp


subsection{*Comparisons*}

(*Maps #n to n for n = 1, 2*)
lemmas numerals = numeral_1_eq_1 [where 'a=nat] numeral_2_eq_2


subsection{*Powers with Numeric Exponents*}

text{*Squares of literal numerals will be evaluated.*}
(* FIXME: replace with more general rules for powers of numerals *)
lemmas power2_eq_square_numeral [simp] =
    power2_eq_square [of "numeral w"] for w


text{*Simprules for comparisons where common factors can be cancelled.*}
lemmas zero_compare_simps =
    add_strict_increasing add_strict_increasing2 add_increasing
    zero_le_mult_iff zero_le_divide_iff 
    zero_less_mult_iff zero_less_divide_iff 
    mult_le_0_iff divide_le_0_iff 
    mult_less_0_iff divide_less_0_iff 
    zero_le_power2 power2_less_0

subsubsection{*Nat *}

lemma Suc_pred': "0 < n ==> n = Suc(n - 1)"
by simp

(*Expresses a natural number constant as the Suc of another one.
  NOT suitable for rewriting because n recurs on the right-hand side.*)
lemmas expand_Suc = Suc_pred' [of "numeral v", OF zero_less_numeral] for v

subsubsection{*Arith *}

lemma Suc_eq_plus1: "Suc n = n + 1"
  unfolding One_nat_def by simp

lemma Suc_eq_plus1_left: "Suc n = 1 + n"
  unfolding One_nat_def by simp

(* These two can be useful when m = numeral... *)

lemma add_eq_if: "(m::nat) + n = (if m=0 then n else Suc ((m - 1) + n))"
  unfolding One_nat_def by (cases m) simp_all

lemma mult_eq_if: "(m::nat) * n = (if m=0 then 0 else n + ((m - 1) * n))"
  unfolding One_nat_def by (cases m) simp_all

lemma power_eq_if: "(p ^ m :: nat) = (if m=0 then 1 else p * (p ^ (m - 1)))"
  unfolding One_nat_def by (cases m) simp_all


subsection{*Comparisons involving  @{term Suc} *}

lemma eq_numeral_Suc [simp]: "numeral v = Suc n \<longleftrightarrow> nat (numeral v - 1) = n"
  by (subst expand_Suc, simp only: nat.inject nat_numeral_diff_1)

lemma Suc_eq_numeral [simp]: "Suc n = numeral v \<longleftrightarrow> n = nat (numeral v - 1)"
  by (subst expand_Suc, simp only: nat.inject nat_numeral_diff_1)

lemma less_numeral_Suc [simp]: "numeral v < Suc n \<longleftrightarrow> nat (numeral v - 1) < n"
  by (subst expand_Suc, simp only: Suc_less_eq nat_numeral_diff_1)

lemma less_Suc_numeral [simp]: "Suc n < numeral v \<longleftrightarrow> n < nat (numeral v - 1)"
  by (subst expand_Suc, simp only: Suc_less_eq nat_numeral_diff_1)

lemma le_numeral_Suc [simp]: "numeral v \<le> Suc n \<longleftrightarrow> nat (numeral v - 1) \<le> n"
  by (subst expand_Suc, simp only: Suc_le_mono nat_numeral_diff_1)

lemma le_Suc_numeral [simp]: "Suc n \<le> numeral v \<longleftrightarrow> n \<le> nat (numeral v - 1)"
  by (subst expand_Suc, simp only: Suc_le_mono nat_numeral_diff_1)


subsection{*Max and Min Combined with @{term Suc} *}

lemma max_Suc_numeral [simp]:
  "max (Suc n) (numeral v) = Suc (max n (nat (numeral v - 1)))"
  by (subst expand_Suc, simp only: max_Suc_Suc nat_numeral_diff_1)

lemma max_numeral_Suc [simp]:
  "max (numeral v) (Suc n) = Suc (max (nat (numeral v - 1)) n)"
  by (subst expand_Suc, simp only: max_Suc_Suc nat_numeral_diff_1)

lemma min_Suc_numeral [simp]:
  "min (Suc n) (numeral v) = Suc (min n (nat (numeral v - 1)))"
  by (subst expand_Suc, simp only: min_Suc_Suc nat_numeral_diff_1)

lemma min_numeral_Suc [simp]:
  "min (numeral v) (Suc n) = Suc (min (nat (numeral v - 1)) n)"
  by (subst expand_Suc, simp only: min_Suc_Suc nat_numeral_diff_1)
 
subsection{*Literal arithmetic involving powers*}

(* TODO: replace with more generic rule for powers of numerals *)
lemma power_nat_numeral:
  "(numeral v :: nat) ^ n = nat ((numeral v :: int) ^ n)"
  by (simp only: nat_power_eq zero_le_numeral nat_numeral)

lemmas power_nat_numeral_numeral = power_nat_numeral [of _ "numeral w"] for w
declare power_nat_numeral_numeral [simp]


text{*For arbitrary rings*}

lemma power_numeral_even:
  fixes z :: "'a::monoid_mult"
  shows "z ^ numeral (Num.Bit0 w) = (let w = z ^ (numeral w) in w * w)"
  unfolding numeral_Bit0 power_add Let_def ..

lemma power_numeral_odd:
  fixes z :: "'a::monoid_mult"
  shows "z ^ numeral (Num.Bit1 w) = (let w = z ^ (numeral w) in z * w * w)"
  unfolding numeral_Bit1 One_nat_def add_Suc_right add_0_right
  unfolding power_Suc power_add Let_def mult_assoc ..

lemmas zpower_numeral_even = power_numeral_even [where 'a=int]
lemmas zpower_numeral_odd = power_numeral_odd [where 'a=int]

lemmas power_numeral_even_numeral [simp] =
    power_numeral_even [of "numeral v"] for v

lemmas power_numeral_odd_numeral [simp] =
    power_numeral_odd [of "numeral v"] for v

lemma nat_numeral_Bit0:
  "numeral (Num.Bit0 w) = (let n::nat = numeral w in n + n)"
  unfolding numeral_Bit0 Let_def ..

lemma nat_numeral_Bit1:
  "numeral (Num.Bit1 w) = (let n = numeral w in Suc (n + n))"
  unfolding numeral_Bit1 Let_def by simp

lemmas eval_nat_numeral =
  nat_numeral_Bit0 nat_numeral_Bit1

lemmas nat_arith =
  diff_nat_numeral

lemmas semiring_norm =
  Let_def arith_simps nat_arith rel_simps
  if_False if_True
  add_0 add_Suc add_numeral_left
  add_neg_numeral_left mult_numeral_left
  numeral_1_eq_1 [symmetric] Suc_eq_plus1
  eq_numeral_iff_iszero not_iszero_Numeral1

lemma Let_Suc [simp]: "Let (Suc n) f == f (Suc n)"
  by (fact Let_def)

lemma power_m1_even: "(-1) ^ (2*n) = (1::'a::ring_1)"
  by (fact power_minus1_even) (* FIXME: duplicate *)

lemma power_m1_odd: "(-1) ^ Suc(2*n) = (-1::'a::ring_1)"
  by (fact power_minus1_odd) (* FIXME: duplicate *)


subsection{*Literal arithmetic and @{term of_nat}*}

lemma of_nat_double:
     "0 \<le> x ==> of_nat (nat (2 * x)) = of_nat (nat x) + of_nat (nat x)"
by (simp only: mult_2 nat_add_distrib of_nat_add) 


subsubsection{*For simplifying @{term "Suc m - K"} and  @{term "K - Suc m"}*}

text{*Where K above is a literal*}

lemma Suc_diff_eq_diff_pred: "0 < n ==> Suc m - n = m - (n - Numeral1)"
by (simp split: nat_diff_split)

text{*No longer required as a simprule because of the @{text inverse_fold}
   simproc*}
lemma Suc_diff_numeral: "Suc m - (numeral v) = m - (numeral v - 1)"
  by (subst expand_Suc, simp only: diff_Suc_Suc)

lemma diff_Suc_eq_diff_pred: "m - Suc n = (m - 1) - n"
by (simp split: nat_diff_split)


subsubsection{*For @{term nat_case} and @{term nat_rec}*}

lemma nat_case_numeral [simp]:
  "nat_case a f (numeral v) = (let pv = nat (numeral v - 1) in f pv)"
  by (subst expand_Suc, simp only: nat.cases nat_numeral_diff_1 Let_def)

lemma nat_case_add_eq_if [simp]:
  "nat_case a f ((numeral v) + n) = (let pv = nat (numeral v - 1) in f (pv + n))"
  by (subst expand_Suc, simp only: nat.cases nat_numeral_diff_1 Let_def add_Suc)

lemma nat_rec_numeral [simp]:
  "nat_rec a f (numeral v) = (let pv = nat (numeral v - 1) in f pv (nat_rec a f pv))"
  by (subst expand_Suc, simp only: nat_rec_Suc nat_numeral_diff_1 Let_def)

lemma nat_rec_add_eq_if [simp]:
  "nat_rec a f (numeral v + n) =
    (let pv = nat (numeral v - 1) in f (pv + n) (nat_rec a f (pv + n)))"
  by (subst expand_Suc, simp only: nat_rec_Suc nat_numeral_diff_1 Let_def add_Suc)


subsubsection{*Various Other Lemmas*}

lemma card_UNIV_bool[simp]: "card (UNIV :: bool set) = 2"
by(simp add: UNIV_bool)

text {*Evens and Odds, for Mutilated Chess Board*}

text{*Lemmas for specialist use, NOT as default simprules*}
lemma nat_mult_2: "2 * z = (z+z::nat)"
by (rule mult_2) (* FIXME: duplicate *)

lemma nat_mult_2_right: "z * 2 = (z+z::nat)"
by (rule mult_2_right) (* FIXME: duplicate *)

text{*Case analysis on @{term "n<2"}*}
lemma less_2_cases: "(n::nat) < 2 ==> n = 0 | n = Suc 0"
by (auto simp add: numeral_2_eq_2)

text{*Removal of Small Numerals: 0, 1 and (in additive positions) 2*}

lemma add_2_eq_Suc [simp]: "2 + n = Suc (Suc n)"
by simp

lemma add_2_eq_Suc' [simp]: "n + 2 = Suc (Suc n)"
by simp

text{*Can be used to eliminate long strings of Sucs, but not by default*}
lemma Suc3_eq_add_3: "Suc (Suc (Suc n)) = 3 + n"
by simp

text{*Legacy theorems*}

lemmas nat_1_add_1 = one_add_one [where 'a=nat]

end
