(*  Title:      HOL/Library/Code_Binary_Nat.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Implementation of natural numbers as binary numerals\<close>

theory Code_Binary_Nat
imports Code_Abstract_Nat
begin

text \<open>
  When generating code for functions on natural numbers, the
  canonical representation using \<^term>\<open>0::nat\<close> and
  \<^term>\<open>Suc\<close> is unsuitable for computations involving large
  numbers.  This theory refines the representation of
  natural numbers for code generation to use binary
  numerals, which do not grow linear in size but logarithmic.
\<close>

subsection \<open>Representation\<close>

code_datatype "0::nat" nat_of_num

lemma [code]:
  "num_of_nat 0 = Num.One"
  "num_of_nat (nat_of_num k) = k"
  by (simp_all add: nat_of_num_inverse)

lemma [code]:
  "(1::nat) = Numeral1"
  by simp

lemma [code_abbrev]: "Numeral1 = (1::nat)"
  by simp

lemma [code]:
  "Suc n = n + 1"
  by simp


subsection \<open>Basic arithmetic\<close>

context
begin

declare [[code drop: "plus :: nat \<Rightarrow> _"]]  

lemma plus_nat_code [code]:
  "nat_of_num k + nat_of_num l = nat_of_num (k + l)"
  "m + 0 = (m::nat)"
  "0 + n = (n::nat)"
  by (simp_all add: nat_of_num_numeral)

text \<open>Bounded subtraction needs some auxiliary\<close>

qualified definition dup :: "nat \<Rightarrow> nat" where
  "dup n = n + n"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (nat_of_num k) = nat_of_num (Num.Bit0 k)"
  by (simp_all add: dup_def numeral_Bit0)

qualified definition sub :: "num \<Rightarrow> num \<Rightarrow> nat option" where
  "sub k l = (if k \<ge> l then Some (numeral k - numeral l) else None)"

lemma sub_code [code]:
  "sub Num.One Num.One = Some 0"
  "sub (Num.Bit0 m) Num.One = Some (nat_of_num (Num.BitM m))"
  "sub (Num.Bit1 m) Num.One = Some (nat_of_num (Num.Bit0 m))"
  "sub Num.One (Num.Bit0 n) = None"
  "sub Num.One (Num.Bit1 n) = None"
  "sub (Num.Bit0 m) (Num.Bit0 n) = map_option dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit1 n) = map_option dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit0 n) = map_option (\<lambda>q. dup q + 1) (sub m n)"
  "sub (Num.Bit0 m) (Num.Bit1 n) = (case sub m n of None \<Rightarrow> None
     | Some q \<Rightarrow> if q = 0 then None else Some (dup q - 1))"
  by (auto simp: nat_of_num_numeral Num.dbl_def Num.dbl_inc_def Num.dbl_dec_def
    Let_def le_imp_diff_is_add BitM_plus_one sub_def dup_def 
    sub_non_positive nat_add_distrib sub_non_negative)

declare [[code drop: "minus :: nat \<Rightarrow> _"]]

lemma minus_nat_code [code]:
  "nat_of_num k - nat_of_num l = (case sub k l of None \<Rightarrow> 0 | Some j \<Rightarrow> j)"
  "m - 0 = (m::nat)"
  "0 - n = (0::nat)"
  by (simp_all add: nat_of_num_numeral sub_non_positive sub_def)

declare [[code drop: "times :: nat \<Rightarrow> _"]]

lemma times_nat_code [code]:
  "nat_of_num k * nat_of_num l = nat_of_num (k * l)"
  "m * 0 = (0::nat)"
  "0 * n = (0::nat)"
  by (simp_all add: nat_of_num_numeral)

declare [[code drop: "HOL.equal :: nat \<Rightarrow> _"]]

lemma equal_nat_code [code]:
  "HOL.equal 0 (0::nat) \<longleftrightarrow> True"
  "HOL.equal 0 (nat_of_num l) \<longleftrightarrow> False"
  "HOL.equal (nat_of_num k) 0 \<longleftrightarrow> False"
  "HOL.equal (nat_of_num k) (nat_of_num l) \<longleftrightarrow> HOL.equal k l"
  by (simp_all add: nat_of_num_numeral equal)

lemma equal_nat_refl [code nbe]:
  "HOL.equal (n::nat) n \<longleftrightarrow> True"
  by (rule equal_refl)

declare [[code drop: "less_eq :: nat \<Rightarrow> _"]]

lemma less_eq_nat_code [code]:
  "0 \<le> (n::nat) \<longleftrightarrow> True"
  "nat_of_num k \<le> 0 \<longleftrightarrow> False"
  "nat_of_num k \<le> nat_of_num l \<longleftrightarrow> k \<le> l"
  by (simp_all add: nat_of_num_numeral)

declare [[code drop: "less :: nat \<Rightarrow> _"]]

lemma less_nat_code [code]:
  "(m::nat) < 0 \<longleftrightarrow> False"
  "0 < nat_of_num l \<longleftrightarrow> True"
  "nat_of_num k < nat_of_num l \<longleftrightarrow> k < l"
  by (simp_all add: nat_of_num_numeral)

declare [[code drop: Euclidean_Rings.divmod_nat]]
  
lemma divmod_nat_code [code]:
  "Euclidean_Rings.divmod_nat (nat_of_num k) (nat_of_num l) = divmod k l"
  "Euclidean_Rings.divmod_nat m 0 = (0, m)"
  "Euclidean_Rings.divmod_nat 0 n = (0, 0)"
  by (simp_all add: Euclidean_Rings.divmod_nat_def nat_of_num_numeral)

end


subsection \<open>Conversions\<close>

declare [[code drop: of_nat]]

lemma of_nat_code [code]:
  "of_nat 0 = 0"
  "of_nat (nat_of_num k) = numeral k"
  by (simp_all add: nat_of_num_numeral)


code_identifier
  code_module Code_Binary_Nat \<rightharpoonup>
    (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
