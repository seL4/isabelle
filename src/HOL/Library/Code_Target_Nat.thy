(*  Title:      HOL/Library/Code_Target_Nat.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Implementation of natural numbers by target-language integers *}

theory Code_Target_Nat
imports Code_Abstract_Nat
begin

subsection {* Implementation for @{typ nat} *}

context
includes natural.lifting integer.lifting
begin

lift_definition Nat :: "integer \<Rightarrow> nat"
  is nat
  .

lemma [code_post]:
  "Nat 0 = 0"
  "Nat 1 = 1"
  "Nat (numeral k) = numeral k"
  by (transfer, simp)+

lemma [code_abbrev]:
  "integer_of_nat = of_nat"
  by transfer rule

lemma [code_unfold]:
  "Int.nat (int_of_integer k) = nat_of_integer k"
  by transfer rule

lemma [code abstype]:
  "Code_Target_Nat.Nat (integer_of_nat n) = n"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat (nat_of_integer k) = max 0 k"
  by transfer auto

lemma [code_abbrev]:
  "nat_of_integer (numeral k) = nat_of_num k"
  by transfer (simp add: nat_of_num_numeral)

lemma [code abstract]:
  "integer_of_nat (nat_of_num n) = integer_of_num n"
  by transfer (simp add: nat_of_num_numeral)

lemma [code abstract]:
  "integer_of_nat 0 = 0"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat 1 = 1"
  by transfer simp

lemma [code]:
  "Suc n = n + 1"
  by simp

lemma [code abstract]:
  "integer_of_nat (m + n) = of_nat m + of_nat n"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat (m - n) = max 0 (of_nat m - of_nat n)"
  by transfer simp

lemma [code abstract]:
  "integer_of_nat (m * n) = of_nat m * of_nat n"
  by transfer (simp add: of_nat_mult)

lemma [code abstract]:
  "integer_of_nat (m div n) = of_nat m div of_nat n"
  by transfer (simp add: zdiv_int)

lemma [code abstract]:
  "integer_of_nat (m mod n) = of_nat m mod of_nat n"
  by transfer (simp add: zmod_int)

lemma [code]:
  "Divides.divmod_nat m n = (m div n, m mod n)"
  by (fact divmod_nat_div_mod)

lemma [code]:
  "HOL.equal m n = HOL.equal (of_nat m :: integer) (of_nat n)"
  by transfer (simp add: equal)

lemma [code]:
  "m \<le> n \<longleftrightarrow> (of_nat m :: integer) \<le> of_nat n"
  by simp

lemma [code]:
  "m < n \<longleftrightarrow> (of_nat m :: integer) < of_nat n"
  by simp

lemma num_of_nat_code [code]:
  "num_of_nat = num_of_integer \<circ> of_nat"
  by transfer (simp add: fun_eq_iff)

end

lemma (in semiring_1) of_nat_code_if:
  "of_nat n = (if n = 0 then 0
     else let
       (m, q) = divmod_nat n 2;
       m' = 2 * of_nat m
     in if q = 0 then m' else m' + 1)"
proof -
  from mod_div_equality have *: "of_nat n = of_nat (n div 2 * 2 + n mod 2)" by simp
  show ?thesis
    by (simp add: Let_def divmod_nat_div_mod of_nat_add [symmetric])
      (simp add: * mult_commute of_nat_mult add_commute)
qed

declare of_nat_code_if [code]

definition int_of_nat :: "nat \<Rightarrow> int" where
  [code_abbrev]: "int_of_nat = of_nat"

lemma [code]:
  "int_of_nat n = int_of_integer (of_nat n)"
  by (simp add: int_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (nat k) = max 0 (integer_of_int k)"
  including integer.lifting by transfer auto

lemma term_of_nat_code [code]:
  -- {* Use @{term Code_Numeral.nat_of_integer} in term reconstruction
        instead of @{term Code_Target_Nat.Nat} such that reconstructed
        terms can be fed back to the code generator *}
  "term_of_class.term_of n =
   Code_Evaluation.App
     (Code_Evaluation.Const (STR ''Code_Numeral.nat_of_integer'')
        (typerep.Typerep (STR ''fun'')
           [typerep.Typerep (STR ''Code_Numeral.integer'') [],
         typerep.Typerep (STR ''Nat.nat'') []]))
     (term_of_class.term_of (integer_of_nat n))"
  by (simp add: term_of_anything)

lemma nat_of_integer_code_post [code_post]:
  "nat_of_integer 0 = 0"
  "nat_of_integer 1 = 1"
  "nat_of_integer (numeral k) = numeral k"
  including integer.lifting by (transfer, simp)+

code_identifier
  code_module Code_Target_Nat \<rightharpoonup>
    (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
