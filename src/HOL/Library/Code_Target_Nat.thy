(*  Title:      HOL/Library/Code_Target_Nat.thy
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen
*)

header {* Implementation of natural numbers by target-language integers *}

theory Code_Target_Nat
imports Main Code_Numeral_Types Code_Binary_Nat
begin

subsection {* Implementation for @{typ nat} *}

definition Nat :: "integer \<Rightarrow> nat"
where
  "Nat = nat_of_integer"

definition integer_of_nat :: "nat \<Rightarrow> integer"
where
  [code_abbrev]: "integer_of_nat = of_nat"

lemma int_of_integer_integer_of_nat [simp]:
  "int_of_integer (integer_of_nat n) = of_nat n"
  by (simp add: integer_of_nat_def)

lemma [code_unfold]:
  "Int.nat (int_of_integer k) = nat_of_integer k"
  by (simp add: nat_of_integer_def)

lemma [code abstype]:
  "Code_Target_Nat.Nat (integer_of_nat n) = n"
  by (simp add: Nat_def integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (nat_of_integer k) = max 0 k"
  by (simp add: integer_of_nat_def)

lemma [code_abbrev]:
  "nat_of_integer (Code_Numeral_Types.Pos k) = nat_of_num k"
  by (simp add: nat_of_integer_def nat_of_num_numeral)

lemma [code abstract]:
  "integer_of_nat (nat_of_num n) = integer_of_num n"
  by (simp add: integer_eq_iff integer_of_num_def nat_of_num_numeral)

lemma [code abstract]:
  "integer_of_nat 0 = 0"
  by (simp add: integer_eq_iff integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat 1 = 1"
  by (simp add: integer_eq_iff integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (m + n) = of_nat m + of_nat n"
  by (simp add: integer_eq_iff integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (Code_Binary_Nat.dup n) = Code_Numeral_Types.dup (of_nat n)"
  by (simp add: integer_eq_iff Code_Binary_Nat.dup_def integer_of_nat_def)

lemma [code, code del]:
  "Code_Binary_Nat.sub = Code_Binary_Nat.sub" ..

lemma [code abstract]:
  "integer_of_nat (m - n) = max 0 (of_nat m - of_nat n)"
  by (simp add: integer_eq_iff integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (m * n) = of_nat m * of_nat n"
  by (simp add: integer_eq_iff of_nat_mult integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (m div n) = of_nat m div of_nat n"
  by (simp add: integer_eq_iff zdiv_int integer_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (m mod n) = of_nat m mod of_nat n"
  by (simp add: integer_eq_iff zmod_int integer_of_nat_def)

lemma [code]:
  "Divides.divmod_nat m n = (m div n, m mod n)"
  by (simp add: prod_eq_iff)

lemma [code]:
  "HOL.equal m n = HOL.equal (of_nat m :: integer) (of_nat n)"
  by (simp add: equal integer_eq_iff)

lemma [code]:
  "m \<le> n \<longleftrightarrow> (of_nat m :: integer) \<le> of_nat n"
  by simp

lemma [code]:
  "m < n \<longleftrightarrow> (of_nat m :: integer) < of_nat n"
  by simp

lemma num_of_nat_code [code]:
  "num_of_nat = num_of_integer \<circ> of_nat"
  by (simp add: fun_eq_iff num_of_integer_def integer_of_nat_def)

lemma (in semiring_1) of_nat_code:
  "of_nat n = (if n = 0 then 0
     else let
       (m, q) = divmod_nat n 2;
       m' = 2 * of_nat m
     in if q = 0 then m' else m' + 1)"
proof -
  from mod_div_equality have *: "of_nat n = of_nat (n div 2 * 2 + n mod 2)" by simp
  show ?thesis
    by (simp add: Let_def divmod_nat_div_mod mod_2_not_eq_zero_eq_one_nat
      of_nat_add [symmetric])
      (simp add: * mult_commute of_nat_mult add_commute)
qed

declare of_nat_code [code]

definition int_of_nat :: "nat \<Rightarrow> int" where
  [code_abbrev]: "int_of_nat = of_nat"

lemma [code]:
  "int_of_nat n = int_of_integer (of_nat n)"
  by (simp add: int_of_nat_def)

lemma [code abstract]:
  "integer_of_nat (nat k) = max 0 (integer_of_int k)"
  by (simp add: integer_of_nat_def of_int_of_nat max_def)

code_modulename SML
  Code_Target_Nat Arith

code_modulename OCaml
  Code_Target_Nat Arith

code_modulename Haskell
  Code_Target_Nat Arith

end

