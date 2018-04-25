(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for residue rings over int using type numerals\<close>

theory Residue_Ring
  imports Main "HOL-Library.Type_Length"
begin

class len2 = len0 +
  assumes len_ge_2 [iff]: "2 \<le> LENGTH('a)"
begin

subclass len
proof
  show "0 < LENGTH('a)" using len_ge_2
    by arith
qed

lemma len_not_eq_Suc_0 [simp]:
  "LENGTH('a) \<noteq> Suc 0"
  using len_ge_2 by arith

end

instance bit0 and bit1 :: (len) len2
  by standard (simp_all add: Suc_le_eq)

quotient_type (overloaded) 'a residue_ring = int / "\<lambda>k l. k mod int (LENGTH('a)) = l mod int (LENGTH('a::len2))"
  by (auto intro!: equivpI reflpI sympI transpI)

context semiring_1
begin

lift_definition repr :: "'b::len2 residue_ring \<Rightarrow> 'a"
  is "\<lambda>k. of_nat (nat (k mod int (LENGTH('b))))"
  by simp

end

instantiation residue_ring :: (len2) comm_ring_1
begin

lift_definition zero_residue_ring :: "'a residue_ring"
  is 0 .

lift_definition one_residue_ring :: "'a residue_ring"
  is 1 .

lift_definition plus_residue_ring :: "'a residue_ring \<Rightarrow> 'a residue_ring \<Rightarrow> 'a residue_ring"
  is plus
  by (fact mod_add_cong)

lift_definition uminus_residue_ring :: "'a residue_ring \<Rightarrow> 'a residue_ring"
  is uminus
  by (fact mod_minus_cong)

lift_definition minus_residue_ring :: "'a residue_ring \<Rightarrow> 'a residue_ring \<Rightarrow> 'a residue_ring"
  is minus
  by (fact mod_diff_cong)

lift_definition times_residue_ring :: "'a residue_ring \<Rightarrow> 'a residue_ring \<Rightarrow> 'a residue_ring"
  is times
  by (fact mod_mult_cong)

instance
  by (standard; transfer) (simp_all add: algebra_simps mod_eq_0_iff_dvd)

end

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  "((\<longleftrightarrow>) ===> pcr_residue_ring) of_bool of_bool"
  by (unfold of_bool_def [abs_def]; transfer_prover)

lemma [transfer_rule]:
  "((=) ===> pcr_residue_ring) numeral numeral"
  by (rule transfer_rule_numeral; transfer_prover)

lemma [transfer_rule]:
  "((=) ===> pcr_residue_ring) int of_nat"
  by (rule transfer_rule_of_nat; transfer_prover)

end

end
