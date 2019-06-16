(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for algebraically founded lists of bits\<close>

theory Bit_Lists
  imports Main
begin

context comm_semiring_1
begin

primrec of_unsigned :: "bool list \<Rightarrow> 'a"
  where "of_unsigned [] = 0"
  | "of_unsigned (b # bs) = of_bool b + 2 * of_unsigned bs"

end

context comm_ring_1
begin

definition of_signed :: "bool list \<Rightarrow> 'a"
  where "of_signed bs = (if bs = [] then 0 else if last bs
    then - (of_unsigned (map Not bs) + 1) else of_unsigned bs)"

end

class semiring_bits = unique_euclidean_semiring_with_nat +
  assumes half_measure: "a div 2 \<noteq> a \<Longrightarrow> euclidean_size (a div 2) < euclidean_size a"
  \<comment> \<open>It is not clear whether this could be derived from already existing assumptions.\<close>
begin

function bits_of :: "'a \<Rightarrow> bool list"
  where "bits_of a = odd a # (let b = a div 2 in if a = b then [] else bits_of b)"
  by auto

termination
  by (relation "measure euclidean_size") (auto intro: half_measure)

lemma bits_of_not_empty [simp]:
  "bits_of a \<noteq> []"
  by (induction a rule: bits_of.induct) simp_all

lemma bits_of_0 [simp]:
  "bits_of 0 = [False]"
  by simp

lemma bits_of_1 [simp]:
  "bits_of 1 = [True, False]"
  by simp

lemma bits_of_double [simp]:
  "bits_of (a * 2) = False # (if a = 0 then [] else bits_of a)"
  by simp (simp add: mult_2_right)

lemma bits_of_add_1_double [simp]:
  "bits_of (1 + a * 2) = True # (if a + 1 = 0 then [] else bits_of a)"
  by simp (simp add: mult_2_right algebra_simps)

declare bits_of.simps [simp del]

lemma not_last_bits_of_nat [simp]:
  "\<not> last (bits_of (of_nat n))"
  by (induction n rule: nat_bit_induct)
    (use of_nat_neq_0 in \<open>simp_all add: algebra_simps\<close>)

lemma of_unsigned_bits_of_nat:
  "of_unsigned (bits_of (of_nat n)) = of_nat n"
  by (induction n rule: nat_bit_induct)
    (use of_nat_neq_0 in \<open>simp_all add: algebra_simps\<close>)

end

instance nat :: semiring_bits
  by standard simp

lemma bits_of_Suc_double [simp]:
  "bits_of (Suc (n * 2)) = True # bits_of n"
  using bits_of_add_1_double [of n] by simp

lemma of_unsigned_bits_of:
  "of_unsigned (bits_of n) = n" for n :: nat
  using of_unsigned_bits_of_nat [of n, where ?'a = nat] by simp

class ring_bits = unique_euclidean_ring_with_nat + semiring_bits
begin

lemma bits_of_minus_1 [simp]:
  "bits_of (- 1) = [True]"
  using bits_of.simps [of "- 1"] by simp

lemma bits_of_double [simp]:
  "bits_of (- (a * 2)) = False # (if a = 0 then [] else bits_of (- a))"
  using bits_of.simps [of "- (a * 2)"] nonzero_mult_div_cancel_right [of 2 "- a"]
  by simp (simp add: mult_2_right)

lemma bits_of_minus_1_diff_double [simp]:
  "bits_of (- 1 - a * 2) = True # (if a = 0 then [] else bits_of (- 1 - a))"
proof -
  have [simp]: "- 1 - a = - a - 1"
    by (simp add: algebra_simps)
  show ?thesis
    using bits_of.simps [of "- 1 - a * 2"] div_mult_self1 [of 2 "- 1" "- a"]
    by simp (simp add: mult_2_right algebra_simps)
qed

lemma last_bits_of_neg_of_nat [simp]:
  "last (bits_of (- 1 - of_nat n))"
proof (induction n rule: nat_bit_induct)
  case zero
  then show ?case
    by simp
next
  case (even n)
  then show ?case
    by (simp add: algebra_simps)
next
  case (odd n)
  then have "last (bits_of ((- 1 - of_nat n) * 2))"
    by auto
  also have "(- 1 - of_nat n) * 2 = - 1 - (1 + 2 * of_nat n)"
    by (simp add: algebra_simps)
  finally show ?case
    by simp
qed

lemma of_signed_bits_of_nat:
  "of_signed (bits_of (of_nat n)) = of_nat n"
  by (simp add: of_signed_def of_unsigned_bits_of_nat)

lemma of_signed_bits_neg_of_nat:
  "of_signed (bits_of (- 1 - of_nat n)) = - 1 - of_nat n"
proof -
  have "of_unsigned (map Not (bits_of (- 1 - of_nat n))) = of_nat n"
  proof (induction n rule: nat_bit_induct)
    case zero
    then show ?case
      by simp
  next
    case (even n)
    then show ?case
      by (simp add: algebra_simps)
  next
    case (odd n)
    have *: "- 1 - (1 + of_nat n * 2) = - 2 - of_nat n * 2"
      by (simp add: algebra_simps) (metis add_assoc one_add_one)
    from odd show ?case
      using bits_of_double [of "of_nat (Suc n)"] of_nat_neq_0
      by (simp add: algebra_simps *)
  qed
  then show ?thesis
    by (simp add: of_signed_def algebra_simps)
qed

lemma of_signed_bits_of_int:
  "of_signed (bits_of (of_int k)) = of_int k"
  by (cases k rule: int_cases)
    (simp_all add: of_signed_bits_of_nat of_signed_bits_neg_of_nat)

end

instance int :: ring_bits
  by standard auto

lemma of_signed_bits_of:
  "of_signed (bits_of k) = k" for k :: int
  using of_signed_bits_of_int [of k, where ?'a = int] by simp

end
