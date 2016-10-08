(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for algebraically founded bit word types\<close>

theory Word_Type
  imports
    Main
    "~~/src/HOL/Library/Type_Length"
begin

subsection \<open>Truncating bit representations of numeric types\<close>

class semiring_bits = semiring_div_parity +
  assumes semiring_bits: "(1 + 2 * a) mod of_nat (2 * n) = 1 + 2 * (a mod of_nat n)"

context semiring_bits
begin

definition bits :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where bits_eq_mod: "bits n a = a mod of_nat (2 ^ n)"

lemma bits_bits [simp]:
  "bits n (bits n a) = bits n a"
  by (simp add: bits_eq_mod)
  
lemma bits_0 [simp]:
  "bits 0 a = 0"
  by (simp add: bits_eq_mod)

lemma bits_Suc [simp]:
  "bits (Suc n) a = bits n (a div 2) * 2 + a mod 2"
proof -
  define b and c
    where "b = a div 2" and "c = a mod 2"
  then have a: "a = b * 2 + c" 
    and "c = 0 \<or> c = 1"
    by (simp_all add: mod_div_equality parity)
  from \<open>c = 0 \<or> c = 1\<close>
  have "bits (Suc n) (b * 2 + c) = bits n b * 2 + c"
  proof
    assume "c = 0"
    moreover have "(2 * b) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n)"
      by (simp add: mod_mult_mult1)
    ultimately show ?thesis
      by (simp add: bits_eq_mod ac_simps)
  next
    assume "c = 1"
    with semiring_bits [of b "2 ^ n"] show ?thesis
      by (simp add: bits_eq_mod ac_simps)
  qed
  with a show ?thesis
    by (simp add: b_def c_def)
qed

lemma bits_of_0 [simp]:
  "bits n 0 = 0"
  by (simp add: bits_eq_mod)

lemma bits_plus:
  "bits n (bits n a + bits n b) = bits n (a + b)"
  by (simp add: bits_eq_mod mod_add_eq [symmetric])

lemma bits_of_1_eq_0_iff [simp]:
  "bits n 1 = 0 \<longleftrightarrow> n = 0"
  by (induct n) simp_all

end

instance nat :: semiring_bits
  by standard (simp add: mod_Suc Suc_double_not_eq_double)

instance int :: semiring_bits
  by standard (simp add: pos_zmod_mult_2)

lemma bits_uminus:
  fixes k :: int
  shows "bits n (- (bits n k)) = bits n (- k)"
  by (simp add: bits_eq_mod mod_minus_eq [symmetric])

lemma bits_minus:
  fixes k l :: int
  shows "bits n (bits n k - bits n l) = bits n (k - l)"
  by (simp add: bits_eq_mod mod_diff_eq [symmetric])

lemma bits_nonnegative [simp]:
  fixes k :: int
  shows "bits n k \<ge> 0"
  by (simp add: bits_eq_mod)

definition signed_bits :: "nat \<Rightarrow> int \<Rightarrow> int"
  where signed_bits_eq_bits:
    "signed_bits n k = bits (Suc n) (k + 2 ^ n) - 2 ^ n"

lemma signed_bits_eq_bits':
  assumes "n > 0"
  shows "signed_bits (n - Suc 0) k = bits n (k + 2 ^ (n - 1)) - 2 ^ (n - 1)"
  using assms by (simp add: signed_bits_eq_bits)
  
lemma signed_bits_0 [simp]:
  "signed_bits 0 k = - (k mod 2)"
proof (cases "even k")
  case True
  then have "odd (k + 1)"
    by simp
  then have "(k + 1) mod 2 = 1"
    by (simp add: even_iff_mod_2_eq_zero)
  with True show ?thesis
    by (simp add: signed_bits_eq_bits)
next
  case False
  then show ?thesis
    by (simp add: signed_bits_eq_bits odd_iff_mod_2_eq_one)
qed

lemma signed_bits_Suc [simp]:
  "signed_bits (Suc n) k = signed_bits n (k div 2) * 2 + k mod 2"
  using zero_not_eq_two by (simp add: signed_bits_eq_bits algebra_simps)

lemma signed_bits_of_0 [simp]:
  "signed_bits n 0 = 0"
  by (simp add: signed_bits_eq_bits bits_eq_mod)

lemma signed_bits_of_minus_1 [simp]:
  "signed_bits n (- 1) = - 1"
  by (induct n) simp_all

lemma signed_bits_eq_iff_bits_eq:
  assumes "n > 0"
  shows "signed_bits (n - Suc 0) k = signed_bits (n - Suc 0) l \<longleftrightarrow> bits n k = bits n l" (is "?P \<longleftrightarrow> ?Q")
proof -
  from assms obtain m where m: "n = Suc m"
    by (cases n) auto
  show ?thesis
  proof 
    assume ?Q
    have "bits (Suc m) (k + 2 ^ m) =
      bits (Suc m) (bits (Suc m) k + bits (Suc m) (2 ^ m))"
      by (simp only: bits_plus)
    also have "\<dots> =
      bits (Suc m) (bits (Suc m) l + bits (Suc m) (2 ^ m))"
      by (simp only: \<open>?Q\<close> m [symmetric])
    also have "\<dots> = bits (Suc m) (l + 2 ^ m)"
      by (simp only: bits_plus)
    finally show ?P
      by (simp only: signed_bits_eq_bits m) simp
  next
    assume ?P
    with assms have "(k + 2 ^ (n - Suc 0)) mod 2 ^ n = (l + 2 ^ (n - Suc 0)) mod 2 ^ n"
      by (simp add: signed_bits_eq_bits' bits_eq_mod)
    then have "(i + (k + 2 ^ (n - Suc 0))) mod 2 ^ n = (i + (l + 2 ^ (n - Suc 0))) mod 2 ^ n" for i
      by (metis mod_add_eq)
    then have "k mod 2 ^ n = l mod 2 ^ n"
      by (metis add_diff_cancel_right' uminus_add_conv_diff)
    then show ?Q
      by (simp add: bits_eq_mod)
  qed
qed 


subsection \<open>Bit strings as quotient type\<close>

subsubsection \<open>Basic properties\<close>

quotient_type (overloaded) 'a word = int / "\<lambda>k l. bits LENGTH('a) k = bits LENGTH('a::len0) l"
  by (auto intro!: equivpI reflpI sympI transpI)

instantiation word :: (len0) "{semiring_numeral, comm_semiring_0, comm_ring}"
begin

lift_definition zero_word :: "'a word"
  is 0
  .

lift_definition one_word :: "'a word"
  is 1
  .

lift_definition plus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is plus
  by (subst bits_plus [symmetric]) (simp add: bits_plus)

lift_definition uminus_word :: "'a word \<Rightarrow> 'a word"
  is uminus
  by (subst bits_uminus [symmetric]) (simp add: bits_uminus)

lift_definition minus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is minus
  by (subst bits_minus [symmetric]) (simp add: bits_minus)

lift_definition times_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is times
  by (auto simp add: bits_eq_mod intro: mod_mult_cong)

instance
  by standard (transfer; simp add: algebra_simps)+

end

instance word :: (len) comm_ring_1
  by standard (transfer; simp)+


subsubsection \<open>Conversions\<close>

lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_word int of_nat"
proof -
  note transfer_rule_of_nat [transfer_rule]
  show ?thesis by transfer_prover
qed
  
lemma [transfer_rule]:
  "rel_fun HOL.eq pcr_word (\<lambda>k. k) of_int"
proof -
  note transfer_rule_of_int [transfer_rule]
  have "rel_fun HOL.eq pcr_word (of_int :: int \<Rightarrow> int) (of_int :: int \<Rightarrow> 'a word)"
    by transfer_prover
  then show ?thesis by (simp add: id_def)
qed

context semiring_1
begin

lift_definition unsigned :: "'b::len0 word \<Rightarrow> 'a"
  is "of_nat \<circ> nat \<circ> bits LENGTH('b)"
  by simp

lemma unsigned_0 [simp]:
  "unsigned 0 = 0"
  by transfer simp

end

context semiring_char_0
begin

lemma word_eq_iff_unsigned:
  "a = b \<longleftrightarrow> unsigned a = unsigned b"
  by safe (transfer; simp add: eq_nat_nat_iff)

end

context ring_1
begin

lift_definition signed :: "'b::len word \<Rightarrow> 'a"
  is "of_int \<circ> signed_bits (LENGTH('b) - 1)"
  by (simp add: signed_bits_eq_iff_bits_eq [symmetric])

lemma signed_0 [simp]:
  "signed 0 = 0"
  by transfer simp

end

lemma unsigned_of_nat [simp]:
  "unsigned (of_nat n :: 'a word) = bits LENGTH('a::len) n"
  by transfer (simp add: nat_eq_iff bits_eq_mod zmod_int)

lemma of_nat_unsigned [simp]:
  "of_nat (unsigned a) = a"
  by transfer simp

lemma of_int_unsigned [simp]:
  "of_int (unsigned a) = a"
  by transfer simp

context ring_char_0
begin

lemma word_eq_iff_signed:
  "a = b \<longleftrightarrow> signed a = signed b"
  by safe (transfer; auto simp add: signed_bits_eq_iff_bits_eq)

end

lemma signed_of_int [simp]:
  "signed (of_int k :: 'a word) = signed_bits (LENGTH('a::len) - 1) k"
  by transfer simp

lemma of_int_signed [simp]:
  "of_int (signed a) = a"
  by transfer (simp add: signed_bits_eq_bits bits_eq_mod zdiff_zmod_left)


subsubsection \<open>Properties\<close>


subsubsection \<open>Division\<close>

instantiation word :: (len0) modulo
begin

lift_definition divide_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. bits LENGTH('a) a div bits LENGTH('a) b"
  by simp

lift_definition modulo_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. bits LENGTH('a) a mod bits LENGTH('a) b"
  by simp

instance ..

end


subsubsection \<open>Orderings\<close>

instantiation word :: (len0) linorder
begin

lift_definition less_eq_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. bits LENGTH('a) a \<le> bits LENGTH('a) b"
  by simp

lift_definition less_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. bits LENGTH('a) a < bits LENGTH('a) b"
  by simp

instance
  by standard (transfer; auto)+

end

context linordered_semidom
begin

lemma word_less_eq_iff_unsigned:
  "a \<le> b \<longleftrightarrow> unsigned a \<le> unsigned b"
  by (transfer fixing: less_eq) (simp add: nat_le_eq_zle)

lemma word_less_iff_unsigned:
  "a < b \<longleftrightarrow> unsigned a < unsigned b"
  by (transfer fixing: less) (auto dest: preorder_class.le_less_trans [OF bits_nonnegative])

end

end
