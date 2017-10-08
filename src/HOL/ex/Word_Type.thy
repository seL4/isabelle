(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for algebraically founded bit word types\<close>

theory Word_Type
  imports
    Main
    "HOL-Library.Type_Length"
begin

subsection \<open>Truncating bit representations of numeric types\<close>

class semiring_bits = unique_euclidean_semiring_parity +
  assumes semiring_bits: "(1 + 2 * a) mod of_nat (2 * n) = 1 + 2 * (a mod of_nat n)"
begin

definition bitrunc :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  where bitrunc_eq_mod: "bitrunc n a = a mod of_nat (2 ^ n)"

lemma bitrunc_bitrunc [simp]:
  "bitrunc n (bitrunc n a) = bitrunc n a"
  by (simp add: bitrunc_eq_mod)
  
lemma bitrunc_0 [simp]:
  "bitrunc 0 a = 0"
  by (simp add: bitrunc_eq_mod)

lemma bitrunc_Suc [simp]:
  "bitrunc (Suc n) a = bitrunc n (a div 2) * 2 + a mod 2"
proof -
  define b and c
    where "b = a div 2" and "c = a mod 2"
  then have a: "a = b * 2 + c" 
    and "c = 0 \<or> c = 1"
    by (simp_all add: div_mult_mod_eq parity)
  from \<open>c = 0 \<or> c = 1\<close>
  have "bitrunc (Suc n) (b * 2 + c) = bitrunc n b * 2 + c"
  proof
    assume "c = 0"
    moreover have "(2 * b) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n)"
      by (simp add: mod_mult_mult1)
    ultimately show ?thesis
      by (simp add: bitrunc_eq_mod ac_simps)
  next
    assume "c = 1"
    with semiring_bits [of b "2 ^ n"] show ?thesis
      by (simp add: bitrunc_eq_mod ac_simps)
  qed
  with a show ?thesis
    by (simp add: b_def c_def)
qed

lemma bitrunc_of_0 [simp]:
  "bitrunc n 0 = 0"
  by (simp add: bitrunc_eq_mod)

lemma bitrunc_plus:
  "bitrunc n (bitrunc n a + bitrunc n b) = bitrunc n (a + b)"
  by (simp add: bitrunc_eq_mod mod_add_eq)

lemma bitrunc_of_1_eq_0_iff [simp]:
  "bitrunc n 1 = 0 \<longleftrightarrow> n = 0"
  by (induct n) simp_all

end

instance nat :: semiring_bits
  by standard (simp add: mod_Suc Suc_double_not_eq_double)

instance int :: semiring_bits
  by standard (simp add: pos_zmod_mult_2)

lemma bitrunc_uminus:
  fixes k :: int
  shows "bitrunc n (- (bitrunc n k)) = bitrunc n (- k)"
  by (simp add: bitrunc_eq_mod mod_minus_eq)

lemma bitrunc_minus:
  fixes k l :: int
  shows "bitrunc n (bitrunc n k - bitrunc n l) = bitrunc n (k - l)"
  by (simp add: bitrunc_eq_mod mod_diff_eq)

lemma bitrunc_nonnegative [simp]:
  fixes k :: int
  shows "bitrunc n k \<ge> 0"
  by (simp add: bitrunc_eq_mod)

definition signed_bitrunc :: "nat \<Rightarrow> int \<Rightarrow> int"
  where signed_bitrunc_eq_bitrunc:
    "signed_bitrunc n k = bitrunc (Suc n) (k + 2 ^ n) - 2 ^ n"

lemma signed_bitrunc_eq_bitrunc':
  assumes "n > 0"
  shows "signed_bitrunc (n - Suc 0) k = bitrunc n (k + 2 ^ (n - 1)) - 2 ^ (n - 1)"
  using assms by (simp add: signed_bitrunc_eq_bitrunc)
  
lemma signed_bitrunc_0 [simp]:
  "signed_bitrunc 0 k = - (k mod 2)"
proof (cases "even k")
  case True
  then have "odd (k + 1)"
    by simp
  then have "(k + 1) mod 2 = 1"
    by (simp add: even_iff_mod_2_eq_zero)
  with True show ?thesis
    by (simp add: signed_bitrunc_eq_bitrunc)
next
  case False
  then show ?thesis
    by (simp add: signed_bitrunc_eq_bitrunc odd_iff_mod_2_eq_one)
qed

lemma signed_bitrunc_Suc [simp]:
  "signed_bitrunc (Suc n) k = signed_bitrunc n (k div 2) * 2 + k mod 2"
  using zero_not_eq_two by (simp add: signed_bitrunc_eq_bitrunc algebra_simps)

lemma signed_bitrunc_of_0 [simp]:
  "signed_bitrunc n 0 = 0"
  by (simp add: signed_bitrunc_eq_bitrunc bitrunc_eq_mod)

lemma signed_bitrunc_of_minus_1 [simp]:
  "signed_bitrunc n (- 1) = - 1"
  by (induct n) simp_all

lemma signed_bitrunc_eq_iff_bitrunc_eq:
  assumes "n > 0"
  shows "signed_bitrunc (n - Suc 0) k = signed_bitrunc (n - Suc 0) l \<longleftrightarrow> bitrunc n k = bitrunc n l" (is "?P \<longleftrightarrow> ?Q")
proof -
  from assms obtain m where m: "n = Suc m"
    by (cases n) auto
  show ?thesis
  proof 
    assume ?Q
    have "bitrunc (Suc m) (k + 2 ^ m) =
      bitrunc (Suc m) (bitrunc (Suc m) k + bitrunc (Suc m) (2 ^ m))"
      by (simp only: bitrunc_plus)
    also have "\<dots> =
      bitrunc (Suc m) (bitrunc (Suc m) l + bitrunc (Suc m) (2 ^ m))"
      by (simp only: \<open>?Q\<close> m [symmetric])
    also have "\<dots> = bitrunc (Suc m) (l + 2 ^ m)"
      by (simp only: bitrunc_plus)
    finally show ?P
      by (simp only: signed_bitrunc_eq_bitrunc m) simp
  next
    assume ?P
    with assms have "(k + 2 ^ (n - Suc 0)) mod 2 ^ n = (l + 2 ^ (n - Suc 0)) mod 2 ^ n"
      by (simp add: signed_bitrunc_eq_bitrunc' bitrunc_eq_mod)
    then have "(i + (k + 2 ^ (n - Suc 0))) mod 2 ^ n = (i + (l + 2 ^ (n - Suc 0))) mod 2 ^ n" for i
      by (metis mod_add_eq)
    then have "k mod 2 ^ n = l mod 2 ^ n"
      by (metis add_diff_cancel_right' uminus_add_conv_diff)
    then show ?Q
      by (simp add: bitrunc_eq_mod)
  qed
qed 


subsection \<open>Bit strings as quotient type\<close>

subsubsection \<open>Basic properties\<close>

quotient_type (overloaded) 'a word = int / "\<lambda>k l. bitrunc LENGTH('a) k = bitrunc LENGTH('a::len0) l"
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
  by (subst bitrunc_plus [symmetric]) (simp add: bitrunc_plus)

lift_definition uminus_word :: "'a word \<Rightarrow> 'a word"
  is uminus
  by (subst bitrunc_uminus [symmetric]) (simp add: bitrunc_uminus)

lift_definition minus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is minus
  by (subst bitrunc_minus [symmetric]) (simp add: bitrunc_minus)

lift_definition times_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is times
  by (auto simp add: bitrunc_eq_mod intro: mod_mult_cong)

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
  is "of_nat \<circ> nat \<circ> bitrunc LENGTH('b)"
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
  is "of_int \<circ> signed_bitrunc (LENGTH('b) - 1)"
  by (simp add: signed_bitrunc_eq_iff_bitrunc_eq [symmetric])

lemma signed_0 [simp]:
  "signed 0 = 0"
  by transfer simp

end

lemma unsigned_of_nat [simp]:
  "unsigned (of_nat n :: 'a word) = bitrunc LENGTH('a::len) n"
  by transfer (simp add: nat_eq_iff bitrunc_eq_mod zmod_int)

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
  by safe (transfer; auto simp add: signed_bitrunc_eq_iff_bitrunc_eq)

end

lemma signed_of_int [simp]:
  "signed (of_int k :: 'a word) = signed_bitrunc (LENGTH('a::len) - 1) k"
  by transfer simp

lemma of_int_signed [simp]:
  "of_int (signed a) = a"
  by transfer (simp add: signed_bitrunc_eq_bitrunc bitrunc_eq_mod mod_simps)


subsubsection \<open>Properties\<close>


subsubsection \<open>Division\<close>

instantiation word :: (len0) modulo
begin

lift_definition divide_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. bitrunc LENGTH('a) a div bitrunc LENGTH('a) b"
  by simp

lift_definition modulo_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. bitrunc LENGTH('a) a mod bitrunc LENGTH('a) b"
  by simp

instance ..

end


subsubsection \<open>Orderings\<close>

instantiation word :: (len0) linorder
begin

lift_definition less_eq_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. bitrunc LENGTH('a) a \<le> bitrunc LENGTH('a) b"
  by simp

lift_definition less_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. bitrunc LENGTH('a) a < bitrunc LENGTH('a) b"
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
  by (transfer fixing: less) (auto dest: preorder_class.le_less_trans [OF bitrunc_nonnegative])

end

end
