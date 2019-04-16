(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for algebraically founded bit word types\<close>

theory Word_Type
  imports
    Main
    "HOL-Library.Type_Length"
begin

lemma take_bit_uminus:
  "take_bit n (- (take_bit n k)) = take_bit n (- k)" for k :: int
  by (simp add: take_bit_eq_mod mod_minus_eq)

lemma take_bit_minus:
  "take_bit n (take_bit n k - take_bit n l) = take_bit n (k - l)" for k l :: int
  by (simp add: take_bit_eq_mod mod_diff_eq)

lemma take_bit_nonnegative [simp]:
  "take_bit n k \<ge> 0" for k :: int
  by (simp add: take_bit_eq_mod)

definition signed_take_bit :: "nat \<Rightarrow> int \<Rightarrow> int"
  where signed_take_bit_eq_take_bit:
    "signed_take_bit n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n"

lemma signed_take_bit_eq_take_bit':
  "signed_take_bit (n - Suc 0) k = take_bit n (k + 2 ^ (n - 1)) - 2 ^ (n - 1)" if "n > 0"
  using that by (simp add: signed_take_bit_eq_take_bit)
  
lemma signed_take_bit_0 [simp]:
  "signed_take_bit 0 k = - (k mod 2)"
proof (cases "even k")
  case True
  then have "odd (k + 1)"
    by simp
  then have "(k + 1) mod 2 = 1"
    by (simp add: even_iff_mod_2_eq_zero)
  with True show ?thesis
    by (simp add: signed_take_bit_eq_take_bit)
next
  case False
  then show ?thesis
    by (simp add: signed_take_bit_eq_take_bit odd_iff_mod_2_eq_one)
qed

lemma signed_take_bit_Suc [simp]:
  "signed_take_bit (Suc n) k = signed_take_bit n (k div 2) * 2 + k mod 2"
  by (simp add: odd_iff_mod_2_eq_one signed_take_bit_eq_take_bit algebra_simps)

lemma signed_take_bit_of_0 [simp]:
  "signed_take_bit n 0 = 0"
  by (simp add: signed_take_bit_eq_take_bit take_bit_eq_mod)

lemma signed_take_bit_of_minus_1 [simp]:
  "signed_take_bit n (- 1) = - 1"
  by (induct n) simp_all

lemma signed_take_bit_eq_iff_take_bit_eq:
  "signed_take_bit (n - Suc 0) k = signed_take_bit (n - Suc 0) l \<longleftrightarrow> take_bit n k = take_bit n l" (is "?P \<longleftrightarrow> ?Q")
  if "n > 0"
proof -
  from that obtain m where m: "n = Suc m"
    by (cases n) auto
  show ?thesis
  proof 
    assume ?Q
    have "take_bit (Suc m) (k + 2 ^ m) =
      take_bit (Suc m) (take_bit (Suc m) k + take_bit (Suc m) (2 ^ m))"
      by (simp only: take_bit_add)
    also have "\<dots> =
      take_bit (Suc m) (take_bit (Suc m) l + take_bit (Suc m) (2 ^ m))"
      by (simp only: \<open>?Q\<close> m [symmetric])
    also have "\<dots> = take_bit (Suc m) (l + 2 ^ m)"
      by (simp only: take_bit_add)
    finally show ?P
      by (simp only: signed_take_bit_eq_take_bit m) simp
  next
    assume ?P
    with that have "(k + 2 ^ (n - Suc 0)) mod 2 ^ n = (l + 2 ^ (n - Suc 0)) mod 2 ^ n"
      by (simp add: signed_take_bit_eq_take_bit' take_bit_eq_mod)
    then have "(i + (k + 2 ^ (n - Suc 0))) mod 2 ^ n = (i + (l + 2 ^ (n - Suc 0))) mod 2 ^ n" for i
      by (metis mod_add_eq)
    then have "k mod 2 ^ n = l mod 2 ^ n"
      by (metis add_diff_cancel_right' uminus_add_conv_diff)
    then show ?Q
      by (simp add: take_bit_eq_mod)
  qed
qed 


subsection \<open>Bit strings as quotient type\<close>

subsubsection \<open>Basic properties\<close>

quotient_type (overloaded) 'a word = int / "\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a::len0) l"
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
  by (subst take_bit_add [symmetric]) (simp add: take_bit_add)

lift_definition uminus_word :: "'a word \<Rightarrow> 'a word"
  is uminus
  by (subst take_bit_uminus [symmetric]) (simp add: take_bit_uminus)

lift_definition minus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is minus
  by (subst take_bit_minus [symmetric]) (simp add: take_bit_minus)

lift_definition times_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is times
  by (auto simp add: take_bit_eq_mod intro: mod_mult_cong)

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
  is "of_nat \<circ> nat \<circ> take_bit LENGTH('b)"
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
  is "of_int \<circ> signed_take_bit (LENGTH('b) - 1)"
  by (simp add: signed_take_bit_eq_iff_take_bit_eq [symmetric])

lemma signed_0 [simp]:
  "signed 0 = 0"
  by transfer simp

end

lemma unsigned_of_nat [simp]:
  "unsigned (of_nat n :: 'a word) = take_bit LENGTH('a::len) n"
  by transfer (simp add: nat_eq_iff take_bit_eq_mod zmod_int)

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
  by safe (transfer; auto simp add: signed_take_bit_eq_iff_take_bit_eq)

end

lemma signed_of_int [simp]:
  "signed (of_int k :: 'a word) = signed_take_bit (LENGTH('a::len) - 1) k"
  by transfer simp

lemma of_int_signed [simp]:
  "of_int (signed a) = a"
  by transfer (simp add: signed_take_bit_eq_take_bit take_bit_eq_mod mod_simps)


subsubsection \<open>Properties\<close>


subsubsection \<open>Division\<close>

instantiation word :: (len0) modulo
begin

lift_definition divide_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. take_bit LENGTH('a) a div take_bit LENGTH('a) b"
  by simp

lift_definition modulo_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. take_bit LENGTH('a) a mod take_bit LENGTH('a) b"
  by simp

instance ..

end


subsubsection \<open>Orderings\<close>

instantiation word :: (len0) linorder
begin

lift_definition less_eq_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a \<le> take_bit LENGTH('a) b"
  by simp

lift_definition less_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a < take_bit LENGTH('a) b"
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
  by (transfer fixing: less) (auto dest: preorder_class.le_less_trans [OF take_bit_nonnegative])

end

end
