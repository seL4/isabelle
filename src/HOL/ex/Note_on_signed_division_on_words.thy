theory Note_on_signed_division_on_words
  imports "HOL-Library.Word" "HOL-Library.Rounded_Division"
begin

unbundle bit_operations_syntax

context semiring_bit_operations
begin

lemma take_bit_Suc_from_most:
  \<open>take_bit (Suc n) a = 2 ^ n * of_bool (bit a n) OR take_bit n a\<close>
  by (rule bit_eqI) (auto simp add: bit_simps less_Suc_eq)

end

context ring_bit_operations
begin

lemma signed_take_bit_exp_eq_int:
  \<open>signed_take_bit m (2 ^ n) =
    (if n < m then 2 ^ n else if n = m then - (2 ^ n) else 0)\<close>
  by (rule bit_eqI) (auto simp add: bit_simps simp flip: mask_eq_exp_minus_1)

end

lift_definition signed_divide_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>  (infixl \<open>wdiv\<close> 70)
  is \<open>\<lambda>a b. signed_take_bit (LENGTH('a) - Suc 0) a rdiv signed_take_bit (LENGTH('a) - Suc 0) b\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition signed_modulo_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>  (infixl \<open>wmod\<close> 70)
  is \<open>\<lambda>a b. signed_take_bit (LENGTH('a) - Suc 0) a rmod signed_take_bit (LENGTH('a) - Suc 0) b\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma signed_take_bit_eq_wmod:
  \<open>signed_take_bit n w = w wmod (2 ^ Suc n)\<close>
proof (transfer fixing: n)
  show \<open>take_bit LENGTH('a) (signed_take_bit n (take_bit LENGTH('a) k)) =
    take_bit LENGTH('a) (signed_take_bit (LENGTH('a) - Suc 0) k rmod signed_take_bit (LENGTH('a) - Suc 0) (2 ^ Suc n))\<close> for k :: int
  proof (cases \<open>LENGTH('a) = Suc (Suc n)\<close>)
    case True
    then show ?thesis
      by (simp add: signed_take_bit_exp_eq_int signed_take_bit_take_bit rmod_minus_eq flip: power_Suc signed_take_bit_eq_rmod)
  next
    case False
    then show ?thesis
      by (auto simp add: signed_take_bit_exp_eq_int signed_take_bit_take_bit take_bit_signed_take_bit simp flip: power_Suc signed_take_bit_eq_rmod)
  qed
qed

end
