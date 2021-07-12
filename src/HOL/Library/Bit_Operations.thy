(*  Author:  Florian Haftmann, TUM
*)

section \<open>Bit operations in suitable algebraic structures\<close>

theory Bit_Operations
  imports
    Main
    "HOL-Library.Boolean_Algebra"
begin

subsection \<open>Bit operations\<close>

class semiring_bit_operations = semiring_bit_shifts +
  fixes "and" :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>AND\<close> 64)
    and or :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>OR\<close>  59)
    and xor :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>  (infixr \<open>XOR\<close> 59)
    and mask :: \<open>nat \<Rightarrow> 'a\<close>
    and set_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
    and unset_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
    and flip_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes bit_and_iff [bit_simps]: \<open>bit (a AND b) n \<longleftrightarrow> bit a n \<and> bit b n\<close>
    and bit_or_iff [bit_simps]: \<open>bit (a OR b) n \<longleftrightarrow> bit a n \<or> bit b n\<close>
    and bit_xor_iff [bit_simps]: \<open>bit (a XOR b) n \<longleftrightarrow> bit a n \<noteq> bit b n\<close>
    and mask_eq_exp_minus_1: \<open>mask n = 2 ^ n - 1\<close>
    and set_bit_eq_or: \<open>set_bit n a = a OR push_bit n 1\<close>
    and bit_unset_bit_iff [bit_simps]: \<open>bit (unset_bit m a) n \<longleftrightarrow> bit a n \<and> m \<noteq> n\<close>
    and flip_bit_eq_xor: \<open>flip_bit n a = a XOR push_bit n 1\<close>
begin

text \<open>
  We want the bitwise operations to bind slightly weaker
  than \<open>+\<close> and \<open>-\<close>.
  For the sake of code generation
  the operations \<^const>\<open>and\<close>, \<^const>\<open>or\<close> and \<^const>\<open>xor\<close>
  are specified as definitional class operations.
\<close>

sublocale "and": semilattice \<open>(AND)\<close>
  by standard (auto simp add: bit_eq_iff bit_and_iff)

sublocale or: semilattice_neutr \<open>(OR)\<close> 0
  by standard (auto simp add: bit_eq_iff bit_or_iff)

sublocale xor: comm_monoid \<open>(XOR)\<close> 0
  by standard (auto simp add: bit_eq_iff bit_xor_iff)

lemma even_and_iff:
  \<open>even (a AND b) \<longleftrightarrow> even a \<or> even b\<close>
  using bit_and_iff [of a b 0] by auto

lemma even_or_iff:
  \<open>even (a OR b) \<longleftrightarrow> even a \<and> even b\<close>
  using bit_or_iff [of a b 0] by auto

lemma even_xor_iff:
  \<open>even (a XOR b) \<longleftrightarrow> (even a \<longleftrightarrow> even b)\<close>
  using bit_xor_iff [of a b 0] by auto

lemma zero_and_eq [simp]:
  \<open>0 AND a = 0\<close>
  by (simp add: bit_eq_iff bit_and_iff)

lemma and_zero_eq [simp]:
  \<open>a AND 0 = 0\<close>
  by (simp add: bit_eq_iff bit_and_iff)

lemma one_and_eq:
  \<open>1 AND a = a mod 2\<close>
  by (simp add: bit_eq_iff bit_and_iff) (auto simp add: bit_1_iff)

lemma and_one_eq:
  \<open>a AND 1 = a mod 2\<close>
  using one_and_eq [of a] by (simp add: ac_simps)

lemma one_or_eq:
  \<open>1 OR a = a + of_bool (even a)\<close>
  by (simp add: bit_eq_iff bit_or_iff add.commute [of _ 1] even_bit_succ_iff) (auto simp add: bit_1_iff)

lemma or_one_eq:
  \<open>a OR 1 = a + of_bool (even a)\<close>
  using one_or_eq [of a] by (simp add: ac_simps)

lemma one_xor_eq:
  \<open>1 XOR a = a + of_bool (even a) - of_bool (odd a)\<close>
  by (simp add: bit_eq_iff bit_xor_iff add.commute [of _ 1] even_bit_succ_iff) (auto simp add: bit_1_iff odd_bit_iff_bit_pred elim: oddE)

lemma xor_one_eq:
  \<open>a XOR 1 = a + of_bool (even a) - of_bool (odd a)\<close>
  using one_xor_eq [of a] by (simp add: ac_simps)

lemma take_bit_and [simp]:
  \<open>take_bit n (a AND b) = take_bit n a AND take_bit n b\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_and_iff)

lemma take_bit_or [simp]:
  \<open>take_bit n (a OR b) = take_bit n a OR take_bit n b\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_or_iff)

lemma take_bit_xor [simp]:
  \<open>take_bit n (a XOR b) = take_bit n a XOR take_bit n b\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_xor_iff)

lemma push_bit_and [simp]:
  \<open>push_bit n (a AND b) = push_bit n a AND push_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_push_bit_iff bit_and_iff)

lemma push_bit_or [simp]:
  \<open>push_bit n (a OR b) = push_bit n a OR push_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_push_bit_iff bit_or_iff)

lemma push_bit_xor [simp]:
  \<open>push_bit n (a XOR b) = push_bit n a XOR push_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_push_bit_iff bit_xor_iff)

lemma drop_bit_and [simp]:
  \<open>drop_bit n (a AND b) = drop_bit n a AND drop_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_drop_bit_eq bit_and_iff)

lemma drop_bit_or [simp]:
  \<open>drop_bit n (a OR b) = drop_bit n a OR drop_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_drop_bit_eq bit_or_iff)

lemma drop_bit_xor [simp]:
  \<open>drop_bit n (a XOR b) = drop_bit n a XOR drop_bit n b\<close>
  by (rule bit_eqI) (auto simp add: bit_drop_bit_eq bit_xor_iff)

lemma bit_mask_iff [bit_simps]:
  \<open>bit (mask m) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n < m\<close>
  by (simp add: mask_eq_exp_minus_1 bit_mask_iff)

lemma even_mask_iff:
  \<open>even (mask n) \<longleftrightarrow> n = 0\<close>
  using bit_mask_iff [of n 0] by auto

lemma mask_0 [simp]:
  \<open>mask 0 = 0\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma mask_Suc_0 [simp]:
  \<open>mask (Suc 0) = 1\<close>
  by (simp add: mask_eq_exp_minus_1 add_implies_diff sym)

lemma mask_Suc_exp:
  \<open>mask (Suc n) = 2 ^ n OR mask n\<close>
  by (rule bit_eqI)
    (auto simp add: bit_or_iff bit_mask_iff bit_exp_iff not_less le_less_Suc_eq)

lemma mask_Suc_double:
  \<open>mask (Suc n) = 1 OR 2 * mask n\<close>
proof (rule bit_eqI)
  fix q
  assume \<open>2 ^ q \<noteq> 0\<close>
  show \<open>bit (mask (Suc n)) q \<longleftrightarrow> bit (1 OR 2 * mask n) q\<close>
    by (cases q)
      (simp_all add: even_mask_iff even_or_iff bit_or_iff bit_mask_iff bit_exp_iff bit_double_iff not_less le_less_Suc_eq bit_1_iff, auto simp add: mult_2)
qed

lemma mask_numeral:
  \<open>mask (numeral n) = 1 + 2 * mask (pred_numeral n)\<close>
  by (simp add: numeral_eq_Suc mask_Suc_double one_or_eq ac_simps)

lemma take_bit_mask [simp]:
  \<open>take_bit m (mask n) = mask (min m n)\<close>
  by (rule bit_eqI) (simp add: bit_simps)

lemma take_bit_eq_mask:
  \<open>take_bit n a = a AND mask n\<close>
  by (rule bit_eqI)
    (auto simp add: bit_take_bit_iff bit_and_iff bit_mask_iff)

lemma or_eq_0_iff:
  \<open>a OR b = 0 \<longleftrightarrow> a = 0 \<and> b = 0\<close>
  by (auto simp add: bit_eq_iff bit_or_iff)

lemma disjunctive_add:
  \<open>a + b = a OR b\<close> if \<open>\<And>n. \<not> bit a n \<or> \<not> bit b n\<close>
  by (rule bit_eqI) (use that in \<open>simp add: bit_disjunctive_add_iff bit_or_iff\<close>)

lemma bit_iff_and_drop_bit_eq_1:
  \<open>bit a n \<longleftrightarrow> drop_bit n a AND 1 = 1\<close>
  by (simp add: bit_iff_odd_drop_bit and_one_eq odd_iff_mod_2_eq_one)

lemma bit_iff_and_push_bit_not_eq_0:
  \<open>bit a n \<longleftrightarrow> a AND push_bit n 1 \<noteq> 0\<close>
  apply (cases \<open>2 ^ n = 0\<close>)
  apply (simp_all add: push_bit_of_1 bit_eq_iff bit_and_iff bit_push_bit_iff exp_eq_0_imp_not_bit)
  apply (simp_all add: bit_exp_iff)
  done

lemmas set_bit_def = set_bit_eq_or

lemma bit_set_bit_iff [bit_simps]:
  \<open>bit (set_bit m a) n \<longleftrightarrow> bit a n \<or> (m = n \<and> 2 ^ n \<noteq> 0)\<close>
  by (auto simp add: set_bit_def push_bit_of_1 bit_or_iff bit_exp_iff)

lemma even_set_bit_iff:
  \<open>even (set_bit m a) \<longleftrightarrow> even a \<and> m \<noteq> 0\<close>
  using bit_set_bit_iff [of m a 0] by auto

lemma even_unset_bit_iff:
  \<open>even (unset_bit m a) \<longleftrightarrow> even a \<or> m = 0\<close>
  using bit_unset_bit_iff [of m a 0] by auto

lemma and_exp_eq_0_iff_not_bit:
  \<open>a AND 2 ^ n = 0 \<longleftrightarrow> \<not> bit a n\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?Q
  then show ?P
    by (auto intro: bit_eqI simp add: bit_simps)
next
  assume ?P
  show ?Q
  proof (rule notI)
    assume \<open>bit a n\<close>
    then have \<open>a AND 2 ^ n = 2 ^ n\<close>
      by (auto intro: bit_eqI simp add: bit_simps)
    with \<open>?P\<close> show False
      using \<open>bit a n\<close> exp_eq_0_imp_not_bit by auto
  qed
qed

lemmas flip_bit_def = flip_bit_eq_xor

lemma bit_flip_bit_iff [bit_simps]:
  \<open>bit (flip_bit m a) n \<longleftrightarrow> (m = n \<longleftrightarrow> \<not> bit a n) \<and> 2 ^ n \<noteq> 0\<close>
  by (auto simp add: flip_bit_def push_bit_of_1 bit_xor_iff bit_exp_iff exp_eq_0_imp_not_bit)

lemma even_flip_bit_iff:
  \<open>even (flip_bit m a) \<longleftrightarrow> \<not> (even a \<longleftrightarrow> m = 0)\<close>
  using bit_flip_bit_iff [of m a 0] by auto

lemma set_bit_0 [simp]:
  \<open>set_bit 0 a = 1 + 2 * (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (set_bit 0 a) m = bit (1 + 2 * (a div 2)) m\<close>
    by (simp add: bit_set_bit_iff bit_double_iff even_bit_succ_iff)
      (cases m, simp_all add: bit_Suc)
qed

lemma set_bit_Suc:
  \<open>set_bit (Suc n) a = a mod 2 + 2 * set_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  show \<open>bit (set_bit (Suc n) a) m \<longleftrightarrow> bit (a mod 2 + 2 * set_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_set_bit_iff)
  next
    case (Suc m)
    with * have \<open>2 ^ m \<noteq> 0\<close>
      using mult_2 by auto
    show ?thesis
      by (cases a rule: parity_cases)
        (simp_all add: bit_set_bit_iff bit_double_iff even_bit_succ_iff *,
        simp_all add: Suc \<open>2 ^ m \<noteq> 0\<close> bit_Suc)
  qed
qed

lemma unset_bit_0 [simp]:
  \<open>unset_bit 0 a = 2 * (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (unset_bit 0 a) m = bit (2 * (a div 2)) m\<close>
    by (simp add: bit_unset_bit_iff bit_double_iff)
      (cases m, simp_all add: bit_Suc)
qed

lemma unset_bit_Suc:
  \<open>unset_bit (Suc n) a = a mod 2 + 2 * unset_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (unset_bit (Suc n) a) m \<longleftrightarrow> bit (a mod 2 + 2 * unset_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_unset_bit_iff)
  next
    case (Suc m)
    show ?thesis
      by (cases a rule: parity_cases)
        (simp_all add: bit_unset_bit_iff bit_double_iff even_bit_succ_iff *,
         simp_all add: Suc bit_Suc)
  qed
qed

lemma flip_bit_0 [simp]:
  \<open>flip_bit 0 a = of_bool (even a) + 2 * (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  then show \<open>bit (flip_bit 0 a) m = bit (of_bool (even a) + 2 * (a div 2)) m\<close>
    by (simp add: bit_flip_bit_iff bit_double_iff even_bit_succ_iff)
      (cases m, simp_all add: bit_Suc)
qed

lemma flip_bit_Suc:
  \<open>flip_bit (Suc n) a = a mod 2 + 2 * flip_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  show \<open>bit (flip_bit (Suc n) a) m \<longleftrightarrow> bit (a mod 2 + 2 * flip_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_flip_bit_iff)
  next
    case (Suc m)
    with * have \<open>2 ^ m \<noteq> 0\<close>
      using mult_2 by auto
    show ?thesis
      by (cases a rule: parity_cases)
        (simp_all add: bit_flip_bit_iff bit_double_iff even_bit_succ_iff,
        simp_all add: Suc \<open>2 ^ m \<noteq> 0\<close> bit_Suc)
  qed
qed

lemma flip_bit_eq_if:
  \<open>flip_bit n a = (if bit a n then unset_bit else set_bit) n a\<close>
  by (rule bit_eqI) (auto simp add: bit_set_bit_iff bit_unset_bit_iff bit_flip_bit_iff)

lemma take_bit_set_bit_eq:
  \<open>take_bit n (set_bit m a) = (if n \<le> m then take_bit n a else set_bit m (take_bit n a))\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_set_bit_iff)

lemma take_bit_unset_bit_eq:
  \<open>take_bit n (unset_bit m a) = (if n \<le> m then take_bit n a else unset_bit m (take_bit n a))\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_unset_bit_iff)

lemma take_bit_flip_bit_eq:
  \<open>take_bit n (flip_bit m a) = (if n \<le> m then take_bit n a else flip_bit m (take_bit n a))\<close>
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff bit_flip_bit_iff)


end

class ring_bit_operations = semiring_bit_operations + ring_parity +
  fixes not :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>NOT\<close>)
  assumes bit_not_iff [bit_simps]: \<open>\<And>n. bit (NOT a) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> \<not> bit a n\<close>
  assumes minus_eq_not_minus_1: \<open>- a = NOT (a - 1)\<close>
begin

text \<open>
  For the sake of code generation \<^const>\<open>not\<close> is specified as
  definitional class operation.  Note that \<^const>\<open>not\<close> has no
  sensible definition for unlimited but only positive bit strings
  (type \<^typ>\<open>nat\<close>).
\<close>

lemma bits_minus_1_mod_2_eq [simp]:
  \<open>(- 1) mod 2 = 1\<close>
  by (simp add: mod_2_eq_odd)

lemma not_eq_complement:
  \<open>NOT a = - a - 1\<close>
  using minus_eq_not_minus_1 [of \<open>a + 1\<close>] by simp

lemma minus_eq_not_plus_1:
  \<open>- a = NOT a + 1\<close>
  using not_eq_complement [of a] by simp

lemma bit_minus_iff [bit_simps]:
  \<open>bit (- a) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> \<not> bit (a - 1) n\<close>
  by (simp add: minus_eq_not_minus_1 bit_not_iff)

lemma even_not_iff [simp]:
  \<open>even (NOT a) \<longleftrightarrow> odd a\<close>
  using bit_not_iff [of a 0] by auto

lemma bit_not_exp_iff [bit_simps]:
  \<open>bit (NOT (2 ^ m)) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n \<noteq> m\<close>
  by (auto simp add: bit_not_iff bit_exp_iff)

lemma bit_minus_1_iff [simp]:
  \<open>bit (- 1) n \<longleftrightarrow> 2 ^ n \<noteq> 0\<close>
  by (simp add: bit_minus_iff)

lemma bit_minus_exp_iff [bit_simps]:
  \<open>bit (- (2 ^ m)) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n \<ge> m\<close>
  by (auto simp add: bit_simps simp flip: mask_eq_exp_minus_1)

lemma bit_minus_2_iff [simp]:
  \<open>bit (- 2) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> n > 0\<close>
  by (simp add: bit_minus_iff bit_1_iff)

lemma not_one [simp]:
  \<open>NOT 1 = - 2\<close>
  by (simp add: bit_eq_iff bit_not_iff) (simp add: bit_1_iff)

sublocale "and": semilattice_neutr \<open>(AND)\<close> \<open>- 1\<close>
  by standard (rule bit_eqI, simp add: bit_and_iff)

sublocale bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
  rewrites \<open>bit.xor = (XOR)\<close>
proof -
  interpret bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
    by standard (auto simp add: bit_and_iff bit_or_iff bit_not_iff intro: bit_eqI)
  show \<open>boolean_algebra (AND) (OR) NOT 0 (- 1)\<close>
    by standard
  show \<open>boolean_algebra.xor (AND) (OR) NOT = (XOR)\<close>
    by (rule ext, rule ext, rule bit_eqI)
      (auto simp add: bit.xor_def bit_and_iff bit_or_iff bit_xor_iff bit_not_iff)
qed

lemma and_eq_not_not_or:
  \<open>a AND b = NOT (NOT a OR NOT b)\<close>
  by simp

lemma or_eq_not_not_and:
  \<open>a OR b = NOT (NOT a AND NOT b)\<close>
  by simp

lemma not_add_distrib:
  \<open>NOT (a + b) = NOT a - b\<close>
  by (simp add: not_eq_complement algebra_simps)

lemma not_diff_distrib:
  \<open>NOT (a - b) = NOT a + b\<close>
  using not_add_distrib [of a \<open>- b\<close>] by simp

lemma (in ring_bit_operations) and_eq_minus_1_iff:
  \<open>a AND b = - 1 \<longleftrightarrow> a = - 1 \<and> b = - 1\<close>
proof
  assume \<open>a = - 1 \<and> b = - 1\<close>
  then show \<open>a AND b = - 1\<close>
    by simp
next
  assume \<open>a AND b = - 1\<close>
  have *: \<open>bit a n\<close> \<open>bit b n\<close> if \<open>2 ^ n \<noteq> 0\<close> for n
  proof -
    from \<open>a AND b = - 1\<close>
    have \<open>bit (a AND b) n = bit (- 1) n\<close>
      by (simp add: bit_eq_iff)
    then show \<open>bit a n\<close> \<open>bit b n\<close>
      using that by (simp_all add: bit_and_iff)
  qed
  have \<open>a = - 1\<close>
    by (rule bit_eqI) (simp add: *)
  moreover have \<open>b = - 1\<close>
    by (rule bit_eqI) (simp add: *)
  ultimately show \<open>a = - 1 \<and> b = - 1\<close>
    by simp
qed

lemma disjunctive_diff:
  \<open>a - b = a AND NOT b\<close> if \<open>\<And>n. bit b n \<Longrightarrow> bit a n\<close>
proof -
  have \<open>NOT a + b = NOT a OR b\<close>
    by (rule disjunctive_add) (auto simp add: bit_not_iff dest: that)
  then have \<open>NOT (NOT a + b) = NOT (NOT a OR b)\<close>
    by simp
  then show ?thesis
    by (simp add: not_add_distrib)
qed

lemma push_bit_minus:
  \<open>push_bit n (- a) = - push_bit n a\<close>
  by (simp add: push_bit_eq_mult)

lemma take_bit_not_take_bit:
  \<open>take_bit n (NOT (take_bit n a)) = take_bit n (NOT a)\<close>
  by (auto simp add: bit_eq_iff bit_take_bit_iff bit_not_iff)

lemma take_bit_not_iff:
  \<open>take_bit n (NOT a) = take_bit n (NOT b) \<longleftrightarrow> take_bit n a = take_bit n b\<close>
  apply (simp add: bit_eq_iff)
  apply (simp add: bit_not_iff bit_take_bit_iff bit_exp_iff)
  apply (use exp_eq_0_imp_not_bit in blast)
  done

lemma take_bit_not_eq_mask_diff:
  \<open>take_bit n (NOT a) = mask n - take_bit n a\<close>
proof -
  have \<open>take_bit n (NOT a) = take_bit n (NOT (take_bit n a))\<close>
    by (simp add: take_bit_not_take_bit)
  also have \<open>\<dots> = mask n AND NOT (take_bit n a)\<close>
    by (simp add: take_bit_eq_mask ac_simps)
  also have \<open>\<dots> = mask n - take_bit n a\<close>
    by (subst disjunctive_diff)
      (auto simp add: bit_take_bit_iff bit_mask_iff exp_eq_0_imp_not_bit)
  finally show ?thesis
    by simp
qed

lemma mask_eq_take_bit_minus_one:
  \<open>mask n = take_bit n (- 1)\<close>
  by (simp add: bit_eq_iff bit_mask_iff bit_take_bit_iff conj_commute)

lemma take_bit_minus_one_eq_mask:
  \<open>take_bit n (- 1) = mask n\<close>
  by (simp add: mask_eq_take_bit_minus_one)

lemma minus_exp_eq_not_mask:
  \<open>- (2 ^ n) = NOT (mask n)\<close>
  by (rule bit_eqI) (simp add: bit_minus_iff bit_not_iff flip: mask_eq_exp_minus_1)

lemma push_bit_minus_one_eq_not_mask:
  \<open>push_bit n (- 1) = NOT (mask n)\<close>
  by (simp add: push_bit_eq_mult minus_exp_eq_not_mask)

lemma take_bit_not_mask_eq_0:
  \<open>take_bit m (NOT (mask n)) = 0\<close> if \<open>n \<ge> m\<close>
  by (rule bit_eqI) (use that in \<open>simp add: bit_take_bit_iff bit_not_iff bit_mask_iff\<close>)

lemma unset_bit_eq_and_not:
  \<open>unset_bit n a = a AND NOT (push_bit n 1)\<close>
  by (rule bit_eqI) (auto simp add: bit_simps)

lemmas unset_bit_def = unset_bit_eq_and_not

end


subsection \<open>Instance \<^typ>\<open>int\<close>\<close>

lemma int_bit_bound:
  fixes k :: int
  obtains n where \<open>\<And>m. n \<le> m \<Longrightarrow> bit k m \<longleftrightarrow> bit k n\<close>
    and \<open>n > 0 \<Longrightarrow> bit k (n - 1) \<noteq> bit k n\<close>
proof -
  obtain q where *: \<open>\<And>m. q \<le> m \<Longrightarrow> bit k m \<longleftrightarrow> bit k q\<close>
  proof (cases \<open>k \<ge> 0\<close>)
    case True
    moreover from power_gt_expt [of 2 \<open>nat k\<close>]
    have \<open>nat k < 2 ^ nat k\<close>
      by simp
    then have \<open>int (nat k) < int (2 ^ nat k)\<close>
      by (simp only: of_nat_less_iff)
    ultimately have *: \<open>k div 2 ^ nat k = 0\<close>
      by simp
    show thesis
    proof (rule that [of \<open>nat k\<close>])
      fix m
      assume \<open>nat k \<le> m\<close>
      then show \<open>bit k m \<longleftrightarrow> bit k (nat k)\<close>
        by (auto simp add: * bit_iff_odd power_add zdiv_zmult2_eq dest!: le_Suc_ex)
    qed
  next
    case False
    moreover from power_gt_expt [of 2 \<open>nat (- k)\<close>]
    have \<open>nat (- k) < 2 ^ nat (- k)\<close>
      by simp
    then have \<open>int (nat (- k)) < int (2 ^ nat (- k))\<close>
      by (simp only: of_nat_less_iff)
    ultimately have \<open>- k div - (2 ^ nat (- k)) = - 1\<close>
      by (subst div_pos_neg_trivial) simp_all
    then have *: \<open>k div 2 ^ nat (- k) = - 1\<close>
      by simp
    show thesis
    proof (rule that [of \<open>nat (- k)\<close>])
      fix m
      assume \<open>nat (- k) \<le> m\<close>
      then show \<open>bit k m \<longleftrightarrow> bit k (nat (- k))\<close>
        by (auto simp add: * bit_iff_odd power_add zdiv_zmult2_eq minus_1_div_exp_eq_int dest!: le_Suc_ex)
    qed
  qed
  show thesis
  proof (cases \<open>\<forall>m. bit k m \<longleftrightarrow> bit k q\<close>)
    case True
    then have \<open>bit k 0 \<longleftrightarrow> bit k q\<close>
      by blast
    with True that [of 0] show thesis
      by simp
  next
    case False
    then obtain r where **: \<open>bit k r \<noteq> bit k q\<close>
      by blast
    have \<open>r < q\<close>
      by (rule ccontr) (use * [of r] ** in simp)
    define N where \<open>N = {n. n < q \<and> bit k n \<noteq> bit k q}\<close>
    moreover have \<open>finite N\<close> \<open>r \<in> N\<close>
      using ** N_def \<open>r < q\<close> by auto
    moreover define n where \<open>n = Suc (Max N)\<close>
    ultimately have \<open>\<And>m. n \<le> m \<Longrightarrow> bit k m \<longleftrightarrow> bit k n\<close>
      apply auto
         apply (metis (full_types, lifting) "*" Max_ge_iff Suc_n_not_le_n \<open>finite N\<close> all_not_in_conv mem_Collect_eq not_le)
        apply (metis "*" Max_ge Suc_n_not_le_n \<open>finite N\<close> linorder_not_less mem_Collect_eq)
        apply (metis "*" Max_ge Suc_n_not_le_n \<open>finite N\<close> linorder_not_less mem_Collect_eq)
      apply (metis (full_types, lifting) "*" Max_ge_iff Suc_n_not_le_n \<open>finite N\<close> all_not_in_conv mem_Collect_eq not_le)
      done
    have \<open>bit k (Max N) \<noteq> bit k n\<close>
      by (metis (mono_tags, lifting) "*" Max_in N_def \<open>\<And>m. n \<le> m \<Longrightarrow> bit k m = bit k n\<close> \<open>finite N\<close> \<open>r \<in> N\<close> empty_iff le_cases mem_Collect_eq)
    show thesis apply (rule that [of n])
      using \<open>\<And>m. n \<le> m \<Longrightarrow> bit k m = bit k n\<close> apply blast
      using \<open>bit k (Max N) \<noteq> bit k n\<close> n_def by auto
  qed
qed

instantiation int :: ring_bit_operations
begin

definition not_int :: \<open>int \<Rightarrow> int\<close>
  where \<open>not_int k = - k - 1\<close>

lemma not_int_rec:
  \<open>NOT k = of_bool (even k) + 2 * NOT (k div 2)\<close> for k :: int
  by (auto simp add: not_int_def elim: oddE)

lemma even_not_iff_int:
  \<open>even (NOT k) \<longleftrightarrow> odd k\<close> for k :: int
  by (simp add: not_int_def)

lemma not_int_div_2:
  \<open>NOT k div 2 = NOT (k div 2)\<close> for k :: int
  by (simp add: not_int_def)

lemma bit_not_int_iff [bit_simps]:
  \<open>bit (NOT k) n \<longleftrightarrow> \<not> bit k n\<close>
  for k :: int
  by (simp add: bit_not_int_iff' not_int_def)

function and_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>(k::int) AND l = (if k \<in> {0, - 1} \<and> l \<in> {0, - 1}
    then - of_bool (odd k \<and> odd l)
    else of_bool (odd k \<and> odd l) + 2 * ((k div 2) AND (l div 2)))\<close>
  by auto

termination
  by (relation \<open>measure (\<lambda>(k, l). nat (\<bar>k\<bar> + \<bar>l\<bar>))\<close>) auto

declare and_int.simps [simp del]

lemma and_int_rec:
  \<open>k AND l = of_bool (odd k \<and> odd l) + 2 * ((k div 2) AND (l div 2))\<close>
    for k l :: int
proof (cases \<open>k \<in> {0, - 1} \<and> l \<in> {0, - 1}\<close>)
  case True
  then show ?thesis
    by auto (simp_all add: and_int.simps)
next
  case False
  then show ?thesis
    by (auto simp add: ac_simps and_int.simps [of k l])
qed

lemma bit_and_int_iff:
  \<open>bit (k AND l) n \<longleftrightarrow> bit k n \<and> bit l n\<close> for k l :: int
proof (induction n arbitrary: k l)
  case 0
  then show ?case
    by (simp add: and_int_rec [of k l])
next
  case (Suc n)
  then show ?case
    by (simp add: and_int_rec [of k l] bit_Suc)
qed

lemma even_and_iff_int:
  \<open>even (k AND l) \<longleftrightarrow> even k \<or> even l\<close> for k l :: int
  using bit_and_int_iff [of k l 0] by auto

definition or_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k OR l = NOT (NOT k AND NOT l)\<close> for k l :: int

lemma or_int_rec:
  \<open>k OR l = of_bool (odd k \<or> odd l) + 2 * ((k div 2) OR (l div 2))\<close>
  for k l :: int
  using and_int_rec [of \<open>NOT k\<close> \<open>NOT l\<close>]
  by (simp add: or_int_def even_not_iff_int not_int_div_2)
    (simp_all add: not_int_def)

lemma bit_or_int_iff:
  \<open>bit (k OR l) n \<longleftrightarrow> bit k n \<or> bit l n\<close> for k l :: int
  by (simp add: or_int_def bit_not_int_iff bit_and_int_iff)

definition xor_int :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>k XOR l = k AND NOT l OR NOT k AND l\<close> for k l :: int

lemma xor_int_rec:
  \<open>k XOR l = of_bool (odd k \<noteq> odd l) + 2 * ((k div 2) XOR (l div 2))\<close>
  for k l :: int
  by (simp add: xor_int_def or_int_rec [of \<open>k AND NOT l\<close> \<open>NOT k AND l\<close>] even_and_iff_int even_not_iff_int)
    (simp add: and_int_rec [of \<open>NOT k\<close> \<open>l\<close>] and_int_rec [of \<open>k\<close> \<open>NOT l\<close>] not_int_div_2)

lemma bit_xor_int_iff:
  \<open>bit (k XOR l) n \<longleftrightarrow> bit k n \<noteq> bit l n\<close> for k l :: int
  by (auto simp add: xor_int_def bit_or_int_iff bit_and_int_iff bit_not_int_iff)

definition mask_int :: \<open>nat \<Rightarrow> int\<close>
  where \<open>mask n = (2 :: int) ^ n - 1\<close>

definition set_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>set_bit n k = k OR push_bit n 1\<close> for k :: int

definition unset_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>unset_bit n k = k AND NOT (push_bit n 1)\<close> for k :: int

definition flip_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>flip_bit n k = k XOR push_bit n 1\<close> for k :: int

instance proof
  fix k l :: int and m n :: nat
  show \<open>- k = NOT (k - 1)\<close>
    by (simp add: not_int_def)
  show \<open>bit (k AND l) n \<longleftrightarrow> bit k n \<and> bit l n\<close>
    by (fact bit_and_int_iff)
  show \<open>bit (k OR l) n \<longleftrightarrow> bit k n \<or> bit l n\<close>
    by (fact bit_or_int_iff)
  show \<open>bit (k XOR l) n \<longleftrightarrow> bit k n \<noteq> bit l n\<close>
    by (fact bit_xor_int_iff)
  show \<open>bit (unset_bit m k) n \<longleftrightarrow> bit k n \<and> m \<noteq> n\<close>
  proof -
    have \<open>unset_bit m k = k AND NOT (push_bit m 1)\<close>
      by (simp add: unset_bit_int_def)
    also have \<open>NOT (push_bit m 1 :: int) = - (push_bit m 1 + 1)\<close>
      by (simp add: not_int_def)
    finally show ?thesis by (simp only: bit_simps bit_and_int_iff) (auto simp add: bit_simps)
  qed
qed (simp_all add: bit_not_int_iff mask_int_def set_bit_int_def flip_bit_int_def)

end


lemma mask_half_int:
  \<open>mask n div 2 = (mask (n - 1) :: int)\<close>
  by (cases n) (simp_all add: mask_eq_exp_minus_1 algebra_simps)

lemma mask_nonnegative_int [simp]:
  \<open>mask n \<ge> (0::int)\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma not_mask_negative_int [simp]:
  \<open>\<not> mask n < (0::int)\<close>
  by (simp add: not_less)

lemma not_nonnegative_int_iff [simp]:
  \<open>NOT k \<ge> 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: not_int_def)

lemma not_negative_int_iff [simp]:
  \<open>NOT k < 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (subst Not_eq_iff [symmetric]) (simp add: not_less not_le)

lemma and_nonnegative_int_iff [simp]:
  \<open>k AND l \<ge> 0 \<longleftrightarrow> k \<ge> 0 \<or> l \<ge> 0\<close> for k l :: int
proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even k)
  then show ?case
    using and_int_rec [of \<open>k * 2\<close> l] by (simp add: pos_imp_zdiv_nonneg_iff)
next
  case (odd k)
  from odd have \<open>0 \<le> k AND l div 2 \<longleftrightarrow> 0 \<le> k \<or> 0 \<le> l div 2\<close>
    by simp
  then have \<open>0 \<le> (1 + k * 2) div 2 AND l div 2 \<longleftrightarrow> 0 \<le> (1 + k * 2) div 2\<or> 0 \<le> l div 2\<close>
    by simp
  with and_int_rec [of \<open>1 + k * 2\<close> l]
  show ?case
    by auto
qed

lemma and_negative_int_iff [simp]:
  \<open>k AND l < 0 \<longleftrightarrow> k < 0 \<and> l < 0\<close> for k l :: int
  by (subst Not_eq_iff [symmetric]) (simp add: not_less)

lemma and_less_eq:
  \<open>k AND l \<le> k\<close> if \<open>l < 0\<close> for k l :: int
using that proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even k)
  from even.IH [of \<open>l div 2\<close>] even.hyps even.prems
  show ?case
    by (simp add: and_int_rec [of _ l])
next
  case (odd k)
  from odd.IH [of \<open>l div 2\<close>] odd.hyps odd.prems
  show ?case
    by (simp add: and_int_rec [of _ l])
qed

lemma or_nonnegative_int_iff [simp]:
  \<open>k OR l \<ge> 0 \<longleftrightarrow> k \<ge> 0 \<and> l \<ge> 0\<close> for k l :: int
  by (simp only: or_eq_not_not_and not_nonnegative_int_iff) simp

lemma or_negative_int_iff [simp]:
  \<open>k OR l < 0 \<longleftrightarrow> k < 0 \<or> l < 0\<close> for k l :: int
  by (subst Not_eq_iff [symmetric]) (simp add: not_less)

lemma or_greater_eq:
  \<open>k OR l \<ge> k\<close> if \<open>l \<ge> 0\<close> for k l :: int
using that proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even k)
  from even.IH [of \<open>l div 2\<close>] even.hyps even.prems
  show ?case
    by (simp add: or_int_rec [of _ l])
next
  case (odd k)
  from odd.IH [of \<open>l div 2\<close>] odd.hyps odd.prems
  show ?case
    by (simp add: or_int_rec [of _ l])
qed

lemma xor_nonnegative_int_iff [simp]:
  \<open>k XOR l \<ge> 0 \<longleftrightarrow> (k \<ge> 0 \<longleftrightarrow> l \<ge> 0)\<close> for k l :: int
  by (simp only: bit.xor_def or_nonnegative_int_iff) auto

lemma xor_negative_int_iff [simp]:
  \<open>k XOR l < 0 \<longleftrightarrow> (k < 0) \<noteq> (l < 0)\<close> for k l :: int
  by (subst Not_eq_iff [symmetric]) (auto simp add: not_less)

lemma OR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> x\<close> \<open>x < 2 ^ n\<close> \<open>y < 2 ^ n\<close>
  shows \<open>x OR y < 2 ^ n\<close>
using assms proof (induction x arbitrary: y n rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even x)
  from even.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] even.prems even.hyps
  show ?case 
    by (cases n) (auto simp add: or_int_rec [of \<open>_ * 2\<close>] elim: oddE)
next
  case (odd x)
  from odd.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] odd.prems odd.hyps
  show ?case
    by (cases n) (auto simp add: or_int_rec [of \<open>1 + _ * 2\<close>], linarith)
qed

lemma XOR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> x\<close> \<open>x < 2 ^ n\<close> \<open>y < 2 ^ n\<close>
  shows \<open>x XOR y < 2 ^ n\<close>
using assms proof (induction x arbitrary: y n rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even x)
  from even.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] even.prems even.hyps
  show ?case 
    by (cases n) (auto simp add: xor_int_rec [of \<open>_ * 2\<close>] elim: oddE)
next
  case (odd x)
  from odd.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] odd.prems odd.hyps
  show ?case
    by (cases n) (auto simp add: xor_int_rec [of \<open>1 + _ * 2\<close>])
qed

lemma AND_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> x\<close>
  shows \<open>0 \<le> x AND y\<close>
  using assms by simp

lemma OR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> x\<close> \<open>0 \<le> y\<close>
  shows \<open>0 \<le> x OR y\<close>
  using assms by simp

lemma XOR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> x\<close> \<open>0 \<le> y\<close>
  shows \<open>0 \<le> x XOR y\<close>
  using assms by simp

lemma AND_upper1 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> x\<close>
  shows \<open>x AND y \<le> x\<close>
using assms proof (induction x arbitrary: y rule: int_bit_induct)
  case (odd k)
  then have \<open>k AND y div 2 \<le> k\<close>
    by simp
  then show ?case 
    by (simp add: and_int_rec [of \<open>1 + _ * 2\<close>])
qed (simp_all add: and_int_rec [of \<open>_ * 2\<close>])

lemmas AND_upper1' [simp] = order_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper1'' [simp] = order_le_less_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma AND_upper2 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes \<open>0 \<le> y\<close>
  shows \<open>x AND y \<le> y\<close>
  using assms AND_upper1 [of y x] by (simp add: ac_simps)

lemmas AND_upper2' [simp] = order_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper2'' [simp] = order_le_less_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma plus_and_or: \<open>(x AND y) + (x OR y) = x + y\<close> for x y :: int
proof (induction x arbitrary: y rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even x)
  from even.IH [of \<open>y div 2\<close>]
  show ?case
    by (auto simp add: and_int_rec [of _ y] or_int_rec [of _ y] elim: oddE)
next
  case (odd x)
  from odd.IH [of \<open>y div 2\<close>]
  show ?case
    by (auto simp add: and_int_rec [of _ y] or_int_rec [of _ y] elim: oddE)
qed

lemma set_bit_nonnegative_int_iff [simp]:
  \<open>set_bit n k \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (simp add: set_bit_def)

lemma set_bit_negative_int_iff [simp]:
  \<open>set_bit n k < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: set_bit_def)

lemma unset_bit_nonnegative_int_iff [simp]:
  \<open>unset_bit n k \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (simp add: unset_bit_def)

lemma unset_bit_negative_int_iff [simp]:
  \<open>unset_bit n k < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: unset_bit_def)

lemma flip_bit_nonnegative_int_iff [simp]:
  \<open>flip_bit n k \<ge> 0 \<longleftrightarrow> k \<ge> 0\<close> for k :: int
  by (simp add: flip_bit_def)

lemma flip_bit_negative_int_iff [simp]:
  \<open>flip_bit n k < 0 \<longleftrightarrow> k < 0\<close> for k :: int
  by (simp add: flip_bit_def)

lemma set_bit_greater_eq:
  \<open>set_bit n k \<ge> k\<close> for k :: int
  by (simp add: set_bit_def or_greater_eq)

lemma unset_bit_less_eq:
  \<open>unset_bit n k \<le> k\<close> for k :: int
  by (simp add: unset_bit_def and_less_eq)

lemma set_bit_eq:
  \<open>set_bit n k = k + of_bool (\<not> bit k n) * 2 ^ n\<close> for k :: int
proof (rule bit_eqI)
  fix m
  show \<open>bit (set_bit n k) m \<longleftrightarrow> bit (k + of_bool (\<not> bit k n) * 2 ^ n) m\<close>
  proof (cases \<open>m = n\<close>)
    case True
    then show ?thesis
      apply (simp add: bit_set_bit_iff)
      apply (simp add: bit_iff_odd div_plus_div_distrib_dvd_right)
      done
  next
    case False
    then show ?thesis
      apply (clarsimp simp add: bit_set_bit_iff)
      apply (subst disjunctive_add)
      apply (clarsimp simp add: bit_exp_iff)
      apply (clarsimp simp add: bit_or_iff bit_exp_iff)
      done
  qed
qed

lemma unset_bit_eq:
  \<open>unset_bit n k = k - of_bool (bit k n) * 2 ^ n\<close> for k :: int
proof (rule bit_eqI)
  fix m
  show \<open>bit (unset_bit n k) m \<longleftrightarrow> bit (k - of_bool (bit k n) * 2 ^ n) m\<close>
  proof (cases \<open>m = n\<close>)
    case True
    then show ?thesis
      apply (simp add: bit_unset_bit_iff)
      apply (simp add: bit_iff_odd)
      using div_plus_div_distrib_dvd_right [of \<open>2 ^ n\<close> \<open>- (2 ^ n)\<close> k]
      apply (simp add: dvd_neg_div)
      done
  next
    case False
    then show ?thesis
      apply (clarsimp simp add: bit_unset_bit_iff)
      apply (subst disjunctive_diff)
      apply (clarsimp simp add: bit_exp_iff)
      apply (clarsimp simp add: bit_and_iff bit_not_iff bit_exp_iff)
      done
  qed
qed

lemma take_bit_eq_mask_iff:
  \<open>take_bit n k = mask n \<longleftrightarrow> take_bit n (k + 1) = 0\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  for k :: int
proof
  assume ?P
  then have \<open>take_bit n (take_bit n k + take_bit n 1) = 0\<close>
    by (simp add: mask_eq_exp_minus_1)
  then show ?Q
    by (simp only: take_bit_add)
next
  assume ?Q
  then have \<open>take_bit n (k + 1) - 1 = - 1\<close>
    by simp
  then have \<open>take_bit n (take_bit n (k + 1) - 1) = take_bit n (- 1)\<close>
    by simp
  moreover have \<open>take_bit n (take_bit n (k + 1) - 1) = take_bit n k\<close>
    by (simp add: take_bit_eq_mod mod_simps)
  ultimately show ?P
    by (simp add: take_bit_minus_one_eq_mask)
qed

lemma take_bit_eq_mask_iff_exp_dvd:
  \<open>take_bit n k = mask n \<longleftrightarrow> 2 ^ n dvd k + 1\<close>
  for k :: int
  by (simp add: take_bit_eq_mask_iff flip: take_bit_eq_0_iff)

context ring_bit_operations
begin

lemma even_of_int_iff:
  \<open>even (of_int k) \<longleftrightarrow> even k\<close>
  by (induction k rule: int_bit_induct) simp_all

lemma bit_of_int_iff [bit_simps]:
  \<open>bit (of_int k) n \<longleftrightarrow> (2::'a) ^ n \<noteq> 0 \<and> bit k n\<close>
proof (cases \<open>(2::'a) ^ n = 0\<close>)
  case True
  then show ?thesis
    by (simp add: exp_eq_0_imp_not_bit)
next
  case False
  then have \<open>bit (of_int k) n \<longleftrightarrow> bit k n\<close>
  proof (induction k arbitrary: n rule: int_bit_induct)
    case zero
    then show ?case
      by simp
  next
    case minus
    then show ?case
      by simp
  next
    case (even k)
    then show ?case
      using bit_double_iff [of \<open>of_int k\<close> n] Parity.bit_double_iff [of k n]
      by (cases n) (auto simp add: ac_simps dest: mult_not_zero)
  next
    case (odd k)
    then show ?case
      using bit_double_iff [of \<open>of_int k\<close> n]
      by (cases n) (auto simp add: ac_simps bit_double_iff even_bit_succ_iff Parity.bit_Suc dest: mult_not_zero)
  qed
  with False show ?thesis
    by simp
qed

lemma push_bit_of_int:
  \<open>push_bit n (of_int k) = of_int (push_bit n k)\<close>
  by (simp add: push_bit_eq_mult semiring_bit_shifts_class.push_bit_eq_mult)

lemma of_int_push_bit:
  \<open>of_int (push_bit n k) = push_bit n (of_int k)\<close>
  by (simp add: push_bit_eq_mult semiring_bit_shifts_class.push_bit_eq_mult)

lemma take_bit_of_int:
  \<open>take_bit n (of_int k) = of_int (take_bit n k)\<close>
  by (rule bit_eqI) (simp add: bit_take_bit_iff Parity.bit_take_bit_iff bit_of_int_iff)

lemma of_int_take_bit:
  \<open>of_int (take_bit n k) = take_bit n (of_int k)\<close>
  by (rule bit_eqI) (simp add: bit_take_bit_iff Parity.bit_take_bit_iff bit_of_int_iff)

lemma of_int_not_eq:
  \<open>of_int (NOT k) = NOT (of_int k)\<close>
  by (rule bit_eqI) (simp add: bit_not_iff Bit_Operations.bit_not_iff bit_of_int_iff)

lemma of_int_and_eq:
  \<open>of_int (k AND l) = of_int k AND of_int l\<close>
  by (rule bit_eqI) (simp add: bit_of_int_iff bit_and_iff Bit_Operations.bit_and_iff)

lemma of_int_or_eq:
  \<open>of_int (k OR l) = of_int k OR of_int l\<close>
  by (rule bit_eqI) (simp add: bit_of_int_iff bit_or_iff Bit_Operations.bit_or_iff)

lemma of_int_xor_eq:
  \<open>of_int (k XOR l) = of_int k XOR of_int l\<close>
  by (rule bit_eqI) (simp add: bit_of_int_iff bit_xor_iff Bit_Operations.bit_xor_iff)

lemma of_int_mask_eq:
  \<open>of_int (mask n) = mask n\<close>
  by (induction n) (simp_all add: mask_Suc_double Bit_Operations.mask_Suc_double of_int_or_eq)

end

lemma minus_numeral_inc_eq:
  \<open>- numeral (Num.inc n) = NOT (numeral n :: int)\<close>
  by (simp add: not_int_def sub_inc_One_eq add_One)

lemma sub_one_eq_not_neg:
  \<open>Num.sub n num.One = NOT (- numeral n :: int)\<close>
  by (simp add: not_int_def)

lemma int_not_numerals [simp]:
  \<open>NOT (numeral (Num.Bit0 n) :: int) = - numeral (Num.Bit1 n)\<close>
  \<open>NOT (numeral (Num.Bit1 n) :: int) = - numeral (Num.inc (num.Bit1 n))\<close>
  \<open>NOT (numeral (Num.BitM n) :: int) = - numeral (num.Bit0 n)\<close>
  \<open>NOT (- numeral (Num.Bit0 n) :: int) = numeral (Num.BitM n)\<close>
  \<open>NOT (- numeral (Num.Bit1 n) :: int) = numeral (Num.Bit0 n)\<close>
  by (simp_all add: not_int_def add_One inc_BitM_eq) 

text \<open>FIXME: The rule sets below are very large (24 rules for each
  operator). Is there a simpler way to do this?\<close>

context
begin

private lemma eqI:
  \<open>k = l\<close>
  if num: \<open>\<And>n. bit k (numeral n) \<longleftrightarrow> bit l (numeral n)\<close>
    and even: \<open>even k \<longleftrightarrow> even l\<close>
  for k l :: int
proof (rule bit_eqI)
  fix n
  show \<open>bit k n \<longleftrightarrow> bit l n\<close>
  proof (cases n)
    case 0
    with even show ?thesis
      by simp
  next
    case (Suc n)
    with num [of \<open>num_of_nat (Suc n)\<close>] show ?thesis
      by (simp only: numeral_num_of_nat)
  qed
qed

lemma int_and_numerals [simp]:
  \<open>numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND numeral y)\<close>
  \<open>numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (2 :: int) * (numeral x AND numeral y)\<close>
  \<open>numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND numeral y)\<close>
  \<open>numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x AND numeral y)\<close>
  \<open>numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND - numeral y)\<close>
  \<open>numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (2 :: int) * (numeral x AND - numeral (y + Num.One))\<close>
  \<open>numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND - numeral y)\<close>
  \<open>numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x AND - numeral (y + Num.One))\<close>
  \<open>- numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (2 :: int) * (- numeral x AND numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (2 :: int) * (- numeral x AND numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (2 :: int) * (- numeral (x + Num.One) AND numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) AND numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (- numeral x AND - numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (2 :: int) * (- numeral x AND - numeral (y + Num.One))\<close>
  \<open>- numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (- numeral (x + Num.One) AND - numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) AND - numeral (y + Num.One))\<close>
  \<open>(1::int) AND numeral (Num.Bit0 y) = 0\<close>
  \<open>(1::int) AND numeral (Num.Bit1 y) = 1\<close>
  \<open>(1::int) AND - numeral (Num.Bit0 y) = 0\<close>
  \<open>(1::int) AND - numeral (Num.Bit1 y) = 1\<close>
  \<open>numeral (Num.Bit0 x) AND (1::int) = 0\<close>
  \<open>numeral (Num.Bit1 x) AND (1::int) = 1\<close>
  \<open>- numeral (Num.Bit0 x) AND (1::int) = 0\<close>
  \<open>- numeral (Num.Bit1 x) AND (1::int) = 1\<close>
  by (auto simp add: bit_and_iff bit_minus_iff even_and_iff bit_double_iff even_bit_succ_iff add_One sub_inc_One_eq intro: eqI)

lemma int_or_numerals [simp]:
  \<open>numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (2 :: int) * (numeral x OR numeral y)\<close>
  \<open>numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR numeral y)\<close>
  \<open>numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x OR numeral y)\<close>
  \<open>numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR numeral y)\<close>
  \<open>numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (2 :: int) * (numeral x OR - numeral y)\<close>
  \<open>numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR - numeral (y + Num.One))\<close>
  \<open>numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x OR - numeral y)\<close>
  \<open>numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR - numeral (y + Num.One))\<close>
  \<open>- numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (2 :: int) * (- numeral x OR numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x OR numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (2 :: int) * (- numeral x OR - numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x OR - numeral (y + Num.One))\<close>
  \<open>- numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR - numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR - numeral (y + Num.One))\<close>
  \<open>(1::int) OR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)\<close>
  \<open>(1::int) OR numeral (Num.Bit1 y) = numeral (Num.Bit1 y)\<close>
  \<open>(1::int) OR - numeral (Num.Bit0 y) = - numeral (Num.BitM y)\<close>
  \<open>(1::int) OR - numeral (Num.Bit1 y) = - numeral (Num.Bit1 y)\<close>
  \<open>numeral (Num.Bit0 x) OR (1::int) = numeral (Num.Bit1 x)\<close>
  \<open>numeral (Num.Bit1 x) OR (1::int) = numeral (Num.Bit1 x)\<close>
  \<open>- numeral (Num.Bit0 x) OR (1::int) = - numeral (Num.BitM x)\<close>
  \<open>- numeral (Num.Bit1 x) OR (1::int) = - numeral (Num.Bit1 x)\<close>
  by (auto simp add: bit_or_iff bit_minus_iff even_or_iff bit_double_iff even_bit_succ_iff add_One sub_inc_One_eq sub_BitM_One_eq intro: eqI)

lemma int_xor_numerals [simp]:
  \<open>numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (2 :: int) * (numeral x XOR numeral y)\<close>
  \<open>numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x XOR numeral y)\<close>
  \<open>numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x XOR numeral y)\<close>
  \<open>numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (2 :: int) * (numeral x XOR numeral y)\<close>
  \<open>numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (2 :: int) * (numeral x XOR - numeral y)\<close>
  \<open>numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x XOR - numeral (y + Num.One))\<close>
  \<open>numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x XOR - numeral y)\<close>
  \<open>numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (2 :: int) * (numeral x XOR - numeral (y + Num.One))\<close>
  \<open>- numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (2 :: int) * (- numeral x XOR numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x XOR numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) XOR numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (2 :: int) * (- numeral (x + Num.One) XOR numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (2 :: int) * (- numeral x XOR - numeral y)\<close>
  \<open>- numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x XOR - numeral (y + Num.One))\<close>
  \<open>- numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) XOR - numeral y)\<close>
  \<open>- numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (2 :: int) * (- numeral (x + Num.One) XOR - numeral (y + Num.One))\<close>
  \<open>(1::int) XOR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)\<close>
  \<open>(1::int) XOR numeral (Num.Bit1 y) = numeral (Num.Bit0 y)\<close>
  \<open>(1::int) XOR - numeral (Num.Bit0 y) = - numeral (Num.BitM y)\<close>
  \<open>(1::int) XOR - numeral (Num.Bit1 y) = - numeral (Num.Bit0 (y + Num.One))\<close>
  \<open>numeral (Num.Bit0 x) XOR (1::int) = numeral (Num.Bit1 x)\<close>
  \<open>numeral (Num.Bit1 x) XOR (1::int) = numeral (Num.Bit0 x)\<close>
  \<open>- numeral (Num.Bit0 x) XOR (1::int) = - numeral (Num.BitM x)\<close>
  \<open>- numeral (Num.Bit1 x) XOR (1::int) = - numeral (Num.Bit0 (x + Num.One))\<close>
  by (auto simp add: bit_xor_iff bit_minus_iff even_xor_iff bit_double_iff even_bit_succ_iff add_One sub_inc_One_eq sub_BitM_One_eq intro: eqI)

end


subsection \<open>Bit concatenation\<close>

definition concat_bit :: \<open>nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>concat_bit n k l = take_bit n k OR push_bit n l\<close>

lemma bit_concat_bit_iff [bit_simps]:
  \<open>bit (concat_bit m k l) n \<longleftrightarrow> n < m \<and> bit k n \<or> m \<le> n \<and> bit l (n - m)\<close>
  by (simp add: concat_bit_def bit_or_iff bit_and_iff bit_take_bit_iff bit_push_bit_iff ac_simps)

lemma concat_bit_eq:
  \<open>concat_bit n k l = take_bit n k + push_bit n l\<close>
  by (simp add: concat_bit_def take_bit_eq_mask
    bit_and_iff bit_mask_iff bit_push_bit_iff disjunctive_add)

lemma concat_bit_0 [simp]:
  \<open>concat_bit 0 k l = l\<close>
  by (simp add: concat_bit_def)

lemma concat_bit_Suc:
  \<open>concat_bit (Suc n) k l = k mod 2 + 2 * concat_bit n (k div 2) l\<close>
  by (simp add: concat_bit_eq take_bit_Suc push_bit_double)

lemma concat_bit_of_zero_1 [simp]:
  \<open>concat_bit n 0 l = push_bit n l\<close>
  by (simp add: concat_bit_def)

lemma concat_bit_of_zero_2 [simp]:
  \<open>concat_bit n k 0 = take_bit n k\<close>
  by (simp add: concat_bit_def take_bit_eq_mask)

lemma concat_bit_nonnegative_iff [simp]:
  \<open>concat_bit n k l \<ge> 0 \<longleftrightarrow> l \<ge> 0\<close>
  by (simp add: concat_bit_def)

lemma concat_bit_negative_iff [simp]:
  \<open>concat_bit n k l < 0 \<longleftrightarrow> l < 0\<close>
  by (simp add: concat_bit_def)

lemma concat_bit_assoc:
  \<open>concat_bit n k (concat_bit m l r) = concat_bit (m + n) (concat_bit n k l) r\<close>
  by (rule bit_eqI) (auto simp add: bit_concat_bit_iff ac_simps)

lemma concat_bit_assoc_sym:
  \<open>concat_bit m (concat_bit n k l) r = concat_bit (min m n) k (concat_bit (m - n) l r)\<close>
  by (rule bit_eqI) (auto simp add: bit_concat_bit_iff ac_simps min_def)

lemma concat_bit_eq_iff:
  \<open>concat_bit n k l = concat_bit n r s
    \<longleftrightarrow> take_bit n k = take_bit n r \<and> l = s\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof
  assume ?Q
  then show ?P
    by (simp add: concat_bit_def)
next
  assume ?P
  then have *: \<open>bit (concat_bit n k l) m = bit (concat_bit n r s) m\<close> for m
    by (simp add: bit_eq_iff)
  have \<open>take_bit n k = take_bit n r\<close>
  proof (rule bit_eqI)
    fix m
    from * [of m]
    show \<open>bit (take_bit n k) m \<longleftrightarrow> bit (take_bit n r) m\<close>
      by (auto simp add: bit_take_bit_iff bit_concat_bit_iff)
  qed
  moreover have \<open>push_bit n l = push_bit n s\<close>
  proof (rule bit_eqI)
    fix m
    from * [of m]
    show \<open>bit (push_bit n l) m \<longleftrightarrow> bit (push_bit n s) m\<close>
      by (auto simp add: bit_push_bit_iff bit_concat_bit_iff)
  qed
  then have \<open>l = s\<close>
    by (simp add: push_bit_eq_mult)
  ultimately show ?Q
    by (simp add: concat_bit_def)
qed

lemma take_bit_concat_bit_eq:
  \<open>take_bit m (concat_bit n k l) = concat_bit (min m n) k (take_bit (m - n) l)\<close>
  by (rule bit_eqI)
    (auto simp add: bit_take_bit_iff bit_concat_bit_iff min_def)  

lemma concat_bit_take_bit_eq:
  \<open>concat_bit n (take_bit n b) = concat_bit n b\<close>
  by (simp add: concat_bit_def [abs_def])


subsection \<open>Taking bits with sign propagation\<close>

context ring_bit_operations
begin

definition signed_take_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>signed_take_bit n a = take_bit n a OR (of_bool (bit a n) * NOT (mask n))\<close>

lemma signed_take_bit_eq_if_positive:
  \<open>signed_take_bit n a = take_bit n a\<close> if \<open>\<not> bit a n\<close>
  using that by (simp add: signed_take_bit_def)

lemma signed_take_bit_eq_if_negative:
  \<open>signed_take_bit n a = take_bit n a OR NOT (mask n)\<close> if \<open>bit a n\<close>
  using that by (simp add: signed_take_bit_def)

lemma even_signed_take_bit_iff:
  \<open>even (signed_take_bit m a) \<longleftrightarrow> even a\<close>
  by (auto simp add: signed_take_bit_def even_or_iff even_mask_iff bit_double_iff)

lemma bit_signed_take_bit_iff [bit_simps]:
  \<open>bit (signed_take_bit m a) n \<longleftrightarrow> 2 ^ n \<noteq> 0 \<and> bit a (min m n)\<close>
  by (simp add: signed_take_bit_def bit_take_bit_iff bit_or_iff bit_not_iff bit_mask_iff min_def not_le)
    (use exp_eq_0_imp_not_bit in blast)

lemma signed_take_bit_0 [simp]:
  \<open>signed_take_bit 0 a = - (a mod 2)\<close>
  by (simp add: signed_take_bit_def odd_iff_mod_2_eq_one)

lemma signed_take_bit_Suc:
  \<open>signed_take_bit (Suc n) a = a mod 2 + 2 * signed_take_bit n (a div 2)\<close>
proof (rule bit_eqI)
  fix m
  assume *: \<open>2 ^ m \<noteq> 0\<close>
  show \<open>bit (signed_take_bit (Suc n) a) m \<longleftrightarrow>
    bit (a mod 2 + 2 * signed_take_bit n (a div 2)) m\<close>
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: even_signed_take_bit_iff)
  next
    case (Suc m)
    with * have \<open>2 ^ m \<noteq> 0\<close>
      by (metis mult_not_zero power_Suc)
    with Suc show ?thesis
      by (simp add: bit_signed_take_bit_iff mod2_eq_if bit_double_iff even_bit_succ_iff
        ac_simps flip: bit_Suc)
  qed
qed

lemma signed_take_bit_of_0 [simp]:
  \<open>signed_take_bit n 0 = 0\<close>
  by (simp add: signed_take_bit_def)

lemma signed_take_bit_of_minus_1 [simp]:
  \<open>signed_take_bit n (- 1) = - 1\<close>
  by (simp add: signed_take_bit_def take_bit_minus_one_eq_mask mask_eq_exp_minus_1)

lemma signed_take_bit_Suc_1 [simp]:
  \<open>signed_take_bit (Suc n) 1 = 1\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_rec:
  \<open>signed_take_bit n a = (if n = 0 then - (a mod 2) else a mod 2 + 2 * signed_take_bit (n - 1) (a div 2))\<close>
  by (cases n) (simp_all add: signed_take_bit_Suc)

lemma signed_take_bit_eq_iff_take_bit_eq:
  \<open>signed_take_bit n a = signed_take_bit n b \<longleftrightarrow> take_bit (Suc n) a = take_bit (Suc n) b\<close>
proof -
  have \<open>bit (signed_take_bit n a) = bit (signed_take_bit n b) \<longleftrightarrow> bit (take_bit (Suc n) a) = bit (take_bit (Suc n) b)\<close>
    by (simp add: fun_eq_iff bit_signed_take_bit_iff bit_take_bit_iff not_le less_Suc_eq_le min_def)
      (use exp_eq_0_imp_not_bit in fastforce)
  then show ?thesis
    by (simp add: bit_eq_iff fun_eq_iff)
qed

lemma signed_take_bit_signed_take_bit [simp]:
  \<open>signed_take_bit m (signed_take_bit n a) = signed_take_bit (min m n) a\<close>
proof (rule bit_eqI)
  fix q
  show \<open>bit (signed_take_bit m (signed_take_bit n a)) q \<longleftrightarrow>
    bit (signed_take_bit (min m n) a) q\<close>
    by (simp add: bit_signed_take_bit_iff min_def bit_or_iff bit_not_iff bit_mask_iff bit_take_bit_iff)
      (use le_Suc_ex exp_add_not_zero_imp in blast)
qed

lemma signed_take_bit_take_bit:
  \<open>signed_take_bit m (take_bit n a) = (if n \<le> m then take_bit n else signed_take_bit m) a\<close>
  by (rule bit_eqI) (auto simp add: bit_signed_take_bit_iff min_def bit_take_bit_iff)

lemma take_bit_signed_take_bit:
  \<open>take_bit m (signed_take_bit n a) = take_bit m a\<close> if \<open>m \<le> Suc n\<close>
  using that by (rule le_SucE; intro bit_eqI)
   (auto simp add: bit_take_bit_iff bit_signed_take_bit_iff min_def less_Suc_eq)

end

text \<open>Modulus centered around 0\<close>

lemma signed_take_bit_eq_concat_bit:
  \<open>signed_take_bit n k = concat_bit n k (- of_bool (bit k n))\<close>
  by (simp add: concat_bit_def signed_take_bit_def push_bit_minus_one_eq_not_mask)

lemma signed_take_bit_add:
  \<open>signed_take_bit n (signed_take_bit n k + signed_take_bit n l) = signed_take_bit n (k + l)\<close>
  for k l :: int
proof -
  have \<open>take_bit (Suc n)
     (take_bit (Suc n) (signed_take_bit n k) +
      take_bit (Suc n) (signed_take_bit n l)) =
    take_bit (Suc n) (k + l)\<close>
    by (simp add: take_bit_signed_take_bit take_bit_add)
  then show ?thesis
    by (simp only: signed_take_bit_eq_iff_take_bit_eq take_bit_add)
qed

lemma signed_take_bit_diff:
  \<open>signed_take_bit n (signed_take_bit n k - signed_take_bit n l) = signed_take_bit n (k - l)\<close>
  for k l :: int
proof -
  have \<open>take_bit (Suc n)
     (take_bit (Suc n) (signed_take_bit n k) -
      take_bit (Suc n) (signed_take_bit n l)) =
    take_bit (Suc n) (k - l)\<close>
    by (simp add: take_bit_signed_take_bit take_bit_diff)
  then show ?thesis
    by (simp only: signed_take_bit_eq_iff_take_bit_eq take_bit_diff)
qed

lemma signed_take_bit_minus:
  \<open>signed_take_bit n (- signed_take_bit n k) = signed_take_bit n (- k)\<close>
  for k :: int
proof -
  have \<open>take_bit (Suc n)
     (- take_bit (Suc n) (signed_take_bit n k)) =
    take_bit (Suc n) (- k)\<close>
    by (simp add: take_bit_signed_take_bit take_bit_minus)
  then show ?thesis
    by (simp only: signed_take_bit_eq_iff_take_bit_eq take_bit_minus)
qed

lemma signed_take_bit_mult:
  \<open>signed_take_bit n (signed_take_bit n k * signed_take_bit n l) = signed_take_bit n (k * l)\<close>
  for k l :: int
proof -
  have \<open>take_bit (Suc n)
     (take_bit (Suc n) (signed_take_bit n k) *
      take_bit (Suc n) (signed_take_bit n l)) =
    take_bit (Suc n) (k * l)\<close>
    by (simp add: take_bit_signed_take_bit take_bit_mult)
  then show ?thesis
    by (simp only: signed_take_bit_eq_iff_take_bit_eq take_bit_mult)
qed

lemma signed_take_bit_eq_take_bit_minus:
  \<open>signed_take_bit n k = take_bit (Suc n) k - 2 ^ Suc n * of_bool (bit k n)\<close>
  for k :: int
proof (cases \<open>bit k n\<close>)
  case True
  have \<open>signed_take_bit n k = take_bit (Suc n) k OR NOT (mask (Suc n))\<close>
    by (rule bit_eqI) (auto simp add: bit_signed_take_bit_iff min_def bit_take_bit_iff bit_or_iff bit_not_iff bit_mask_iff less_Suc_eq True)
  then have \<open>signed_take_bit n k = take_bit (Suc n) k + NOT (mask (Suc n))\<close>
    by (simp add: disjunctive_add bit_take_bit_iff bit_not_iff bit_mask_iff)
  with True show ?thesis
    by (simp flip: minus_exp_eq_not_mask)
next
  case False
  show ?thesis
    by (rule bit_eqI) (simp add: False bit_signed_take_bit_iff bit_take_bit_iff min_def less_Suc_eq)
qed

lemma signed_take_bit_eq_take_bit_shift:
  \<open>signed_take_bit n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n\<close>
  for k :: int
proof -
  have *: \<open>take_bit n k OR 2 ^ n = take_bit n k + 2 ^ n\<close>
    by (simp add: disjunctive_add bit_exp_iff bit_take_bit_iff)
  have \<open>take_bit n k - 2 ^ n = take_bit n k + NOT (mask n)\<close>
    by (simp add: minus_exp_eq_not_mask)
  also have \<open>\<dots> = take_bit n k OR NOT (mask n)\<close>
    by (rule disjunctive_add)
      (simp add: bit_exp_iff bit_take_bit_iff bit_not_iff bit_mask_iff)
  finally have **: \<open>take_bit n k - 2 ^ n = take_bit n k OR NOT (mask n)\<close> .
  have \<open>take_bit (Suc n) (k + 2 ^ n) = take_bit (Suc n) (take_bit (Suc n) k + take_bit (Suc n) (2 ^ n))\<close>
    by (simp only: take_bit_add)
  also have \<open>take_bit (Suc n) k = 2 ^ n * of_bool (bit k n) + take_bit n k\<close>
    by (simp add: take_bit_Suc_from_most)
  finally have \<open>take_bit (Suc n) (k + 2 ^ n) = take_bit (Suc n) (2 ^ (n + of_bool (bit k n)) + take_bit n k)\<close>
    by (simp add: ac_simps)
  also have \<open>2 ^ (n + of_bool (bit k n)) + take_bit n k = 2 ^ (n + of_bool (bit k n)) OR take_bit n k\<close>
    by (rule disjunctive_add)
      (auto simp add: disjunctive_add bit_take_bit_iff bit_double_iff bit_exp_iff)
  finally show ?thesis
    using * ** by (simp add: signed_take_bit_def concat_bit_Suc min_def ac_simps)
qed

lemma signed_take_bit_nonnegative_iff [simp]:
  \<open>0 \<le> signed_take_bit n k \<longleftrightarrow> \<not> bit k n\<close>
  for k :: int
  by (simp add: signed_take_bit_def not_less concat_bit_def)

lemma signed_take_bit_negative_iff [simp]:
  \<open>signed_take_bit n k < 0 \<longleftrightarrow> bit k n\<close>
  for k :: int
  by (simp add: signed_take_bit_def not_less concat_bit_def)

lemma signed_take_bit_int_greater_eq_minus_exp [simp]:
  \<open>- (2 ^ n) \<le> signed_take_bit n k\<close>
  for k :: int
  by (simp add: signed_take_bit_eq_take_bit_shift)

lemma signed_take_bit_int_less_exp [simp]:
  \<open>signed_take_bit n k < 2 ^ n\<close>
  for k :: int
  using take_bit_int_less_exp [of \<open>Suc n\<close>]
  by (simp add: signed_take_bit_eq_take_bit_shift)

lemma signed_take_bit_int_eq_self_iff:
  \<open>signed_take_bit n k = k \<longleftrightarrow> - (2 ^ n) \<le> k \<and> k < 2 ^ n\<close>
  for k :: int
  by (auto simp add: signed_take_bit_eq_take_bit_shift take_bit_int_eq_self_iff algebra_simps)

lemma signed_take_bit_int_eq_self:
  \<open>signed_take_bit n k = k\<close> if \<open>- (2 ^ n) \<le> k\<close> \<open>k < 2 ^ n\<close>
  for k :: int
  using that by (simp add: signed_take_bit_int_eq_self_iff)

lemma signed_take_bit_int_less_eq_self_iff:
  \<open>signed_take_bit n k \<le> k \<longleftrightarrow> - (2 ^ n) \<le> k\<close>
  for k :: int
  by (simp add: signed_take_bit_eq_take_bit_shift take_bit_int_less_eq_self_iff algebra_simps)
    linarith

lemma signed_take_bit_int_less_self_iff:
  \<open>signed_take_bit n k < k \<longleftrightarrow> 2 ^ n \<le> k\<close>
  for k :: int
  by (simp add: signed_take_bit_eq_take_bit_shift take_bit_int_less_self_iff algebra_simps)

lemma signed_take_bit_int_greater_self_iff:
  \<open>k < signed_take_bit n k \<longleftrightarrow> k < - (2 ^ n)\<close>
  for k :: int
  by (simp add: signed_take_bit_eq_take_bit_shift take_bit_int_greater_self_iff algebra_simps)
    linarith

lemma signed_take_bit_int_greater_eq_self_iff:
  \<open>k \<le> signed_take_bit n k \<longleftrightarrow> k < 2 ^ n\<close>
  for k :: int
  by (simp add: signed_take_bit_eq_take_bit_shift take_bit_int_greater_eq_self_iff algebra_simps)

lemma signed_take_bit_int_greater_eq:
  \<open>k + 2 ^ Suc n \<le> signed_take_bit n k\<close> if \<open>k < - (2 ^ n)\<close>
  for k :: int
  using that take_bit_int_greater_eq [of \<open>k + 2 ^ n\<close> \<open>Suc n\<close>]
  by (simp add: signed_take_bit_eq_take_bit_shift)

lemma signed_take_bit_int_less_eq:
  \<open>signed_take_bit n k \<le> k - 2 ^ Suc n\<close> if \<open>k \<ge> 2 ^ n\<close>
  for k :: int
  using that take_bit_int_less_eq [of \<open>Suc n\<close> \<open>k + 2 ^ n\<close>]
  by (simp add: signed_take_bit_eq_take_bit_shift)

lemma signed_take_bit_Suc_bit0 [simp]:
  \<open>signed_take_bit (Suc n) (numeral (Num.Bit0 k)) = signed_take_bit n (numeral k) * (2 :: int)\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_bit1 [simp]:
  \<open>signed_take_bit (Suc n) (numeral (Num.Bit1 k)) = signed_take_bit n (numeral k) * 2 + (1 :: int)\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_minus_bit0 [simp]:
  \<open>signed_take_bit (Suc n) (- numeral (Num.Bit0 k)) = signed_take_bit n (- numeral k) * (2 :: int)\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_Suc_minus_bit1 [simp]:
  \<open>signed_take_bit (Suc n) (- numeral (Num.Bit1 k)) = signed_take_bit n (- numeral k - 1) * 2 + (1 :: int)\<close>
  by (simp add: signed_take_bit_Suc)

lemma signed_take_bit_numeral_bit0 [simp]:
  \<open>signed_take_bit (numeral l) (numeral (Num.Bit0 k)) = signed_take_bit (pred_numeral l) (numeral k) * (2 :: int)\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_numeral_bit1 [simp]:
  \<open>signed_take_bit (numeral l) (numeral (Num.Bit1 k)) = signed_take_bit (pred_numeral l) (numeral k) * 2 + (1 :: int)\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_numeral_minus_bit0 [simp]:
  \<open>signed_take_bit (numeral l) (- numeral (Num.Bit0 k)) = signed_take_bit (pred_numeral l) (- numeral k) * (2 :: int)\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_numeral_minus_bit1 [simp]:
  \<open>signed_take_bit (numeral l) (- numeral (Num.Bit1 k)) = signed_take_bit (pred_numeral l) (- numeral k - 1) * 2 + (1 :: int)\<close>
  by (simp add: signed_take_bit_rec)

lemma signed_take_bit_code [code]:
  \<open>signed_take_bit n a =
  (let l = take_bit (Suc n) a
   in if bit l n then l + push_bit (Suc n) (- 1) else l)\<close>
proof -
  have *: \<open>take_bit (Suc n) a + push_bit n (- 2) =
    take_bit (Suc n) a OR NOT (mask (Suc n))\<close>
    by (auto simp add: bit_take_bit_iff bit_push_bit_iff bit_not_iff bit_mask_iff disjunctive_add
       simp flip: push_bit_minus_one_eq_not_mask)
  show ?thesis
    by (rule bit_eqI)
      (auto simp add: Let_def * bit_signed_take_bit_iff bit_take_bit_iff min_def less_Suc_eq bit_not_iff bit_mask_iff bit_or_iff)
qed


subsection \<open>Instance \<^typ>\<open>nat\<close>\<close>

instantiation nat :: semiring_bit_operations
begin

definition and_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m AND n = nat (int m AND int n)\<close> for m n :: nat

definition or_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m OR n = nat (int m OR int n)\<close> for m n :: nat

definition xor_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>m XOR n = nat (int m XOR int n)\<close> for m n :: nat

definition mask_nat :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>mask n = (2 :: nat) ^ n - 1\<close>

definition set_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>set_bit m n = n OR push_bit m 1\<close> for m n :: nat

definition unset_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>unset_bit m n = (if bit n m then n - push_bit m 1 else n)\<close> for m n :: nat

definition flip_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>flip_bit m n = n XOR push_bit m 1\<close> for m n :: nat

instance proof
  fix m n q :: nat
  show \<open>bit (m AND n) q \<longleftrightarrow> bit m q \<and> bit n q\<close>
    by (simp add: and_nat_def bit_simps)
  show \<open>bit (m OR n) q \<longleftrightarrow> bit m q \<or> bit n q\<close>
    by (simp add: or_nat_def bit_simps)
  show \<open>bit (m XOR n) q \<longleftrightarrow> bit m q \<noteq> bit n q\<close>
    by (simp add: xor_nat_def bit_simps)
  show \<open>bit (unset_bit m n) q \<longleftrightarrow> bit n q \<and> m \<noteq> q\<close>
  proof (cases \<open>bit n m\<close>)
    case False
    then show ?thesis by (auto simp add: unset_bit_nat_def)
  next
    case True
    have \<open>push_bit m (drop_bit m n) + take_bit m n = n\<close>
      by (fact bits_ident)
    also from \<open>bit n m\<close> have \<open>drop_bit m n = 2 * drop_bit (Suc m) n  + 1\<close>
      by (simp add: drop_bit_Suc drop_bit_half even_drop_bit_iff_not_bit ac_simps)
    finally have \<open>push_bit m (2 * drop_bit (Suc m) n) + take_bit m n + push_bit m 1 = n\<close>
      by (simp only: push_bit_add ac_simps)
    then have \<open>n - push_bit m 1 = push_bit m (2 * drop_bit (Suc m) n) + take_bit m n\<close>
      by simp
    then have \<open>n - push_bit m 1 = push_bit m (2 * drop_bit (Suc m) n) OR take_bit m n\<close>
      by (simp add: or_nat_def bit_simps flip: disjunctive_add)
    with \<open>bit n m\<close> show ?thesis
      by (auto simp add: unset_bit_nat_def or_nat_def bit_simps)
  qed
qed (simp_all add: mask_nat_def set_bit_nat_def flip_bit_nat_def)

end

lemma and_nat_rec:
  \<open>m AND n = of_bool (odd m \<and> odd n) + 2 * ((m div 2) AND (n div 2))\<close> for m n :: nat
  by (simp add: and_nat_def and_int_rec [of \<open>int m\<close> \<open>int n\<close>] zdiv_int nat_add_distrib nat_mult_distrib)

lemma or_nat_rec:
  \<open>m OR n = of_bool (odd m \<or> odd n) + 2 * ((m div 2) OR (n div 2))\<close> for m n :: nat
  by (simp add: or_nat_def or_int_rec [of \<open>int m\<close> \<open>int n\<close>] zdiv_int nat_add_distrib nat_mult_distrib)

lemma xor_nat_rec:
  \<open>m XOR n = of_bool (odd m \<noteq> odd n) + 2 * ((m div 2) XOR (n div 2))\<close> for m n :: nat
  by (simp add: xor_nat_def xor_int_rec [of \<open>int m\<close> \<open>int n\<close>] zdiv_int nat_add_distrib nat_mult_distrib)

lemma Suc_0_and_eq [simp]:
  \<open>Suc 0 AND n = n mod 2\<close>
  using one_and_eq [of n] by simp

lemma and_Suc_0_eq [simp]:
  \<open>n AND Suc 0 = n mod 2\<close>
  using and_one_eq [of n] by simp

lemma Suc_0_or_eq:
  \<open>Suc 0 OR n = n + of_bool (even n)\<close>
  using one_or_eq [of n] by simp

lemma or_Suc_0_eq:
  \<open>n OR Suc 0 = n + of_bool (even n)\<close>
  using or_one_eq [of n] by simp

lemma Suc_0_xor_eq:
  \<open>Suc 0 XOR n = n + of_bool (even n) - of_bool (odd n)\<close>
  using one_xor_eq [of n] by simp

lemma xor_Suc_0_eq:
  \<open>n XOR Suc 0 = n + of_bool (even n) - of_bool (odd n)\<close>
  using xor_one_eq [of n] by simp

context semiring_bit_operations
begin

lemma of_nat_and_eq:
  \<open>of_nat (m AND n) = of_nat m AND of_nat n\<close>
  by (rule bit_eqI) (simp add: bit_of_nat_iff bit_and_iff Bit_Operations.bit_and_iff)

lemma of_nat_or_eq:
  \<open>of_nat (m OR n) = of_nat m OR of_nat n\<close>
  by (rule bit_eqI) (simp add: bit_of_nat_iff bit_or_iff Bit_Operations.bit_or_iff)

lemma of_nat_xor_eq:
  \<open>of_nat (m XOR n) = of_nat m XOR of_nat n\<close>
  by (rule bit_eqI) (simp add: bit_of_nat_iff bit_xor_iff Bit_Operations.bit_xor_iff)

end

context ring_bit_operations
begin

lemma of_nat_mask_eq:
  \<open>of_nat (mask n) = mask n\<close>
  by (induction n) (simp_all add: mask_Suc_double Bit_Operations.mask_Suc_double of_nat_or_eq)

end

lemma Suc_mask_eq_exp:
  \<open>Suc (mask n) = 2 ^ n\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma less_eq_mask:
  \<open>n \<le> mask n\<close>
  by (simp add: mask_eq_exp_minus_1 le_diff_conv2)
    (metis Suc_mask_eq_exp diff_Suc_1 diff_le_diff_pow diff_zero le_refl not_less_eq_eq power_0)

lemma less_mask:
  \<open>n < mask n\<close> if \<open>Suc 0 < n\<close>
proof -
  define m where \<open>m = n - 2\<close>
  with that have *: \<open>n = m + 2\<close>
    by simp
  have \<open>Suc (Suc (Suc m)) < 4 * 2 ^ m\<close>
    by (induction m) simp_all
  then have \<open>Suc (m + 2) < Suc (mask (m + 2))\<close>
    by (simp add: Suc_mask_eq_exp)
  then have \<open>m + 2 < mask (m + 2)\<close>
    by (simp add: less_le)
  with * show ?thesis
    by simp
qed


subsection \<open>Symbolic computations on numeral expressions\<close> \<^marker>\<open>contributor \<open>Andreas Lochbihler\<close>\<close>

fun and_num :: \<open>num \<Rightarrow> num \<Rightarrow> num option\<close>
where
  \<open>and_num num.One num.One = Some num.One\<close>
| \<open>and_num num.One (num.Bit0 n) = None\<close>
| \<open>and_num num.One (num.Bit1 n) = Some num.One\<close>
| \<open>and_num (num.Bit0 m) num.One = None\<close>
| \<open>and_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (and_num m n)\<close>
| \<open>and_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (and_num m n)\<close>
| \<open>and_num (num.Bit1 m) num.One = Some num.One\<close>
| \<open>and_num (num.Bit1 m) (num.Bit0 n) = map_option num.Bit0 (and_num m n)\<close>
| \<open>and_num (num.Bit1 m) (num.Bit1 n) = (case and_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))\<close>

fun and_not_num :: \<open>num \<Rightarrow> num \<Rightarrow> num option\<close>
where
  \<open>and_not_num num.One num.One = None\<close>
| \<open>and_not_num num.One (num.Bit0 n) = Some num.One\<close>
| \<open>and_not_num num.One (num.Bit1 n) = None\<close>
| \<open>and_not_num (num.Bit0 m) num.One = Some (num.Bit0 m)\<close>
| \<open>and_not_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (and_not_num m n)\<close>
| \<open>and_not_num (num.Bit0 m) (num.Bit1 n) = map_option num.Bit0 (and_not_num m n)\<close>
| \<open>and_not_num (num.Bit1 m) num.One = Some (num.Bit0 m)\<close>
| \<open>and_not_num (num.Bit1 m) (num.Bit0 n) = (case and_not_num m n of None \<Rightarrow> Some num.One | Some n' \<Rightarrow> Some (num.Bit1 n'))\<close>
| \<open>and_not_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (and_not_num m n)\<close>

fun or_num :: \<open>num \<Rightarrow> num \<Rightarrow> num\<close>
where
  \<open>or_num num.One num.One = num.One\<close>
| \<open>or_num num.One (num.Bit0 n) = num.Bit1 n\<close>
| \<open>or_num num.One (num.Bit1 n) = num.Bit1 n\<close>
| \<open>or_num (num.Bit0 m) num.One = num.Bit1 m\<close>
| \<open>or_num (num.Bit0 m) (num.Bit0 n) = num.Bit0 (or_num m n)\<close>
| \<open>or_num (num.Bit0 m) (num.Bit1 n) = num.Bit1 (or_num m n)\<close>
| \<open>or_num (num.Bit1 m) num.One = num.Bit1 m\<close>
| \<open>or_num (num.Bit1 m) (num.Bit0 n) = num.Bit1 (or_num m n)\<close>
| \<open>or_num (num.Bit1 m) (num.Bit1 n) = num.Bit1 (or_num m n)\<close>

fun or_not_num_neg :: \<open>num \<Rightarrow> num \<Rightarrow> num\<close>
where
  \<open>or_not_num_neg num.One num.One = num.One\<close>
| \<open>or_not_num_neg num.One (num.Bit0 m) = num.Bit1 m\<close>
| \<open>or_not_num_neg num.One (num.Bit1 m) = num.Bit1 m\<close>
| \<open>or_not_num_neg (num.Bit0 n) num.One = num.Bit0 num.One\<close>
| \<open>or_not_num_neg (num.Bit0 n) (num.Bit0 m) = Num.BitM (or_not_num_neg n m)\<close>
| \<open>or_not_num_neg (num.Bit0 n) (num.Bit1 m) = num.Bit0 (or_not_num_neg n m)\<close>
| \<open>or_not_num_neg (num.Bit1 n) num.One = num.One\<close>
| \<open>or_not_num_neg (num.Bit1 n) (num.Bit0 m) = Num.BitM (or_not_num_neg n m)\<close>
| \<open>or_not_num_neg (num.Bit1 n) (num.Bit1 m) = Num.BitM (or_not_num_neg n m)\<close>

fun xor_num :: \<open>num \<Rightarrow> num \<Rightarrow> num option\<close>
where
  \<open>xor_num num.One num.One = None\<close>
| \<open>xor_num num.One (num.Bit0 n) = Some (num.Bit1 n)\<close>
| \<open>xor_num num.One (num.Bit1 n) = Some (num.Bit0 n)\<close>
| \<open>xor_num (num.Bit0 m) num.One = Some (num.Bit1 m)\<close>
| \<open>xor_num (num.Bit0 m) (num.Bit0 n) = map_option num.Bit0 (xor_num m n)\<close>
| \<open>xor_num (num.Bit0 m) (num.Bit1 n) = Some (case xor_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')\<close>
| \<open>xor_num (num.Bit1 m) num.One = Some (num.Bit0 m)\<close>
| \<open>xor_num (num.Bit1 m) (num.Bit0 n) = Some (case xor_num m n of None \<Rightarrow> num.One | Some n' \<Rightarrow> num.Bit1 n')\<close>
| \<open>xor_num (num.Bit1 m) (num.Bit1 n) = map_option num.Bit0 (xor_num m n)\<close>

lemma int_numeral_and_num:
  \<open>numeral m AND numeral n = (case and_num m n of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')\<close>
  by (induction m n rule: and_num.induct) (simp_all split: option.split)

lemma and_num_eq_None_iff:
  \<open>and_num m n = None \<longleftrightarrow> numeral m AND numeral n = (0::int)\<close>
  by (simp add: int_numeral_and_num split: option.split)

lemma and_num_eq_Some_iff:
  \<open>and_num m n = Some q \<longleftrightarrow> numeral m AND numeral n = (numeral q :: int)\<close>
  by (simp add: int_numeral_and_num split: option.split)

lemma int_numeral_and_not_num:
  \<open>numeral m AND NOT (numeral n) = (case and_not_num m n of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')\<close>
  by (induction m n rule: and_not_num.induct) (simp_all add: add_One BitM_inc_eq not_int_def split: option.split)

lemma int_numeral_not_and_num:
  \<open>NOT (numeral m) AND numeral n = (case and_not_num n m of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')\<close>
  using int_numeral_and_not_num [of n m] by (simp add: ac_simps)

lemma and_not_num_eq_None_iff:
  \<open>and_not_num m n = None \<longleftrightarrow> numeral m AND NOT (numeral n) = (0::int)\<close>
  by (simp add: int_numeral_and_not_num split: option.split)

lemma and_not_num_eq_Some_iff:
  \<open>and_not_num m n = Some q \<longleftrightarrow> numeral m AND NOT (numeral n) = (numeral q :: int)\<close>
  by (simp add: int_numeral_and_not_num split: option.split)

lemma int_numeral_or_num:
  \<open>numeral m OR numeral n = (numeral (or_num m n) :: int)\<close>
  by (induction m n rule: or_num.induct) simp_all

lemma numeral_or_num_eq:
  \<open>numeral (or_num m n) = (numeral m OR numeral n :: int)\<close>
  by (simp add: int_numeral_or_num)

lemma int_numeral_or_not_num_neg:
  \<open>numeral m OR NOT (numeral n :: int) = - numeral (or_not_num_neg m n)\<close>
  by (induction m n rule: or_not_num_neg.induct) (simp_all add: add_One BitM_inc_eq not_int_def)

lemma int_numeral_not_or_num_neg:
  \<open>NOT (numeral m) OR (numeral n :: int) = - numeral (or_not_num_neg n m)\<close>
  using int_numeral_or_not_num_neg [of n m] by (simp add: ac_simps)

lemma numeral_or_not_num_eq:
  \<open>numeral (or_not_num_neg m n) = - (numeral m OR NOT (numeral n :: int))\<close>
  using int_numeral_or_not_num_neg [of m n] by simp

lemma int_numeral_xor_num:
  \<open>numeral m XOR numeral n = (case xor_num m n of None \<Rightarrow> 0 :: int | Some n' \<Rightarrow> numeral n')\<close>
  by (induction m n rule: xor_num.induct) (simp_all split: option.split)

lemma xor_num_eq_None_iff:
  \<open>xor_num m n = None \<longleftrightarrow> numeral m XOR numeral n = (0::int)\<close>
  by (simp add: int_numeral_xor_num split: option.split)

lemma xor_num_eq_Some_iff:
  \<open>xor_num m n = Some q \<longleftrightarrow> numeral m XOR numeral n = (numeral q :: int)\<close>
  by (simp add: int_numeral_xor_num split: option.split)


subsection \<open>Instances for \<^typ>\<open>integer\<close> and \<^typ>\<open>natural\<close>\<close>

unbundle integer.lifting natural.lifting

instantiation integer :: ring_bit_operations
begin

lift_definition not_integer :: \<open>integer \<Rightarrow> integer\<close>
  is not .

lift_definition and_integer :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is \<open>and\<close> .

lift_definition or_integer :: \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is or .

lift_definition xor_integer ::  \<open>integer \<Rightarrow> integer \<Rightarrow> integer\<close>
  is xor .

lift_definition mask_integer :: \<open>nat \<Rightarrow> integer\<close>
  is mask .

lift_definition set_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is set_bit .

lift_definition unset_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is unset_bit .

lift_definition flip_bit_integer :: \<open>nat \<Rightarrow> integer \<Rightarrow> integer\<close>
  is flip_bit .

instance by (standard; transfer)
  (simp_all add: minus_eq_not_minus_1 mask_eq_exp_minus_1
    bit_not_iff bit_and_iff bit_or_iff bit_xor_iff
    set_bit_def bit_unset_bit_iff flip_bit_def)

end

lemma [code]:
  \<open>mask n = 2 ^ n - (1::integer)\<close>
  by (simp add: mask_eq_exp_minus_1)

instantiation natural :: semiring_bit_operations
begin

lift_definition and_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>and\<close> .

lift_definition or_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is or .

lift_definition xor_natural ::  \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is xor .

lift_definition mask_natural :: \<open>nat \<Rightarrow> natural\<close>
  is mask .

lift_definition set_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is set_bit .

lift_definition unset_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is unset_bit .

lift_definition flip_bit_natural :: \<open>nat \<Rightarrow> natural \<Rightarrow> natural\<close>
  is flip_bit .

instance by (standard; transfer)
  (simp_all add: mask_eq_exp_minus_1
    bit_and_iff bit_or_iff bit_xor_iff
    set_bit_def bit_unset_bit_iff flip_bit_def)

end

lemma [code]:
  \<open>integer_of_natural (mask n) = mask n\<close>
  by transfer (simp add: mask_eq_exp_minus_1 of_nat_diff)

lifting_update integer.lifting
lifting_forget integer.lifting

lifting_update natural.lifting
lifting_forget natural.lifting


subsection \<open>Key ideas of bit operations\<close>

text \<open>
  When formalizing bit operations, it is tempting to represent
  bit values as explicit lists over a binary type. This however
  is a bad idea, mainly due to the inherent ambiguities in
  representation concerning repeating leading bits.

  Hence this approach avoids such explicit lists altogether
  following an algebraic path:

  \<^item> Bit values are represented by numeric types: idealized
    unbounded bit values can be represented by type \<^typ>\<open>int\<close>,
    bounded bit values by quotient types over \<^typ>\<open>int\<close>.

  \<^item> (A special case are idealized unbounded bit values ending
    in @{term [source] 0} which can be represented by type \<^typ>\<open>nat\<close> but
    only support a restricted set of operations).

  \<^item> From this idea follows that

      \<^item> multiplication by \<^term>\<open>2 :: int\<close> is a bit shift to the left and

      \<^item> division by \<^term>\<open>2 :: int\<close> is a bit shift to the right.

  \<^item> Concerning bounded bit values, iterated shifts to the left
    may result in eliminating all bits by shifting them all
    beyond the boundary.  The property \<^prop>\<open>(2 :: int) ^ n \<noteq> 0\<close>
    represents that \<^term>\<open>n\<close> is \<^emph>\<open>not\<close> beyond that boundary.

  \<^item> The projection on a single bit is then @{thm bit_iff_odd [where ?'a = int, no_vars]}.

  \<^item> This leads to the most fundamental properties of bit values:

      \<^item> Equality rule: @{thm bit_eqI [where ?'a = int, no_vars]}

      \<^item> Induction rule: @{thm bits_induct [where ?'a = int, no_vars]}

  \<^item> Typical operations are characterized as follows:

      \<^item> Singleton \<^term>\<open>n\<close>th bit: \<^term>\<open>(2 :: int) ^ n\<close>

      \<^item> Bit mask upto bit \<^term>\<open>n\<close>: @{thm mask_eq_exp_minus_1 [where ?'a = int, no_vars]}

      \<^item> Left shift: @{thm push_bit_eq_mult [where ?'a = int, no_vars]}

      \<^item> Right shift: @{thm drop_bit_eq_div [where ?'a = int, no_vars]}

      \<^item> Truncation: @{thm take_bit_eq_mod [where ?'a = int, no_vars]}

      \<^item> Negation: @{thm bit_not_iff [where ?'a = int, no_vars]}

      \<^item> And: @{thm bit_and_iff [where ?'a = int, no_vars]}

      \<^item> Or: @{thm bit_or_iff [where ?'a = int, no_vars]}

      \<^item> Xor: @{thm bit_xor_iff [where ?'a = int, no_vars]}

      \<^item> Set a single bit: @{thm set_bit_def [where ?'a = int, no_vars]}

      \<^item> Unset a single bit: @{thm unset_bit_def [where ?'a = int, no_vars]}

      \<^item> Flip a single bit: @{thm flip_bit_def [where ?'a = int, no_vars]}

      \<^item> Signed truncation, or modulus centered around \<^term>\<open>0::int\<close>: @{thm signed_take_bit_def [no_vars]}

      \<^item> Bit concatenation: @{thm concat_bit_def [no_vars]}

      \<^item> (Bounded) conversion from and to a list of bits: @{thm horner_sum_bit_eq_take_bit [where ?'a = int, no_vars]}
\<close>

code_identifier
  type_class semiring_bits \<rightharpoonup>
  (SML) Bit_Operations.semiring_bits and (OCaml) Bit_Operations.semiring_bits and (Haskell) Bit_Operations.semiring_bits and (Scala) Bit_Operations.semiring_bits
| class_relation semiring_bits < semiring_parity \<rightharpoonup>
  (SML) Bit_Operations.semiring_parity_semiring_bits and (OCaml) Bit_Operations.semiring_parity_semiring_bits and (Haskell) Bit_Operations.semiring_parity_semiring_bits and (Scala) Bit_Operations.semiring_parity_semiring_bits
| constant bit \<rightharpoonup>
  (SML) Bit_Operations.bit and (OCaml) Bit_Operations.bit and (Haskell) Bit_Operations.bit and (Scala) Bit_Operations.bit
| class_instance nat :: semiring_bits \<rightharpoonup>
  (SML) Bit_Operations.semiring_bits_nat and (OCaml) Bit_Operations.semiring_bits_nat and (Haskell) Bit_Operations.semiring_bits_nat and (Scala) Bit_Operations.semiring_bits_nat
| class_instance int :: semiring_bits \<rightharpoonup>
  (SML) Bit_Operations.semiring_bits_int and (OCaml) Bit_Operations.semiring_bits_int and (Haskell) Bit_Operations.semiring_bits_int and (Scala) Bit_Operations.semiring_bits_int
| type_class semiring_bit_shifts \<rightharpoonup>
  (SML) Bit_Operations.semiring_bit_shifts and (OCaml) Bit_Operations.semiring_bit_shifts and (Haskell) Bit_Operations.semiring_bits and (Scala) Bit_Operations.semiring_bit_shifts
| class_relation semiring_bit_shifts < semiring_bits \<rightharpoonup>
  (SML) Bit_Operations.semiring_bits_semiring_bit_shifts and (OCaml) Bit_Operations.semiring_bits_semiring_bit_shifts and (Haskell) Bit_Operations.semiring_bits_semiring_bit_shifts and (Scala) Bit_Operations.semiring_bits_semiring_bit_shifts
| constant push_bit \<rightharpoonup>
  (SML) Bit_Operations.push_bit and (OCaml) Bit_Operations.push_bit and (Haskell) Bit_Operations.push_bit and (Scala) Bit_Operations.push_bit
| constant drop_bit \<rightharpoonup>
  (SML) Bit_Operations.drop_bit and (OCaml) Bit_Operations.drop_bit and (Haskell) Bit_Operations.drop_bit and (Scala) Bit_Operations.drop_bit
| constant take_bit \<rightharpoonup>
  (SML) Bit_Operations.take_bit and (OCaml) Bit_Operations.take_bit and (Haskell) Bit_Operations.take_bit and (Scala) Bit_Operations.take_bit
| class_instance nat :: semiring_bit_shifts \<rightharpoonup>
  (SML) Bit_Operations.semiring_bit_shifts and (OCaml) Bit_Operations.semiring_bit_shifts and (Haskell) Bit_Operations.semiring_bit_shifts and (Scala) Bit_Operations.semiring_bit_shifts
| class_instance int :: semiring_bit_shifts \<rightharpoonup>
  (SML) Bit_Operations.semiring_bit_shifts and (OCaml) Bit_Operations.semiring_bit_shifts and (Haskell) Bit_Operations.semiring_bit_shifts and (Scala) Bit_Operations.semiring_bit_shifts

end
