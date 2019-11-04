(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof of concept for purely algebraically founded lists of bits\<close>

theory Bit_Operations
  imports
    "HOL-Library.Boolean_Algebra"
    Word
begin

hide_const (open) drop_bit take_bit

subsection \<open>Algebraic structures with bits\<close>

class semiring_bits = semiring_parity +
  assumes bit_split_eq: \<open>\<And>a. of_bool (odd a) + 2 * (a div 2) = a\<close>
    and bit_eq_rec: \<open>\<And>a b. a = b \<longleftrightarrow> (even a = even b) \<and> a div 2 = b div 2\<close>
    and bit_induct [case_names stable rec]:
    \<open>(\<And>a. a div 2 = a \<Longrightarrow> P a)
     \<Longrightarrow> (\<And>a b. P a \<Longrightarrow> (of_bool b + 2 * a) div 2 = a \<Longrightarrow> P (of_bool b + 2 * a))
        \<Longrightarrow> P a\<close>


subsubsection \<open>Instance \<^typ>\<open>nat\<close>\<close>

instance nat :: semiring_bits
proof
  show \<open>of_bool (odd n) + 2 * (n div 2) = n\<close>
    for n :: nat
    by simp
  show \<open>m = n \<longleftrightarrow> (even m \<longleftrightarrow> even n) \<and> m div 2 = n div 2\<close>
    for m n :: nat
    by (auto dest: odd_two_times_div_two_succ)
  show \<open>P n\<close> if stable: \<open>\<And>n. n div 2 = n \<Longrightarrow> P n\<close>
    and rec: \<open>\<And>n b. P n \<Longrightarrow> (of_bool b + 2 * n) div 2 = n \<Longrightarrow> P (of_bool b + 2 * n)\<close>
    for P and n :: nat
  proof (induction n rule: nat_bit_induct)
    case zero
    from stable [of 0] show ?case
      by simp
  next
    case (even n)
    with rec [of n False] show ?case
      by simp
  next
    case (odd n)
    with rec [of n True] show ?case
      by simp
  qed
qed


subsubsection \<open>Instance \<^typ>\<open>int\<close>\<close>

instance int :: semiring_bits
proof
  show \<open>of_bool (odd k) + 2 * (k div 2) = k\<close>
    for k :: int
    by (auto elim: oddE)
  show \<open>k = l \<longleftrightarrow> (even k \<longleftrightarrow> even l) \<and> k div 2 = l div 2\<close>
    for k l :: int
    by (auto dest: odd_two_times_div_two_succ)
  show \<open>P k\<close> if stable: \<open>\<And>k. k div 2 = k \<Longrightarrow> P k\<close>
    and rec: \<open>\<And>k b. P k \<Longrightarrow> (of_bool b + 2 * k) div 2 = k \<Longrightarrow> P (of_bool b + 2 * k)\<close>
    for P and k :: int
  proof (induction k rule: int_bit_induct)
    case zero
    from stable [of 0] show ?case
      by simp
  next
    case minus
    from stable [of \<open>- 1\<close>] show ?case
      by simp
  next
    case (even k)
    with rec [of k False] show ?case
      by (simp add: ac_simps)
  next
    case (odd k)
    with rec [of k True] show ?case
      by (simp add: ac_simps)
  qed
qed


subsubsection \<open>Instance \<^typ>\<open>'a word\<close>\<close>

instance word :: (len) semiring_bits
proof
  show \<open>of_bool (odd a) + 2 * (a div 2) = a\<close>
    for a :: \<open>'a word\<close>
    apply (cases \<open>even a\<close>; simp, transfer; cases rule: length_cases [where ?'a = 'a])
      apply auto
    apply (auto simp add: take_bit_eq_mod)
    apply (metis add.commute even_take_bit_eq len_not_eq_0 mod_mod_trivial odd_two_times_div_two_succ take_bit_eq_mod)
    done
  show \<open>a = b \<longleftrightarrow> (even a \<longleftrightarrow> even b) \<and> a div 2 = b div 2\<close>
    for a b :: \<open>'a word\<close>
    apply transfer
    apply (cases rule: length_cases [where ?'a = 'a])
     apply auto
       apply (metis even_take_bit_eq len_not_eq_0)
      apply (metis even_take_bit_eq len_not_eq_0)
    apply (metis (no_types, hide_lams) diff_add_cancel dvd_div_mult_self even_take_bit_eq mult_2_right take_bit_add take_bit_minus)
    apply (metis bit_ident drop_bit_eq_div drop_bit_half even_take_bit_eq even_two_times_div_two mod_div_trivial odd_two_times_div_two_succ take_bit_eq_mod)
    done
  show \<open>P a\<close> if stable: \<open>\<And>a. a div 2 = a \<Longrightarrow> P a\<close>
    and rec: \<open>\<And>a b. P a \<Longrightarrow> (of_bool b + 2 * a) div 2 = a \<Longrightarrow> P (of_bool b + 2 * a)\<close>
  for P and a :: \<open>'a word\<close>
  proof (induction a rule: word_bit_induct)
    case zero
    from stable [of 0] show ?case
      by simp
  next
    case (even a)
    with rec [of a False] show ?case
      using bit_word_half_eq [of a False] by (simp add: ac_simps)
  next
    case (odd a)
    with rec [of a True] show ?case
      using bit_word_half_eq [of a True] by (simp add: ac_simps)
  qed
qed


subsection \<open>Bit shifts in suitable algebraic structures\<close>

class semiring_bit_shifts = semiring_bits +
  fixes shift_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes shift_bit_eq_mult: \<open>shift_bit n a = a * 2 ^ n\<close>
  fixes drop_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  assumes drop_bit_eq_div: \<open>drop_bit n a = a div 2 ^ n\<close>
begin

definition take_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where take_bit_eq_mod: \<open>take_bit n a = a mod 2 ^ n\<close>

text \<open>
  Logically, \<^const>\<open>shift_bit\<close>,
  \<^const>\<open>drop_bit\<close> and \<^const>\<open>take_bit\<close> are just aliases; having them
  as separate operations makes proofs easier, otherwise proof automation
  would fiddle with concrete expressions \<^term>\<open>2 ^ n\<close> in a way obfuscating the basic
  algebraic relationships between those operations; having
  \<^const>\<open>push_bit\<close> and \<^const>\<open>drop_bit\<close> as definitional class operations
  takes into account that specific instances of these can be implemented
  differently wrt. code generation.
\<close>

end

subsubsection \<open>Instance \<^typ>\<open>nat\<close>\<close>

instantiation nat :: semiring_bit_shifts
begin

definition shift_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>shift_bit_nat n m = m * 2 ^ n\<close>

definition drop_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat\<close>
  where \<open>drop_bit_nat n m = m div 2 ^ n\<close>

instance proof
  show \<open>shift_bit n m = m * 2 ^ n\<close> for n m :: nat
    by (simp add: shift_bit_nat_def)
  show \<open>drop_bit n m = m div 2 ^ n\<close> for n m :: nat
    by (simp add: drop_bit_nat_def)
qed

end


subsubsection \<open>Instance \<^typ>\<open>int\<close>\<close>

instantiation int :: semiring_bit_shifts
begin

definition shift_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>shift_bit_int n k = k * 2 ^ n\<close>

definition drop_bit_int :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>drop_bit_int n k = k div 2 ^ n\<close>

instance proof
  show \<open>shift_bit n k = k * 2 ^ n\<close> for n :: nat and k :: int
    by (simp add: shift_bit_int_def)
  show \<open>drop_bit n k = k div 2 ^ n\<close> for n :: nat and k :: int
    by (simp add: drop_bit_int_def)
qed

end

lemma shift_bit_eq_push_bit:
  \<open>shift_bit = (push_bit :: nat \<Rightarrow> int \<Rightarrow> int)\<close>
  by (simp add: fun_eq_iff push_bit_eq_mult shift_bit_eq_mult)

lemma drop_bit_eq_drop_bit:
  \<open>drop_bit = (Parity.drop_bit :: nat \<Rightarrow> int \<Rightarrow> int)\<close>
  by (simp add: fun_eq_iff drop_bit_eq_div Parity.drop_bit_eq_div)

lemma take_bit_eq_take_bit:
  \<open>take_bit = (Parity.take_bit :: nat \<Rightarrow> int \<Rightarrow> int)\<close>
  by (simp add: fun_eq_iff take_bit_eq_mod Parity.take_bit_eq_mod)


subsubsection \<open>Instance \<^typ>\<open>'a word\<close>\<close>

instantiation word :: (len) semiring_bit_shifts
begin

lift_definition shift_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is shift_bit
proof -
  show \<open>Parity.take_bit LENGTH('a) (shift_bit n k) = Parity.take_bit LENGTH('a) (shift_bit n l)\<close>
    if \<open>Parity.take_bit LENGTH('a) k = Parity.take_bit LENGTH('a) l\<close> for k l :: int and n :: nat
  proof -
    from that
    have \<open>Parity.take_bit (LENGTH('a) - n) (Parity.take_bit LENGTH('a) k)
      = Parity.take_bit (LENGTH('a) - n) (Parity.take_bit LENGTH('a) l)\<close>
      by simp
    moreover have \<open>min (LENGTH('a) - n) LENGTH('a) = LENGTH('a) - n\<close>
      by simp
    ultimately show ?thesis
      by (simp add: shift_bit_eq_push_bit take_bit_push_bit)
  qed
qed

lift_definition drop_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>n. drop_bit n \<circ> take_bit LENGTH('a)\<close>
  by (simp add: take_bit_eq_mod Parity.take_bit_eq_mod)

instance proof
  show \<open>shift_bit n a = a * 2 ^ n\<close> for n :: nat and a :: "'a word"
    by transfer (simp add: shift_bit_eq_mult)
  show \<open>drop_bit n a = a div 2 ^ n\<close> for n :: nat and a :: "'a word"
  proof (cases \<open>n < LENGTH('a)\<close>)
    case True
    then show ?thesis
      by transfer
        (simp add: Parity.take_bit_eq_mod take_bit_eq_mod drop_bit_eq_div)
  next
    case False
    then obtain m where n: \<open>n = LENGTH('a) + m\<close>
      by (auto simp add: not_less dest: le_Suc_ex)
    then show ?thesis
      by transfer
        (simp add: Parity.take_bit_eq_mod take_bit_eq_mod drop_bit_eq_div power_add zdiv_zmult2_eq)
  qed
qed

end


subsection \<open>Bit operations in suitable algebraic structures\<close>

class semiring_bit_operations = semiring_bit_shifts +
  fixes "and" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "AND" 64)
    and or :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "OR"  59)
    and xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "XOR" 59)
begin

text \<open>
  We want the bitwise operations to bind slightly weaker
  than \<open>+\<close> and \<open>-\<close>, but \<open>~~\<close> to
  bind slightly stronger than \<open>*\<close>.
  For the sake of code generation
  the operations \<^const>\<open>and\<close>, \<^const>\<open>or\<close> and \<^const>\<open>xor\<close>
  are specified as definitional class operations.

\<close>

definition bit :: \<open>'a \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>bit a n \<longleftrightarrow> odd (drop_bit n a)\<close>

definition map_bit :: \<open>nat \<Rightarrow> (bool \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>map_bit n f a = take_bit n a + shift_bit n (of_bool (f (bit a n)) + drop_bit (Suc n) a)\<close>

definition set_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>set_bit n = map_bit n top\<close>

definition unset_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>unset_bit n = map_bit n bot\<close>

definition flip_bit :: \<open>nat \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  where \<open>flip_bit n = map_bit n Not\<close>

text \<open>
  The logical core are \<^const>\<open>bit\<close> and \<^const>\<open>map_bit\<close>; having 
  <^const>\<open>set_bit\<close>, \<^const>\<open>unset_bit\<close> and \<^const>\<open>flip_bit\<close> as separate
  operations allows to implement them using bit masks later.
\<close>

end

class ring_bit_operations = semiring_bit_operations + ring_parity +
  fixes not :: \<open>'a \<Rightarrow> 'a\<close>  (\<open>NOT\<close>)
  assumes boolean_algebra: \<open>boolean_algebra (AND) (OR) NOT 0 (- 1)\<close>
    and boolean_algebra_xor_eq: \<open>boolean_algebra.xor (AND) (OR) NOT = (XOR)\<close>
begin

sublocale bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
  rewrites \<open>bit.xor = (XOR)\<close>
proof -
  interpret bit: boolean_algebra \<open>(AND)\<close> \<open>(OR)\<close> NOT 0 \<open>- 1\<close>
    by (fact boolean_algebra)
  show \<open>boolean_algebra (AND) (OR) NOT 0 (- 1)\<close>
    by standard
  show \<open>boolean_algebra.xor (AND) (OR) NOT = (XOR)\<close>  
    by (fact boolean_algebra_xor_eq)
qed

text \<open>
  For the sake of code generation \<^const>\<open>not\<close> is specified as
  definitional class operation.  Note that \<^const>\<open>not\<close> has no
  sensible definition for unlimited but only positive bit strings
  (type \<^typ>\<open>nat\<close>).
\<close>

end


subsubsection \<open>Instance \<^typ>\<open>nat\<close>\<close>

locale zip_nat = single: abel_semigroup f
    for f :: "bool \<Rightarrow> bool \<Rightarrow> bool"  (infixl "\<^bold>*" 70) +
  assumes end_of_bits: "\<not> False \<^bold>* False"
begin

lemma False_P_imp:
  "False \<^bold>* True \<and> P" if "False \<^bold>* P"
  using that end_of_bits by (cases P) simp_all

function F :: "nat \<Rightarrow> nat \<Rightarrow> nat"  (infixl "\<^bold>\<times>" 70)
  where "m \<^bold>\<times> n = (if m = 0 \<and> n = 0 then 0
    else of_bool (odd m \<^bold>* odd n) + (m div 2) \<^bold>\<times> (n div 2) * 2)"
  by auto

termination
  by (relation "measure (case_prod (+))") auto

lemma zero_left_eq:
  "0 \<^bold>\<times> n = of_bool (False \<^bold>* True) * n"
  by (induction n rule: nat_bit_induct) (simp_all add: end_of_bits)

lemma zero_right_eq:
  "m \<^bold>\<times> 0 = of_bool (True \<^bold>* False) * m"
  by (induction m rule: nat_bit_induct) (simp_all add: end_of_bits)

lemma simps [simp]:
  "0 \<^bold>\<times> 0 = 0"
  "0 \<^bold>\<times> n = of_bool (False \<^bold>* True) * n"
  "m \<^bold>\<times> 0 = of_bool (True \<^bold>* False) * m"
  "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> m \<^bold>\<times> n = of_bool (odd m \<^bold>* odd n) + (m div 2) \<^bold>\<times> (n div 2) * 2"
  by (simp_all only: zero_left_eq zero_right_eq) simp

lemma rec:
  "m \<^bold>\<times> n = of_bool (odd m \<^bold>* odd n) + (m div 2) \<^bold>\<times> (n div 2) * 2"
  by (cases "m = 0 \<and> n = 0") (auto simp add: end_of_bits)

declare F.simps [simp del]

sublocale abel_semigroup F
proof
  show "m \<^bold>\<times> n \<^bold>\<times> q = m \<^bold>\<times> (n \<^bold>\<times> q)" for m n q :: nat
  proof (induction m arbitrary: n q rule: nat_bit_induct)
    case zero
    show ?case
      by simp
  next
    case (even m)
    with rec [of "2 * m"] rec [of _ q] show ?case
      by (cases "even n") (auto dest: False_P_imp)
  next
    case (odd m)
    with rec [of "Suc (2 * m)"] rec [of _ q] show ?case
      by (cases "even n"; cases "even q")
        (auto dest: False_P_imp simp add: ac_simps)
  qed
  show "m \<^bold>\<times> n = n \<^bold>\<times> m" for m n :: nat
  proof (induction m arbitrary: n rule: nat_bit_induct)
    case zero
    show ?case
      by (simp add: ac_simps)
  next
    case (even m)
    with rec [of "2 * m" n] rec [of n "2 * m"] show ?case
      by (simp add: ac_simps)
  next
    case (odd m)
    with rec [of "Suc (2 * m)" n] rec [of n "Suc (2 * m)"] show ?case
      by (simp add: ac_simps)
  qed
qed

lemma self [simp]:
  "n \<^bold>\<times> n = of_bool (True \<^bold>* True) * n"
  by (induction n rule: nat_bit_induct) (simp_all add: end_of_bits)

lemma even_iff [simp]:
  "even (m \<^bold>\<times> n) \<longleftrightarrow> \<not> (odd m \<^bold>* odd n)"
proof (induction m arbitrary: n rule: nat_bit_induct)
  case zero
  show ?case
    by (cases "even n") (simp_all add: end_of_bits)
next
  case (even m)
  then show ?case
    by (simp add: rec [of "2 * m"])
next
  case (odd m)
  then show ?case
    by (simp add: rec [of "Suc (2 * m)"])
qed

end

instantiation nat :: semiring_bit_operations
begin

global_interpretation and_nat: zip_nat "(\<and>)"
  defines and_nat = and_nat.F
  by standard auto

global_interpretation and_nat: semilattice "(AND) :: nat \<Rightarrow> nat \<Rightarrow> nat"
proof (rule semilattice.intro, fact and_nat.abel_semigroup_axioms, standard)
  show "n AND n = n" for n :: nat
    by (simp add: and_nat.self)
qed

declare and_nat.simps [simp] \<comment> \<open>inconsistent declaration handling by
  \<open>global_interpretation\<close> in \<open>instantiation\<close>\<close>

lemma zero_nat_and_eq [simp]:
  "0 AND n = 0" for n :: nat
  by simp

lemma and_zero_nat_eq [simp]:
  "n AND 0 = 0" for n :: nat
  by simp

global_interpretation or_nat: zip_nat "(\<or>)"
  defines or_nat = or_nat.F
  by standard auto

global_interpretation or_nat: semilattice "(OR) :: nat \<Rightarrow> nat \<Rightarrow> nat"
proof (rule semilattice.intro, fact or_nat.abel_semigroup_axioms, standard)
  show "n OR n = n" for n :: nat
    by (simp add: or_nat.self)
qed

declare or_nat.simps [simp] \<comment> \<open>inconsistent declaration handling by
  \<open>global_interpretation\<close> in \<open>instantiation\<close>\<close>

lemma zero_nat_or_eq [simp]:
  "0 OR n = n" for n :: nat
  by simp

lemma or_zero_nat_eq [simp]:
  "n OR 0 = n" for n :: nat
  by simp

global_interpretation xor_nat: zip_nat "(\<noteq>)"
  defines xor_nat = xor_nat.F
  by standard auto

declare xor_nat.simps [simp] \<comment> \<open>inconsistent declaration handling by
  \<open>global_interpretation\<close> in \<open>instantiation\<close>\<close>

lemma zero_nat_xor_eq [simp]:
  "0 XOR n = n" for n :: nat
  by simp

lemma xor_zero_nat_eq [simp]:
  "n XOR 0 = n" for n :: nat
  by simp

instance ..

end

global_interpretation or_nat: semilattice_neutr "(OR)" "0 :: nat"
  by standard simp

global_interpretation xor_nat: comm_monoid "(XOR)" "0 :: nat"
  by standard simp

lemma Suc_0_and_eq [simp]:
  "Suc 0 AND n = n mod 2"
  by (cases n) auto

lemma and_Suc_0_eq [simp]:
  "n AND Suc 0 = n mod 2"
  using Suc_0_and_eq [of n] by (simp add: ac_simps)

lemma Suc_0_or_eq [simp]:
  "Suc 0 OR n = n + of_bool (even n)"
  by (cases n) (simp_all add: ac_simps)

lemma or_Suc_0_eq [simp]:
  "n OR Suc 0 = n + of_bool (even n)"
  using Suc_0_or_eq [of n] by (simp add: ac_simps)

lemma Suc_0_xor_eq [simp]:
  "Suc 0 XOR n = n + of_bool (even n) - of_bool (odd n)"
  by (cases n) (simp_all add: ac_simps)

lemma xor_Suc_0_eq [simp]:
  "n XOR Suc 0 = n + of_bool (even n) - of_bool (odd n)"
  using Suc_0_xor_eq [of n] by (simp add: ac_simps)


subsubsection \<open>Instance \<^typ>\<open>int\<close>\<close>

abbreviation (input) complement :: "int \<Rightarrow> int"
  where "complement k \<equiv> - k - 1"

lemma complement_half:
  "complement (k * 2) div 2 = complement k"
  by simp

lemma complement_div_2:
  "complement (k div 2) = complement k div 2"
  by linarith

locale zip_int = single: abel_semigroup f
  for f :: "bool \<Rightarrow> bool \<Rightarrow> bool"  (infixl "\<^bold>*" 70)
begin
 
lemma False_False_imp_True_True:
  "True \<^bold>* True" if "False \<^bold>* False"
proof (rule ccontr)
  assume "\<not> True \<^bold>* True"
  with that show False
    using single.assoc [of False True True]
    by (cases "False \<^bold>* True") simp_all
qed

function F :: "int \<Rightarrow> int \<Rightarrow> int"  (infixl "\<^bold>\<times>" 70)
  where "k \<^bold>\<times> l = (if k \<in> {0, - 1} \<and> l \<in> {0, - 1}
    then - of_bool (odd k \<^bold>* odd l)
    else of_bool (odd k \<^bold>* odd l) + (k div 2) \<^bold>\<times> (l div 2) * 2)"
  by auto

termination
  by (relation "measure (\<lambda>(k, l). nat (\<bar>k\<bar> + \<bar>l\<bar>))") auto

lemma zero_left_eq:
  "0 \<^bold>\<times> l = (case (False \<^bold>* False, False \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> l
     | (True, False) \<Rightarrow> complement l
     | (True, True) \<Rightarrow> - 1)"
  by (induction l rule: int_bit_induct)
   (simp_all split: bool.split) 

lemma minus_left_eq:
  "- 1 \<^bold>\<times> l = (case (True \<^bold>* False, True \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> l
     | (True, False) \<Rightarrow> complement l
     | (True, True) \<Rightarrow> - 1)"
  by (induction l rule: int_bit_induct)
   (simp_all split: bool.split) 

lemma zero_right_eq:
  "k \<^bold>\<times> 0 = (case (False \<^bold>* False, False \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> k
     | (True, False) \<Rightarrow> complement k
     | (True, True) \<Rightarrow> - 1)"
  by (induction k rule: int_bit_induct)
    (simp_all add: ac_simps split: bool.split)

lemma minus_right_eq:
  "k \<^bold>\<times> - 1 = (case (True \<^bold>* False, True \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> k
     | (True, False) \<Rightarrow> complement k
     | (True, True) \<Rightarrow> - 1)"
  by (induction k rule: int_bit_induct)
    (simp_all add: ac_simps split: bool.split)

lemma simps [simp]:
  "0 \<^bold>\<times> 0 = - of_bool (False \<^bold>* False)"
  "- 1 \<^bold>\<times> 0 = - of_bool (True \<^bold>* False)"
  "0 \<^bold>\<times> - 1 = - of_bool (False \<^bold>* True)"
  "- 1 \<^bold>\<times> - 1 = - of_bool (True \<^bold>* True)"
  "0 \<^bold>\<times> l = (case (False \<^bold>* False, False \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> l
     | (True, False) \<Rightarrow> complement l
     | (True, True) \<Rightarrow> - 1)"
  "- 1 \<^bold>\<times> l = (case (True \<^bold>* False, True \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> l
     | (True, False) \<Rightarrow> complement l
     | (True, True) \<Rightarrow> - 1)"
  "k \<^bold>\<times> 0 = (case (False \<^bold>* False, False \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> k
     | (True, False) \<Rightarrow> complement k
     | (True, True) \<Rightarrow> - 1)"
  "k \<^bold>\<times> - 1 = (case (True \<^bold>* False, True \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> k
     | (True, False) \<Rightarrow> complement k
     | (True, True) \<Rightarrow> - 1)"
  "k \<noteq> 0 \<Longrightarrow> k \<noteq> - 1 \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> l \<noteq> - 1
    \<Longrightarrow> k \<^bold>\<times> l = of_bool (odd k \<^bold>* odd l) + (k div 2) \<^bold>\<times> (l div 2) * 2"
  by simp_all[4] (simp_all only: zero_left_eq minus_left_eq zero_right_eq minus_right_eq, simp)

declare F.simps [simp del]

lemma rec:
  "k \<^bold>\<times> l = of_bool (odd k \<^bold>* odd l) + (k div 2) \<^bold>\<times> (l div 2) * 2"
  by (cases "k \<in> {0, - 1} \<and> l \<in> {0, - 1}") (auto simp add: ac_simps F.simps [of k l] split: bool.split)

sublocale abel_semigroup F
proof
  show "k \<^bold>\<times> l \<^bold>\<times> r = k \<^bold>\<times> (l \<^bold>\<times> r)" for k l r :: int
  proof (induction k arbitrary: l r rule: int_bit_induct)
    case zero
    have "complement l \<^bold>\<times> r = complement (l \<^bold>\<times> r)" if "False \<^bold>* False" "\<not> False \<^bold>* True"
    proof (induction l arbitrary: r rule: int_bit_induct)
      case zero
      from that show ?case
        by (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
    next
      case minus
      from that show ?case
        by (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
    next
      case (even l)
      with that rec [of _ r] show ?case
        by (cases "even r")
          (auto simp add: complement_half ac_simps False_False_imp_True_True split: bool.splits)
    next
      case (odd l)
      moreover have "- l - 1 = - 1 - l"
        by simp
      ultimately show ?case
        using that rec [of _ r]
        by (cases "even r")
          (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
    qed
    then show ?case
      by (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
  next
    case minus
    have "complement l \<^bold>\<times> r = complement (l \<^bold>\<times> r)" if "\<not> True \<^bold>* True" "False \<^bold>* True"
    proof (induction l arbitrary: r rule: int_bit_induct)
      case zero
      from that show ?case
        by (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
    next
      case minus
      from that show ?case
        by (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
    next
      case (even l)
      with that rec [of _ r] show ?case
        by (cases "even r")
          (auto simp add: complement_half ac_simps False_False_imp_True_True split: bool.splits)
    next
      case (odd l)
      moreover have "- l - 1 = - 1 - l"
        by simp
      ultimately show ?case
        using that rec [of _ r]
        by (cases "even r")
          (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
    qed
    then show ?case
      by (auto simp add: ac_simps False_False_imp_True_True split: bool.splits)
  next
    case (even k)
    with rec [of "k * 2"] rec [of _ r] show ?case
      by (cases "even r"; cases "even l") (auto simp add: ac_simps False_False_imp_True_True)
  next
    case (odd k)
    with rec [of "1 + k * 2"] rec [of _ r] show ?case
      by (cases "even r"; cases "even l") (auto simp add: ac_simps False_False_imp_True_True)
  qed
  show "k \<^bold>\<times> l = l \<^bold>\<times> k" for k l :: int
  proof (induction k arbitrary: l rule: int_bit_induct)
    case zero
    show ?case
      by simp
  next
    case minus
    show ?case
      by simp
  next
    case (even k)
    with rec [of "k * 2" l] rec [of l "k * 2"] show ?case
      by (simp add: ac_simps)
  next
    case (odd k)
    with rec [of "k * 2 + 1" l] rec [of l "k * 2 + 1"] show ?case
      by (simp add: ac_simps)
  qed
qed

lemma self [simp]:
  "k \<^bold>\<times> k = (case (False \<^bold>* False, True \<^bold>* True)
    of (False, False) \<Rightarrow> 0
     | (False, True) \<Rightarrow> k
     | (True, True) \<Rightarrow> - 1)"
  by (induction k rule: int_bit_induct) (auto simp add: False_False_imp_True_True split: bool.split)

lemma even_iff [simp]:
  "even (k \<^bold>\<times> l) \<longleftrightarrow> \<not> (odd k \<^bold>* odd l)"
proof (induction k arbitrary: l rule: int_bit_induct)
  case zero
  show ?case
    by (cases "even l") (simp_all split: bool.splits)
next
  case minus
  show ?case
    by (cases "even l") (simp_all split: bool.splits)
next
  case (even k)
  then show ?case
    by (simp add: rec [of "k * 2"])
next
  case (odd k)
  then show ?case
    by (simp add: rec [of "1 + k * 2"])
qed

end

instantiation int :: ring_bit_operations
begin

definition not_int :: "int \<Rightarrow> int"
  where "not_int = complement"

global_interpretation and_int: zip_int "(\<and>)"
  defines and_int = and_int.F
  by standard

declare and_int.simps [simp] \<comment> \<open>inconsistent declaration handling by
  \<open>global_interpretation\<close> in \<open>instantiation\<close>\<close>

global_interpretation and_int: semilattice "(AND) :: int \<Rightarrow> int \<Rightarrow> int"
proof (rule semilattice.intro, fact and_int.abel_semigroup_axioms, standard)
  show "k AND k = k" for k :: int
    by (simp add: and_int.self)
qed

lemma zero_int_and_eq [simp]:
  "0 AND k = 0" for k :: int
  by simp

lemma and_zero_int_eq [simp]:
  "k AND 0 = 0" for k :: int
  by simp

lemma minus_int_and_eq [simp]:
  "- 1 AND k = k" for k :: int
  by simp

lemma and_minus_int_eq [simp]:
  "k AND - 1 = k" for k :: int
  by simp

global_interpretation or_int: zip_int "(\<or>)"
  defines or_int = or_int.F
  by standard

declare or_int.simps [simp] \<comment> \<open>inconsistent declaration handling by
  \<open>global_interpretation\<close> in \<open>instantiation\<close>\<close>

global_interpretation or_int: semilattice "(OR) :: int \<Rightarrow> int \<Rightarrow> int"
proof (rule semilattice.intro, fact or_int.abel_semigroup_axioms, standard)
  show "k OR k = k" for k :: int
    by (simp add: or_int.self)
qed

lemma zero_int_or_eq [simp]:
  "0 OR k = k" for k :: int
  by simp

lemma and_zero_or_eq [simp]:
  "k OR 0 = k" for k :: int
  by simp

lemma minus_int_or_eq [simp]:
  "- 1 OR k = - 1" for k :: int
  by simp

lemma or_minus_int_eq [simp]:
  "k OR - 1 = - 1" for k :: int
  by simp

global_interpretation xor_int: zip_int "(\<noteq>)"
  defines xor_int = xor_int.F
  by standard

declare xor_int.simps [simp] \<comment> \<open>inconsistent declaration handling by
  \<open>global_interpretation\<close> in \<open>instantiation\<close>\<close>

lemma zero_int_xor_eq [simp]:
  "0 XOR k = k" for k :: int
  by simp

lemma and_zero_xor_eq [simp]:
  "k XOR 0 = k" for k :: int
  by simp

lemma minus_int_xor_eq [simp]:
  "- 1 XOR k = complement k" for k :: int
  by simp

lemma xor_minus_int_eq [simp]:
  "k XOR - 1 = complement k" for k :: int
  by simp

lemma not_div_2:
  "NOT k div 2 = NOT (k div 2)"
  for k :: int
  by (simp add: complement_div_2 not_int_def)

lemma not_int_simps [simp]:
  "NOT 0 = (- 1 :: int)"
  "NOT (- 1) = (0 :: int)"
  "k \<noteq> 0 \<Longrightarrow> k \<noteq> - 1 \<Longrightarrow> NOT k = of_bool (even k) + 2 * NOT (k div 2)" for k :: int
  by (auto simp add: not_int_def elim: oddE)

lemma not_one_int [simp]:
  "NOT 1 = (- 2 :: int)"
  by simp

lemma even_not_iff [simp]:
  "even (NOT k) \<longleftrightarrow> odd k"
  for k :: int
  by (simp add: not_int_def)

instance proof
  interpret bit_int: boolean_algebra "(AND)" "(OR)" NOT 0 "- 1 :: int"
  proof
    show "k AND (l OR r) = k AND l OR k AND r"
      for k l r :: int
    proof (induction k arbitrary: l r rule: int_bit_induct)
      case zero
      show ?case
        by simp
    next
      case minus
      show ?case
        by simp
    next
      case (even k)
      then show ?case by (simp add: and_int.rec [of "k * 2"]
        or_int.rec [of "(k AND l div 2) * 2"] or_int.rec [of l])
    next
      case (odd k)
      then show ?case by (simp add: and_int.rec [of "1 + k * 2"]
        or_int.rec [of "(k AND l div 2) * 2"] or_int.rec [of "1 + (k AND l div 2) * 2"] or_int.rec [of l])
    qed
    show "k OR l AND r = (k OR l) AND (k OR r)"
      for k l r :: int
    proof (induction k arbitrary: l r rule: int_bit_induct)
      case zero
      then show ?case
        by simp
    next
      case minus
      then show ?case
        by simp
    next
      case (even k)
      then show ?case by (simp add: or_int.rec [of "k * 2"]
        and_int.rec [of "(k OR l div 2) * 2"] and_int.rec [of "1 + (k OR l div 2) * 2"] and_int.rec [of l])
    next
      case (odd k)
      then show ?case by (simp add: or_int.rec [of "1 + k * 2"]
        and_int.rec [of "1 + (k OR l div 2) * 2"] and_int.rec [of l])
    qed
    show "k AND NOT k = 0" for k :: int
      by (induction k rule: int_bit_induct)
        (simp_all add: not_int_def complement_half minus_diff_commute [of 1])
    show "k OR NOT k = - 1" for k :: int
      by (induction k rule: int_bit_induct)
        (simp_all add: not_int_def complement_half minus_diff_commute [of 1])
  qed (simp_all add: and_int.assoc or_int.assoc,
    simp_all add: and_int.commute or_int.commute)
  show "boolean_algebra (AND) (OR) NOT 0 (- 1 :: int)"
    by (fact bit_int.boolean_algebra_axioms)
  show "bit_int.xor = ((XOR) :: int \<Rightarrow> _)"
  proof (rule ext)+
    fix k l :: int
    have "k XOR l = k AND NOT l OR NOT k AND l"
    proof (induction k arbitrary: l rule: int_bit_induct)
      case zero
      show ?case
        by simp
    next
      case minus
      show ?case
        by (simp add: not_int_def)
    next
      case (even k)
      then show ?case
        by (simp add: xor_int.rec [of "k * 2"] and_int.rec [of "k * 2"]
          or_int.rec [of _ "1 + 2 * NOT k AND l"] not_div_2)
          (simp add: and_int.rec [of _ l])
    next
      case (odd k)
      then show ?case
        by (simp add: xor_int.rec [of "1 + k * 2"] and_int.rec [of "1 + k * 2"]
          or_int.rec [of _ "2 * NOT k AND l"] not_div_2)
          (simp add: and_int.rec [of _ l])
    qed
    then show "bit_int.xor k l = k XOR l"
      by (simp add: bit_int.xor_def)
  qed
qed

end

lemma one_and_int_eq [simp]:
  "1 AND k = k mod 2" for k :: int
  using and_int.rec [of 1] by (simp add: mod2_eq_if)

lemma and_one_int_eq [simp]:
  "k AND 1 = k mod 2" for k :: int
  using one_and_int_eq [of 1] by (simp add: ac_simps)

lemma one_or_int_eq [simp]:
  "1 OR k = k + of_bool (even k)" for k :: int
  using or_int.rec [of 1] by (auto elim: oddE)

lemma or_one_int_eq [simp]:
  "k OR 1 = k + of_bool (even k)" for k :: int
  using one_or_int_eq [of k] by (simp add: ac_simps)

lemma one_xor_int_eq [simp]:
  "1 XOR k = k + of_bool (even k) - of_bool (odd k)" for k :: int
  using xor_int.rec [of 1] by (auto elim: oddE)

lemma xor_one_int_eq [simp]:
  "k XOR 1 = k + of_bool (even k) - of_bool (odd k)" for k :: int
  using one_xor_int_eq [of k] by (simp add: ac_simps)

lemma take_bit_complement_iff:
  "Parity.take_bit n (complement k) = Parity.take_bit n (complement l) \<longleftrightarrow> Parity.take_bit n k = Parity.take_bit n l"
  for k l :: int
  by (simp add: Parity.take_bit_eq_mod mod_eq_dvd_iff dvd_diff_commute)

lemma take_bit_not_iff:
  "Parity.take_bit n (NOT k) = Parity.take_bit n (NOT l) \<longleftrightarrow> Parity.take_bit n k = Parity.take_bit n l"
  for k l :: int
  by (simp add: not_int_def take_bit_complement_iff)

lemma take_bit_and [simp]:
  "Parity.take_bit n (k AND l) = Parity.take_bit n k AND Parity.take_bit n l"
  for k l :: int
  apply (induction n arbitrary: k l)
   apply simp
  apply (subst and_int.rec)
  apply (subst (2) and_int.rec)
  apply simp
  done

lemma take_bit_or [simp]:
  "Parity.take_bit n (k OR l) = Parity.take_bit n k OR Parity.take_bit n l"
  for k l :: int
  apply (induction n arbitrary: k l)
   apply simp
  apply (subst or_int.rec)
  apply (subst (2) or_int.rec)
  apply simp
  done

lemma take_bit_xor [simp]:
  "Parity.take_bit n (k XOR l) = Parity.take_bit n k XOR Parity.take_bit n l"
  for k l :: int
  apply (induction n arbitrary: k l)
   apply simp
  apply (subst xor_int.rec)
  apply (subst (2) xor_int.rec)
  apply simp
  done


subsubsection \<open>Instance \<^typ>\<open>'a word\<close>\<close>

instantiation word :: (len) ring_bit_operations
begin

lift_definition not_word :: "'a word \<Rightarrow> 'a word"
  is not
  by (simp add: take_bit_not_iff)

lift_definition and_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "and"
  by simp

lift_definition or_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is or
  by simp

lift_definition xor_word ::  "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is xor
  by simp

instance proof
  interpret bit_word: boolean_algebra "(AND)" "(OR)" NOT 0 "- 1 :: 'a word"
  proof
    show "a AND (b OR c) = a AND b OR a AND c"
      for a b c :: "'a word"
      by transfer (simp add: bit.conj_disj_distrib)
    show "a OR b AND c = (a OR b) AND (a OR c)"
      for a b c :: "'a word"
      by transfer (simp add: bit.disj_conj_distrib)
  qed (transfer; simp add: ac_simps)+
  show "boolean_algebra (AND) (OR) NOT 0 (- 1 :: 'a word)"
    by (fact bit_word.boolean_algebra_axioms)
  show "bit_word.xor = ((XOR) :: 'a word \<Rightarrow> _)"
  proof (rule ext)+
    fix a b :: "'a word"
    have "a XOR b = a AND NOT b OR NOT a AND b"
      by transfer (simp add: bit.xor_def)
    then show "bit_word.xor a b = a XOR b"
      by (simp add: bit_word.xor_def)
  qed
qed

end

end
