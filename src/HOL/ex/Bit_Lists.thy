(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof(s) of concept for algebraically founded lists of bits\<close>

theory Bit_Lists
  imports Main
begin

subsection \<open>Bit representations\<close>

subsubsection \<open>Mere syntactic bit representation\<close>

class bit_representation =
  fixes bits_of :: "'a \<Rightarrow> bool list"
    and of_bits :: "bool list \<Rightarrow> 'a"
  assumes of_bits_of [simp]: "of_bits (bits_of a) = a"


subsubsection \<open>Algebraic bit representation\<close>

context comm_semiring_1
begin
 
primrec radix_value :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a"
  where "radix_value f b [] = 0"
  | "radix_value f b (a # as) = f a + radix_value f b as * b"

abbreviation (input) unsigned_of_bits :: "bool list \<Rightarrow> 'a"
  where "unsigned_of_bits \<equiv> radix_value of_bool 2"

lemma unsigned_of_bits_replicate_False [simp]:
  "unsigned_of_bits (replicate n False) = 0"
  by (induction n) simp_all

end

context unique_euclidean_semiring_with_nat
begin

lemma unsigned_of_bits_append [simp]:
  "unsigned_of_bits (bs @ cs) = unsigned_of_bits bs
    + push_bit (length bs) (unsigned_of_bits cs)"
  by (induction bs) (simp_all add: push_bit_double,
    simp_all add: algebra_simps)

lemma unsigned_of_bits_take [simp]:
  "unsigned_of_bits (take n bs) = take_bit n (unsigned_of_bits bs)"
proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
    by (cases n) (simp_all add: ac_simps)
qed

lemma unsigned_of_bits_drop [simp]:
  "unsigned_of_bits (drop n bs) = drop_bit n (unsigned_of_bits bs)"
proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
    by (cases n) simp_all
qed

end


subsubsection \<open>Instances\<close>

text \<open>Unclear whether a \<^typ>\<open>bool\<close> instantiation is needed or not\<close>

instantiation nat :: bit_representation
begin

fun bits_of_nat :: "nat \<Rightarrow> bool list"
  where "bits_of (n::nat) =
    (if n = 0 then [] else odd n # bits_of (n div 2))"

lemma bits_of_nat_simps [simp]:
  "bits_of (0::nat) = []"
  "n > 0 \<Longrightarrow> bits_of n = odd n # bits_of (n div 2)" for n :: nat
  by simp_all

declare bits_of_nat.simps [simp del]

definition of_bits_nat :: "bool list \<Rightarrow> nat"
  where [simp]: "of_bits_nat = unsigned_of_bits"
  \<comment> \<open>remove simp\<close>

instance proof
  show "of_bits (bits_of n) = n" for n :: nat
    by (induction n rule: nat_bit_induct) simp_all
qed

end

lemma bits_of_Suc_0 [simp]:
  "bits_of (Suc 0) = [True]"
  by simp

lemma bits_of_1_nat [simp]:
  "bits_of (1 :: nat) = [True]"
  by simp

lemma bits_of_nat_numeral_simps [simp]:
  "bits_of (numeral Num.One :: nat) = [True]" (is ?One)
  "bits_of (numeral (Num.Bit0 n) :: nat) = False # bits_of (numeral n :: nat)" (is ?Bit0)
  "bits_of (numeral (Num.Bit1 n) :: nat) = True # bits_of (numeral n :: nat)" (is ?Bit1)
proof -
  show ?One
    by simp
  define m :: nat where "m = numeral n"
  then have "m > 0" and *: "numeral n = m" "numeral (Num.Bit0 n) = 2 * m" "numeral (Num.Bit1 n) = Suc (2 * m)"
    by simp_all
  from \<open>m > 0\<close> show ?Bit0 ?Bit1
    by (simp_all add: *)
qed

lemma unsigned_of_bits_of_nat [simp]:
  "unsigned_of_bits (bits_of n) = n" for n :: nat
  using of_bits_of [of n] by simp

instantiation int :: bit_representation
begin

fun bits_of_int :: "int \<Rightarrow> bool list"
  where "bits_of_int k = odd k #
    (if k = 0 \<or> k = - 1 then [] else bits_of_int (k div 2))"

lemma bits_of_int_simps [simp]:
  "bits_of (0 :: int) = [False]"
  "bits_of (- 1 :: int) = [True]"
  "k \<noteq> 0 \<Longrightarrow> k \<noteq> - 1 \<Longrightarrow> bits_of k = odd k # bits_of (k div 2)" for k :: int
  by simp_all

lemma bits_of_not_Nil [simp]:
  "bits_of k \<noteq> []" for k :: int
  by simp

declare bits_of_int.simps [simp del]

definition of_bits_int :: "bool list \<Rightarrow> int"
  where "of_bits_int bs = (if bs = [] \<or> \<not> last bs then unsigned_of_bits bs
    else unsigned_of_bits bs - 2 ^ length bs)"

lemma of_bits_int_simps [simp]:
  "of_bits [] = (0 :: int)"
  "of_bits [False] = (0 :: int)"
  "of_bits [True] = (- 1 :: int)"
  "of_bits (bs @ [b]) = (unsigned_of_bits bs :: int) - (2 ^ length bs) * of_bool b"
  "of_bits (False # bs) = 2 * (of_bits bs :: int)"
  "bs \<noteq> [] \<Longrightarrow> of_bits (True # bs) = 1 + 2 * (of_bits bs :: int)"
  by (simp_all add: of_bits_int_def push_bit_of_1)

instance proof
  show "of_bits (bits_of k) = k" for k :: int
    by (induction k rule: int_bit_induct) simp_all
qed

lemma bits_of_1_int [simp]:
  "bits_of (1 :: int) = [True, False]"
  by simp

lemma bits_of_int_numeral_simps [simp]:
  "bits_of (numeral Num.One :: int) = [True, False]" (is ?One)
  "bits_of (numeral (Num.Bit0 n) :: int) = False # bits_of (numeral n :: int)" (is ?Bit0)
  "bits_of (numeral (Num.Bit1 n) :: int) = True # bits_of (numeral n :: int)" (is ?Bit1)
  "bits_of (- numeral (Num.Bit0 n) :: int) = False # bits_of (- numeral n :: int)" (is ?nBit0)
  "bits_of (- numeral (Num.Bit1 n) :: int) = True # bits_of (- numeral (Num.inc n) :: int)" (is ?nBit1)
proof -
  show ?One
    by simp
  define k :: int where "k = numeral n"
  then have "k > 0" and *: "numeral n = k" "numeral (Num.Bit0 n) = 2 * k" "numeral (Num.Bit1 n) = 2 * k + 1"
    "numeral (Num.inc n) = k + 1"
    by (simp_all add: add_One)
  have "- (2 * k) div 2 = - k" "(- (2 * k) - 1) div 2 = - k - 1"
    by simp_all
  with \<open>k > 0\<close> show ?Bit0 ?Bit1 ?nBit0 ?nBit1
    by (simp_all add: *)
qed

lemma of_bits_append [simp]:
  "of_bits (bs @ cs) = of_bits bs + push_bit (length bs) (of_bits cs :: int)"
    if "bs \<noteq> []" "\<not> last bs"
using that proof (induction bs rule: list_nonempty_induct)
  case (single b)
  then show ?case
    by simp
next
  case (cons b bs)
  then show ?case
    by (cases b) (simp_all add: push_bit_double)
qed

lemma of_bits_replicate_False [simp]:
  "of_bits (replicate n False) = (0 :: int)"
  by (auto simp add: of_bits_int_def)

lemma of_bits_drop [simp]:
  "of_bits (drop n bs) = drop_bit n (of_bits bs :: int)"
    if "n < length bs"
using that proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc n)
    with Cons.prems have "bs \<noteq> []"
      by auto
    with Suc Cons.IH [of n] Cons.prems show ?thesis
      by (cases b) simp_all
  qed
qed

end


subsection \<open>Syntactic bit operations\<close>

class bit_operations = bit_representation +
  fixes not :: "'a \<Rightarrow> 'a"  ("NOT _" [70] 71)
    and "and" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "AND" 64)
    and or :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "OR"  59)
    and xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr "XOR" 59)
    and shift_left :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  (infixl "<<" 55)
    and shift_right :: "'a \<Rightarrow> nat \<Rightarrow> 'a"  (infixl ">>" 55)
  assumes not_eq: "not = of_bits \<circ> map Not \<circ> bits_of"
    and and_eq: "length bs = length cs \<Longrightarrow>
      of_bits bs AND of_bits cs = of_bits (map2 (\<and>) bs cs)"
    and semilattice_and: "semilattice (AND)"
    and or_eq: "length bs = length cs \<Longrightarrow>
      of_bits bs OR of_bits cs = of_bits (map2 (\<or>) bs cs)"
    and semilattice_or: "semilattice (OR)"
    and xor_eq: "length bs = length cs \<Longrightarrow>
      of_bits bs XOR of_bits cs = of_bits (map2 (\<noteq>) bs cs)"
    and abel_semigroup_xor: "abel_semigroup (XOR)"
    and shift_right_eq: "a << n = of_bits (replicate n False @ bits_of a)"
    and shift_left_eq: "n < length (bits_of a) \<Longrightarrow> a >> n = of_bits (drop n (bits_of a))"
begin

text \<open>
  We want the bitwise operations to bind slightly weaker
  than \<open>+\<close> and \<open>-\<close>, but \<open>~~\<close> to
  bind slightly stronger than \<open>*\<close>.
\<close>

sublocale "and": semilattice "(AND)"
  by (fact semilattice_and)

sublocale or: semilattice "(OR)"
  by (fact semilattice_or)

sublocale xor: abel_semigroup "(XOR)"
  by (fact abel_semigroup_xor)

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

lemma of_bits:
  "of_bits bs \<^bold>\<times> of_bits cs = (of_bits (map2 (\<^bold>*) bs cs) :: nat)"
    if "length bs = length cs" for bs cs
using that proof (induction bs cs rule: list_induct2)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs c cs)
  then show ?case
    by (cases "of_bits bs = (0::nat) \<or> of_bits cs = (0::nat)")
      (auto simp add: ac_simps end_of_bits rec [of "Suc 0"])
qed

end

instantiation nat :: bit_operations
begin

definition not_nat :: "nat \<Rightarrow> nat"
  where "not_nat = of_bits \<circ> map Not \<circ> bits_of"

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

definition shift_left_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where [simp]: "m << n = push_bit n m" for m :: nat

definition shift_right_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where [simp]: "m >> n = drop_bit n m" for m :: nat

instance proof
  show "semilattice ((AND) :: nat \<Rightarrow> _)"
    by (fact and_nat.semilattice_axioms)
  show "semilattice ((OR):: nat \<Rightarrow> _)"
    by (fact or_nat.semilattice_axioms)
  show "abel_semigroup ((XOR):: nat \<Rightarrow> _)"
    by (fact xor_nat.abel_semigroup_axioms)
  show "(not :: nat \<Rightarrow> _) = of_bits \<circ> map Not \<circ> bits_of"
    by (fact not_nat_def)
  show "of_bits bs AND of_bits cs = (of_bits (map2 (\<and>) bs cs) :: nat)"
    if "length bs = length cs" for bs cs
    using that by (fact and_nat.of_bits)
  show "of_bits bs OR of_bits cs = (of_bits (map2 (\<or>) bs cs) :: nat)"
    if "length bs = length cs" for bs cs
    using that by (fact or_nat.of_bits)
  show "of_bits bs XOR of_bits cs = (of_bits (map2 (\<noteq>) bs cs) :: nat)"
    if "length bs = length cs" for bs cs
    using that by (fact xor_nat.of_bits)
  show "m << n = of_bits (replicate n False @ bits_of m)"
    for m n :: nat
    by simp
  show "m >> n = of_bits (drop n (bits_of m))"
    for m n :: nat
    by simp
qed

end

global_interpretation or_nat: semilattice_neutr "(OR)" "0 :: nat"
  by standard simp

global_interpretation xor_nat: comm_monoid "(XOR)" "0 :: nat"
  by standard simp

lemma not_nat_simps [simp]:
  "NOT 0 = (0::nat)"
  "n > 0 \<Longrightarrow> NOT n = of_bool (even n) + 2 * NOT (n div 2)" for n :: nat
  by (simp_all add: not_eq)

lemma not_1_nat [simp]:
  "NOT 1 = (0::nat)"
  by simp

lemma not_Suc_0 [simp]:
  "NOT (Suc 0) = (0::nat)"
  by simp

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

lemma of_bits:
  "of_bits bs \<^bold>\<times> of_bits cs = (of_bits (map2 (\<^bold>*) bs cs) :: int)"
    if "length bs = length cs" and "\<not> False \<^bold>* False" for bs cs
using \<open>length bs = length cs\<close> proof (induction bs cs rule: list_induct2)
  case Nil
  then show ?case
    using \<open>\<not> False \<^bold>* False\<close> by (auto simp add: False_False_imp_True_True split: bool.splits)
next
  case (Cons b bs c cs)
  show ?case
  proof (cases "bs = []")
    case True
    with Cons show ?thesis
      using \<open>\<not> False \<^bold>* False\<close> by (cases b; cases c)
        (auto simp add: ac_simps split: bool.splits)
  next
    case False
    with Cons.hyps have "cs \<noteq> []"
      by auto
    with \<open>bs \<noteq> []\<close> have "map2 (\<^bold>*) bs cs \<noteq> []"
      by (simp add: zip_eq_Nil_iff)
    from \<open>bs \<noteq> []\<close> \<open>cs \<noteq> []\<close> \<open>map2 (\<^bold>*) bs cs \<noteq> []\<close> Cons show ?thesis
      by (cases b; cases c)
        (auto simp add: \<open>\<not> False \<^bold>* False\<close> ac_simps
          rec [of "of_bits bs * 2"] rec [of "of_bits cs * 2"]
          rec [of "1 + of_bits bs * 2"])
  qed
qed

end

instantiation int :: bit_operations
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

definition shift_left_int :: "int \<Rightarrow> nat \<Rightarrow> int"
  where [simp]: "k << n = push_bit n k" for k :: int

definition shift_right_int :: "int \<Rightarrow> nat \<Rightarrow> int"
  where [simp]: "k >> n = drop_bit n k" for k :: int

instance proof
  show "semilattice ((AND) :: int \<Rightarrow> _)"
    by (fact and_int.semilattice_axioms)
  show "semilattice ((OR) :: int \<Rightarrow> _)"
    by (fact or_int.semilattice_axioms)
  show "abel_semigroup ((XOR) :: int \<Rightarrow> _)"
    by (fact xor_int.abel_semigroup_axioms)
  show "(not :: int \<Rightarrow> _) = of_bits \<circ> map Not \<circ> bits_of"
  proof (rule sym, rule ext)
    fix k :: int
    show "(of_bits \<circ> map Not \<circ> bits_of) k = NOT k"
      by (induction k rule: int_bit_induct) (simp_all add: not_int_def)
  qed
  show "of_bits bs AND of_bits cs = (of_bits (map2 (\<and>) bs cs) :: int)"
    if "length bs = length cs" for bs cs
    using that by (rule and_int.of_bits) simp
  show "of_bits bs OR of_bits cs = (of_bits (map2 (\<or>) bs cs) :: int)"
    if "length bs = length cs" for bs cs
    using that by (rule or_int.of_bits) simp
  show "of_bits bs XOR of_bits cs = (of_bits (map2 (\<noteq>) bs cs) :: int)"
    if "length bs = length cs" for bs cs
    using that by (rule xor_int.of_bits) simp
  show "k << n = of_bits (replicate n False @ bits_of k)"
    for k :: int and n :: nat
    by (cases "n = 0") simp_all
  show "k >> n = of_bits (drop n (bits_of k))"
    if "n < length (bits_of k)"
    for k :: int and n :: nat
    using that by simp
qed

end

global_interpretation and_int: semilattice_neutr "(AND)" "- 1 :: int"
  by standard simp

global_interpretation or_int: semilattice_neutr "(OR)" "0 :: int"
  by standard simp

global_interpretation xor_int: comm_monoid "(XOR)" "0 :: int"
  by standard simp

lemma not_int_simps [simp]:
  "NOT 0 = (- 1 :: int)"
  "NOT - 1 = (0 :: int)"
  "k \<noteq> 0 \<Longrightarrow> k \<noteq> - 1 \<Longrightarrow> NOT k = of_bool (even k) + 2 * NOT (k div 2)" for k :: int
  by (auto simp add: not_int_def elim: oddE)

lemma not_one_int [simp]:
  "NOT 1 = (- 2 :: int)"
  by simp

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

end
