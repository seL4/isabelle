(*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof(s) of concept for algebraically founded lists of bits\<close>

theory Bit_Lists
  imports
    Word
begin

subsection \<open>Fragments of algebraic bit representations\<close>

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

context unique_euclidean_semiring_with_bit_shifts
begin

lemma unsigned_of_bits_append [simp]:
  "unsigned_of_bits (bs @ cs) = unsigned_of_bits bs
    + push_bit (length bs) (unsigned_of_bits cs)"
  by (induction bs) (simp_all add: push_bit_double,
    simp_all add: algebra_simps)

lemma unsigned_of_bits_take [simp]:
  "unsigned_of_bits (take n bs) = Parity.take_bit n (unsigned_of_bits bs)"
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
  "unsigned_of_bits (drop n bs) = Parity.drop_bit n (unsigned_of_bits bs)"
proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
    by (cases n) simp_all
qed

primrec n_bits_of :: "nat \<Rightarrow> 'a \<Rightarrow> bool list"
  where
    "n_bits_of 0 a = []"
  | "n_bits_of (Suc n) a = odd a # n_bits_of n (a div 2)"

lemma n_bits_of_eq_iff:
  "n_bits_of n a = n_bits_of n b \<longleftrightarrow> Parity.take_bit n a = Parity.take_bit n b"
  apply (induction n arbitrary: a b)
   apply (auto elim!: evenE oddE)
   apply (metis dvd_triv_right even_plus_one_iff)
  apply (metis dvd_triv_right even_plus_one_iff)
  done

lemma take_n_bits_of [simp]:
  "take m (n_bits_of n a) = n_bits_of (min m n) a"
proof -
  define q and v and w where "q = min m n" and "v = m - q" and "w = n - q"
  then have "v = 0 \<or> w = 0"
    by auto
  then have "take (q + v) (n_bits_of (q + w) a) = n_bits_of q a"
    by (induction q arbitrary: a) auto
  with q_def v_def w_def show ?thesis
    by simp
qed

lemma unsigned_of_bits_n_bits_of [simp]:
  "unsigned_of_bits (n_bits_of n a) = Parity.take_bit n a"
  by (induction n arbitrary: a) (simp_all add: ac_simps)

end


subsection \<open>Syntactic bit representation\<close>

class bit_representation =
  fixes bits_of :: "'a \<Rightarrow> bool list"
    and of_bits :: "bool list \<Rightarrow> 'a"
  assumes of_bits_of [simp]: "of_bits (bits_of a) = a"

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
  "of_bits (drop n bs) = Parity.drop_bit n (of_bits bs :: int)"
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

lemma unsigned_of_bits_eq_of_bits:
  "unsigned_of_bits bs = (of_bits (bs @ [False]) :: int)"
  by (simp add: of_bits_int_def)

instantiation word :: (len) bit_representation
begin

lift_definition bits_of_word :: "'a word \<Rightarrow> bool list"
  is "n_bits_of LENGTH('a)"
  by (simp add: n_bits_of_eq_iff)

lift_definition of_bits_word :: "bool list \<Rightarrow> 'a word"
  is unsigned_of_bits .

instance proof
  fix a :: "'a word"
  show "of_bits (bits_of a) = a"
    by transfer simp
qed

end


subsection \<open>Bit representations with bit operations\<close>

class semiring_bit_representation = semiring_bit_operations + bit_representation +
  assumes and_eq: "length bs = length cs \<Longrightarrow>
      of_bits bs AND of_bits cs = of_bits (map2 (\<and>) bs cs)"
    and or_eq: "length bs = length cs \<Longrightarrow>
      of_bits bs OR of_bits cs = of_bits (map2 (\<or>) bs cs)"
    and xor_eq: "length bs = length cs \<Longrightarrow>
      of_bits bs XOR of_bits cs = of_bits (map2 (\<noteq>) bs cs)"
    and push_bit_eq: "push_bit n a = of_bits (replicate n False @ bits_of a)"
    and drop_bit_eq: "n < length (bits_of a) \<Longrightarrow> drop_bit n a = of_bits (drop n (bits_of a))"

class ring_bit_representation = ring_bit_operations + semiring_bit_representation +
  assumes not_eq: "not = of_bits \<circ> map Not \<circ> bits_of"


context zip_nat
begin

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

instance nat :: semiring_bit_representation
  apply standard
      apply (simp_all only: and_nat.of_bits or_nat.of_bits xor_nat.of_bits)
   apply simp_all
  done

context zip_int
begin
 
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

instance int :: ring_bit_representation
proof
  show "(not :: int \<Rightarrow> _) = of_bits \<circ> map Not \<circ> bits_of"
  proof (rule sym, rule ext)
    fix k :: int
    show "(of_bits \<circ> map Not \<circ> bits_of) k = NOT k"
      by (induction k rule: int_bit_induct) (simp_all add: not_int_def)
  qed
  show "push_bit n k = of_bits (replicate n False @ bits_of k)"
    for k :: int and n :: nat
    by (cases "n = 0") simp_all
qed (simp_all add: and_int.of_bits or_int.of_bits xor_int.of_bits)

end
