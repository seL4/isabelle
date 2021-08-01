 (*  Author:  Florian Haftmann, TUM
*)

section \<open>Proof(s) of concept for algebraically founded lists of bits\<close>

theory Bit_Lists
  imports
    "HOL-Library.Word" "HOL-Library.More_List"
begin

subsection \<open>Fragments of algebraic bit representations\<close>

context comm_semiring_1
begin
 
abbreviation (input) unsigned_of_bits :: "bool list \<Rightarrow> 'a"
  where "unsigned_of_bits \<equiv> horner_sum of_bool 2"

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
  "unsigned_of_bits (take n bs) = take_bit n (unsigned_of_bits bs)"
proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
    by (cases n) (simp_all add: ac_simps take_bit_Suc)
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
    by (cases n) (simp_all add: drop_bit_Suc)
qed

lemma bit_unsigned_of_bits_iff:
  \<open>bit (unsigned_of_bits bs) n \<longleftrightarrow> nth_default False bs n\<close>
proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
    by (cases n) (simp_all add: bit_Suc)
qed

primrec n_bits_of :: "nat \<Rightarrow> 'a \<Rightarrow> bool list"
  where
    "n_bits_of 0 a = []"
  | "n_bits_of (Suc n) a = odd a # n_bits_of n (a div 2)"

lemma n_bits_of_eq_iff:
  "n_bits_of n a = n_bits_of n b \<longleftrightarrow> take_bit n a = take_bit n b"
  apply (induction n arbitrary: a b)
   apply (auto elim!: evenE oddE simp add: take_bit_Suc mod_2_eq_odd)
    apply (metis dvd_triv_right even_plus_one_iff odd_iff_mod_2_eq_one)
   apply (metis dvd_triv_right even_plus_one_iff odd_iff_mod_2_eq_one)
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
  "unsigned_of_bits (n_bits_of n a) = take_bit n a"
  by (induction n arbitrary: a) (simp_all add: ac_simps take_bit_Suc mod_2_eq_odd)

end


subsection \<open>Syntactic bit representation\<close>

class bit_representation =
  fixes bits_of :: "'a \<Rightarrow> bool list"
    and of_bits :: "bool list \<Rightarrow> 'a"
  assumes of_bits_of [simp]: "of_bits (bits_of a) = a"

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

lemma bit_of_bits_nat_iff:
  \<open>bit (of_bits bs :: nat) n \<longleftrightarrow> nth_default False bs n\<close>
  by (simp add: bit_unsigned_of_bits_iff)

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

lemma bit_of_bits_int_iff:
  \<open>bit (of_bits bs :: int) n \<longleftrightarrow> nth_default (bs \<noteq> [] \<and> last bs) bs n\<close>
proof (induction bs arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  then show ?case
    by (cases n; cases b; cases bs) (simp_all add: bit_Suc)
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
      by (cases b) (simp_all add: drop_bit_Suc)
  qed
qed

end

lemma unsigned_of_bits_eq_of_bits:
  "unsigned_of_bits bs = (of_bits (bs @ [False]) :: int)"
  by (simp add: of_bits_int_def)

unbundle word.lifting

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

lifting_update word.lifting
lifting_forget word.lifting


subsection \<open>Bit representations with bit operations\<close>

class semiring_bit_representation = semiring_bit_operations + bit_representation
  opening bit_operations_syntax +
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

instance nat :: semiring_bit_representation
  by standard (simp_all add: bit_eq_iff bit_unsigned_of_bits_iff nth_default_map2 [of _ _ _ False False]
    bit_and_iff bit_or_iff bit_xor_iff)

instance int :: ring_bit_representation
including bit_operations_syntax proof
  {
    fix bs cs :: \<open>bool list\<close>
    assume \<open>length bs = length cs\<close>
    then have \<open>cs = [] \<longleftrightarrow> bs = []\<close>
      by auto
    with \<open>length bs = length cs\<close> have \<open>zip bs cs \<noteq> [] \<and> last (map2 (\<and>) bs cs) \<longleftrightarrow> (bs \<noteq> [] \<and> last bs) \<and> (cs \<noteq> [] \<and> last cs)\<close>
      and \<open>zip bs cs \<noteq> [] \<and> last (map2 (\<or>) bs cs) \<longleftrightarrow> (bs \<noteq> [] \<and> last bs) \<or> (cs \<noteq> [] \<and> last cs)\<close>
      and \<open>zip bs cs \<noteq> [] \<and> last (map2 (\<noteq>) bs cs) \<longleftrightarrow> ((bs \<noteq> [] \<and> last bs) \<noteq> (cs \<noteq> [] \<and> last cs))\<close>
      by (auto simp add: last_map last_zip zip_eq_Nil_iff prod_eq_iff)
    then show \<open>of_bits bs AND of_bits cs = (of_bits (map2 (\<and>) bs cs) :: int)\<close>
      and \<open>of_bits bs OR of_bits cs = (of_bits (map2 (\<or>) bs cs) :: int)\<close>
      and \<open>of_bits bs XOR of_bits cs = (of_bits (map2 (\<noteq>) bs cs) :: int)\<close>
      by (simp_all add: fun_eq_iff bit_eq_iff bit_and_iff bit_or_iff bit_xor_iff bit_not_iff bit_of_bits_int_iff \<open>length bs = length cs\<close> nth_default_map2 [of bs cs _ \<open>bs \<noteq> [] \<and> last bs\<close> \<open>cs \<noteq> [] \<and> last cs\<close>])
  }
  show \<open>push_bit n k = of_bits (replicate n False @ bits_of k)\<close>
    for k :: int and n :: nat
    by (cases "n = 0") simp_all
  show \<open>drop_bit n k = of_bits (drop n (bits_of k))\<close>
    if \<open>n < length (bits_of k)\<close> for k :: int and n :: nat
    using that by simp
  show \<open>(not :: int \<Rightarrow> _) = of_bits \<circ> map Not \<circ> bits_of\<close>
  proof (rule sym, rule ext)
    fix k :: int
    show \<open>(of_bits \<circ> map Not \<circ> bits_of) k = NOT k\<close>
      by (induction k rule: int_bit_induct) (simp_all add: not_int_def)
  qed
qed

end
