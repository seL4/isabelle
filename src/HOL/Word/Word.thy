(*  Title:      HOL/Word/Word.thy
    Author:     Jeremy Dawson and Gerwin Klein, NICTA
*)

section \<open>A type of finite bit strings\<close>

theory Word
imports
  "HOL-Library.Type_Length"
  "HOL-Library.Boolean_Algebra"
  "HOL-Library.Bit_Operations"
  Bits_Int
  Bit_Comprehension
  Bit_Lists
  Misc_Typedef
begin

subsection \<open>Type definition\<close>

quotient_type (overloaded) 'a word = int / \<open>\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a::len) l\<close>
  morphisms rep_word word_of_int by (auto intro!: equivpI reflpI sympI transpI)

lift_definition uint :: \<open>'a::len word \<Rightarrow> int\<close>
  is \<open>take_bit LENGTH('a)\<close> .

lemma uint_nonnegative: "0 \<le> uint w"
  by transfer simp

lemma uint_bounded: "uint w < 2 ^ LENGTH('a)"
  for w :: "'a::len word"
  by transfer (simp add: take_bit_eq_mod)

lemma uint_idem: "uint w mod 2 ^ LENGTH('a) = uint w"
  for w :: "'a::len word"
  using uint_nonnegative uint_bounded by (rule mod_pos_pos_trivial)

lemma word_uint_eqI: "uint a = uint b \<Longrightarrow> a = b"
  by transfer simp

lemma word_uint_eq_iff: "a = b \<longleftrightarrow> uint a = uint b"
  using word_uint_eqI by auto

lemma uint_word_of_int: "uint (word_of_int k :: 'a::len word) = k mod 2 ^ LENGTH('a)"
  by transfer (simp add: take_bit_eq_mod)
  
lemma word_of_int_uint: "word_of_int (uint w) = w"
  by transfer simp

lemma split_word_all: "(\<And>x::'a::len word. PROP P x) \<equiv> (\<And>x. PROP P (word_of_int x))"
proof
  fix x :: "'a word"
  assume "\<And>x. PROP P (word_of_int x)"
  then have "PROP P (word_of_int (uint x))" .
  then show "PROP P x" by (simp add: word_of_int_uint)
qed


subsection \<open>Type conversions and casting\<close>

definition sint :: "'a::len word \<Rightarrow> int"
  \<comment> \<open>treats the most-significant-bit as a sign bit\<close>
  where sint_uint: "sint w = sbintrunc (LENGTH('a) - 1) (uint w)"

definition unat :: "'a::len word \<Rightarrow> nat"
  where "unat w = nat (uint w)"

definition scast :: "'a::len word \<Rightarrow> 'b::len word"
  \<comment> \<open>cast a word to a different length\<close>
  where "scast w = word_of_int (sint w)"

definition ucast :: "'a::len word \<Rightarrow> 'b::len word"
  where "ucast w = word_of_int (uint w)"

instantiation word :: (len) size
begin

definition word_size: "size (w :: 'a word) = LENGTH('a)"

instance ..

end

lemma word_size_gt_0 [iff]: "0 < size w"
  for w :: "'a::len word"
  by (simp add: word_size)

lemmas lens_gt_0 = word_size_gt_0 len_gt_0

lemma lens_not_0 [iff]:
  \<open>size w \<noteq> 0\<close> for  w :: \<open>'a::len word\<close>
  by auto

definition source_size :: "('a::len word \<Rightarrow> 'b) \<Rightarrow> nat"
  \<comment> \<open>whether a cast (or other) function is to a longer or shorter length\<close>
  where [code del]: "source_size c = (let arb = undefined; x = c arb in size arb)"

definition target_size :: "('a \<Rightarrow> 'b::len word) \<Rightarrow> nat"
  where [code del]: "target_size c = size (c undefined)"

definition is_up :: "('a::len word \<Rightarrow> 'b::len word) \<Rightarrow> bool"
  where "is_up c \<longleftrightarrow> source_size c \<le> target_size c"

definition is_down :: "('a::len word \<Rightarrow> 'b::len word) \<Rightarrow> bool"
  where "is_down c \<longleftrightarrow> target_size c \<le> source_size c"

definition of_bl :: "bool list \<Rightarrow> 'a::len word"
  where "of_bl bl = word_of_int (bl_to_bin bl)"

definition to_bl :: "'a::len word \<Rightarrow> bool list"
  where "to_bl w = bin_to_bl (LENGTH('a)) (uint w)"

definition word_int_case :: "(int \<Rightarrow> 'b) \<Rightarrow> 'a::len word \<Rightarrow> 'b"
  where "word_int_case f w = f (uint w)"

translations
  "case x of XCONST of_int y \<Rightarrow> b" \<rightleftharpoons> "CONST word_int_case (\<lambda>y. b) x"
  "case x of (XCONST of_int :: 'a) y \<Rightarrow> b" \<rightharpoonup> "CONST word_int_case (\<lambda>y. b) x"


subsection \<open>Basic code generation setup\<close>

definition Word :: "int \<Rightarrow> 'a::len word"
  where [code_post]: "Word = word_of_int"

lemma [code abstype]: "Word (uint w) = w"
  by (simp add: Word_def word_of_int_uint)

declare uint_word_of_int [code abstract]

instantiation word :: (len) equal
begin

definition equal_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  where "equal_word k l \<longleftrightarrow> HOL.equal (uint k) (uint l)"

instance
  by standard (simp add: equal equal_word_def word_uint_eq_iff)

end

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation word :: ("{len, typerep}") random
begin

definition
  "random_word i = Random.range i \<circ>\<rightarrow> (\<lambda>k. Pair (
     let j = word_of_int (int_of_integer (integer_of_natural k)) :: 'a word
     in (j, \<lambda>_::unit. Code_Evaluation.term_of j)))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)


subsection \<open>Type-definition locale instantiations\<close>

lemmas uint_0 = uint_nonnegative (* FIXME duplicate *)
lemmas uint_lt = uint_bounded (* FIXME duplicate *)
lemmas uint_mod_same = uint_idem (* FIXME duplicate *)

definition uints :: "nat \<Rightarrow> int set"
  \<comment> \<open>the sets of integers representing the words\<close>
  where "uints n = range (bintrunc n)"

definition sints :: "nat \<Rightarrow> int set"
  where "sints n = range (sbintrunc (n - 1))"

lemma uints_num: "uints n = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (simp add: uints_def range_bintrunc)

lemma sints_num: "sints n = {i. - (2 ^ (n - 1)) \<le> i \<and> i < 2 ^ (n - 1)}"
  by (simp add: sints_def range_sbintrunc)

definition unats :: "nat \<Rightarrow> nat set"
  where "unats n = {i. i < 2 ^ n}"

\<comment> \<open>naturals\<close>
lemma uints_unats: "uints n = int ` unats n"
  apply (unfold unats_def uints_num)
  apply safe
    apply (rule_tac image_eqI)
     apply (erule_tac nat_0_le [symmetric])
  by auto

lemma unats_uints: "unats n = nat ` uints n"
  by (auto simp: uints_unats image_iff)

lemma td_ext_uint:
  "td_ext (uint :: 'a word \<Rightarrow> int) word_of_int (uints (LENGTH('a::len)))
    (\<lambda>w::int. w mod 2 ^ LENGTH('a))"
  apply (unfold td_ext_def')
  apply transfer
  apply (simp add: uints_num take_bit_eq_mod)
  done

interpretation word_uint:
  td_ext
    "uint::'a::len word \<Rightarrow> int"
    word_of_int
    "uints (LENGTH('a::len))"
    "\<lambda>w. w mod 2 ^ LENGTH('a::len)"
  by (fact td_ext_uint)

lemmas td_uint = word_uint.td_thm
lemmas int_word_uint = word_uint.eq_norm

lemma td_ext_ubin:
  "td_ext (uint :: 'a word \<Rightarrow> int) word_of_int (uints (LENGTH('a::len)))
    (bintrunc (LENGTH('a)))"
  by (unfold no_bintr_alt1) (fact td_ext_uint)

interpretation word_ubin:
  td_ext
    "uint::'a::len word \<Rightarrow> int"
    word_of_int
    "uints (LENGTH('a::len))"
    "bintrunc (LENGTH('a::len))"
  by (fact td_ext_ubin)


subsection \<open>Arithmetic operations\<close>

lift_definition word_succ :: "'a::len word \<Rightarrow> 'a word" is "\<lambda>x. x + 1"
  by (auto simp add: bintrunc_mod2p intro: mod_add_cong)

lift_definition word_pred :: "'a::len word \<Rightarrow> 'a word" is "\<lambda>x. x - 1"
  by (auto simp add: bintrunc_mod2p intro: mod_diff_cong)

instantiation word :: (len) "{neg_numeral, modulo, comm_monoid_mult, comm_ring}"
begin

lift_definition zero_word :: "'a word" is "0" .

lift_definition one_word :: "'a word" is "1" .

lift_definition plus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" is "(+)"
  by (auto simp add: bintrunc_mod2p intro: mod_add_cong)

lift_definition minus_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" is "(-)"
  by (auto simp add: bintrunc_mod2p intro: mod_diff_cong)

lift_definition uminus_word :: "'a word \<Rightarrow> 'a word" is uminus
  by (auto simp add: bintrunc_mod2p intro: mod_minus_cong)

lift_definition times_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" is "(*)"
  by (auto simp add: bintrunc_mod2p intro: mod_mult_cong)

lift_definition divide_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. take_bit LENGTH('a) a div take_bit LENGTH('a) b"
  by simp

lift_definition modulo_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda>a b. take_bit LENGTH('a) a mod take_bit LENGTH('a) b"
  by simp

instance
  by standard (transfer, simp add: algebra_simps)+

end

lemma word_div_def [code]:
  "a div b = word_of_int (uint a div uint b)"
  by transfer rule

lemma word_mod_def [code]:
  "a mod b = word_of_int (uint a mod uint b)"
  by transfer rule

quickcheck_generator word
  constructors:
    "zero_class.zero :: ('a::len) word",
    "numeral :: num \<Rightarrow> ('a::len) word",
    "uminus :: ('a::len) word \<Rightarrow> ('a::len) word"

context
  includes lifting_syntax
  notes power_transfer [transfer_rule]
begin

lemma power_transfer_word [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (^) (^)\<close>
  by transfer_prover

end



text \<open>Legacy theorems:\<close>

lemma word_arith_wis [code]:
  shows word_add_def: "a + b = word_of_int (uint a + uint b)"
    and word_sub_wi: "a - b = word_of_int (uint a - uint b)"
    and word_mult_def: "a * b = word_of_int (uint a * uint b)"
    and word_minus_def: "- a = word_of_int (- uint a)"
    and word_succ_alt: "word_succ a = word_of_int (uint a + 1)"
    and word_pred_alt: "word_pred a = word_of_int (uint a - 1)"
    and word_0_wi: "0 = word_of_int 0"
    and word_1_wi: "1 = word_of_int 1"
         apply (simp_all flip: plus_word.abs_eq minus_word.abs_eq
           times_word.abs_eq uminus_word.abs_eq
           zero_word.abs_eq one_word.abs_eq)
   apply transfer
   apply simp
  apply transfer
  apply simp
  done

lemma wi_homs:
  shows wi_hom_add: "word_of_int a + word_of_int b = word_of_int (a + b)"
    and wi_hom_sub: "word_of_int a - word_of_int b = word_of_int (a - b)"
    and wi_hom_mult: "word_of_int a * word_of_int b = word_of_int (a * b)"
    and wi_hom_neg: "- word_of_int a = word_of_int (- a)"
    and wi_hom_succ: "word_succ (word_of_int a) = word_of_int (a + 1)"
    and wi_hom_pred: "word_pred (word_of_int a) = word_of_int (a - 1)"
  by (transfer, simp)+

lemmas wi_hom_syms = wi_homs [symmetric]

lemmas word_of_int_homs = wi_homs word_0_wi word_1_wi

lemmas word_of_int_hom_syms = word_of_int_homs [symmetric]

instance word :: (len) comm_monoid_add ..

instance word :: (len) semiring_numeral ..

instance word :: (len) comm_ring_1
proof
  have *: "0 < LENGTH('a)" by (rule len_gt_0)
  show "(0::'a word) \<noteq> 1"
    by transfer (use * in \<open>auto simp add: gr0_conv_Suc\<close>)
qed

lemma word_of_nat: "of_nat n = word_of_int (int n)"
  by (induct n) (auto simp add : word_of_int_hom_syms)

lemma word_of_int: "of_int = word_of_int"
  apply (rule ext)
  apply (case_tac x rule: int_diff_cases)
  apply (simp add: word_of_nat wi_hom_sub)
  done

context
  includes lifting_syntax
  notes 
    transfer_rule_of_bool [transfer_rule]
    transfer_rule_numeral [transfer_rule]
    transfer_rule_of_nat [transfer_rule]
    transfer_rule_of_int [transfer_rule]
begin

lemma [transfer_rule]:
  "((=) ===> (pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> bool)) of_bool of_bool"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> (pcr_word :: int \<Rightarrow> 'a::len word \<Rightarrow> bool)) numeral numeral"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> pcr_word) int of_nat"
  by transfer_prover

lemma [transfer_rule]:
  "((=) ===> pcr_word) (\<lambda>k. k) of_int"
proof -
  have "((=) ===> pcr_word) of_int of_int"
    by transfer_prover
  then show ?thesis by (simp add: id_def)
qed

end

lemma word_of_int_eq:
  "word_of_int = of_int"
  by (rule ext) (transfer, rule)

definition udvd :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" (infixl "udvd" 50)
  where "a udvd b = (\<exists>n\<ge>0. uint b = n * uint a)"

context
  includes lifting_syntax
begin

lemma [transfer_rule]:
  \<open>(pcr_word ===> (\<longleftrightarrow>)) even ((dvd) 2 :: 'a::len word \<Rightarrow> bool)\<close>
proof -
  have even_word_unfold: "even k \<longleftrightarrow> (\<exists>l. take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l))" (is "?P \<longleftrightarrow> ?Q")
    for k :: int
  proof
    assume ?P
    then show ?Q
      by auto
  next
    assume ?Q
    then obtain l where "take_bit LENGTH('a) k = take_bit LENGTH('a) (2 * l)" ..
    then have "even (take_bit LENGTH('a) k)"
      by simp
    then show ?P
      by simp
  qed
  show ?thesis by (simp only: even_word_unfold [abs_def] dvd_def [where ?'a = "'a word", abs_def])
    transfer_prover
qed

end

instance word :: (len) semiring_modulo
proof
  show "a div b * b + a mod b = a" for a b :: "'a word"
  proof transfer
    fix k l :: int
    define r :: int where "r = 2 ^ LENGTH('a)"
    then have r: "take_bit LENGTH('a) k = k mod r" for k
      by (simp add: take_bit_eq_mod)
    have "k mod r = ((k mod r) div (l mod r) * (l mod r)
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: div_mult_mod_eq)
    also have "... = (((k mod r) div (l mod r) * (l mod r)) mod r
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_add_left_eq)
    also have "... = (((k mod r) div (l mod r) * l) mod r
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_mult_right_eq)
    finally have "k mod r = ((k mod r) div (l mod r) * l
      + (k mod r) mod (l mod r)) mod r"
      by (simp add: mod_simps)
    with r show "take_bit LENGTH('a) (take_bit LENGTH('a) k div take_bit LENGTH('a) l * l
      + take_bit LENGTH('a) k mod take_bit LENGTH('a) l) = take_bit LENGTH('a) k"
      by simp
  qed
qed

instance word :: (len) semiring_parity
proof
  show "\<not> 2 dvd (1::'a word)"
    by transfer simp
  show even_iff_mod_2_eq_0: "2 dvd a \<longleftrightarrow> a mod 2 = 0"
    for a :: "'a word"
    by transfer (simp_all add: mod_2_eq_odd take_bit_Suc)
  show "\<not> 2 dvd a \<longleftrightarrow> a mod 2 = 1"
    for a :: "'a word"
    by transfer (simp_all add: mod_2_eq_odd take_bit_Suc)
qed

lemma exp_eq_zero_iff:
  \<open>2 ^ n = (0 :: 'a::len word) \<longleftrightarrow> n \<ge> LENGTH('a)\<close>
  by transfer simp

lemma double_eq_zero_iff:
  \<open>2 * a = 0 \<longleftrightarrow> a = 0 \<or> a = 2 ^ (LENGTH('a) - Suc 0)\<close>
  for a :: \<open>'a::len word\<close>
proof -
  define n where \<open>n = LENGTH('a) - Suc 0\<close>
  then have *: \<open>LENGTH('a) = Suc n\<close>
    by simp
  have \<open>a = 0\<close> if \<open>2 * a = 0\<close> and \<open>a \<noteq> 2 ^ (LENGTH('a) - Suc 0)\<close>
    using that by transfer
      (auto simp add: take_bit_eq_0_iff take_bit_eq_mod *)
  moreover have \<open>2 ^ LENGTH('a) = (0 :: 'a word)\<close>
    by transfer simp
  then have \<open>2 * 2 ^ (LENGTH('a) - Suc 0) = (0 :: 'a word)\<close>
    by (simp add: *)
  ultimately show ?thesis
    by auto
qed


subsection \<open>Ordering\<close>

instantiation word :: (len) linorder
begin

lift_definition less_eq_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a \<le> take_bit LENGTH('a) b"
  by simp

lift_definition less_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  is "\<lambda>a b. take_bit LENGTH('a) a < take_bit LENGTH('a) b"
  by simp

instance
  by (standard; transfer) auto

end

interpretation word_order: ordering_top \<open>(\<le>)\<close> \<open>(<)\<close> \<open>- 1 :: 'a::len word\<close>
  by (standard; transfer) (simp add: take_bit_eq_mod zmod_minus1)

interpretation word_coorder: ordering_top \<open>(\<ge>)\<close> \<open>(>)\<close> \<open>0 :: 'a::len word\<close>
  by (standard; transfer) simp

lemma word_le_def [code]:
  "a \<le> b \<longleftrightarrow> uint a \<le> uint b"
  by transfer rule

lemma word_less_def [code]:
  "a < b \<longleftrightarrow> uint a < uint b"
  by transfer rule

lemma word_greater_zero_iff:
  \<open>a > 0 \<longleftrightarrow> a \<noteq> 0\<close> for a :: \<open>'a::len word\<close>
  by transfer (simp add: less_le)

lemma of_nat_word_eq_iff:
  \<open>of_nat m = (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m = take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_less_eq_iff:
  \<open>of_nat m \<le> (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m \<le> take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_less_iff:
  \<open>of_nat m < (of_nat n :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) m < take_bit LENGTH('a) n\<close>
  by transfer (simp add: take_bit_of_nat)

lemma of_nat_word_eq_0_iff:
  \<open>of_nat n = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd n\<close>
  using of_nat_word_eq_iff [where ?'a = 'a, of n 0] by (simp add: take_bit_eq_0_iff)

lemma of_int_word_eq_iff:
  \<open>of_int k = (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_less_eq_iff:
  \<open>of_int k \<le> (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k \<le> take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_less_iff:
  \<open>of_int k < (of_int l :: 'a::len word) \<longleftrightarrow> take_bit LENGTH('a) k < take_bit LENGTH('a) l\<close>
  by transfer rule

lemma of_int_word_eq_0_iff:
  \<open>of_int k = (0 :: 'a::len word) \<longleftrightarrow> 2 ^ LENGTH('a) dvd k\<close>
  using of_int_word_eq_iff [where ?'a = 'a, of k 0] by (simp add: take_bit_eq_0_iff)

definition word_sle :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool"  ("(_/ <=s _)" [50, 51] 50)
  where "a <=s b \<longleftrightarrow> sint a \<le> sint b"

definition word_sless :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool"  ("(_/ <s _)" [50, 51] 50)
  where "x <s y \<longleftrightarrow> x <=s y \<and> x \<noteq> y"


subsection \<open>Bit-wise operations\<close>

lemma word_bit_induct [case_names zero even odd]:
  \<open>P a\<close> if word_zero: \<open>P 0\<close>
    and word_even: \<open>\<And>a. P a \<Longrightarrow> 0 < a \<Longrightarrow> a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> P (2 * a)\<close>
    and word_odd: \<open>\<And>a. P a \<Longrightarrow> a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> P (1 + 2 * a)\<close>
  for P and a :: \<open>'a::len word\<close>
proof -
  define m :: nat where \<open>m = LENGTH('a) - 1\<close>
  then have l: \<open>LENGTH('a) = Suc m\<close>
    by simp
  define n :: nat where \<open>n = unat a\<close>
  then have \<open>n < 2 ^ LENGTH('a)\<close>
    by (unfold unat_def) (transfer, simp add: take_bit_eq_mod)
  then have \<open>n < 2 * 2 ^ m\<close>
    by (simp add: l)
  then have \<open>P (of_nat n)\<close>
  proof (induction n rule: nat_bit_induct)
    case zero
    show ?case
      by simp (rule word_zero)
  next
    case (even n)
    then have \<open>n < 2 ^ m\<close>
      by simp
    with even.IH have \<open>P (of_nat n)\<close>
      by simp
    moreover from \<open>n < 2 ^ m\<close> even.hyps have \<open>0 < (of_nat n :: 'a word)\<close>
      by (auto simp add: word_greater_zero_iff of_nat_word_eq_0_iff l)
    moreover from \<open>n < 2 ^ m\<close> have \<open>(of_nat n :: 'a word) < 2 ^ (LENGTH('a) - 1)\<close>
      using of_nat_word_less_iff [where ?'a = 'a, of n \<open>2 ^ m\<close>]
      by (cases \<open>m = 0\<close>) (simp_all add: not_less take_bit_eq_self ac_simps l)
    ultimately have \<open>P (2 * of_nat n)\<close>
      by (rule word_even)
    then show ?case
      by simp
  next
    case (odd n)
    then have \<open>Suc n \<le> 2 ^ m\<close>
      by simp
    with odd.IH have \<open>P (of_nat n)\<close>
      by simp
    moreover from \<open>Suc n \<le> 2 ^ m\<close> have \<open>(of_nat n :: 'a word) < 2 ^ (LENGTH('a) - 1)\<close>
      using of_nat_word_less_iff [where ?'a = 'a, of n \<open>2 ^ m\<close>]
      by (cases \<open>m = 0\<close>) (simp_all add: not_less take_bit_eq_self ac_simps l)
    ultimately have \<open>P (1 + 2 * of_nat n)\<close>
      by (rule word_odd)
    then show ?case
      by simp
  qed
  moreover have \<open>of_nat (nat (uint a)) = a\<close>
    by transfer simp
  ultimately show ?thesis
    by (simp add: n_def unat_def)
qed

lemma bit_word_half_eq:
  \<open>(of_bool b + a * 2) div 2 = a\<close>
    if \<open>a < 2 ^ (LENGTH('a) - Suc 0)\<close>
    for a :: \<open>'a::len word\<close>
proof (cases \<open>2 \<le> LENGTH('a::len)\<close>)
  case False
  have \<open>of_bool (odd k) < (1 :: int) \<longleftrightarrow> even k\<close> for k :: int
    by auto
  with False that show ?thesis
    by transfer (simp add: eq_iff)
next
  case True
  obtain n where length: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  show ?thesis proof (cases b)
    case False
    moreover have \<open>a * 2 div 2 = a\<close>
    using that proof transfer
      fix k :: int
      from length have \<open>k * 2 mod 2 ^ LENGTH('a) = (k mod 2 ^ n) * 2\<close>
        by simp
      moreover assume \<open>take_bit LENGTH('a) k < take_bit LENGTH('a) (2 ^ (LENGTH('a) - Suc 0))\<close>
      with \<open>LENGTH('a) = Suc n\<close>
      have \<open>k mod 2 ^ LENGTH('a) = k mod 2 ^ n\<close>
        by (simp add: take_bit_eq_mod divmod_digit_0)
      ultimately have \<open>take_bit LENGTH('a) (k * 2) = take_bit LENGTH('a) k * 2\<close>
        by (simp add: take_bit_eq_mod)
      with True show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (k * 2) div take_bit LENGTH('a) 2)
        = take_bit LENGTH('a) k\<close>
        by simp
    qed
    ultimately show ?thesis
      by simp
  next
    case True
    moreover have \<open>(1 + a * 2) div 2 = a\<close>
    using that proof transfer
      fix k :: int
      from length have \<open>(1 + k * 2) mod 2 ^ LENGTH('a) = 1 + (k mod 2 ^ n) * 2\<close>
        using pos_zmod_mult_2 [of \<open>2 ^ n\<close> k] by (simp add: ac_simps)
      moreover assume \<open>take_bit LENGTH('a) k < take_bit LENGTH('a) (2 ^ (LENGTH('a) - Suc 0))\<close>
      with \<open>LENGTH('a) = Suc n\<close>
      have \<open>k mod 2 ^ LENGTH('a) = k mod 2 ^ n\<close>
        by (simp add: take_bit_eq_mod divmod_digit_0)
      ultimately have \<open>take_bit LENGTH('a) (1 + k * 2) = 1 + take_bit LENGTH('a) k * 2\<close>
        by (simp add: take_bit_eq_mod)
      with True show \<open>take_bit LENGTH('a) (take_bit LENGTH('a) (1 + k * 2) div take_bit LENGTH('a) 2)
        = take_bit LENGTH('a) k\<close>
        by (auto simp add: take_bit_Suc)
    qed
    ultimately show ?thesis
      by simp
  qed
qed

lemma even_mult_exp_div_word_iff:
  \<open>even (a * 2 ^ m div 2 ^ n) \<longleftrightarrow> \<not> (
    m \<le> n \<and>
    n < LENGTH('a) \<and> odd (a div 2 ^ (n - m)))\<close> for a :: \<open>'a::len word\<close>
  by transfer
    (auto simp flip: drop_bit_eq_div simp add: even_drop_bit_iff_not_bit bit_take_bit_iff,
      simp_all flip: push_bit_eq_mult add: bit_push_bit_iff_int)

instantiation word :: (len) semiring_bits
begin

lift_definition bit_word :: \<open>'a word \<Rightarrow> nat \<Rightarrow> bool\<close>
  is \<open>\<lambda>k n. n < LENGTH('a) \<and> bit k n\<close>
proof
  fix k l :: int and n :: nat
  assume *: \<open>take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  show \<open>n < LENGTH('a) \<and> bit k n \<longleftrightarrow> n < LENGTH('a) \<and> bit l n\<close>
  proof (cases \<open>n < LENGTH('a)\<close>)
    case True
    from * have \<open>bit (take_bit LENGTH('a) k) n \<longleftrightarrow> bit (take_bit LENGTH('a) l) n\<close>
      by simp
    then show ?thesis
      by (simp add: bit_take_bit_iff)
  next
    case False
    then show ?thesis
      by simp
  qed
qed

instance proof
  show \<open>P a\<close> if stable: \<open>\<And>a. a div 2 = a \<Longrightarrow> P a\<close>
    and rec: \<open>\<And>a b. P a \<Longrightarrow> (of_bool b + 2 * a) div 2 = a \<Longrightarrow> P (of_bool b + 2 * a)\<close>
  for P and a :: \<open>'a word\<close>
  proof (induction a rule: word_bit_induct)
    case zero
    have \<open>0 div 2 = (0::'a word)\<close>
      by transfer simp
    with stable [of 0] show ?case
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
  show \<open>bit a n \<longleftrightarrow> odd (a div 2 ^ n)\<close> for a :: \<open>'a word\<close> and n
    by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit bit_iff_odd_drop_bit)
  show \<open>0 div a = 0\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>a div 1 = a\<close>
    for a :: \<open>'a word\<close>
    by transfer simp
  show \<open>a mod b div b = 0\<close>
    for a b :: \<open>'a word\<close>
    apply transfer
    apply (simp add: take_bit_eq_mod)
    apply (subst (3) mod_pos_pos_trivial [of _ \<open>2 ^ LENGTH('a)\<close>])
      apply simp_all
     apply (metis le_less mod_by_0 pos_mod_conj zero_less_numeral zero_less_power)
    using pos_mod_bound [of \<open>2 ^ LENGTH('a)\<close>] apply simp
  proof -
    fix aa :: int and ba :: int
    have f1: "\<And>i n. (i::int) mod 2 ^ n = 0 \<or> 0 < i mod 2 ^ n"
      by (metis le_less take_bit_eq_mod take_bit_nonnegative)
    have "(0::int) < 2 ^ len_of (TYPE('a)::'a itself) \<and> ba mod 2 ^ len_of (TYPE('a)::'a itself) \<noteq> 0 \<or> aa mod 2 ^ len_of (TYPE('a)::'a itself) mod (ba mod 2 ^ len_of (TYPE('a)::'a itself)) < 2 ^ len_of (TYPE('a)::'a itself)"
      by (metis (no_types) mod_by_0 unique_euclidean_semiring_numeral_class.pos_mod_bound zero_less_numeral zero_less_power)
    then show "aa mod 2 ^ len_of (TYPE('a)::'a itself) mod (ba mod 2 ^ len_of (TYPE('a)::'a itself)) < 2 ^ len_of (TYPE('a)::'a itself)"
      using f1 by (meson le_less less_le_trans unique_euclidean_semiring_numeral_class.pos_mod_bound)
  qed
  show \<open>(1 + a) div 2 = a div 2\<close>
    if \<open>even a\<close>
    for a :: \<open>'a word\<close>
    using that by transfer
      (auto dest: le_Suc_ex simp add: mod_2_eq_odd take_bit_Suc elim!: evenE)
  show \<open>(2 :: 'a word) ^ m div 2 ^ n = of_bool ((2 :: 'a word) ^ m \<noteq> 0 \<and> n \<le> m) * 2 ^ (m - n)\<close>
    for m n :: nat
    by transfer (simp, simp add: exp_div_exp_eq)
  show "a div 2 ^ m div 2 ^ n = a div 2 ^ (m + n)"
    for a :: "'a word" and m n :: nat
    apply transfer
    apply (auto simp add: not_less take_bit_drop_bit ac_simps simp flip: drop_bit_eq_div)
    apply (simp add: drop_bit_take_bit)
    done
  show "a mod 2 ^ m mod 2 ^ n = a mod 2 ^ min m n"
    for a :: "'a word" and m n :: nat
    by transfer (auto simp flip: take_bit_eq_mod simp add: ac_simps)
  show \<open>a * 2 ^ m mod 2 ^ n = a mod 2 ^ (n - m) * 2 ^ m\<close>
    if \<open>m \<le> n\<close> for a :: "'a word" and m n :: nat
    using that apply transfer
    apply (auto simp flip: take_bit_eq_mod)
           apply (auto simp flip: push_bit_eq_mult simp add: push_bit_take_bit split: split_min_lin)
    done
  show \<open>a div 2 ^ n mod 2 ^ m = a mod (2 ^ (n + m)) div 2 ^ n\<close>
    for a :: "'a word" and m n :: nat
    by transfer (auto simp add: not_less take_bit_drop_bit ac_simps simp flip: take_bit_eq_mod drop_bit_eq_div split: split_min_lin)
  show \<open>even ((2 ^ m - 1) div (2::'a word) ^ n) \<longleftrightarrow> 2 ^ n = (0::'a word) \<or> m \<le> n\<close>
    for m n :: nat
    by transfer (auto simp add: take_bit_of_mask even_mask_div_iff)
  show \<open>even (a * 2 ^ m div 2 ^ n) \<longleftrightarrow> n < m \<or> (2::'a word) ^ n = 0 \<or> m \<le> n \<and> even (a div 2 ^ (n - m))\<close>
    for a :: \<open>'a word\<close> and m n :: nat
  proof transfer
    show \<open>even (take_bit LENGTH('a) (k * 2 ^ m) div take_bit LENGTH('a) (2 ^ n)) \<longleftrightarrow>
      n < m
      \<or> take_bit LENGTH('a) ((2::int) ^ n) = take_bit LENGTH('a) 0
      \<or> (m \<le> n \<and> even (take_bit LENGTH('a) k div take_bit LENGTH('a) (2 ^ (n - m))))\<close>
    for m n :: nat and k l :: int
      by (auto simp flip: take_bit_eq_mod drop_bit_eq_div push_bit_eq_mult
        simp add: div_push_bit_of_1_eq_drop_bit drop_bit_take_bit drop_bit_push_bit_int [of n m])
  qed
qed

end

instantiation word :: (len) semiring_bit_shifts
begin

lift_definition push_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is push_bit
proof -
  show \<open>take_bit LENGTH('a) (push_bit n k) = take_bit LENGTH('a) (push_bit n l)\<close>
    if \<open>take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close> for k l :: int and n :: nat
  proof -
    from that
    have \<open>take_bit (LENGTH('a) - n) (take_bit LENGTH('a) k)
      = take_bit (LENGTH('a) - n) (take_bit LENGTH('a) l)\<close>
      by simp
    moreover have \<open>min (LENGTH('a) - n) LENGTH('a) = LENGTH('a) - n\<close>
      by simp
    ultimately show ?thesis
      by (simp add: take_bit_push_bit)
  qed
qed

lift_definition drop_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>n. drop_bit n \<circ> take_bit LENGTH('a)\<close>
  by (simp add: take_bit_eq_mod)

lift_definition take_bit_word :: \<open>nat \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>n. take_bit (min LENGTH('a) n)\<close>
  by (simp add: ac_simps) (simp only: flip: take_bit_take_bit)

instance proof
  show \<open>push_bit n a = a * 2 ^ n\<close> for n :: nat and a :: \<open>'a word\<close>
    by transfer (simp add: push_bit_eq_mult)
  show \<open>drop_bit n a = a div 2 ^ n\<close> for n :: nat and a :: \<open>'a word\<close>
    by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit)
  show \<open>take_bit n a = a mod 2 ^ n\<close> for n :: nat and a :: \<open>'a word\<close>
    by transfer (auto simp flip: take_bit_eq_mod)
qed

end

lemma bit_word_eqI:
  \<open>a = b\<close> if \<open>\<And>n. n \<le> LENGTH('a) \<Longrightarrow> bit a n \<longleftrightarrow> bit b n\<close>
  for a b :: \<open>'a::len word\<close>
  using that by transfer (auto simp add: nat_less_le bit_eq_iff bit_take_bit_iff)

lemma bit_imp_le_length:
  \<open>n < LENGTH('a)\<close> if \<open>bit w n\<close>
    for w :: \<open>'a::len word\<close>
  using that by transfer simp

lemma not_bit_length [simp]:
  \<open>\<not> bit w LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  by transfer simp

lemma take_bit_length_eq [simp]:
  \<open>take_bit LENGTH('a) w = w\<close> for w :: \<open>'a::len word\<close>
  by transfer simp

lemma bit_word_of_int_iff:
  \<open>bit (word_of_int k :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> bit k n\<close>
  by transfer rule

lemma bit_uint_iff:
  \<open>bit (uint w) n \<longleftrightarrow> n < LENGTH('a) \<and> bit w n\<close>
    for w :: \<open>'a::len word\<close>
  by transfer (simp add: bit_take_bit_iff)

lemma bit_sint_iff:
  \<open>bit (sint w) n \<longleftrightarrow> n \<ge> LENGTH('a) \<and> bit w (LENGTH('a) - 1) \<or> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp
  apply (simp add: sint_uint nth_sbintr not_less bit_uint_iff not_le Suc_le_eq)
  apply (auto simp add: le_less dest: bit_imp_le_length)
  done

lemma bit_word_ucast_iff:
  \<open>bit (ucast w :: 'b::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> n < LENGTH('b) \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: ucast_def bit_word_of_int_iff bit_uint_iff ac_simps)

lemma bit_word_scast_iff:
  \<open>bit (scast w :: 'b::len word) n \<longleftrightarrow>
    n < LENGTH('b) \<and> (bit w n \<or> LENGTH('a) \<le> n \<and> bit w (LENGTH('a) - Suc 0))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: scast_def bit_word_of_int_iff bit_sint_iff ac_simps)

definition shiftl1 :: "'a::len word \<Rightarrow> 'a word"
  where "shiftl1 w = word_of_int (2 * uint w)"

lemma shiftl1_eq_mult_2:
  \<open>shiftl1 = (*) 2\<close>
  apply (simp add: fun_eq_iff shiftl1_def)
  apply transfer
  apply (simp only: mult_2 take_bit_add)
  apply simp
  done

lemma bit_shiftl1_iff:
  \<open>bit (shiftl1 w) n \<longleftrightarrow> 0 < n \<and> n < LENGTH('a) \<and> bit w (n - 1)\<close>
    for w :: \<open>'a::len word\<close>
  by (simp add: shiftl1_eq_mult_2 bit_double_iff exp_eq_zero_iff not_le) (simp add: ac_simps)

definition shiftr1 :: "'a::len word \<Rightarrow> 'a word"
  \<comment> \<open>shift right as unsigned or as signed, ie logical or arithmetic\<close>
  where "shiftr1 w = word_of_int (bin_rest (uint w))"

lemma shiftr1_eq_div_2:
  \<open>shiftr1 w = w div 2\<close>
  apply (simp add: fun_eq_iff shiftr1_def)
  apply transfer
  apply (auto simp add: not_le dest: less_2_cases)
  done

lemma bit_shiftr1_iff:
  \<open>bit (shiftr1 w) n \<longleftrightarrow> bit w (Suc n)\<close>
    for w :: \<open>'a::len word\<close>
  by (simp add: shiftr1_eq_div_2 bit_Suc)

instantiation word :: (len) ring_bit_operations
begin

lift_definition not_word :: \<open>'a word \<Rightarrow> 'a word\<close>
  is not
  by (simp add: take_bit_not_iff)

lift_definition and_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>and\<close>
  by simp

lift_definition or_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is or
  by simp

lift_definition xor_word ::  \<open>'a word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is xor
  by simp

instance proof
  fix a b :: \<open>'a word\<close> and n :: nat
  show \<open>- a = NOT (a - 1)\<close>
    by transfer (simp add: minus_eq_not_minus_1)
  show \<open>bit (NOT a) n \<longleftrightarrow> (2 :: 'a word) ^ n \<noteq> 0 \<and> \<not> bit a n\<close>
    by transfer (simp add: bit_not_iff)
  show \<open>bit (a AND b) n \<longleftrightarrow> bit a n \<and> bit b n\<close>
    by transfer (auto simp add: bit_and_iff)
  show \<open>bit (a OR b) n \<longleftrightarrow> bit a n \<or> bit b n\<close>
    by transfer (auto simp add: bit_or_iff)
  show \<open>bit (a XOR b) n \<longleftrightarrow> bit a n \<noteq> bit b n\<close>
    by transfer (auto simp add: bit_xor_iff)
qed

end

context
  includes lifting_syntax
begin

lemma set_bit_word_transfer:
  \<open>((=) ===> pcr_word ===> pcr_word) set_bit set_bit\<close>
  by (unfold set_bit_def) transfer_prover

lemma unset_bit_word_transfer:
  \<open>((=) ===> pcr_word ===> pcr_word) unset_bit unset_bit\<close>
  by (unfold unset_bit_def) transfer_prover

lemma flip_bit_word_transfer:
  \<open>((=) ===> pcr_word ===> pcr_word) flip_bit flip_bit\<close>
  by (unfold flip_bit_def) transfer_prover

end

instantiation word :: (len) semiring_bit_syntax
begin

definition word_test_bit_def: "test_bit a = bin_nth (uint a)"

definition shiftl_def: "w << n = (shiftl1 ^^ n) w"

definition shiftr_def: "w >> n = (shiftr1 ^^ n) w"

lemma test_bit_word_eq:
  \<open>test_bit w = bit w\<close> for w :: \<open>'a::len word\<close>
  apply (simp add: word_test_bit_def fun_eq_iff)
  apply transfer
  apply (simp add: bit_take_bit_iff)
  done

lemma shiftl_word_eq:
  \<open>w << n = push_bit n w\<close> for w :: \<open>'a::len word\<close>
  by (induction n) (simp_all add: shiftl_def shiftl1_eq_mult_2 push_bit_double)

lemma shiftr_word_eq:
  \<open>w >> n = drop_bit n w\<close> for w :: \<open>'a::len word\<close>
  by (induction n) (simp_all add: shiftr_def shiftr1_eq_div_2 drop_bit_Suc drop_bit_half)

instance by standard
  (simp_all add: fun_eq_iff test_bit_word_eq shiftl_word_eq shiftr_word_eq)

end

lemma bit_shiftl_word_iff:
  \<open>bit (w << m) n \<longleftrightarrow> m \<le> n \<and> n < LENGTH('a) \<and> bit w (n - m)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftl_word_eq bit_push_bit_iff exp_eq_zero_iff not_le)

lemma [code]:
  \<open>push_bit n w = w << n\<close> for w :: \<open>'a::len word\<close>
  by (simp add: shiftl_word_eq)

lemma bit_shiftr_word_iff:
  \<open>bit (w >> m) n \<longleftrightarrow> bit w (m + n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: shiftr_word_eq bit_drop_bit_eq)

lemma [code]:
  \<open>drop_bit n w = w >> n\<close> for w :: \<open>'a::len word\<close>
  by (simp add: shiftr_word_eq)

lemma [code]:
  \<open>take_bit n a = a AND Bit_Operations.mask n\<close> for a :: \<open>'a::len word\<close>
  by (fact take_bit_eq_mask)

lemma [code_abbrev]:
  \<open>push_bit n 1 = (2 :: 'a::len word) ^ n\<close>
  by (fact push_bit_of_1)

lemma [code]:
  shows word_not_def: "NOT (a::'a::len word) = word_of_int (NOT (uint a))"
    and word_and_def: "(a::'a word) AND b = word_of_int (uint a AND uint b)"
    and word_or_def: "(a::'a word) OR b = word_of_int (uint a OR uint b)"
    and word_xor_def: "(a::'a word) XOR b = word_of_int (uint a XOR uint b)"
  by (transfer, simp add: take_bit_not_take_bit)+

definition setBit :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word"
  where \<open>setBit w n = Bit_Operations.set_bit n w\<close>

lemma bit_setBit_iff:
  \<open>bit (setBit w m) n \<longleftrightarrow> (m = n \<and> n < LENGTH('a) \<or> bit w n)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: setBit_def bit_set_bit_iff exp_eq_zero_iff not_le ac_simps)

definition clearBit :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word"
  where \<open>clearBit w n = unset_bit n w\<close>

lemma bit_clearBit_iff:
  \<open>bit (clearBit w m) n \<longleftrightarrow> m \<noteq> n \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: clearBit_def bit_unset_bit_iff ac_simps)

definition even_word :: \<open>'a::len word \<Rightarrow> bool\<close>
  where [code_abbrev]: \<open>even_word = even\<close>

lemma even_word_iff [code]:
  \<open>even_word a \<longleftrightarrow> a AND 1 = 0\<close>
  by (simp add: and_one_eq even_iff_mod_2_eq_zero even_word_def)

lemma bit_word_iff_drop_bit_and [code]:
  \<open>bit a n \<longleftrightarrow> drop_bit n a AND 1 = 1\<close> for a :: \<open>'a::len word\<close>
  by (simp add: bit_iff_odd_drop_bit odd_iff_mod_2_eq_one and_one_eq)


subsection \<open>Shift operations\<close>

definition sshiftr1 :: "'a::len word \<Rightarrow> 'a word"
  where "sshiftr1 w = word_of_int (bin_rest (sint w))"

definition bshiftr1 :: "bool \<Rightarrow> 'a::len word \<Rightarrow> 'a word"
  where "bshiftr1 b w = of_bl (b # butlast (to_bl w))"

definition sshiftr :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word"  (infixl ">>>" 55)
  where "w >>> n = (sshiftr1 ^^ n) w"

definition mask :: "nat \<Rightarrow> 'a::len word"
  where "mask n = (1 << n) - 1"


subsection \<open>Rotation\<close>

definition rotater1 :: "'a list \<Rightarrow> 'a list"
  where "rotater1 ys =
    (case ys of [] \<Rightarrow> [] | x # xs \<Rightarrow> last ys # butlast ys)"

definition rotater :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "rotater n = rotater1 ^^ n"

definition word_rotr :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  where "word_rotr n w = of_bl (rotater n (to_bl w))"

definition word_rotl :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  where "word_rotl n w = of_bl (rotate n (to_bl w))"

definition word_roti :: "int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
  where "word_roti i w =
    (if i \<ge> 0 then word_rotr (nat i) w else word_rotl (nat (- i)) w)"


subsection \<open>Split and cat operations\<close>

definition word_cat :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word"
  where "word_cat a b = word_of_int (bin_cat (uint a) (LENGTH('b)) (uint b))"

lemma word_cat_eq:
  \<open>(word_cat v w :: 'c::len word) = push_bit LENGTH('b) (ucast v) + ucast w\<close>
  for v :: \<open>'a::len word\<close> and w :: \<open>'b::len word\<close>
  apply (simp add: word_cat_def bin_cat_eq_push_bit_add_take_bit ucast_def)
  apply transfer apply simp
  done

lemma bit_word_cat_iff:
  \<open>bit (word_cat v w :: 'c::len word) n \<longleftrightarrow> n < LENGTH('c) \<and> (if n < LENGTH('b) then bit w n else bit v (n - LENGTH('b)))\<close> 
  for v :: \<open>'a::len word\<close> and w :: \<open>'b::len word\<close>
  by (auto simp add: word_cat_def bit_word_of_int_iff bin_nth_cat bit_uint_iff not_less bit_imp_le_length)

definition word_split :: "'a::len word \<Rightarrow> 'b::len word \<times> 'c::len word"
  where "word_split a =
    (case bin_split (LENGTH('c)) (uint a) of
      (u, v) \<Rightarrow> (word_of_int u, word_of_int v))"

definition word_rcat :: "'a::len word list \<Rightarrow> 'b::len word"
  where "word_rcat ws = word_of_int (bin_rcat (LENGTH('a)) (map uint ws))"

definition word_rsplit :: "'a::len word \<Rightarrow> 'b::len word list"
  where "word_rsplit w = map word_of_int (bin_rsplit (LENGTH('b)) (LENGTH('a), uint w))"

abbreviation (input) max_word :: \<open>'a::len word\<close>
  \<comment> \<open>Largest representable machine integer.\<close>
  where "max_word \<equiv> - 1"


subsection \<open>Theorems about typedefs\<close>

lemma sint_sbintrunc': "sint (word_of_int bin :: 'a word) = sbintrunc (LENGTH('a::len) - 1) bin"
  by (auto simp: sint_uint word_ubin.eq_norm sbintrunc_bintrunc_lt)

lemma uint_sint: "uint w = bintrunc (LENGTH('a)) (sint w)"
  for w :: "'a::len word"
  by (auto simp: sint_uint bintrunc_sbintrunc_le)

lemma bintr_uint: "LENGTH('a) \<le> n \<Longrightarrow> bintrunc n (uint w) = uint w"
  for w :: "'a::len word"
  apply (subst word_ubin.norm_Rep [symmetric])
  apply (simp only: bintrunc_bintrunc_min word_size)
  apply (simp add: min.absorb2)
  done

lemma wi_bintr:
  "LENGTH('a::len) \<le> n \<Longrightarrow>
    word_of_int (bintrunc n w) = (word_of_int w :: 'a word)"
  by (auto simp: word_ubin.norm_eq_iff [symmetric] min.absorb1)

lemma td_ext_sbin:
  "td_ext (sint :: 'a word \<Rightarrow> int) word_of_int (sints (LENGTH('a::len)))
    (sbintrunc (LENGTH('a) - 1))"
  apply (unfold td_ext_def' sint_uint)
  apply (simp add : word_ubin.eq_norm)
  apply (cases "LENGTH('a)")
   apply (auto simp add : sints_def)
  apply (rule sym [THEN trans])
   apply (rule word_ubin.Abs_norm)
  apply (simp only: bintrunc_sbintrunc)
  apply (drule sym)
  apply simp
  done

lemma td_ext_sint:
  "td_ext (sint :: 'a word \<Rightarrow> int) word_of_int (sints (LENGTH('a::len)))
     (\<lambda>w. (w + 2 ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('a) -
         2 ^ (LENGTH('a) - 1))"
  using td_ext_sbin [where ?'a = 'a] by (simp add: no_sbintr_alt2)

text \<open>
  We do \<open>sint\<close> before \<open>sbin\<close>, before \<open>sint\<close> is the user version
  and interpretations do not produce thm duplicates. I.e.
  we get the name \<open>word_sint.Rep_eqD\<close>, but not \<open>word_sbin.Req_eqD\<close>,
  because the latter is the same thm as the former.
\<close>
interpretation word_sint:
  td_ext
    "sint ::'a::len word \<Rightarrow> int"
    word_of_int
    "sints (LENGTH('a::len))"
    "\<lambda>w. (w + 2^(LENGTH('a::len) - 1)) mod 2^LENGTH('a::len) -
      2 ^ (LENGTH('a::len) - 1)"
  by (rule td_ext_sint)

interpretation word_sbin:
  td_ext
    "sint ::'a::len word \<Rightarrow> int"
    word_of_int
    "sints (LENGTH('a::len))"
    "sbintrunc (LENGTH('a::len) - 1)"
  by (rule td_ext_sbin)

lemmas int_word_sint = td_ext_sint [THEN td_ext.eq_norm]

lemmas td_sint = word_sint.td

lemma to_bl_def': "(to_bl :: 'a::len word \<Rightarrow> bool list) = bin_to_bl (LENGTH('a)) \<circ> uint"
  by (auto simp: to_bl_def)

lemma uints_mod: "uints n = range (\<lambda>w. w mod 2 ^ n)"
  by (fact uints_def [unfolded no_bintr_alt1])

lemma word_numeral_alt: "numeral b = word_of_int (numeral b)"
  by (induct b, simp_all only: numeral.simps word_of_int_homs)

declare word_numeral_alt [symmetric, code_abbrev]

lemma word_neg_numeral_alt: "- numeral b = word_of_int (- numeral b)"
  by (simp only: word_numeral_alt wi_hom_neg)

declare word_neg_numeral_alt [symmetric, code_abbrev]

lemma uint_bintrunc [simp]:
  "uint (numeral bin :: 'a word) =
    bintrunc (LENGTH('a::len)) (numeral bin)"
  unfolding word_numeral_alt by (rule word_ubin.eq_norm)

lemma uint_bintrunc_neg [simp]:
  "uint (- numeral bin :: 'a word) = bintrunc (LENGTH('a::len)) (- numeral bin)"
  by (simp only: word_neg_numeral_alt word_ubin.eq_norm)

lemma sint_sbintrunc [simp]:
  "sint (numeral bin :: 'a word) = sbintrunc (LENGTH('a::len) - 1) (numeral bin)"
  by (simp only: word_numeral_alt word_sbin.eq_norm)

lemma sint_sbintrunc_neg [simp]:
  "sint (- numeral bin :: 'a word) = sbintrunc (LENGTH('a::len) - 1) (- numeral bin)"
  by (simp only: word_neg_numeral_alt word_sbin.eq_norm)

lemma unat_bintrunc [simp]:
  "unat (numeral bin :: 'a::len word) = nat (bintrunc (LENGTH('a)) (numeral bin))"
  by (simp only: unat_def uint_bintrunc)

lemma unat_bintrunc_neg [simp]:
  "unat (- numeral bin :: 'a::len word) = nat (bintrunc (LENGTH('a)) (- numeral bin))"
  by (simp only: unat_def uint_bintrunc_neg)

lemma size_0_eq: "size w = 0 \<Longrightarrow> v = w"
  for v w :: "'a::len word"
  apply (unfold word_size)
  apply (rule word_uint.Rep_eqD)
  apply (rule box_equals)
    defer
    apply (rule word_ubin.norm_Rep)+
  apply simp
  done

lemma uint_ge_0 [iff]: "0 \<le> uint x"
  for x :: "'a::len word"
  using word_uint.Rep [of x] by (simp add: uints_num)

lemma uint_lt2p [iff]: "uint x < 2 ^ LENGTH('a)"
  for x :: "'a::len word"
  using word_uint.Rep [of x] by (simp add: uints_num)

lemma word_exp_length_eq_0 [simp]:
  \<open>(2 :: 'a::len word) ^ LENGTH('a) = 0\<close>
  by transfer (simp add: bintrunc_mod2p)

lemma sint_ge: "- (2 ^ (LENGTH('a) - 1)) \<le> sint x"
  for x :: "'a::len word"
  using word_sint.Rep [of x] by (simp add: sints_num)

lemma sint_lt: "sint x < 2 ^ (LENGTH('a) - 1)"
  for x :: "'a::len word"
  using word_sint.Rep [of x] by (simp add: sints_num)

lemma sign_uint_Pls [simp]: "bin_sign (uint x) = 0"
  by (simp add: sign_Pls_ge_0)

lemma uint_m2p_neg: "uint x - 2 ^ LENGTH('a) < 0"
  for x :: "'a::len word"
  by (simp only: diff_less_0_iff_less uint_lt2p)

lemma uint_m2p_not_non_neg: "\<not> 0 \<le> uint x - 2 ^ LENGTH('a)"
  for x :: "'a::len word"
  by (simp only: not_le uint_m2p_neg)

lemma lt2p_lem: "LENGTH('a) \<le> n \<Longrightarrow> uint w < 2 ^ n"
  for w :: "'a::len word"
  by (metis bintr_lt2p bintr_uint)

lemma uint_le_0_iff [simp]: "uint x \<le> 0 \<longleftrightarrow> uint x = 0"
  by (fact uint_ge_0 [THEN leD, THEN antisym_conv1])

lemma uint_nat: "uint w = int (unat w)"
  by (auto simp: unat_def)

lemma uint_numeral: "uint (numeral b :: 'a::len word) = numeral b mod 2 ^ LENGTH('a)"
  by (simp only: word_numeral_alt int_word_uint)

lemma uint_neg_numeral: "uint (- numeral b :: 'a::len word) = - numeral b mod 2 ^ LENGTH('a)"
  by (simp only: word_neg_numeral_alt int_word_uint)

lemma unat_numeral: "unat (numeral b :: 'a::len word) = numeral b mod 2 ^ LENGTH('a)"
  apply (unfold unat_def)
  apply (clarsimp simp only: uint_numeral)
  apply (rule nat_mod_distrib [THEN trans])
    apply (rule zero_le_numeral)
   apply (simp_all add: nat_power_eq)
  done

lemma sint_numeral:
  "sint (numeral b :: 'a::len word) =
    (numeral b +
      2 ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('a) -
      2 ^ (LENGTH('a) - 1)"
  unfolding word_numeral_alt by (rule int_word_sint)

lemma word_of_int_0 [simp, code_post]: "word_of_int 0 = 0"
  unfolding word_0_wi ..

lemma word_of_int_1 [simp, code_post]: "word_of_int 1 = 1"
  unfolding word_1_wi ..

lemma word_of_int_neg_1 [simp]: "word_of_int (- 1) = - 1"
  by (simp add: wi_hom_syms)

lemma word_of_int_numeral [simp] : "(word_of_int (numeral bin) :: 'a::len word) = numeral bin"
  by (simp only: word_numeral_alt)

lemma word_of_int_neg_numeral [simp]:
  "(word_of_int (- numeral bin) :: 'a::len word) = - numeral bin"
  by (simp only: word_numeral_alt wi_hom_syms)

lemma word_int_case_wi:
  "word_int_case f (word_of_int i :: 'b word) = f (i mod 2 ^ LENGTH('b::len))"
  by (simp add: word_int_case_def word_uint.eq_norm)

lemma word_int_split:
  "P (word_int_case f x) =
    (\<forall>i. x = (word_of_int i :: 'b::len word) \<and> 0 \<le> i \<and> i < 2 ^ LENGTH('b) \<longrightarrow> P (f i))"
  by (auto simp: word_int_case_def word_uint.eq_norm)

lemma word_int_split_asm:
  "P (word_int_case f x) =
    (\<nexists>n. x = (word_of_int n :: 'b::len word) \<and> 0 \<le> n \<and> n < 2 ^ LENGTH('b::len) \<and> \<not> P (f n))"
  by (auto simp: word_int_case_def word_uint.eq_norm)

lemmas uint_range' = word_uint.Rep [unfolded uints_num mem_Collect_eq]
lemmas sint_range' = word_sint.Rep [unfolded One_nat_def sints_num mem_Collect_eq]

lemma uint_range_size: "0 \<le> uint w \<and> uint w < 2 ^ size w"
  unfolding word_size by (rule uint_range')

lemma sint_range_size: "- (2 ^ (size w - Suc 0)) \<le> sint w \<and> sint w < 2 ^ (size w - Suc 0)"
  unfolding word_size by (rule sint_range')

lemma sint_above_size: "2 ^ (size w - 1) \<le> x \<Longrightarrow> sint w < x"
  for w :: "'a::len word"
  unfolding word_size by (rule less_le_trans [OF sint_lt])

lemma sint_below_size: "x \<le> - (2 ^ (size w - 1)) \<Longrightarrow> x \<le> sint w"
  for w :: "'a::len word"
  unfolding word_size by (rule order_trans [OF _ sint_ge])


subsection \<open>Testing bits\<close>

lemma test_bit_eq_iff: "test_bit u = test_bit v \<longleftrightarrow> u = v"
  for u v :: "'a::len word"
  unfolding word_test_bit_def by (simp add: bin_nth_eq_iff)

lemma test_bit_size [rule_format] : "w !! n \<longrightarrow> n < size w"
  for w :: "'a::len word"
  apply (unfold word_test_bit_def)
  apply (subst word_ubin.norm_Rep [symmetric])
  apply (simp only: nth_bintr word_size)
  apply fast
  done

lemma word_eq_iff: "x = y \<longleftrightarrow> (\<forall>n<LENGTH('a). x !! n = y !! n)" (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  for x y :: "'a::len word"
proof
  assume ?P
  then show ?Q
    by simp
next
  assume ?Q
  then have *: \<open>bit (uint x) n \<longleftrightarrow> bit (uint y) n\<close> if \<open>n < LENGTH('a)\<close> for n
    using that by (simp add: word_test_bit_def)
  show ?P
  proof (rule word_uint_eqI, rule bit_eqI, rule iffI)
    fix n
    assume \<open>bit (uint x) n\<close>
    then have \<open>n < LENGTH('a)\<close>
      by (simp add: bit_take_bit_iff uint.rep_eq)
    with * \<open>bit (uint x) n\<close>
    show \<open>bit (uint y) n\<close>
      by simp
  next
    fix n
    assume \<open>bit (uint y) n\<close>
    then have \<open>n < LENGTH('a)\<close>
      by (simp add: bit_take_bit_iff uint.rep_eq)
    with * \<open>bit (uint y) n\<close>
    show \<open>bit (uint x) n\<close>
      by simp
  qed
qed  

lemma word_eqI: "(\<And>n. n < size u \<longrightarrow> u !! n = v !! n) \<Longrightarrow> u = v"
  for u :: "'a::len word"
  by (simp add: word_size word_eq_iff)

lemma word_eqD: "u = v \<Longrightarrow> u !! x = v !! x"
  for u v :: "'a::len word"
  by simp

lemma test_bit_bin': "w !! n \<longleftrightarrow> n < size w \<and> bin_nth (uint w) n"
  by (simp add: word_test_bit_def word_size nth_bintr [symmetric])

lemmas test_bit_bin = test_bit_bin' [unfolded word_size]

lemma bin_nth_uint_imp: "bin_nth (uint w) n \<Longrightarrow> n < LENGTH('a)"
  for w :: "'a::len word"
  apply (rule nth_bintr [THEN iffD1, THEN conjunct1])
  apply (subst word_ubin.norm_Rep)
  apply assumption
  done

lemma bin_nth_sint:
  "LENGTH('a) \<le> n \<Longrightarrow>
    bin_nth (sint w) n = bin_nth (sint w) (LENGTH('a) - 1)"
  for w :: "'a::len word"
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (auto simp add: nth_sbintr)
  done

\<comment> \<open>type definitions theorem for in terms of equivalent bool list\<close>
lemma td_bl:
  "type_definition
    (to_bl :: 'a::len word \<Rightarrow> bool list)
    of_bl
    {bl. length bl = LENGTH('a)}"
  apply (unfold type_definition_def of_bl_def to_bl_def)
  apply (simp add: word_ubin.eq_norm)
  apply safe
  apply (drule sym)
  apply simp
  done

interpretation word_bl:
  type_definition
    "to_bl :: 'a::len word \<Rightarrow> bool list"
    of_bl
    "{bl. length bl = LENGTH('a::len)}"
  by (fact td_bl)

lemmas word_bl_Rep' = word_bl.Rep [unfolded mem_Collect_eq, iff]

lemma word_size_bl: "size w = size (to_bl w)"
  by (auto simp: word_size)

lemma to_bl_use_of_bl: "to_bl w = bl \<longleftrightarrow> w = of_bl bl \<and> length bl = length (to_bl w)"
  by (fastforce elim!: word_bl.Abs_inverse [unfolded mem_Collect_eq])

lemma length_bl_gt_0 [iff]: "0 < length (to_bl x)"
  for x :: "'a::len word"
  unfolding word_bl_Rep' by (rule len_gt_0)

lemma bl_not_Nil [iff]: "to_bl x \<noteq> []"
  for x :: "'a::len word"
  by (fact length_bl_gt_0 [unfolded length_greater_0_conv])

lemma length_bl_neq_0 [iff]: "length (to_bl x) \<noteq> 0"
  for x :: "'a::len word"
  by (fact length_bl_gt_0 [THEN gr_implies_not0])

lemma hd_bl_sign_sint: "hd (to_bl w) = (bin_sign (sint w) = -1)"
  apply (unfold to_bl_def sint_uint)
  apply (rule trans [OF _ bl_sbin_sign])
  apply simp
  done

lemma of_bl_drop':
  "lend = length bl - LENGTH('a::len) \<Longrightarrow>
    of_bl (drop lend bl) = (of_bl bl :: 'a word)"
  by (auto simp: of_bl_def trunc_bl2bin [symmetric])

lemma test_bit_of_bl:
  "(of_bl bl::'a::len word) !! n = (rev bl ! n \<and> n < LENGTH('a) \<and> n < length bl)"
  by (auto simp add: of_bl_def word_test_bit_def word_size
      word_ubin.eq_norm nth_bintr bin_nth_of_bl)

lemma bit_of_bl_iff:
  \<open>bit (of_bl bs :: 'a word) n \<longleftrightarrow> rev bs ! n \<and> n < LENGTH('a::len) \<and> n < length bs\<close>
  using test_bit_of_bl [of bs n] by (simp add: test_bit_word_eq)

lemma no_of_bl: "(numeral bin ::'a::len word) = of_bl (bin_to_bl (LENGTH('a)) (numeral bin))"
  by (simp add: of_bl_def)

lemma uint_bl: "to_bl w = bin_to_bl (size w) (uint w)"
  by (auto simp: word_size to_bl_def)

lemma to_bl_bin: "bl_to_bin (to_bl w) = uint w"
  by (simp add: uint_bl word_size)

lemma to_bl_of_bin: "to_bl (word_of_int bin::'a::len word) = bin_to_bl (LENGTH('a)) bin"
  by (auto simp: uint_bl word_ubin.eq_norm word_size)

lemma to_bl_numeral [simp]:
  "to_bl (numeral bin::'a::len word) =
    bin_to_bl (LENGTH('a)) (numeral bin)"
  unfolding word_numeral_alt by (rule to_bl_of_bin)

lemma to_bl_neg_numeral [simp]:
  "to_bl (- numeral bin::'a::len word) =
    bin_to_bl (LENGTH('a)) (- numeral bin)"
  unfolding word_neg_numeral_alt by (rule to_bl_of_bin)

lemma to_bl_to_bin [simp] : "bl_to_bin (to_bl w) = uint w"
  by (simp add: uint_bl word_size)

lemma uint_bl_bin: "bl_to_bin (bin_to_bl (LENGTH('a)) (uint x)) = uint x"
  for x :: "'a::len word"
  by (rule trans [OF bin_bl_bin word_ubin.norm_Rep])

lemmas bintr_num =
  word_ubin.norm_eq_iff [of "numeral a" "numeral b", symmetric, folded word_numeral_alt] for a b
lemmas sbintr_num =
  word_sbin.norm_eq_iff [of "numeral a" "numeral b", symmetric, folded word_numeral_alt] for a b

lemma num_of_bintr':
  "bintrunc (LENGTH('a::len)) (numeral a) = (numeral b) \<Longrightarrow>
    numeral a = (numeral b :: 'a word)"
  unfolding bintr_num by (erule subst, simp)

lemma num_of_sbintr':
  "sbintrunc (LENGTH('a::len) - 1) (numeral a) = (numeral b) \<Longrightarrow>
    numeral a = (numeral b :: 'a word)"
  unfolding sbintr_num by (erule subst, simp)

lemma num_abs_bintr:
  "(numeral x :: 'a word) =
    word_of_int (bintrunc (LENGTH('a::len)) (numeral x))"
  by (simp only: word_ubin.Abs_norm word_numeral_alt)

lemma num_abs_sbintr:
  "(numeral x :: 'a word) =
    word_of_int (sbintrunc (LENGTH('a::len) - 1) (numeral x))"
  by (simp only: word_sbin.Abs_norm word_numeral_alt)

text \<open>
  \<open>cast\<close> -- note, no arg for new length, as it's determined by type of result,
  thus in \<open>cast w = w\<close>, the type means cast to length of \<open>w\<close>!
\<close>

lemma bit_ucast_iff:
  \<open>Parity.bit (ucast a :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a::len) \<and> Parity.bit a n\<close>
  by (simp add: ucast_def, transfer) (auto simp add: bit_take_bit_iff)

lemma ucast_id: "ucast w = w"
  by (auto simp: ucast_def)

lemma scast_id: "scast w = w"
  by (auto simp: scast_def)

lemma ucast_bl: "ucast w = of_bl (to_bl w)"
  by (auto simp: ucast_def of_bl_def uint_bl word_size)

lemma nth_ucast: "(ucast w::'a::len word) !! n = (w !! n \<and> n < LENGTH('a))"
  by (simp add: ucast_def test_bit_bin word_ubin.eq_norm nth_bintr word_size)
    (fast elim!: bin_nth_uint_imp)

context
  includes lifting_syntax
begin

lemma transfer_rule_mask_word [transfer_rule]:
  \<open>((=) ===> pcr_word) Bit_Operations.mask Bit_Operations.mask\<close>
  by (simp only: mask_eq_exp_minus_1 [abs_def]) transfer_prover

end

lemma ucast_mask_eq:
  \<open>ucast (Bit_Operations.mask n :: 'b word) = Bit_Operations.mask (min LENGTH('b::len) n)\<close>
  by (simp add: bit_eq_iff) (auto simp add: bit_mask_iff bit_ucast_iff exp_eq_zero_iff)

\<comment> \<open>literal u(s)cast\<close>
lemma ucast_bintr [simp]:
  "ucast (numeral w :: 'a::len word) =
    word_of_int (bintrunc (LENGTH('a)) (numeral w))"
  by (simp add: ucast_def)

(* TODO: neg_numeral *)

lemma scast_sbintr [simp]:
  "scast (numeral w ::'a::len word) =
    word_of_int (sbintrunc (LENGTH('a) - Suc 0) (numeral w))"
  by (simp add: scast_def)

lemma source_size: "source_size (c::'a::len word \<Rightarrow> _) = LENGTH('a)"
  unfolding source_size_def word_size Let_def ..

lemma target_size: "target_size (c::_ \<Rightarrow> 'b::len word) = LENGTH('b)"
  unfolding target_size_def word_size Let_def ..

lemma is_down: "is_down c \<longleftrightarrow> LENGTH('b) \<le> LENGTH('a)"
  for c :: "'a::len word \<Rightarrow> 'b::len word"
  by (simp only: is_down_def source_size target_size)

lemma is_up: "is_up c \<longleftrightarrow> LENGTH('a) \<le> LENGTH('b)"
  for c :: "'a::len word \<Rightarrow> 'b::len word"
  by (simp only: is_up_def source_size target_size)

lemmas is_up_down = trans [OF is_up is_down [symmetric]]

lemma down_cast_same [OF refl]: "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc = scast"
  apply (unfold is_down)
  apply safe
  apply (rule ext)
  apply (unfold ucast_def scast_def uint_sint)
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply simp
  done

lemma word_rev_tf:
  "to_bl (of_bl bl::'a::len word) =
    rev (takefill False (LENGTH('a)) (rev bl))"
  by (auto simp: of_bl_def uint_bl bl_bin_bl_rtf word_ubin.eq_norm word_size)

lemma word_rep_drop:
  "to_bl (of_bl bl::'a::len word) =
    replicate (LENGTH('a) - length bl) False @
    drop (length bl - LENGTH('a)) bl"
  by (simp add: word_rev_tf takefill_alt rev_take)

lemma to_bl_ucast:
  "to_bl (ucast (w::'b::len word) ::'a::len word) =
    replicate (LENGTH('a) - LENGTH('b)) False @
    drop (LENGTH('b) - LENGTH('a)) (to_bl w)"
  apply (unfold ucast_bl)
  apply (rule trans)
   apply (rule word_rep_drop)
  apply simp
  done

lemma ucast_up_app [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc + n = target_size uc \<Longrightarrow>
    to_bl (uc w) = replicate n False @ (to_bl w)"
  by (auto simp add : source_size target_size to_bl_ucast)

lemma ucast_down_drop [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow>
    to_bl (uc w) = drop n (to_bl w)"
  by (auto simp add : source_size target_size to_bl_ucast)

lemma scast_down_drop [OF refl]:
  "sc = scast \<Longrightarrow> source_size sc = target_size sc + n \<Longrightarrow>
    to_bl (sc w) = drop n (to_bl w)"
  apply (subgoal_tac "sc = ucast")
   apply safe
   apply simp
   apply (erule ucast_down_drop)
  apply (rule down_cast_same [symmetric])
  apply (simp add : source_size target_size is_down)
  done

lemma sint_up_scast [OF refl]: "sc = scast \<Longrightarrow> is_up sc \<Longrightarrow> sint (sc w) = sint w"
  apply (unfold is_up)
  apply safe
  apply (simp add: scast_def word_sbin.eq_norm)
  apply (rule box_equals)
    prefer 3
    apply (rule word_sbin.norm_Rep)
   apply (rule sbintrunc_sbintrunc_l)
   defer
   apply (subst word_sbin.norm_Rep)
   apply (rule refl)
  apply simp
  done

lemma uint_up_ucast [OF refl]: "uc = ucast \<Longrightarrow> is_up uc \<Longrightarrow> uint (uc w) = uint w"
  apply (unfold is_up)
  apply safe
  apply (rule bin_eqI)
  apply (fold word_test_bit_def)
  apply (auto simp add: nth_ucast)
  apply (auto simp add: test_bit_bin)
  done

lemma ucast_up_ucast [OF refl]: "uc = ucast \<Longrightarrow> is_up uc \<Longrightarrow> ucast (uc w) = ucast w"
  apply (simp (no_asm) add: ucast_def)
  apply (clarsimp simp add: uint_up_ucast)
  done

lemma scast_up_scast [OF refl]: "sc = scast \<Longrightarrow> is_up sc \<Longrightarrow> scast (sc w) = scast w"
  apply (simp (no_asm) add: scast_def)
  apply (clarsimp simp add: sint_up_scast)
  done

lemma ucast_of_bl_up [OF refl]: "w = of_bl bl \<Longrightarrow> size bl \<le> size w \<Longrightarrow> ucast w = of_bl bl"
  by (auto simp add : nth_ucast word_size test_bit_of_bl intro!: word_eqI)

lemmas ucast_up_ucast_id = trans [OF ucast_up_ucast ucast_id]
lemmas scast_up_scast_id = trans [OF scast_up_scast scast_id]

lemmas isduu = is_up_down [where c = "ucast", THEN iffD2]
lemmas isdus = is_up_down [where c = "scast", THEN iffD2]
lemmas ucast_down_ucast_id = isduu [THEN ucast_up_ucast_id]
lemmas scast_down_scast_id = isdus [THEN ucast_up_ucast_id]

lemma up_ucast_surj:
  "is_up (ucast :: 'b::len word \<Rightarrow> 'a::len word) \<Longrightarrow>
    surj (ucast :: 'a word \<Rightarrow> 'b word)"
  by (rule surjI) (erule ucast_up_ucast_id)

lemma up_scast_surj:
  "is_up (scast :: 'b::len word \<Rightarrow> 'a::len word) \<Longrightarrow>
    surj (scast :: 'a word \<Rightarrow> 'b word)"
  by (rule surjI) (erule scast_up_scast_id)

lemma down_scast_inj:
  "is_down (scast :: 'b::len word \<Rightarrow> 'a::len word) \<Longrightarrow>
    inj_on (ucast :: 'a word \<Rightarrow> 'b word) A"
  by (rule inj_on_inverseI, erule scast_down_scast_id)

lemma down_ucast_inj:
  "is_down (ucast :: 'b::len word \<Rightarrow> 'a::len word) \<Longrightarrow>
    inj_on (ucast :: 'a word \<Rightarrow> 'b word) A"
  by (rule inj_on_inverseI) (erule ucast_down_ucast_id)

lemma of_bl_append_same: "of_bl (X @ to_bl w) = w"
  by (rule word_bl.Rep_eqD) (simp add: word_rep_drop)

lemma ucast_down_wi [OF refl]: "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc (word_of_int x) = word_of_int x"
  apply (unfold is_down)
  apply (clarsimp simp add: ucast_def word_ubin.eq_norm)
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply (erule bintrunc_bintrunc_ge)
  done

lemma ucast_down_no [OF refl]: "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc (numeral bin) = numeral bin"
  unfolding word_numeral_alt by clarify (rule ucast_down_wi)

lemma ucast_down_bl [OF refl]: "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc (of_bl bl) = of_bl bl"
  unfolding of_bl_def by clarify (erule ucast_down_wi)

lemmas test_bit_def' = word_test_bit_def [THEN fun_cong]

lemmas word_log_defs = word_and_def word_or_def word_xor_def word_not_def

lemma bit_last_iff:
  \<open>bit w (LENGTH('a) - Suc 0) \<longleftrightarrow> sint w < 0\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  for w :: \<open>'a::len word\<close>
proof -
  have \<open>?P \<longleftrightarrow> bit (uint w) (LENGTH('a) - Suc 0)\<close>
    by (simp add: bit_uint_iff)
  also have \<open>\<dots> \<longleftrightarrow> ?Q\<close>
    by (simp add: sint_uint)
  finally show ?thesis .
qed

lemma drop_bit_eq_zero_iff_not_bit_last:
  \<open>drop_bit (LENGTH('a) - Suc 0) w = 0 \<longleftrightarrow> \<not> bit w (LENGTH('a) - Suc 0)\<close>
  for w :: "'a::len word"
    apply (cases \<open>LENGTH('a)\<close>)
    apply simp_all
    apply (simp add: bit_iff_odd_drop_bit)
    apply transfer
    apply (simp add: take_bit_drop_bit)
    apply (auto simp add: drop_bit_eq_div take_bit_eq_mod min_def)
    apply (auto elim!: evenE)
    apply (metis div_exp_eq mod_div_trivial mult.commute nonzero_mult_div_cancel_left power_Suc0_right power_add zero_neq_numeral)
    done


subsection \<open>Word Arithmetic\<close>

lemma word_less_alt: "a < b \<longleftrightarrow> uint a < uint b"
  by (fact word_less_def)

lemma signed_linorder: "class.linorder word_sle word_sless"
  by standard (auto simp: word_sle_def word_sless_def)

interpretation signed: linorder "word_sle" "word_sless"
  by (rule signed_linorder)

lemma udvdI: "0 \<le> n \<Longrightarrow> uint b = n * uint a \<Longrightarrow> a udvd b"
  by (auto simp: udvd_def)

lemmas word_div_no [simp] = word_div_def [of "numeral a" "numeral b"] for a b
lemmas word_mod_no [simp] = word_mod_def [of "numeral a" "numeral b"] for a b
lemmas word_less_no [simp] = word_less_def [of "numeral a" "numeral b"] for a b
lemmas word_le_no [simp] = word_le_def [of "numeral a" "numeral b"] for a b
lemmas word_sless_no [simp] = word_sless_def [of "numeral a" "numeral b"] for a b
lemmas word_sle_no [simp] = word_sle_def [of "numeral a" "numeral b"] for a b

lemma word_m1_wi: "- 1 = word_of_int (- 1)"
  by (simp add: word_neg_numeral_alt [of Num.One])

lemma word_0_bl [simp]: "of_bl [] = 0"
  by (simp add: of_bl_def)

lemma word_1_bl: "of_bl [True] = 1"
  by (simp add: of_bl_def bl_to_bin_def)

lemma uint_eq_0 [simp]: "uint 0 = 0"
  unfolding word_0_wi word_ubin.eq_norm by simp

lemma of_bl_0 [simp]: "of_bl (replicate n False) = 0"
  by (simp add: of_bl_def bl_to_bin_rep_False)

lemma to_bl_0 [simp]: "to_bl (0::'a::len word) = replicate (LENGTH('a)) False"
  by (simp add: uint_bl word_size bin_to_bl_zero)

lemma uint_0_iff: "uint x = 0 \<longleftrightarrow> x = 0"
  by (simp add: word_uint_eq_iff)

lemma unat_0_iff: "unat x = 0 \<longleftrightarrow> x = 0"
  by (auto simp: unat_def nat_eq_iff uint_0_iff)

lemma unat_0 [simp]: "unat 0 = 0"
  by (auto simp: unat_def)

lemma size_0_same': "size w = 0 \<Longrightarrow> w = v"
  for v w :: "'a::len word"
  apply (unfold word_size)
  apply (rule box_equals)
    defer
    apply (rule word_uint.Rep_inverse)+
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply simp
  done

lemmas size_0_same = size_0_same' [unfolded word_size]

lemmas unat_eq_0 = unat_0_iff
lemmas unat_eq_zero = unat_0_iff

lemma unat_gt_0: "0 < unat x \<longleftrightarrow> x \<noteq> 0"
  by (auto simp: unat_0_iff [symmetric])

lemma ucast_0 [simp]: "ucast 0 = 0"
  by (simp add: ucast_def)

lemma sint_0 [simp]: "sint 0 = 0"
  by (simp add: sint_uint)

lemma scast_0 [simp]: "scast 0 = 0"
  by (simp add: scast_def)

lemma sint_n1 [simp] : "sint (- 1) = - 1"
  by (simp only: word_m1_wi word_sbin.eq_norm) simp

lemma scast_n1 [simp]: "scast (- 1) = - 1"
  by (simp add: scast_def)

lemma uint_1 [simp]: "uint (1::'a::len word) = 1"
  by (simp only: word_1_wi word_ubin.eq_norm) simp

lemma unat_1 [simp]: "unat (1::'a::len word) = 1"
  by (simp add: unat_def)

lemma ucast_1 [simp]: "ucast (1::'a::len word) = 1"
  by (simp add: ucast_def)

\<comment> \<open>now, to get the weaker results analogous to \<open>word_div\<close>/\<open>mod_def\<close>\<close>


subsection \<open>Transferring goals from words to ints\<close>

lemma word_ths:
  shows word_succ_p1: "word_succ a = a + 1"
    and word_pred_m1: "word_pred a = a - 1"
    and word_pred_succ: "word_pred (word_succ a) = a"
    and word_succ_pred: "word_succ (word_pred a) = a"
    and word_mult_succ: "word_succ a * b = b + a * b"
  by (transfer, simp add: algebra_simps)+

lemma uint_cong: "x = y \<Longrightarrow> uint x = uint y"
  by simp

lemma uint_word_ariths:
  fixes a b :: "'a::len word"
  shows "uint (a + b) = (uint a + uint b) mod 2 ^ LENGTH('a::len)"
    and "uint (a - b) = (uint a - uint b) mod 2 ^ LENGTH('a)"
    and "uint (a * b) = uint a * uint b mod 2 ^ LENGTH('a)"
    and "uint (- a) = - uint a mod 2 ^ LENGTH('a)"
    and "uint (word_succ a) = (uint a + 1) mod 2 ^ LENGTH('a)"
    and "uint (word_pred a) = (uint a - 1) mod 2 ^ LENGTH('a)"
    and "uint (0 :: 'a word) = 0 mod 2 ^ LENGTH('a)"
    and "uint (1 :: 'a word) = 1 mod 2 ^ LENGTH('a)"
  by (simp_all add: word_arith_wis [THEN trans [OF uint_cong int_word_uint]])

lemma uint_word_arith_bintrs:
  fixes a b :: "'a::len word"
  shows "uint (a + b) = bintrunc (LENGTH('a)) (uint a + uint b)"
    and "uint (a - b) = bintrunc (LENGTH('a)) (uint a - uint b)"
    and "uint (a * b) = bintrunc (LENGTH('a)) (uint a * uint b)"
    and "uint (- a) = bintrunc (LENGTH('a)) (- uint a)"
    and "uint (word_succ a) = bintrunc (LENGTH('a)) (uint a + 1)"
    and "uint (word_pred a) = bintrunc (LENGTH('a)) (uint a - 1)"
    and "uint (0 :: 'a word) = bintrunc (LENGTH('a)) 0"
    and "uint (1 :: 'a word) = bintrunc (LENGTH('a)) 1"
  by (simp_all add: uint_word_ariths bintrunc_mod2p)

lemma sint_word_ariths:
  fixes a b :: "'a::len word"
  shows "sint (a + b) = sbintrunc (LENGTH('a) - 1) (sint a + sint b)"
    and "sint (a - b) = sbintrunc (LENGTH('a) - 1) (sint a - sint b)"
    and "sint (a * b) = sbintrunc (LENGTH('a) - 1) (sint a * sint b)"
    and "sint (- a) = sbintrunc (LENGTH('a) - 1) (- sint a)"
    and "sint (word_succ a) = sbintrunc (LENGTH('a) - 1) (sint a + 1)"
    and "sint (word_pred a) = sbintrunc (LENGTH('a) - 1) (sint a - 1)"
    and "sint (0 :: 'a word) = sbintrunc (LENGTH('a) - 1) 0"
    and "sint (1 :: 'a word) = sbintrunc (LENGTH('a) - 1) 1"
         apply (simp_all only: word_sbin.inverse_norm [symmetric])
         apply (simp_all add: wi_hom_syms)
   apply transfer apply simp
  apply transfer apply simp
  done

lemmas uint_div_alt = word_div_def [THEN trans [OF uint_cong int_word_uint]]
lemmas uint_mod_alt = word_mod_def [THEN trans [OF uint_cong int_word_uint]]

lemma word_pred_0_n1: "word_pred 0 = word_of_int (- 1)"
  unfolding word_pred_m1 by simp

lemma succ_pred_no [simp]:
    "word_succ (numeral w) = numeral w + 1"
    "word_pred (numeral w) = numeral w - 1"
    "word_succ (- numeral w) = - numeral w + 1"
    "word_pred (- numeral w) = - numeral w - 1"
  by (simp_all add: word_succ_p1 word_pred_m1)

lemma word_sp_01 [simp]:
  "word_succ (- 1) = 0 \<and> word_succ 0 = 1 \<and> word_pred 0 = - 1 \<and> word_pred 1 = 0"
  by (simp_all add: word_succ_p1 word_pred_m1)

\<comment> \<open>alternative approach to lifting arithmetic equalities\<close>
lemma word_of_int_Ex: "\<exists>y. x = word_of_int y"
  by (rule_tac x="uint x" in exI) simp


subsection \<open>Order on fixed-length words\<close>

lemma word_zero_le [simp]: "0 \<le> y"
  for y :: "'a::len word"
  unfolding word_le_def by auto

lemma word_m1_ge [simp] : "word_pred 0 \<ge> y" (* FIXME: delete *)
  by transfer (simp add: take_bit_minus_one_eq_mask mask_eq_exp_minus_1 bintr_lt2p)

lemma word_n1_ge [simp]: "y \<le> -1"
  for y :: "'a::len word"
  by (fact word_order.extremum)

lemmas word_not_simps [simp] =
  word_zero_le [THEN leD] word_m1_ge [THEN leD] word_n1_ge [THEN leD]

lemma word_gt_0: "0 < y \<longleftrightarrow> 0 \<noteq> y"
  for y :: "'a::len word"
  by (simp add: less_le)

lemmas word_gt_0_no [simp] = word_gt_0 [of "numeral y"] for y

lemma word_sless_alt: "a <s b \<longleftrightarrow> sint a < sint b"
  by (auto simp add: word_sle_def word_sless_def less_le)

lemma word_le_nat_alt: "a \<le> b \<longleftrightarrow> unat a \<le> unat b"
  unfolding unat_def word_le_def
  by (rule nat_le_eq_zle [symmetric]) simp

lemma word_less_nat_alt: "a < b \<longleftrightarrow> unat a < unat b"
  unfolding unat_def word_less_alt
  by (rule nat_less_eq_zless [symmetric]) simp

lemmas unat_mono = word_less_nat_alt [THEN iffD1]

instance word :: (len) wellorder
proof
  fix P :: "'a word \<Rightarrow> bool" and a
  assume *: "(\<And>b. (\<And>a. a < b \<Longrightarrow> P a) \<Longrightarrow> P b)"
  have "wf (measure unat)" ..
  moreover have "{(a, b :: ('a::len) word). a < b} \<subseteq> measure unat"
    by (auto simp add: word_less_nat_alt)
  ultimately have "wf {(a, b :: ('a::len) word). a < b}"
    by (rule wf_subset)
  then show "P a" using *
    by induction blast
qed

lemma wi_less:
  "(word_of_int n < (word_of_int m :: 'a::len word)) =
    (n mod 2 ^ LENGTH('a) < m mod 2 ^ LENGTH('a))"
  unfolding word_less_alt by (simp add: word_uint.eq_norm)

lemma wi_le:
  "(word_of_int n \<le> (word_of_int m :: 'a::len word)) =
    (n mod 2 ^ LENGTH('a) \<le> m mod 2 ^ LENGTH('a))"
  unfolding word_le_def by (simp add: word_uint.eq_norm)

lemma udvd_nat_alt: "a udvd b \<longleftrightarrow> (\<exists>n\<ge>0. unat b = n * unat a)"
  apply (unfold udvd_def)
  apply safe
   apply (simp add: unat_def nat_mult_distrib)
  apply (simp add: uint_nat)
  apply (rule exI)
  apply safe
   prefer 2
   apply (erule notE)
   apply (rule refl)
  apply force
  done

lemma udvd_iff_dvd: "x udvd y \<longleftrightarrow> unat x dvd unat y"
  unfolding dvd_def udvd_nat_alt by force

lemma unat_minus_one:
  assumes "w \<noteq> 0"
  shows "unat (w - 1) = unat w - 1"
proof -
  have "0 \<le> uint w" by (fact uint_nonnegative)
  moreover from assms have "0 \<noteq> uint w"
    by (simp add: uint_0_iff)
  ultimately have "1 \<le> uint w"
    by arith
  from uint_lt2p [of w] have "uint w - 1 < 2 ^ LENGTH('a)"
    by arith
  with \<open>1 \<le> uint w\<close> have "(uint w - 1) mod 2 ^ LENGTH('a) = uint w - 1"
    by (auto intro: mod_pos_pos_trivial)
  with \<open>1 \<le> uint w\<close> have "nat ((uint w - 1) mod 2 ^ LENGTH('a)) = nat (uint w) - 1"
    by auto
  then show ?thesis
    by (simp only: unat_def int_word_uint word_arith_wis mod_diff_right_eq)
qed

lemma measure_unat: "p \<noteq> 0 \<Longrightarrow> unat (p - 1) < unat p"
  by (simp add: unat_minus_one) (simp add: unat_0_iff [symmetric])

lemmas uint_add_ge0 [simp] = add_nonneg_nonneg [OF uint_ge_0 uint_ge_0]
lemmas uint_mult_ge0 [simp] = mult_nonneg_nonneg [OF uint_ge_0 uint_ge_0]

lemma uint_sub_lt2p [simp]: "uint x - uint y < 2 ^ LENGTH('a)"
  for x :: "'a::len word" and y :: "'b::len word"
  using uint_ge_0 [of y] uint_lt2p [of x] by arith


subsection \<open>Conditions for the addition (etc) of two words to overflow\<close>

lemma uint_add_lem:
  "(uint x + uint y < 2 ^ LENGTH('a)) =
    (uint (x + y) = uint x + uint y)"
  for x y :: "'a::len word"
  by (metis add.right_neutral add_mono_thms_linordered_semiring(1) mod_pos_pos_trivial of_nat_0_le_iff uint_lt2p uint_nat uint_word_ariths(1))

lemma uint_mult_lem:
  "(uint x * uint y < 2 ^ LENGTH('a)) =
    (uint (x * y) = uint x * uint y)"
  for x y :: "'a::len word"
  by (metis mod_pos_pos_trivial uint_lt2p uint_mult_ge0 uint_word_ariths(3))

lemma uint_sub_lem: "uint x \<ge> uint y \<longleftrightarrow> uint (x - y) = uint x - uint y"
  by (metis (mono_tags, hide_lams) diff_ge_0_iff_ge mod_pos_pos_trivial of_nat_0_le_iff take_bit_eq_mod uint_nat uint_sub_lt2p word_sub_wi word_ubin.eq_norm)  find_theorems uint \<open>- _\<close>

lemma uint_add_le: "uint (x + y) \<le> uint x + uint y"
  unfolding uint_word_ariths by (simp add: zmod_le_nonneg_dividend) 

lemma uint_sub_ge: "uint (x - y) \<ge> uint x - uint y"
  unfolding uint_word_ariths by (simp add: int_mod_ge)
  
lemma mod_add_if_z:
  "x < z \<Longrightarrow> y < z \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> z \<Longrightarrow>
    (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  for x y z :: int
  apply (auto simp add: not_less)
  apply (rule antisym)
  apply (metis diff_ge_0_iff_ge minus_mod_self2 zmod_le_nonneg_dividend)
   apply (simp only: flip: minus_mod_self2 [of \<open>x + y\<close> z])
  apply (rule int_mod_ge)
   apply simp_all
  done

lemma uint_plus_if':
  "uint (a + b) =
    (if uint a + uint b < 2 ^ LENGTH('a) then uint a + uint b
     else uint a + uint b - 2 ^ LENGTH('a))"
  for a b :: "'a::len word"
  using mod_add_if_z [of "uint a" _ "uint b"] by (simp add: uint_word_ariths)

lemma mod_sub_if_z:
  "x < z \<Longrightarrow> y < z \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> z \<Longrightarrow>
    (x - y) mod z = (if y \<le> x then x - y else x - y + z)"
  for x y z :: int
  apply (auto simp add: not_le)
  apply (rule antisym)
   apply (simp only: flip: mod_add_self2 [of \<open>x - y\<close> z])
   apply (rule zmod_le_nonneg_dividend)
   apply simp
  apply (metis add.commute add.right_neutral add_le_cancel_left diff_ge_0_iff_ge int_mod_ge le_less le_less_trans mod_add_self1 not_less)
  done

lemma uint_sub_if':
  "uint (a - b) =
    (if uint b \<le> uint a then uint a - uint b
     else uint a - uint b + 2 ^ LENGTH('a))"
  for a b :: "'a::len word"
  using mod_sub_if_z [of "uint a" _ "uint b"] by (simp add: uint_word_ariths)


subsection \<open>Definition of \<open>uint_arith\<close>\<close>

lemma word_of_int_inverse:
  "word_of_int r = a \<Longrightarrow> 0 \<le> r \<Longrightarrow> r < 2 ^ LENGTH('a) \<Longrightarrow> uint a = r"
  for a :: "'a::len word"
  apply (erule word_uint.Abs_inverse' [rotated])
  apply (simp add: uints_num)
  done

lemma uint_split:
  "P (uint x) = (\<forall>i. word_of_int i = x \<and> 0 \<le> i \<and> i < 2^LENGTH('a) \<longrightarrow> P i)"
  for x :: "'a::len word"
  apply (fold word_int_case_def)
  apply (auto dest!: word_of_int_inverse simp: int_word_uint
      split: word_int_split)
  done

lemma uint_split_asm:
  "P (uint x) = (\<nexists>i. word_of_int i = x \<and> 0 \<le> i \<and> i < 2^LENGTH('a) \<and> \<not> P i)"
  for x :: "'a::len word"
  by (auto dest!: word_of_int_inverse
      simp: int_word_uint
      split: uint_split)

lemmas uint_splits = uint_split uint_split_asm

lemmas uint_arith_simps =
  word_le_def word_less_alt
  word_uint.Rep_inject [symmetric]
  uint_sub_if' uint_plus_if'

\<comment> \<open>use this to stop, eg. \<open>2 ^ LENGTH(32)\<close> being simplified\<close>
lemma power_False_cong: "False \<Longrightarrow> a ^ b = c ^ d"
  by auto

\<comment> \<open>\<open>uint_arith_tac\<close>: reduce to arithmetic on int, try to solve by arith\<close>
ML \<open>
fun uint_arith_simpset ctxt =
  ctxt addsimps @{thms uint_arith_simps}
     delsimps @{thms word_uint.Rep_inject}
     |> fold Splitter.add_split @{thms if_split_asm}
     |> fold Simplifier.add_cong @{thms power_False_cong}

fun uint_arith_tacs ctxt =
  let
    fun arith_tac' n t =
      Arith_Data.arith_tac ctxt n t
        handle Cooper.COOPER _ => Seq.empty;
  in
    [ clarify_tac ctxt 1,
      full_simp_tac (uint_arith_simpset ctxt) 1,
      ALLGOALS (full_simp_tac
        (put_simpset HOL_ss ctxt
          |> fold Splitter.add_split @{thms uint_splits}
          |> fold Simplifier.add_cong @{thms power_False_cong})),
      rewrite_goals_tac ctxt @{thms word_size},
      ALLGOALS  (fn n => REPEAT (resolve_tac ctxt [allI, impI] n) THEN
                         REPEAT (eresolve_tac ctxt [conjE] n) THEN
                         REPEAT (dresolve_tac ctxt @{thms word_of_int_inverse} n
                                 THEN assume_tac ctxt n
                                 THEN assume_tac ctxt n)),
      TRYALL arith_tac' ]
  end

fun uint_arith_tac ctxt = SELECT_GOAL (EVERY (uint_arith_tacs ctxt))
\<close>

method_setup uint_arith =
  \<open>Scan.succeed (SIMPLE_METHOD' o uint_arith_tac)\<close>
  "solving word arithmetic via integers and arith"


subsection \<open>More on overflows and monotonicity\<close>

lemma no_plus_overflow_uint_size: "x \<le> x + y \<longleftrightarrow> uint x + uint y < 2 ^ size x"
  for x y :: "'a::len word"
  unfolding word_size by uint_arith

lemmas no_olen_add = no_plus_overflow_uint_size [unfolded word_size]

lemma no_ulen_sub: "x \<ge> x - y \<longleftrightarrow> uint y \<le> uint x"
  for x y :: "'a::len word"
  by uint_arith

lemma no_olen_add': "x \<le> y + x \<longleftrightarrow> uint y + uint x < 2 ^ LENGTH('a)"
  for x y :: "'a::len word"
  by (simp add: ac_simps no_olen_add)

lemmas olen_add_eqv = trans [OF no_olen_add no_olen_add' [symmetric]]

lemmas uint_plus_simple_iff = trans [OF no_olen_add uint_add_lem]
lemmas uint_plus_simple = uint_plus_simple_iff [THEN iffD1]
lemmas uint_minus_simple_iff = trans [OF no_ulen_sub uint_sub_lem]
lemmas uint_minus_simple_alt = uint_sub_lem [folded word_le_def]
lemmas word_sub_le_iff = no_ulen_sub [folded word_le_def]
lemmas word_sub_le = word_sub_le_iff [THEN iffD2]

lemma word_less_sub1: "x \<noteq> 0 \<Longrightarrow> 1 < x \<longleftrightarrow> 0 < x - 1"
  for x :: "'a::len word"
  by uint_arith

lemma word_le_sub1: "x \<noteq> 0 \<Longrightarrow> 1 \<le> x \<longleftrightarrow> 0 \<le> x - 1"
  for x :: "'a::len word"
  by uint_arith

lemma sub_wrap_lt: "x < x - z \<longleftrightarrow> x < z"
  for x z :: "'a::len word"
  by uint_arith

lemma sub_wrap: "x \<le> x - z \<longleftrightarrow> z = 0 \<or> x < z"
  for x z :: "'a::len word"
  by uint_arith

lemma plus_minus_not_NULL_ab: "x \<le> ab - c \<Longrightarrow> c \<le> ab \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> x + c \<noteq> 0"
  for x ab c :: "'a::len word"
  by uint_arith

lemma plus_minus_no_overflow_ab: "x \<le> ab - c \<Longrightarrow> c \<le> ab \<Longrightarrow> x \<le> x + c"
  for x ab c :: "'a::len word"
  by uint_arith

lemma le_minus': "a + c \<le> b \<Longrightarrow> a \<le> a + c \<Longrightarrow> c \<le> b - a"
  for a b c :: "'a::len word"
  by uint_arith

lemma le_plus': "a \<le> b \<Longrightarrow> c \<le> b - a \<Longrightarrow> a + c \<le> b"
  for a b c :: "'a::len word"
  by uint_arith

lemmas le_plus = le_plus' [rotated]

lemmas le_minus = leD [THEN thin_rl, THEN le_minus'] (* FIXME *)

lemma word_plus_mono_right: "y \<le> z \<Longrightarrow> x \<le> x + z \<Longrightarrow> x + y \<le> x + z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_minus_cancel: "y - x < z - x \<Longrightarrow> x \<le> z \<Longrightarrow> y < z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_minus_mono_left: "y < z \<Longrightarrow> x \<le> y \<Longrightarrow> y - x < z - x"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_minus_mono: "a < c \<Longrightarrow> d < b \<Longrightarrow> a - b < a \<Longrightarrow> c - d < c \<Longrightarrow> a - b < c - d"
  for a b c d :: "'a::len word"
  by uint_arith

lemma word_le_minus_cancel: "y - x \<le> z - x \<Longrightarrow> x \<le> z \<Longrightarrow> y \<le> z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_le_minus_mono_left: "y \<le> z \<Longrightarrow> x \<le> y \<Longrightarrow> y - x \<le> z - x"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_le_minus_mono:
  "a \<le> c \<Longrightarrow> d \<le> b \<Longrightarrow> a - b \<le> a \<Longrightarrow> c - d \<le> c \<Longrightarrow> a - b \<le> c - d"
  for a b c d :: "'a::len word"
  by uint_arith

lemma plus_le_left_cancel_wrap: "x + y' < x \<Longrightarrow> x + y < x \<Longrightarrow> x + y' < x + y \<longleftrightarrow> y' < y"
  for x y y' :: "'a::len word"
  by uint_arith

lemma plus_le_left_cancel_nowrap: "x \<le> x + y' \<Longrightarrow> x \<le> x + y \<Longrightarrow> x + y' < x + y \<longleftrightarrow> y' < y"
  for x y y' :: "'a::len word"
  by uint_arith

lemma word_plus_mono_right2: "a \<le> a + b \<Longrightarrow> c \<le> b \<Longrightarrow> a \<le> a + c"
  for a b c :: "'a::len word"
  by uint_arith

lemma word_less_add_right: "x < y - z \<Longrightarrow> z \<le> y \<Longrightarrow> x + z < y"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_sub_right: "x < y + z \<Longrightarrow> y \<le> x \<Longrightarrow> x - y < z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_le_plus_either: "x \<le> y \<or> x \<le> z \<Longrightarrow> y \<le> y + z \<Longrightarrow> x \<le> y + z"
  for x y z :: "'a::len word"
  by uint_arith

lemma word_less_nowrapI: "x < z - k \<Longrightarrow> k \<le> z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  for x z k :: "'a::len word"
  by uint_arith

lemma inc_le: "i < m \<Longrightarrow> i + 1 \<le> m"
  for i m :: "'a::len word"
  by uint_arith

lemma inc_i: "1 \<le> i \<Longrightarrow> i < m \<Longrightarrow> 1 \<le> i + 1 \<and> i + 1 \<le> m"
  for i m :: "'a::len word"
  by uint_arith

lemma udvd_incr_lem:
  "up < uq \<Longrightarrow> up = ua + n * uint K \<Longrightarrow>
    uq = ua + n' * uint K \<Longrightarrow> up + uint K \<le> uq"
  by auto (metis int_distrib(1) linorder_not_less mult.left_neutral mult_right_mono uint_nonnegative zless_imp_add1_zle)

lemma udvd_incr':
  "p < q \<Longrightarrow> uint p = ua + n * uint K \<Longrightarrow>
    uint q = ua + n' * uint K \<Longrightarrow> p + K \<le> q"
  apply (unfold word_less_alt word_le_def)
  apply (drule (2) udvd_incr_lem)
  apply (erule uint_add_le [THEN order_trans])
  done

lemma udvd_decr':
  "p < q \<Longrightarrow> uint p = ua + n * uint K \<Longrightarrow>
    uint q = ua + n' * uint K \<Longrightarrow> p \<le> q - K"
  apply (unfold word_less_alt word_le_def)
  apply (drule (2) udvd_incr_lem)
  apply (drule le_diff_eq [THEN iffD2])
  apply (erule order_trans)
  apply (rule uint_sub_ge)
  done

lemmas udvd_incr_lem0 = udvd_incr_lem [where ua=0, unfolded add_0_left]
lemmas udvd_incr0 = udvd_incr' [where ua=0, unfolded add_0_left]
lemmas udvd_decr0 = udvd_decr' [where ua=0, unfolded add_0_left]

lemma udvd_minus_le': "xy < k \<Longrightarrow> z udvd xy \<Longrightarrow> z udvd k \<Longrightarrow> xy \<le> k - z"
  apply (unfold udvd_def)
  apply clarify
  apply (erule (2) udvd_decr0)
  done

lemma udvd_incr2_K:
  "p < a + s \<Longrightarrow> a \<le> a + s \<Longrightarrow> K udvd s \<Longrightarrow> K udvd p - a \<Longrightarrow> a \<le> p \<Longrightarrow>
    0 < K \<Longrightarrow> p \<le> p + K \<and> p + K \<le> a + s"
  supply [[simproc del: linordered_ring_less_cancel_factor]]
  apply (unfold udvd_def)
  apply clarify
  apply (simp add: uint_arith_simps split: if_split_asm)
   prefer 2
   apply (insert uint_range' [of s])[1]
   apply arith
  apply (drule add.commute [THEN xtrans(1)])
  apply (simp flip: diff_less_eq)
  apply (subst (asm) mult_less_cancel_right)
  apply simp
  apply (simp add: diff_eq_eq not_less)
  apply (subst (asm) (3) zless_iff_Suc_zadd)
  apply auto
    apply (auto simp add: algebra_simps)
  apply (drule less_le_trans [of _ \<open>2 ^ LENGTH('a)\<close>]) apply assumption
  apply (simp add: mult_less_0_iff)
  done

\<comment> \<open>links with \<open>rbl\<close> operations\<close>
lemma word_succ_rbl: "to_bl w = bl \<Longrightarrow> to_bl (word_succ w) = rev (rbl_succ (rev bl))"
  apply (unfold word_succ_alt)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_succ)
  done

lemma word_pred_rbl: "to_bl w = bl \<Longrightarrow> to_bl (word_pred w) = rev (rbl_pred (rev bl))"
  apply (unfold word_pred_alt)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_pred)
  done

lemma word_add_rbl:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow>
    to_bl (v + w) = rev (rbl_add (rev vbl) (rev wbl))"
  apply (unfold word_add_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_add)
  done

lemma word_mult_rbl:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow>
    to_bl (v * w) = rev (rbl_mult (rev vbl) (rev wbl))"
  apply (unfold word_mult_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_mult)
  done

lemma rtb_rbl_ariths:
  "rev (to_bl w) = ys \<Longrightarrow> rev (to_bl (word_succ w)) = rbl_succ ys"
  "rev (to_bl w) = ys \<Longrightarrow> rev (to_bl (word_pred w)) = rbl_pred ys"
  "rev (to_bl v) = ys \<Longrightarrow> rev (to_bl w) = xs \<Longrightarrow> rev (to_bl (v * w)) = rbl_mult ys xs"
  "rev (to_bl v) = ys \<Longrightarrow> rev (to_bl w) = xs \<Longrightarrow> rev (to_bl (v + w)) = rbl_add ys xs"
  by (auto simp: rev_swap [symmetric] word_succ_rbl word_pred_rbl word_mult_rbl word_add_rbl)


subsection \<open>Arithmetic type class instantiations\<close>

lemmas word_le_0_iff [simp] =
  word_zero_le [THEN leD, THEN antisym_conv1]

lemma word_of_int_nat: "0 \<le> x \<Longrightarrow> word_of_int x = of_nat (nat x)"
  by (simp add: word_of_int)

text \<open>
  note that \<open>iszero_def\<close> is only for class \<open>comm_semiring_1_cancel\<close>,
  which requires word length \<open>\<ge> 1\<close>, ie \<open>'a::len word\<close>
\<close>
lemma iszero_word_no [simp]:
  "iszero (numeral bin :: 'a::len word) =
    iszero (bintrunc (LENGTH('a)) (numeral bin))"
  using word_ubin.norm_eq_iff [where 'a='a, of "numeral bin" 0]
  by (simp add: iszero_def [symmetric])

text \<open>Use \<open>iszero\<close> to simplify equalities between word numerals.\<close>

lemmas word_eq_numeral_iff_iszero [simp] =
  eq_numeral_iff_iszero [where 'a="'a::len word"]


subsection \<open>Word and nat\<close>

lemma td_ext_unat [OF refl]:
  "n = LENGTH('a::len) \<Longrightarrow>
    td_ext (unat :: 'a word \<Rightarrow> nat) of_nat (unats n) (\<lambda>i. i mod 2 ^ n)"
  apply (unfold td_ext_def' unat_def word_of_nat unats_uints)
  apply (auto intro!: imageI simp add : word_of_int_hom_syms)
   apply (erule word_uint.Abs_inverse [THEN arg_cong])
  apply (simp add: int_word_uint nat_mod_distrib nat_power_eq)
  done

lemmas unat_of_nat = td_ext_unat [THEN td_ext.eq_norm]

interpretation word_unat:
  td_ext
    "unat::'a::len word \<Rightarrow> nat"
    of_nat
    "unats (LENGTH('a::len))"
    "\<lambda>i. i mod 2 ^ LENGTH('a::len)"
  by (rule td_ext_unat)

lemmas td_unat = word_unat.td_thm

lemmas unat_lt2p [iff] = word_unat.Rep [unfolded unats_def mem_Collect_eq]

lemma unat_le: "y \<le> unat z \<Longrightarrow> y \<in> unats (LENGTH('a))"
  for z :: "'a::len word"
  apply (unfold unats_def)
  apply clarsimp
  apply (rule xtrans, rule unat_lt2p, assumption)
  done

lemma word_nchotomy: "\<forall>w :: 'a::len word. \<exists>n. w = of_nat n \<and> n < 2 ^ LENGTH('a)"
  apply (rule allI)
  apply (rule word_unat.Abs_cases)
  apply (unfold unats_def)
  apply auto
  done

lemma of_nat_eq: "of_nat n = w \<longleftrightarrow> (\<exists>q. n = unat w + q * 2 ^ LENGTH('a))"
  for w :: "'a::len word"
  using mod_div_mult_eq [of n "2 ^ LENGTH('a)", symmetric]
  by (auto simp add: word_unat.inverse_norm)

lemma of_nat_eq_size: "of_nat n = w \<longleftrightarrow> (\<exists>q. n = unat w + q * 2 ^ size w)"
  unfolding word_size by (rule of_nat_eq)

lemma of_nat_0: "of_nat m = (0::'a::len word) \<longleftrightarrow> (\<exists>q. m = q * 2 ^ LENGTH('a))"
  by (simp add: of_nat_eq)

lemma of_nat_2p [simp]: "of_nat (2 ^ LENGTH('a)) = (0::'a::len word)"
  by (fact mult_1 [symmetric, THEN iffD2 [OF of_nat_0 exI]])

lemma of_nat_gt_0: "of_nat k \<noteq> 0 \<Longrightarrow> 0 < k"
  by (cases k) auto

lemma of_nat_neq_0: "0 < k \<Longrightarrow> k < 2 ^ LENGTH('a::len) \<Longrightarrow> of_nat k \<noteq> (0 :: 'a word)"
  by (auto simp add : of_nat_0)

lemma Abs_fnat_hom_add: "of_nat a + of_nat b = of_nat (a + b)"
  by simp

lemma Abs_fnat_hom_mult: "of_nat a * of_nat b = (of_nat (a * b) :: 'a::len word)"
  by (simp add: word_of_nat wi_hom_mult)

lemma Abs_fnat_hom_Suc: "word_succ (of_nat a) = of_nat (Suc a)"
  by (simp add: word_of_nat wi_hom_succ ac_simps)

lemma Abs_fnat_hom_0: "(0::'a::len word) = of_nat 0"
  by simp

lemma Abs_fnat_hom_1: "(1::'a::len word) = of_nat (Suc 0)"
  by simp

lemmas Abs_fnat_homs =
  Abs_fnat_hom_add Abs_fnat_hom_mult Abs_fnat_hom_Suc
  Abs_fnat_hom_0 Abs_fnat_hom_1

lemma word_arith_nat_add: "a + b = of_nat (unat a + unat b)"
  by simp

lemma word_arith_nat_mult: "a * b = of_nat (unat a * unat b)"
  by simp

lemma word_arith_nat_Suc: "word_succ a = of_nat (Suc (unat a))"
  by (subst Abs_fnat_hom_Suc [symmetric]) simp

lemma word_arith_nat_div: "a div b = of_nat (unat a div unat b)"
  by (simp add: word_div_def word_of_nat zdiv_int uint_nat)

lemma word_arith_nat_mod: "a mod b = of_nat (unat a mod unat b)"
  by (simp add: word_mod_def word_of_nat zmod_int uint_nat)

lemmas word_arith_nat_defs =
  word_arith_nat_add word_arith_nat_mult
  word_arith_nat_Suc Abs_fnat_hom_0
  Abs_fnat_hom_1 word_arith_nat_div
  word_arith_nat_mod

lemma unat_cong: "x = y \<Longrightarrow> unat x = unat y"
  by simp

lemmas unat_word_ariths = word_arith_nat_defs
  [THEN trans [OF unat_cong unat_of_nat]]

lemmas word_sub_less_iff = word_sub_le_iff
  [unfolded linorder_not_less [symmetric] Not_eq_iff]

lemma unat_add_lem:
  "unat x + unat y < 2 ^ LENGTH('a) \<longleftrightarrow> unat (x + y) = unat x + unat y"
  for x y :: "'a::len word"
  apply (auto simp: unat_word_ariths)
  apply (metis unat_lt2p word_unat.eq_norm)
  done

lemma unat_mult_lem:
  "unat x * unat y < 2 ^ LENGTH('a) \<longleftrightarrow> unat (x * y) = unat x * unat y"
  for x y :: "'a::len word"
  apply (auto simp: unat_word_ariths)
  apply (metis unat_lt2p word_unat.eq_norm)
  done

lemma unat_plus_if':
  \<open>unat (a + b) =
    (if unat a + unat b < 2 ^ LENGTH('a)
    then unat a + unat b
    else unat a + unat b - 2 ^ LENGTH('a))\<close> for a b :: \<open>'a::len word\<close>
  apply (auto simp: unat_word_ariths not_less)
  apply (subst (asm) le_iff_add)
  apply auto
  apply (metis add_less_cancel_left add_less_cancel_right le_less_trans less_imp_le mod_less unat_lt2p)
  done

lemma le_no_overflow: "x \<le> b \<Longrightarrow> a \<le> a + b \<Longrightarrow> x \<le> a + b"
  for a b x :: "'a::len word"
  apply (erule order_trans)
  apply (erule olen_add_eqv [THEN iffD1])
  done

lemmas un_ui_le =
  trans [OF word_le_nat_alt [symmetric] word_le_def]

lemma unat_sub_if_size:
  "unat (x - y) =
    (if unat y \<le> unat x
     then unat x - unat y
     else unat x + 2 ^ size x - unat y)"
  apply (unfold word_size)
  apply (simp add: un_ui_le)
  apply (auto simp add: unat_def uint_sub_if')
   apply (rule nat_diff_distrib)
    prefer 3
    apply (simp add: algebra_simps)
    apply (rule nat_diff_distrib [THEN trans])
      prefer 3
      apply (subst nat_add_distrib)
        prefer 3
        apply (simp add: nat_power_eq)
       apply auto
  apply uint_arith
  done

lemmas unat_sub_if' = unat_sub_if_size [unfolded word_size]

lemma uint_div:
  \<open>uint (x div y) = uint x div uint y\<close>
  by (metis div_le_dividend le_less_trans mod_less uint_nat unat_lt2p unat_word_ariths(6) zdiv_int)

lemma unat_div:
  \<open>unat (x div y) = unat x div unat y\<close>
  by (simp add: unat_def uint_div add: nat_div_distrib)

lemma uint_mod:
  \<open>uint (x mod y) = uint x mod uint y\<close>
  by (metis (no_types, lifting) le_less_trans mod_by_0 mod_le_divisor mod_less neq0_conv uint_nat unat_lt2p unat_word_ariths(7) zmod_int)
  
lemma unat_mod: "unat (x mod y) = unat x mod unat y"
  for x y :: "'a::len word"
  by (simp add: unat_def uint_mod add: nat_mod_distrib)


text \<open>Definition of \<open>unat_arith\<close> tactic\<close>

lemma unat_split: "P (unat x) \<longleftrightarrow> (\<forall>n. of_nat n = x \<and> n < 2^LENGTH('a) \<longrightarrow> P n)"
  for x :: "'a::len word"
  by (auto simp: unat_of_nat)

lemma unat_split_asm: "P (unat x) \<longleftrightarrow> (\<nexists>n. of_nat n = x \<and> n < 2^LENGTH('a) \<and> \<not> P n)"
  for x :: "'a::len word"
  by (auto simp: unat_of_nat)

lemmas of_nat_inverse =
  word_unat.Abs_inverse' [rotated, unfolded unats_def, simplified]

lemmas unat_splits = unat_split unat_split_asm

lemmas unat_arith_simps =
  word_le_nat_alt word_less_nat_alt
  word_unat.Rep_inject [symmetric]
  unat_sub_if' unat_plus_if' unat_div unat_mod

\<comment> \<open>\<open>unat_arith_tac\<close>: tactic to reduce word arithmetic to \<open>nat\<close>, try to solve via \<open>arith\<close>\<close>
ML \<open>
fun unat_arith_simpset ctxt =
  ctxt addsimps @{thms unat_arith_simps}
     delsimps @{thms word_unat.Rep_inject}
     |> fold Splitter.add_split @{thms if_split_asm}
     |> fold Simplifier.add_cong @{thms power_False_cong}

fun unat_arith_tacs ctxt =
  let
    fun arith_tac' n t =
      Arith_Data.arith_tac ctxt n t
        handle Cooper.COOPER _ => Seq.empty;
  in
    [ clarify_tac ctxt 1,
      full_simp_tac (unat_arith_simpset ctxt) 1,
      ALLGOALS (full_simp_tac
        (put_simpset HOL_ss ctxt
          |> fold Splitter.add_split @{thms unat_splits}
          |> fold Simplifier.add_cong @{thms power_False_cong})),
      rewrite_goals_tac ctxt @{thms word_size},
      ALLGOALS (fn n => REPEAT (resolve_tac ctxt [allI, impI] n) THEN
                         REPEAT (eresolve_tac ctxt [conjE] n) THEN
                         REPEAT (dresolve_tac ctxt @{thms of_nat_inverse} n THEN assume_tac ctxt n)),
      TRYALL arith_tac' ]
  end

fun unat_arith_tac ctxt = SELECT_GOAL (EVERY (unat_arith_tacs ctxt))
\<close>

method_setup unat_arith =
  \<open>Scan.succeed (SIMPLE_METHOD' o unat_arith_tac)\<close>
  "solving word arithmetic via natural numbers and arith"

lemma no_plus_overflow_unat_size: "x \<le> x + y \<longleftrightarrow> unat x + unat y < 2 ^ size x"
  for x y :: "'a::len word"
  unfolding word_size by unat_arith

lemmas no_olen_add_nat =
  no_plus_overflow_unat_size [unfolded word_size]

lemmas unat_plus_simple =
  trans [OF no_olen_add_nat unat_add_lem]

lemma word_div_mult: "0 < y \<Longrightarrow> unat x * unat y < 2 ^ LENGTH('a) \<Longrightarrow> x * y div y = x"
  for x y :: "'a::len word"
  apply unat_arith
  apply clarsimp
  apply (subst unat_mult_lem [THEN iffD1])
   apply auto
  done

lemma div_lt': "i \<le> k div x \<Longrightarrow> unat i * unat x < 2 ^ LENGTH('a)"
  for i k x :: "'a::len word"
  apply unat_arith
  apply clarsimp
  apply (drule mult_le_mono1)
  apply (erule order_le_less_trans)
  apply (metis add_lessD1 div_mult_mod_eq unat_lt2p)
  done

lemmas div_lt'' = order_less_imp_le [THEN div_lt']

lemma div_lt_mult: "i < k div x \<Longrightarrow> 0 < x \<Longrightarrow> i * x < k"
  for i k x :: "'a::len word"
  apply (frule div_lt'' [THEN unat_mult_lem [THEN iffD1]])
  apply (simp add: unat_arith_simps)
  apply (drule (1) mult_less_mono1)
  apply (erule order_less_le_trans)
  apply auto
  done

lemma div_le_mult: "i \<le> k div x \<Longrightarrow> 0 < x \<Longrightarrow> i * x \<le> k"
  for i k x :: "'a::len word"
  apply (frule div_lt' [THEN unat_mult_lem [THEN iffD1]])
  apply (simp add: unat_arith_simps)
  apply (drule mult_le_mono1)
  apply (erule order_trans)
  apply auto
  done

lemma div_lt_uint': "i \<le> k div x \<Longrightarrow> uint i * uint x < 2 ^ LENGTH('a)"
  for i k x :: "'a::len word"
  apply (unfold uint_nat)
  apply (drule div_lt')
  apply (metis of_nat_less_iff of_nat_mult of_nat_numeral of_nat_power)
  done

lemmas div_lt_uint'' = order_less_imp_le [THEN div_lt_uint']

lemma word_le_exists': "x \<le> y \<Longrightarrow> \<exists>z. y = x + z \<and> uint x + uint z < 2 ^ LENGTH('a)"
  for x y z :: "'a::len word"
  by (metis add_diff_cancel_left' add_diff_eq uint_add_lem uint_plus_simple)
  
lemmas plus_minus_not_NULL = order_less_imp_le [THEN plus_minus_not_NULL_ab]

lemmas plus_minus_no_overflow =
  order_less_imp_le [THEN plus_minus_no_overflow_ab]

lemmas mcs = word_less_minus_cancel word_less_minus_mono_left
  word_le_minus_cancel word_le_minus_mono_left

lemmas word_l_diffs = mcs [where y = "w + x", unfolded add_diff_cancel] for w x
lemmas word_diff_ls = mcs [where z = "w + x", unfolded add_diff_cancel] for w x
lemmas word_plus_mcs = word_diff_ls [where y = "v + x", unfolded add_diff_cancel] for v x

lemmas le_unat_uoi = unat_le [THEN word_unat.Abs_inverse]

lemmas thd = times_div_less_eq_dividend

lemmas uno_simps [THEN le_unat_uoi] = mod_le_divisor div_le_dividend

lemma word_mod_div_equality: "(n div b) * b + (n mod b) = n"
  for n b :: "'a::len word"
  by (fact div_mult_mod_eq)

lemma word_div_mult_le: "a div b * b \<le> a"
  for a b :: "'a::len word"
  by (metis div_le_mult mult_not_zero order.not_eq_order_implies_strict order_refl word_zero_le)

lemma word_mod_less_divisor: "0 < n \<Longrightarrow> m mod n < n"
  for m n :: "'a::len word"
  by (simp add: unat_arith_simps)
  
lemma word_of_int_power_hom: "word_of_int a ^ n = (word_of_int (a ^ n) :: 'a::len word)"
  by (induct n) (simp_all add: wi_hom_mult [symmetric])

lemma word_arith_power_alt: "a ^ n = (word_of_int (uint a ^ n) :: 'a::len word)"
  by (simp add : word_of_int_power_hom [symmetric])

lemma of_bl_length_less:
  "length x = k \<Longrightarrow> k < LENGTH('a) \<Longrightarrow> (of_bl x :: 'a::len word) < 2 ^ k"
  apply (unfold of_bl_def word_less_alt word_numeral_alt)
  apply safe
  apply (simp (no_asm) add: word_of_int_power_hom word_uint.eq_norm
      del: word_of_int_numeral)
  apply simp
  apply (subst mod_pos_pos_trivial)
    apply (rule bl_to_bin_ge0)
   apply (rule order_less_trans)
    apply (rule bl_to_bin_lt2p)
   apply simp
  apply (rule bl_to_bin_lt2p)
  done

lemma unatSuc: "1 + n \<noteq> 0 \<Longrightarrow> unat (1 + n) = Suc (unat n)"
  for n :: "'a::len word"
  by unat_arith


subsection \<open>Cardinality, finiteness of set of words\<close>

lemma inj_on_word_of_int: \<open>inj_on (word_of_int :: int \<Rightarrow> 'a word) {0..<2 ^ LENGTH('a::len)}\<close>
  by (rule inj_onI) (simp add: word.abs_eq_iff take_bit_eq_mod)

lemma inj_uint: \<open>inj uint\<close>
  by (rule injI) simp

lemma range_uint: \<open>range (uint :: 'a word \<Rightarrow> int) = {0..<2 ^ LENGTH('a::len)}\<close>
  by transfer (auto simp add: bintr_lt2p range_bintrunc)

lemma UNIV_eq: \<open>(UNIV :: 'a word set) = word_of_int ` {0..<2 ^ LENGTH('a::len)}\<close>
proof -
  have \<open>uint ` (UNIV :: 'a word set) = uint ` (word_of_int :: int \<Rightarrow> 'a word) ` {0..<2 ^ LENGTH('a::len)}\<close>
    by (simp add: range_uint image_image uint.abs_eq take_bit_eq_mod)
  then show ?thesis
    using inj_image_eq_iff [of \<open>uint :: 'a word \<Rightarrow> int\<close> \<open>UNIV :: 'a word set\<close> \<open>word_of_int ` {0..<2 ^ LENGTH('a)} :: 'a word set\<close>, OF inj_uint]
    by simp
qed

lemma card_word: "CARD('a word) = 2 ^ LENGTH('a::len)"
  by (simp add: UNIV_eq card_image inj_on_word_of_int)

lemma card_word_size: "CARD('a word) = 2 ^ size x"
  for x :: "'a::len word"
  unfolding word_size by (rule card_word)

instance word :: (len) finite
  by standard (simp add: UNIV_eq)


subsection \<open>Bitwise Operations on Words\<close>

lemma word_eq_rbl_eq: "x = y \<longleftrightarrow> rev (to_bl x) = rev (to_bl y)"
  by simp

lemmas bin_log_bintrs = bin_trunc_not bin_trunc_xor bin_trunc_and bin_trunc_or

\<comment> \<open>following definitions require both arithmetic and bit-wise word operations\<close>

\<comment> \<open>to get \<open>word_no_log_defs\<close> from \<open>word_log_defs\<close>, using \<open>bin_log_bintrs\<close>\<close>
lemmas wils1 = bin_log_bintrs [THEN word_ubin.norm_eq_iff [THEN iffD1],
  folded word_ubin.eq_norm, THEN eq_reflection]

\<comment> \<open>the binary operations only\<close>  (* BH: why is this needed? *)
lemmas word_log_binary_defs =
  word_and_def word_or_def word_xor_def

lemma word_wi_log_defs:
  "NOT (word_of_int a) = word_of_int (NOT a)"
  "word_of_int a AND word_of_int b = word_of_int (a AND b)"
  "word_of_int a OR word_of_int b = word_of_int (a OR b)"
  "word_of_int a XOR word_of_int b = word_of_int (a XOR b)"
  by (transfer, rule refl)+

lemma word_no_log_defs [simp]:
  "NOT (numeral a) = word_of_int (NOT (numeral a))"
  "NOT (- numeral a) = word_of_int (NOT (- numeral a))"
  "numeral a AND numeral b = word_of_int (numeral a AND numeral b)"
  "numeral a AND - numeral b = word_of_int (numeral a AND - numeral b)"
  "- numeral a AND numeral b = word_of_int (- numeral a AND numeral b)"
  "- numeral a AND - numeral b = word_of_int (- numeral a AND - numeral b)"
  "numeral a OR numeral b = word_of_int (numeral a OR numeral b)"
  "numeral a OR - numeral b = word_of_int (numeral a OR - numeral b)"
  "- numeral a OR numeral b = word_of_int (- numeral a OR numeral b)"
  "- numeral a OR - numeral b = word_of_int (- numeral a OR - numeral b)"
  "numeral a XOR numeral b = word_of_int (numeral a XOR numeral b)"
  "numeral a XOR - numeral b = word_of_int (numeral a XOR - numeral b)"
  "- numeral a XOR numeral b = word_of_int (- numeral a XOR numeral b)"
  "- numeral a XOR - numeral b = word_of_int (- numeral a XOR - numeral b)"
  by (transfer, rule refl)+

text \<open>Special cases for when one of the arguments equals 1.\<close>

lemma word_bitwise_1_simps [simp]:
  "NOT (1::'a::len word) = -2"
  "1 AND numeral b = word_of_int (1 AND numeral b)"
  "1 AND - numeral b = word_of_int (1 AND - numeral b)"
  "numeral a AND 1 = word_of_int (numeral a AND 1)"
  "- numeral a AND 1 = word_of_int (- numeral a AND 1)"
  "1 OR numeral b = word_of_int (1 OR numeral b)"
  "1 OR - numeral b = word_of_int (1 OR - numeral b)"
  "numeral a OR 1 = word_of_int (numeral a OR 1)"
  "- numeral a OR 1 = word_of_int (- numeral a OR 1)"
  "1 XOR numeral b = word_of_int (1 XOR numeral b)"
  "1 XOR - numeral b = word_of_int (1 XOR - numeral b)"
  "numeral a XOR 1 = word_of_int (numeral a XOR 1)"
  "- numeral a XOR 1 = word_of_int (- numeral a XOR 1)"
  by (transfer, simp)+

text \<open>Special cases for when one of the arguments equals -1.\<close>

lemma word_bitwise_m1_simps [simp]:
  "NOT (-1::'a::len word) = 0"
  "(-1::'a::len word) AND x = x"
  "x AND (-1::'a::len word) = x"
  "(-1::'a::len word) OR x = -1"
  "x OR (-1::'a::len word) = -1"
  " (-1::'a::len word) XOR x = NOT x"
  "x XOR (-1::'a::len word) = NOT x"
  by (transfer, simp)+

lemma uint_and:
  \<open>uint (x AND y) = uint x AND uint y\<close>
  by transfer simp

lemma uint_or:
  \<open>uint (x OR y) = uint x OR uint y\<close>
  by transfer simp

lemma uint_xor:
  \<open>uint (x XOR y) = uint x XOR uint y\<close>
  by transfer simp

lemma test_bit_wi [simp]:
  "(word_of_int x :: 'a::len word) !! n \<longleftrightarrow> n < LENGTH('a) \<and> bin_nth x n"
  by (simp add: word_test_bit_def word_ubin.eq_norm nth_bintr)

lemma word_test_bit_transfer [transfer_rule]:
  "(rel_fun pcr_word (rel_fun (=) (=)))
    (\<lambda>x n. n < LENGTH('a) \<and> bin_nth x n) (test_bit :: 'a::len word \<Rightarrow> _)"
  unfolding rel_fun_def word.pcr_cr_eq cr_word_def by simp

lemma word_ops_nth_size:
  "n < size x \<Longrightarrow>
    (x OR y) !! n = (x !! n | y !! n) \<and>
    (x AND y) !! n = (x !! n \<and> y !! n) \<and>
    (x XOR y) !! n = (x !! n \<noteq> y !! n) \<and>
    (NOT x) !! n = (\<not> x !! n)"
  for x :: "'a::len word"
  unfolding word_size by transfer (simp add: bin_nth_ops)

lemma word_ao_nth:
  "(x OR y) !! n = (x !! n | y !! n) \<and>
    (x AND y) !! n = (x !! n \<and> y !! n)"
  for x :: "'a::len word"
  by transfer (auto simp add: bin_nth_ops)

lemmas msb0 = len_gt_0 [THEN diff_Suc_less, THEN word_ops_nth_size [unfolded word_size]]
lemmas msb1 = msb0 [where i = 0]

lemma test_bit_numeral [simp]:
  "(numeral w :: 'a::len word) !! n \<longleftrightarrow>
    n < LENGTH('a) \<and> bin_nth (numeral w) n"
  by transfer (rule refl)

lemma test_bit_neg_numeral [simp]:
  "(- numeral w :: 'a::len word) !! n \<longleftrightarrow>
    n < LENGTH('a) \<and> bin_nth (- numeral w) n"
  by transfer (rule refl)

lemma test_bit_1 [simp]: "(1 :: 'a::len word) !! n \<longleftrightarrow> n = 0"
  by transfer auto

lemma nth_0 [simp]: "\<not> (0 :: 'a::len word) !! n"
  by transfer simp

lemma nth_minus1 [simp]: "(-1 :: 'a::len word) !! n \<longleftrightarrow> n < LENGTH('a)"
  by transfer simp

\<comment> \<open>get from commutativity, associativity etc of \<open>int_and\<close> etc to same for \<open>word_and etc\<close>\<close>
lemmas bwsimps =
  wi_hom_add
  word_wi_log_defs

lemma word_bw_assocs:
  "(x AND y) AND z = x AND y AND z"
  "(x OR y) OR z = x OR y OR z"
  "(x XOR y) XOR z = x XOR y XOR z"
  for x :: "'a::len word"
  by (auto simp: word_eq_iff word_ops_nth_size [unfolded word_size])

lemma word_bw_comms:
  "x AND y = y AND x"
  "x OR y = y OR x"
  "x XOR y = y XOR x"
  for x :: "'a::len word"
  by (auto simp: word_eq_iff word_ops_nth_size [unfolded word_size])

lemma word_bw_lcs:
  "y AND x AND z = x AND y AND z"
  "y OR x OR z = x OR y OR z"
  "y XOR x XOR z = x XOR y XOR z"
  for x :: "'a::len word"
  by (auto simp: word_eq_iff word_ops_nth_size [unfolded word_size])

lemma word_log_esimps:
  "x AND 0 = 0"
  "x AND -1 = x"
  "x OR 0 = x"
  "x OR -1 = -1"
  "x XOR 0 = x"
  "x XOR -1 = NOT x"
  "0 AND x = 0"
  "-1 AND x = x"
  "0 OR x = x"
  "-1 OR x = -1"
  "0 XOR x = x"
  "-1 XOR x = NOT x"
  for x :: "'a::len word"
  by simp_all

lemma word_not_dist:
  "NOT (x OR y) = NOT x AND NOT y"
  "NOT (x AND y) = NOT x OR NOT y"
  for x :: "'a::len word"
  by simp_all

lemma word_bw_same:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: "'a::len word"
  by simp_all

lemma word_ao_absorbs [simp]:
  "x AND (y OR x) = x"
  "x OR y AND x = x"
  "x AND (x OR y) = x"
  "y AND x OR x = x"
  "(y OR x) AND x = x"
  "x OR x AND y = x"
  "(x OR y) AND x = x"
  "x AND y OR x = x"
  for x :: "'a::len word"
  by (auto simp: word_eq_iff word_ops_nth_size [unfolded word_size])

lemma word_not_not [simp]: "NOT (NOT x) = x"
  for x :: "'a::len word"
  by simp

lemma word_ao_dist: "(x OR y) AND z = x AND z OR y AND z"
  for x :: "'a::len word"
  by (auto simp: word_eq_iff word_ops_nth_size [unfolded word_size])

lemma word_oa_dist: "x AND y OR z = (x OR z) AND (y OR z)"
  for x :: "'a::len word"
  by (auto simp: word_eq_iff word_ops_nth_size [unfolded word_size])

lemma word_add_not [simp]: "x + NOT x = -1"
  for x :: "'a::len word"
  by transfer (simp add: bin_add_not)

lemma word_plus_and_or [simp]: "(x AND y) + (x OR y) = x + y"
  for x :: "'a::len word"
  by transfer (simp add: plus_and_or)

lemma leoa: "w = x OR y \<Longrightarrow> y = w AND y"
  for x :: "'a::len word"
  by auto

lemma leao: "w' = x' AND y' \<Longrightarrow> x' = x' OR w'"
  for x' :: "'a::len word"
  by auto

lemma word_ao_equiv: "w = w OR w' \<longleftrightarrow> w' = w AND w'"
  for w w' :: "'a::len word"
  by (auto intro: leoa leao)

lemma le_word_or2: "x \<le> x OR y"
  for x y :: "'a::len word"
  by (auto simp: word_le_def uint_or intro: le_int_or)

lemmas le_word_or1 = xtrans(3) [OF word_bw_comms (2) le_word_or2]
lemmas word_and_le1 = xtrans(3) [OF word_ao_absorbs (4) [symmetric] le_word_or2]
lemmas word_and_le2 = xtrans(3) [OF word_ao_absorbs (8) [symmetric] le_word_or2]

lemma bl_word_not: "to_bl (NOT w) = map Not (to_bl w)"
  unfolding to_bl_def word_log_defs bl_not_bin
  by (simp add: word_ubin.eq_norm)

lemma bl_word_xor: "to_bl (v XOR w) = map2 (\<noteq>) (to_bl v) (to_bl w)"
  unfolding to_bl_def word_log_defs bl_xor_bin
  by (simp add: word_ubin.eq_norm)

lemma bl_word_or: "to_bl (v OR w) = map2 (\<or>) (to_bl v) (to_bl w)"
  unfolding to_bl_def word_log_defs bl_or_bin
  by (simp add: word_ubin.eq_norm)

lemma bl_word_and: "to_bl (v AND w) = map2 (\<and>) (to_bl v) (to_bl w)"
  unfolding to_bl_def word_log_defs bl_and_bin
  by (simp add: word_ubin.eq_norm)

lemma bin_nth_uint': "bin_nth (uint w) n \<longleftrightarrow> rev (bin_to_bl (size w) (uint w)) ! n \<and> n < size w"
  apply (unfold word_size)
  apply (safe elim!: bin_nth_uint_imp)
   apply (frule bin_nth_uint_imp)
   apply (fast dest!: bin_nth_bl)+
  done

lemmas bin_nth_uint = bin_nth_uint' [unfolded word_size]

lemma test_bit_bl: "w !! n \<longleftrightarrow> rev (to_bl w) ! n \<and> n < size w"
  unfolding to_bl_def word_test_bit_def word_size by (rule bin_nth_uint)

lemma to_bl_nth: "n < size w \<Longrightarrow> to_bl w ! n = w !! (size w - Suc n)"
  by (simp add: word_size rev_nth test_bit_bl)

lemma map_bit_interval_eq:
  \<open>map (bit w) [0..<n] = takefill False n (rev (to_bl w))\<close> for w :: \<open>'a::len word\<close>
proof (rule nth_equalityI)
  show \<open>length (map (bit w) [0..<n]) =
    length (takefill False n (rev (to_bl w)))\<close>
    by simp
  fix m
  assume \<open>m < length (map (bit w) [0..<n])\<close>
  then have \<open>m < n\<close>
    by simp
  then have \<open>bit w m \<longleftrightarrow> takefill False n (rev (to_bl w)) ! m\<close>
    by (auto simp add: nth_takefill not_less rev_nth to_bl_nth word_size test_bit_word_eq dest: bit_imp_le_length)
  with \<open>m < n \<close>show \<open>map (bit w) [0..<n] ! m \<longleftrightarrow> takefill False n (rev (to_bl w)) ! m\<close>
    by simp
qed

lemma to_bl_unfold:
  \<open>to_bl w = rev (map (bit w) [0..<LENGTH('a)])\<close> for w :: \<open>'a::len word\<close>
  by (simp add: map_bit_interval_eq takefill_bintrunc to_bl_def flip: bin_to_bl_def)

lemma nth_rev_to_bl:
  \<open>rev (to_bl w) ! n \<longleftrightarrow> bit w n\<close>
  if \<open>n < LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  using that by (simp add: to_bl_unfold)

lemma nth_to_bl:
  \<open>to_bl w ! n \<longleftrightarrow> bit w (LENGTH('a) - Suc n)\<close>
  if \<open>n < LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  using that by (simp add: to_bl_unfold rev_nth)

lemma of_bl_rep_False: "of_bl (replicate n False @ bs) = of_bl bs"
  by (auto simp: of_bl_def bl_to_bin_rep_F)

lemma bit_horner_sum_bit_word_iff:
  \<open>bit (horner_sum of_bool (2 :: 'a::len word) bs) n
    \<longleftrightarrow> n < min LENGTH('a) (length bs) \<and> bs ! n\<close>
  by transfer (simp add: bit_horner_sum_bit_iff)

lemma of_bl_eq:
  \<open>of_bl bs = horner_sum of_bool 2 (rev bs)\<close>
  by (rule bit_word_eqI) (simp add: bit_of_bl_iff bit_horner_sum_bit_word_iff ac_simps)

definition word_reverse :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>word_reverse w = horner_sum of_bool 2 (rev (map (bit w) [0..<LENGTH('a)]))\<close>

lemma bit_word_reverse_iff:
  \<open>bit (word_reverse w) n \<longleftrightarrow> n < LENGTH('a) \<and> bit w (LENGTH('a) - Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (cases \<open>n < LENGTH('a)\<close>)
    (simp_all add: word_reverse_def bit_horner_sum_bit_word_iff rev_nth)

lemma word_reverse_eq_of_bl_rev_to_bl:
  \<open>word_reverse w = of_bl (rev (to_bl w))\<close>
  by (rule bit_word_eqI)
    (auto simp add: bit_word_reverse_iff bit_of_bl_iff nth_to_bl)

lemmas word_reverse_no_def [simp] =
  word_reverse_eq_of_bl_rev_to_bl [of "numeral w"] for w

lemma to_bl_word_rev: "to_bl (word_reverse w) = rev (to_bl w)"
  by (rule nth_equalityI) (simp_all add: nth_rev_to_bl word_reverse_def word_rep_drop flip: of_bl_eq)

lemma word_rev_rev [simp] : "word_reverse (word_reverse w) = w"
  by (rule bit_word_eqI)
    (auto simp add: bit_word_reverse_iff bit_imp_le_length Suc_diff_Suc)

lemma word_rev_gal: "word_reverse w = u \<Longrightarrow> word_reverse u = w"
  by (metis word_rev_rev)

lemma word_rev_gal': "u = word_reverse w \<Longrightarrow> w = word_reverse u"
  by simp

lemmas lsb0 = len_gt_0 [THEN word_ops_nth_size [unfolded word_size]]

lemma nth_sint:
  fixes w :: "'a::len word"
  defines "l \<equiv> LENGTH('a)"
  shows "bin_nth (sint w) n = (if n < l - 1 then w !! n else w !! (l - 1))"
  unfolding sint_uint l_def
  by (auto simp: nth_sbintr word_test_bit_def [symmetric])

lemma setBit_no [simp]: "setBit (numeral bin) n = word_of_int (bin_sc n True (numeral bin))"
  apply (simp add: setBit_def bin_sc_eq set_bit_def)
  apply transfer
  apply simp
  done
 
lemma clearBit_no [simp]:
  "clearBit (numeral bin) n = word_of_int (bin_sc n False (numeral bin))"
  apply (simp add: clearBit_def bin_sc_eq unset_bit_def)
  apply transfer
  apply simp
  done

lemma to_bl_n1 [simp]: "to_bl (-1::'a::len word) = replicate (LENGTH('a)) True"
  apply (rule word_bl.Abs_inverse')
   apply simp
  apply (rule word_eqI)
  apply (clarsimp simp add: word_size)
  apply (auto simp add: word_bl.Abs_inverse test_bit_bl word_size)
  done

lemma test_bit_2p: "(word_of_int (2 ^ n)::'a::len word) !! m \<longleftrightarrow> m = n \<and> m < LENGTH('a)"
  by (auto simp: word_test_bit_def word_ubin.eq_norm nth_bintr nth_2p_bin)

lemma nth_w2p: "((2::'a::len word) ^ n) !! m \<longleftrightarrow> m = n \<and> m < LENGTH('a::len)"
  by (simp add: test_bit_2p [symmetric] word_of_int [symmetric])

lemma uint_2p: "(0::'a::len word) < 2 ^ n \<Longrightarrow> uint (2 ^ n::'a::len word) = 2 ^ n"
  apply (unfold word_arith_power_alt)
  apply (case_tac "LENGTH('a)")
   apply clarsimp
  apply (case_tac "nat")
   apply clarsimp
   apply (case_tac "n")
    apply clarsimp
   apply clarsimp
  apply (drule word_gt_0 [THEN iffD1])
  apply (safe intro!: word_eqI)
   apply (auto simp add: nth_2p_bin)
  apply (erule notE)
  apply (simp (no_asm_use) add: uint_word_of_int word_size)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule power_strict_increasing)
    apply simp_all
  done

lemma word_of_int_2p: "(word_of_int (2 ^ n) :: 'a::len word) = 2 ^ n"
  by (induct n) (simp_all add: wi_hom_syms)

lemma bang_is_le: "x !! m \<Longrightarrow> 2 ^ m \<le> x"
  for x :: "'a::len word"
  apply (rule xtrans(3))
   apply (rule_tac [2] y = "x" in le_word_or2)
  apply (rule word_eqI)
  apply (auto simp add: word_ao_nth nth_w2p word_size)
  done

lemma rbl_word_or: "rev (to_bl (x OR y)) = map2 (\<or>) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: zip_rev bl_word_or rev_map)

lemma rbl_word_and: "rev (to_bl (x AND y)) = map2 (\<and>) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: zip_rev bl_word_and rev_map)

lemma rbl_word_xor: "rev (to_bl (x XOR y)) = map2 (\<noteq>) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: zip_rev bl_word_xor rev_map)

lemma rbl_word_not: "rev (to_bl (NOT x)) = map Not (rev (to_bl x))"
  by (simp add: bl_word_not rev_map)


subsection \<open>Bit comprehension\<close>

instantiation word :: (len) bit_comprehension
begin

definition word_set_bits_def:
  \<open>(BITS n. P n) = (horner_sum of_bool 2 (map P [0..<LENGTH('a)]) :: 'a word)\<close>

instance ..

end

lemma bit_set_bits_word_iff:
  \<open>bit (set_bits P :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> P n\<close>
  by (auto simp add: word_set_bits_def bit_horner_sum_bit_word_iff)

lemma set_bits_bit_eq:
  \<open>set_bits (bit w) = w\<close> for w :: \<open>'a::len word\<close>
  by (rule bit_word_eqI) (auto simp add: bit_set_bits_word_iff bit_imp_le_length)

lemma set_bits_K_False [simp]:
  \<open>set_bits (\<lambda>_. False) = (0 :: 'a :: len word)\<close>
  by (rule bit_word_eqI) (simp add: bit_set_bits_word_iff)

lemmas of_nth_def = word_set_bits_def (* FIXME duplicate *)

interpretation test_bit:
  td_ext
    "(!!) :: 'a::len word \<Rightarrow> nat \<Rightarrow> bool"
    set_bits
    "{f. \<forall>i. f i \<longrightarrow> i < LENGTH('a::len)}"
    "(\<lambda>h i. h i \<and> i < LENGTH('a::len))"
  by standard
    (auto simp add: test_bit_word_eq bit_imp_le_length bit_set_bits_word_iff set_bits_bit_eq)

lemmas td_nth = test_bit.td_thm


subsection \<open>Shifting, Rotating, and Splitting Words\<close>

lemma shiftl1_wi [simp]: "shiftl1 (word_of_int w) = word_of_int (2 * w)"
  unfolding shiftl1_def
  apply (simp add: word_ubin.norm_eq_iff [symmetric] word_ubin.eq_norm)
  apply (simp add: mod_mult_right_eq take_bit_eq_mod)
  done

lemma shiftl1_numeral [simp]: "shiftl1 (numeral w) = numeral (Num.Bit0 w)"
  unfolding word_numeral_alt shiftl1_wi by simp

lemma shiftl1_neg_numeral [simp]: "shiftl1 (- numeral w) = - numeral (Num.Bit0 w)"
  unfolding word_neg_numeral_alt shiftl1_wi by simp

lemma shiftl1_0 [simp] : "shiftl1 0 = 0"
  by (simp add: shiftl1_def)

lemma shiftl1_def_u: "shiftl1 w = word_of_int (2 * uint w)"
  by (fact shiftl1_def)

lemma shiftl1_def_s: "shiftl1 w = word_of_int (2 * sint w)"
  by (simp add: shiftl1_def wi_hom_syms)

lemma shiftr1_0 [simp]: "shiftr1 0 = 0"
  by (simp add: shiftr1_def)

lemma sshiftr1_0 [simp]: "sshiftr1 0 = 0"
  by (simp add: sshiftr1_def)

lemma sshiftr1_n1 [simp]: "sshiftr1 (- 1) = - 1"
  by (simp add: sshiftr1_def)

lemma shiftl_0 [simp]: "(0::'a::len word) << n = 0"
  by (induct n) (auto simp: shiftl_def)

lemma shiftr_0 [simp]: "(0::'a::len word) >> n = 0"
  by (induct n) (auto simp: shiftr_def)

lemma sshiftr_0 [simp]: "0 >>> n = 0"
  by (induct n) (auto simp: sshiftr_def)

lemma sshiftr_n1 [simp]: "-1 >>> n = -1"
  by (induct n) (auto simp: sshiftr_def)

lemma nth_shiftl1: "shiftl1 w !! n \<longleftrightarrow> n < size w \<and> n > 0 \<and> w !! (n - 1)"
  apply (unfold shiftl1_def word_test_bit_def)
  apply (simp add: nth_bintr word_ubin.eq_norm word_size)
  apply (cases n)
  apply (simp_all add: bit_Suc)
  done

lemma nth_shiftl': "(w << m) !! n \<longleftrightarrow> n < size w \<and> n >= m \<and> w !! (n - m)"
  for w :: "'a::len word"
  apply (unfold shiftl_def)
  apply (induct m arbitrary: n)
   apply (force elim!: test_bit_size)
  apply (clarsimp simp add : nth_shiftl1 word_size)
  apply arith
  done

lemmas nth_shiftl = nth_shiftl' [unfolded word_size]

lemma nth_shiftr1: "shiftr1 w !! n = w !! Suc n"
  apply (auto simp add: shiftr1_def word_test_bit_def word_ubin.eq_norm bit_take_bit_iff bit_Suc)
  apply (metis (no_types, hide_lams) add_Suc_right add_diff_cancel_left' bit_Suc diff_is_0_eq' le_Suc_ex less_imp_le linorder_not_le test_bit_bin word_test_bit_def)
  done

lemma nth_shiftr: "(w >> m) !! n = w !! (n + m)"
  for w :: "'a::len word"
  apply (unfold shiftr_def)
  apply (induct "m" arbitrary: n)
   apply (auto simp add: nth_shiftr1)
  done

text \<open>
  see paper page 10, (1), (2), \<open>shiftr1_def\<close> is of the form of (1),
  where \<open>f\<close> (ie \<open>bin_rest\<close>) takes normal arguments to normal results,
  thus we get (2) from (1)
\<close>

lemma uint_shiftr1: "uint (shiftr1 w) = bin_rest (uint w)"
  apply (unfold shiftr1_def word_ubin.eq_norm bin_rest_trunc_i)
  apply (subst bintr_uint [symmetric, OF order_refl])
  apply (simp only : bintrunc_bintrunc_l)
  apply simp
  done

lemma bit_sshiftr1_iff:
  \<open>bit (sshiftr1 w) n \<longleftrightarrow> bit w (if n = LENGTH('a) - 1 then LENGTH('a) - 1 else Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp
  apply (simp add: sshiftr1_def bit_word_of_int_iff bit_sint_iff flip: bit_Suc)
  apply transfer apply auto
  done

lemma bit_sshiftr_word_iff:
  \<open>bit (w >>> m) n \<longleftrightarrow> bit w (if LENGTH('a) - m \<le> n \<and> n < LENGTH('a) then LENGTH('a) - 1 else (m + n))\<close>
  for w :: \<open>'a::len word\<close>
  apply (cases \<open>LENGTH('a)\<close>)
   apply simp
  apply (simp only:)
  apply (induction m arbitrary: n)
   apply (auto simp add: sshiftr_def bit_sshiftr1_iff not_le less_diff_conv)
  done

lemma nth_sshiftr1: "sshiftr1 w !! n = (if n = size w - 1 then w !! n else w !! Suc n)"
  apply (unfold sshiftr1_def word_test_bit_def)
  apply (simp add: nth_bintr word_ubin.eq_norm bit_Suc [symmetric] word_size)
  apply (simp add: nth_bintr uint_sint)
  apply (auto simp add: bin_nth_sint)
  done

lemma nth_sshiftr [rule_format] :
  "\<forall>n. sshiftr w m !! n =
    (n < size w \<and> (if n + m \<ge> size w then w !! (size w - 1) else w !! (n + m)))"
  apply (unfold sshiftr_def)
  apply (induct_tac m)
   apply (simp add: test_bit_bl)
  apply (clarsimp simp add: nth_sshiftr1 word_size)
  apply safe
       apply arith
      apply arith
     apply (erule thin_rl)
     apply (case_tac n)
      apply safe
      apply simp
     apply simp
    apply (erule thin_rl)
    apply (case_tac n)
     apply safe
     apply simp
    apply simp
   apply arith+
  done

lemma shiftr1_div_2: "uint (shiftr1 w) = uint w div 2"
  apply (unfold shiftr1_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num pos_imp_zdiv_nonneg_iff)
  apply (metis uint_lt2p uint_shiftr1)
  done

lemma sshiftr1_div_2: "sint (sshiftr1 w) = sint w div 2"
  apply (unfold sshiftr1_def)
  apply (simp add: word_sbin.eq_norm)
  apply (rule trans)
   defer
   apply (subst word_sbin.norm_Rep [symmetric])
   apply (rule refl)
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (unfold One_nat_def)
  apply (rule sbintrunc_rest)
  done

lemma shiftr_div_2n: "uint (shiftr w n) = uint w div 2 ^ n"
  apply (unfold shiftr_def)
  apply (induct n)
   apply simp
  apply (simp add: shiftr1_div_2 mult.commute zdiv_zmult2_eq [symmetric])
  done

lemma sshiftr_div_2n: "sint (sshiftr w n) = sint w div 2 ^ n"
  apply (unfold sshiftr_def)
  apply (induct n)
   apply simp
  apply (simp add: sshiftr1_div_2 mult.commute zdiv_zmult2_eq [symmetric])
  done

lemma bit_bshiftr1_iff:
  \<open>bit (bshiftr1 b w) n \<longleftrightarrow> b \<and> n = LENGTH('a) - 1 \<or> bit w (Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp
  apply (simp add: bshiftr1_def bit_of_bl_iff nth_append not_less rev_nth nth_butlast nth_to_bl)
  apply (use bit_imp_le_length in fastforce)
  done


subsubsection \<open>shift functions in terms of lists of bools\<close>

lemma bshiftr1_numeral [simp]:
  \<open>bshiftr1 b (numeral w :: 'a word) = of_bl (b # butlast (bin_to_bl LENGTH('a::len) (numeral w)))\<close>
  by (simp add: bshiftr1_def)

lemma bshiftr1_bl: "to_bl (bshiftr1 b w) = b # butlast (to_bl w)"
  unfolding bshiftr1_def by (rule word_bl.Abs_inverse) simp

lemma shiftl1_of_bl: "shiftl1 (of_bl bl) = of_bl (bl @ [False])"
  by (simp add: of_bl_def bl_to_bin_append)

lemma shiftl1_bl: "shiftl1 w = of_bl (to_bl w @ [False])"
  for w :: "'a::len word"
proof -
  have "shiftl1 w = shiftl1 (of_bl (to_bl w))"
    by simp
  also have "\<dots> = of_bl (to_bl w @ [False])"
    by (rule shiftl1_of_bl)
  finally show ?thesis .
qed

lemma bl_shiftl1: "to_bl (shiftl1 w) = tl (to_bl w) @ [False]"
  for w :: "'a::len word"
  by (simp add: shiftl1_bl word_rep_drop drop_Suc drop_Cons') (fast intro!: Suc_leI)

\<comment> \<open>Generalized version of \<open>bl_shiftl1\<close>. Maybe this one should replace it?\<close>
lemma bl_shiftl1': "to_bl (shiftl1 w) = tl (to_bl w @ [False])"
  by (simp add: shiftl1_bl word_rep_drop drop_Suc del: drop_append)

lemma shiftr1_bl: "shiftr1 w = of_bl (butlast (to_bl w))"
  apply (unfold shiftr1_def uint_bl of_bl_def)
  apply (simp add: butlast_rest_bin word_size)
  apply (simp add: bin_rest_trunc [symmetric, unfolded One_nat_def])
  done

lemma bl_shiftr1: "to_bl (shiftr1 w) = False # butlast (to_bl w)"
  for w :: "'a::len word"
  by (simp add: shiftr1_bl word_rep_drop len_gt_0 [THEN Suc_leI])

\<comment> \<open>Generalized version of \<open>bl_shiftr1\<close>. Maybe this one should replace it?\<close>
lemma bl_shiftr1': "to_bl (shiftr1 w) = butlast (False # to_bl w)"
  apply (rule word_bl.Abs_inverse')
   apply (simp del: butlast.simps)
  apply (simp add: shiftr1_bl of_bl_def)
  done

lemma shiftl1_rev: "shiftl1 w = word_reverse (shiftr1 (word_reverse w))"
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_shiftl1_iff bit_word_reverse_iff bit_shiftr1_iff Suc_diff_Suc)
  done

lemma shiftl_rev: "shiftl w n = word_reverse (shiftr (word_reverse w) n)"
  by (induct n) (auto simp add: shiftl_def shiftr_def shiftl1_rev)

lemma rev_shiftl: "word_reverse w << n = word_reverse (w >> n)"
  by (simp add: shiftl_rev)

lemma shiftr_rev: "w >> n = word_reverse (word_reverse w << n)"
  by (simp add: rev_shiftl)

lemma rev_shiftr: "word_reverse w >> n = word_reverse (w << n)"
  by (simp add: shiftr_rev)

lemma bl_sshiftr1: "to_bl (sshiftr1 w) = hd (to_bl w) # butlast (to_bl w)"
  for w :: "'a::len word"
  apply (unfold sshiftr1_def uint_bl word_size)
  apply (simp add: butlast_rest_bin word_ubin.eq_norm)
  apply (simp add: sint_uint)
  apply (rule nth_equalityI)
   apply clarsimp
  apply clarsimp
  apply (case_tac i)
   apply (simp_all add: hd_conv_nth length_0_conv [symmetric]
      nth_bin_to_bl bit_Suc [symmetric] nth_sbintr)
   apply force
  apply (rule impI)
  apply (rule_tac f = "bin_nth (uint w)" in arg_cong)
  apply simp
  done

lemma drop_shiftr: "drop n (to_bl (w >> n)) = take (size w - n) (to_bl w)"
  for w :: "'a::len word"
  apply (unfold shiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: drop_Suc bl_shiftr1 butlast_drop [symmetric])
   apply (rule butlast_take [THEN trans])
    apply (auto simp: word_size)
  done

lemma drop_sshiftr: "drop n (to_bl (w >>> n)) = take (size w - n) (to_bl w)"
  for w :: "'a::len word"
  apply (unfold sshiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: drop_Suc bl_sshiftr1 butlast_drop [symmetric])
   apply (rule butlast_take [THEN trans])
    apply (auto simp: word_size)
  done

lemma take_shiftr: "n \<le> size w \<Longrightarrow> take n (to_bl (w >> n)) = replicate n False"
  apply (unfold shiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: bl_shiftr1' length_0_conv [symmetric] word_size)
   apply (rule take_butlast [THEN trans])
    apply (auto simp: word_size)
  done

lemma take_sshiftr' [rule_format] :
  "n \<le> size w \<longrightarrow> hd (to_bl (w >>> n)) = hd (to_bl w) \<and>
    take n (to_bl (w >>> n)) = replicate n (hd (to_bl w))"
  for w :: "'a::len word"
  apply (unfold sshiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: bl_sshiftr1)
   apply (rule impI)
   apply (rule take_butlast [THEN trans])
    apply (auto simp: word_size)
  done

lemmas hd_sshiftr = take_sshiftr' [THEN conjunct1]
lemmas take_sshiftr = take_sshiftr' [THEN conjunct2]

lemma atd_lem: "take n xs = t \<Longrightarrow> drop n xs = d \<Longrightarrow> xs = t @ d"
  by (auto intro: append_take_drop_id [symmetric])

lemmas bl_shiftr = atd_lem [OF take_shiftr drop_shiftr]
lemmas bl_sshiftr = atd_lem [OF take_sshiftr drop_sshiftr]

lemma shiftl_of_bl: "of_bl bl << n = of_bl (bl @ replicate n False)"
  by (induct n) (auto simp: shiftl_def shiftl1_of_bl replicate_app_Cons_same)

lemma shiftl_bl: "w << n = of_bl (to_bl w @ replicate n False)"
  for w :: "'a::len word"
proof -
  have "w << n = of_bl (to_bl w) << n"
    by simp
  also have "\<dots> = of_bl (to_bl w @ replicate n False)"
    by (rule shiftl_of_bl)
  finally show ?thesis .
qed

lemma shiftl_numeral [simp]:
  \<open>numeral k << numeral l = (push_bit (numeral l) (numeral k) :: 'a::len word)\<close>
  by (fact shiftl_word_eq)

lemma bl_shiftl: "to_bl (w << n) = drop n (to_bl w) @ replicate (min (size w) n) False"
  by (simp add: shiftl_bl word_rep_drop word_size)

lemma shiftl_zero_size: "size x \<le> n \<Longrightarrow> x << n = 0"
  for x :: "'a::len word"
  apply (unfold word_size)
  apply (rule word_eqI)
  apply (clarsimp simp add: shiftl_bl word_size test_bit_of_bl nth_append)
  done

\<comment> \<open>note -- the following results use \<open>'a::len word < number_ring\<close>\<close>

lemma shiftl1_2t: "shiftl1 w = 2 * w"
  for w :: "'a::len word"
  by (simp add: shiftl1_def wi_hom_mult [symmetric])

lemma shiftl1_p: "shiftl1 w = w + w"
  for w :: "'a::len word"
  by (simp add: shiftl1_2t)

lemma shiftl_t2n: "shiftl w n = 2 ^ n * w"
  for w :: "'a::len word"
  by (induct n) (auto simp: shiftl_def shiftl1_2t)

lemma shiftr1_bintr [simp]:
  "(shiftr1 (numeral w) :: 'a::len word) =
    word_of_int (bin_rest (bintrunc (LENGTH('a)) (numeral w)))"
  unfolding shiftr1_def word_numeral_alt by (simp add: word_ubin.eq_norm)

lemma sshiftr1_sbintr [simp]:
  "(sshiftr1 (numeral w) :: 'a::len word) =
    word_of_int (bin_rest (sbintrunc (LENGTH('a) - 1) (numeral w)))"
  unfolding sshiftr1_def word_numeral_alt by (simp add: word_sbin.eq_norm)

text \<open>TODO: rules for \<^term>\<open>- (numeral n)\<close>\<close>

lemma drop_bit_word_numeral [simp]:
  \<open>drop_bit (numeral n) (numeral k) =
    (word_of_int (drop_bit (numeral n) (take_bit LENGTH('a) (numeral k))) :: 'a::len word)\<close>
  by transfer simp

lemma shiftr_numeral [simp]:
  \<open>(numeral k >> numeral n :: 'a::len word) = drop_bit (numeral n) (numeral k)\<close>
  by (fact shiftr_word_eq)

lemma sshiftr_numeral [simp]:
  \<open>(numeral k >>> numeral n :: 'a::len word) =
    word_of_int (drop_bit (numeral n) (sbintrunc (LENGTH('a) - 1) (numeral k)))\<close>
  apply (rule word_eqI)
  apply (cases \<open>LENGTH('a)\<close>)
   apply (simp_all add: word_size bit_drop_bit_eq nth_sshiftr nth_sbintr not_le not_less less_Suc_eq_le ac_simps)
  done

lemma shiftr1_bl_of:
  "length bl \<le> LENGTH('a) \<Longrightarrow>
    shiftr1 (of_bl bl::'a::len word) = of_bl (butlast bl)"
  by (clarsimp simp: shiftr1_def of_bl_def butlast_rest_bl2bin word_ubin.eq_norm trunc_bl2bin)

lemma shiftr_bl_of:
  "length bl \<le> LENGTH('a) \<Longrightarrow>
    (of_bl bl::'a::len word) >> n = of_bl (take (length bl - n) bl)"
  apply (unfold shiftr_def)
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (subst shiftr1_bl_of)
   apply simp
  apply (simp add: butlast_take)
  done

lemma shiftr_bl: "x >> n \<equiv> of_bl (take (LENGTH('a) - n) (to_bl x))"
  for x :: "'a::len word"
  using shiftr_bl_of [where 'a='a, of "to_bl x"] by simp

lemma zip_replicate: "n \<ge> length ys \<Longrightarrow> zip (replicate n x) ys = map (\<lambda>y. (x, y)) ys"
  apply (induct ys arbitrary: n)
   apply simp_all
  apply (case_tac n)
   apply simp_all
  done

lemma align_lem_or [rule_format] :
  "\<forall>x m. length x = n + m \<longrightarrow> length y = n + m \<longrightarrow>
    drop m x = replicate n False \<longrightarrow> take m y = replicate m False \<longrightarrow>
    map2 (|) x y = take m x @ drop m y"
  apply (induct y)
   apply force
  apply clarsimp
  apply (case_tac x)
   apply force
  apply (case_tac m)
   apply auto
  apply (drule_tac t="length xs" for xs in sym)
  apply (auto simp: zip_replicate o_def)
  done

lemma align_lem_and [rule_format] :
  "\<forall>x m. length x = n + m \<longrightarrow> length y = n + m \<longrightarrow>
    drop m x = replicate n False \<longrightarrow> take m y = replicate m False \<longrightarrow>
    map2 (\<and>) x y = replicate (n + m) False"
  apply (induct y)
   apply force
  apply clarsimp
  apply (case_tac x)
   apply force
  apply (case_tac m)
  apply auto
  apply (drule_tac t="length xs" for xs in sym)
  apply (auto simp: zip_replicate o_def map_replicate_const)
  done

lemma aligned_bl_add_size [OF refl]:
  "size x - n = m \<Longrightarrow> n \<le> size x \<Longrightarrow> drop m (to_bl x) = replicate n False \<Longrightarrow>
    take m (to_bl y) = replicate m False \<Longrightarrow>
    to_bl (x + y) = take m (to_bl x) @ drop m (to_bl y)" for x :: \<open>'a::len word\<close>
  apply (subgoal_tac "x AND y = 0")
   prefer 2
   apply (rule word_bl.Rep_eqD)
   apply (simp add: bl_word_and)
   apply (rule align_lem_and [THEN trans])
       apply (simp_all add: word_size)[5]
   apply simp
  apply (subst word_plus_and_or [symmetric])
  apply (simp add : bl_word_or)
  apply (rule align_lem_or)
     apply (simp_all add: word_size)
  done


subsubsection \<open>Mask\<close>

lemma minus_1_eq_mask:
  \<open>- 1 = (Bit_Operations.mask LENGTH('a) :: 'a::len word)\<close>
  by (rule bit_eqI) (simp add: bit_exp_iff bit_mask_iff exp_eq_zero_iff)
  
lemma mask_eq_mask:
  \<open>mask = Bit_Operations.mask\<close>
  by (simp add: fun_eq_iff mask_eq_exp_minus_1 mask_def shiftl_word_eq push_bit_eq_mult)

lemma mask_eq:
  \<open>mask n = 2 ^ n - 1\<close>
  by (simp add: mask_eq_mask mask_eq_exp_minus_1)

lemma mask_Suc_rec:
  \<open>mask (Suc n) = 2 * mask n + 1\<close>
  by (simp add: mask_eq)

context
begin

qualified lemma bit_mask_iff:
  \<open>bit (mask m :: 'a::len word) n \<longleftrightarrow> n < min LENGTH('a) m\<close>
  by (simp add: mask_eq_mask bit_mask_iff exp_eq_zero_iff not_le)

end

lemma nth_mask [simp]:
  \<open>(mask n :: 'a::len word) !! i \<longleftrightarrow> i < n \<and> i < size (mask n :: 'a word)\<close>
  by (auto simp add: test_bit_word_eq word_size Word.bit_mask_iff)

lemma mask_bl: "mask n = of_bl (replicate n True)"
  by (auto simp add : test_bit_of_bl word_size intro: word_eqI)

lemma mask_bin: "mask n = word_of_int (bintrunc n (- 1))"
  by (auto simp add: nth_bintr word_size intro: word_eqI)

lemma and_mask_bintr: "w AND mask n = word_of_int (bintrunc n (uint w))"
  apply (rule word_eqI)
  apply (simp add: nth_bintr word_size word_ops_nth_size)
  apply (auto simp add: test_bit_bin)
  done

lemma and_mask_wi: "word_of_int i AND mask n = word_of_int (bintrunc n i)"
  by (auto simp add: nth_bintr word_size word_ops_nth_size word_eq_iff)

lemma and_mask_wi':
  "word_of_int i AND mask n = (word_of_int (bintrunc (min LENGTH('a) n) i) :: 'a::len word)"
  by (auto simp add: nth_bintr word_size word_ops_nth_size word_eq_iff)

lemma and_mask_no: "numeral i AND mask n = word_of_int (bintrunc n (numeral i))"
  unfolding word_numeral_alt by (rule and_mask_wi)

lemma bl_and_mask':
  "to_bl (w AND mask n :: 'a::len word) =
    replicate (LENGTH('a) - n) False @
    drop (LENGTH('a) - n) (to_bl w)"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp add: to_bl_nth word_size)
  apply (simp add: word_size word_ops_nth_size)
  apply (auto simp add: word_size test_bit_bl nth_append rev_nth)
  done

lemma and_mask_mod_2p: "w AND mask n = word_of_int (uint w mod 2 ^ n)"
  by (simp only: and_mask_bintr bintrunc_mod2p)

lemma and_mask_lt_2p: "uint (w AND mask n) < 2 ^ n"
  by (simp add: and_mask_bintr uint.abs_eq min_def not_le lt2p_lem bintr_lt2p)

lemma eq_mod_iff: "0 < n \<Longrightarrow> b = b mod n \<longleftrightarrow> 0 \<le> b \<and> b < n"
  for b n :: int
  by auto (metis pos_mod_conj)+

lemma mask_eq_iff: "w AND mask n = w \<longleftrightarrow> uint w < 2 ^ n"
  apply (simp add: and_mask_bintr)
  apply (simp add: word_ubin.inverse_norm)
  apply (simp add: eq_mod_iff bintrunc_mod2p min_def)
  apply (fast intro!: lt2p_lem)
  done

lemma and_mask_dvd: "2 ^ n dvd uint w \<longleftrightarrow> w AND mask n = 0"
  apply (simp add: dvd_eq_mod_eq_0 and_mask_mod_2p)
  apply (simp add: word_uint.norm_eq_iff [symmetric] word_of_int_homs del: word_of_int_0)
  apply (subst word_uint.norm_Rep [symmetric])
  apply (simp only: bintrunc_bintrunc_min bintrunc_mod2p [symmetric] min_def)
  apply auto
  done

lemma and_mask_dvd_nat: "2 ^ n dvd unat w \<longleftrightarrow> w AND mask n = 0"
  apply (unfold unat_def)
  apply (rule trans [OF _ and_mask_dvd])
  apply (unfold dvd_def)
  apply auto
   apply (drule uint_ge_0 [THEN nat_int.Abs_inverse' [simplified], symmetric])
   apply simp
  apply (simp add: nat_mult_distrib nat_power_eq)
  done

lemma word_2p_lem: "n < size w \<Longrightarrow> w < 2 ^ n = (uint w < 2 ^ n)"
  for w :: "'a::len word"
  apply (unfold word_size word_less_alt word_numeral_alt)
  apply (auto simp add: word_of_int_power_hom word_uint.eq_norm
      simp del: word_of_int_numeral)
  done

lemma less_mask_eq: "x < 2 ^ n \<Longrightarrow> x AND mask n = x"
  for x :: "'a::len word"
  apply (simp add: and_mask_bintr)
  apply transfer
  apply (simp add: ac_simps)
  apply (auto simp add: min_def)
  apply (metis bintrunc_bintrunc_ge mod_pos_pos_trivial mult.commute mult.left_neutral mult_zero_left not_le of_bool_def take_bit_eq_mod take_bit_nonnegative)
  done

lemmas mask_eq_iff_w2p = trans [OF mask_eq_iff word_2p_lem [symmetric]]

lemmas and_mask_less' = iffD2 [OF word_2p_lem and_mask_lt_2p, simplified word_size]

lemma and_mask_less_size: "n < size x \<Longrightarrow> x AND mask n < 2^n"
  unfolding word_size by (erule and_mask_less')

lemma word_mod_2p_is_mask [OF refl]: "c = 2 ^ n \<Longrightarrow> c > 0 \<Longrightarrow> x mod c = x AND mask n"
  for c x :: "'a::len word"
  by (auto simp: word_mod_def uint_2p and_mask_mod_2p)

lemma mask_eqs:
  "(a AND mask n) + b AND mask n = a + b AND mask n"
  "a + (b AND mask n) AND mask n = a + b AND mask n"
  "(a AND mask n) - b AND mask n = a - b AND mask n"
  "a - (b AND mask n) AND mask n = a - b AND mask n"
  "a * (b AND mask n) AND mask n = a * b AND mask n"
  "(b AND mask n) * a AND mask n = b * a AND mask n"
  "(a AND mask n) + (b AND mask n) AND mask n = a + b AND mask n"
  "(a AND mask n) - (b AND mask n) AND mask n = a - b AND mask n"
  "(a AND mask n) * (b AND mask n) AND mask n = a * b AND mask n"
  "- (a AND mask n) AND mask n = - a AND mask n"
  "word_succ (a AND mask n) AND mask n = word_succ a AND mask n"
  "word_pred (a AND mask n) AND mask n = word_pred a AND mask n"
  using word_of_int_Ex [where x=a] word_of_int_Ex [where x=b]
  by (auto simp: and_mask_wi' word_of_int_homs word.abs_eq_iff bintrunc_mod2p mod_simps)

lemma mask_power_eq: "(x AND mask n) ^ k AND mask n = x ^ k AND mask n"
  using word_of_int_Ex [where x=x]
  by (auto simp: and_mask_wi' word_of_int_power_hom word.abs_eq_iff bintrunc_mod2p mod_simps)

lemma mask_full [simp]: "mask LENGTH('a) = (- 1 :: 'a::len word)"
  by (simp add: mask_def word_size shiftl_zero_size)


subsubsection \<open>Slices\<close>

definition slice1 :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>slice1 n w = (if n < LENGTH('a)
    then ucast (drop_bit (LENGTH('a) - n) w)
    else push_bit (n - LENGTH('a)) (ucast w))\<close>

lemma bit_slice1_iff:
  \<open>bit (slice1 m w :: 'b::len word) n \<longleftrightarrow> m - LENGTH('a) \<le> n \<and> n < min LENGTH('b) m
    \<and> bit w (n + (LENGTH('a) - m) - (m - LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: slice1_def bit_ucast_iff bit_drop_bit_eq bit_push_bit_iff exp_eq_zero_iff not_less not_le ac_simps
    dest: bit_imp_le_length)

lemma slice1_eq_of_bl:
  \<open>(slice1 n w :: 'b::len word) = of_bl (takefill False n (to_bl w))\<close>
  for w :: \<open>'a::len word\<close>
proof (rule bit_word_eqI)
  fix m
  assume \<open>m \<le> LENGTH('b)\<close>
  show \<open>bit (slice1 n w :: 'b::len word) m \<longleftrightarrow> bit (of_bl (takefill False n (to_bl w)) :: 'b word) m\<close>
    by (cases \<open>m \<ge> n\<close>; cases \<open>LENGTH('a) \<ge> n\<close>)
      (auto simp add: bit_slice1_iff bit_of_bl_iff not_less rev_nth not_le nth_takefill nth_to_bl algebra_simps)
qed

definition slice :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>slice n = slice1 (LENGTH('a) - n)\<close>

lemma bit_slice_iff:
  \<open>bit (slice m w :: 'b::len word) n \<longleftrightarrow> n < min LENGTH('b) (LENGTH('a) - m) \<and> bit w (n + LENGTH('a) - (LENGTH('a) - m))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: slice_def word_size bit_slice1_iff)

lemma slice1_no_bin [simp]:
  "slice1 n (numeral w :: 'b word) = of_bl (takefill False n (bin_to_bl (LENGTH('b::len)) (numeral w)))"
  by (simp add: slice1_eq_of_bl) (* TODO: neg_numeral *)

lemma slice_no_bin [simp]:
  "slice n (numeral w :: 'b word) = of_bl (takefill False (LENGTH('b::len) - n)
    (bin_to_bl (LENGTH('b::len)) (numeral w)))"
  by (simp add: slice_def) (* TODO: neg_numeral *)

lemma slice1_0 [simp] : "slice1 n 0 = 0"
  unfolding slice1_def by simp

lemma slice_0 [simp] : "slice n 0 = 0"
  unfolding slice_def by auto

lemma slice_take': "slice n w = of_bl (take (size w - n) (to_bl w))"
  by (simp add: slice_def word_size slice1_eq_of_bl takefill_alt)

lemmas slice_take = slice_take' [unfolded word_size]

\<comment> \<open>shiftr to a word of the same size is just slice,
    slice is just shiftr then ucast\<close>
lemmas shiftr_slice = trans [OF shiftr_bl [THEN meta_eq_to_obj_eq] slice_take [symmetric]]

lemma slice_shiftr: "slice n w = ucast (w >> n)"
  apply (unfold slice_take shiftr_bl)
  apply (rule ucast_of_bl_up [symmetric])
  apply (simp add: word_size)
  done

lemma nth_slice: "(slice n w :: 'a::len word) !! m = (w !! (m + n) \<and> m < LENGTH('a))"
  by (simp add: slice_shiftr nth_ucast nth_shiftr)

lemma slice1_down_alt':
  "sl = slice1 n w \<Longrightarrow> fs = size sl \<Longrightarrow> fs + k = n \<Longrightarrow>
    to_bl sl = takefill False fs (drop k (to_bl w))"
  by (auto simp: slice1_eq_of_bl word_size of_bl_def uint_bl
      word_ubin.eq_norm bl_bin_bl_rep_drop drop_takefill)

lemma slice1_up_alt':
  "sl = slice1 n w \<Longrightarrow> fs = size sl \<Longrightarrow> fs = n + k \<Longrightarrow>
    to_bl sl = takefill False fs (replicate k False @ (to_bl w))"
  apply (unfold slice1_eq_of_bl word_size of_bl_def uint_bl)
  apply (clarsimp simp: word_ubin.eq_norm bl_bin_bl_rep_drop takefill_append [symmetric])
  apply (rule_tac f = "\<lambda>k. takefill False (LENGTH('a))
    (replicate k False @ bin_to_bl (LENGTH('b)) (uint w))" in arg_cong)
  apply arith
  done

lemmas sd1 = slice1_down_alt' [OF refl refl, unfolded word_size]
lemmas su1 = slice1_up_alt' [OF refl refl, unfolded word_size]
lemmas slice1_down_alt = le_add_diff_inverse [THEN sd1]
lemmas slice1_up_alts =
  le_add_diff_inverse [symmetric, THEN su1]
  le_add_diff_inverse2 [symmetric, THEN su1]

lemma ucast_slice1: "ucast w = slice1 (size w) w"
  by (simp add: slice1_def ucast_bl takefill_same' word_size)

lemma ucast_slice: "ucast w = slice 0 w"
  by (simp add: slice_def slice1_def)

lemma slice_id: "slice 0 t = t"
  by (simp only: ucast_slice [symmetric] ucast_id)

lemma slice1_tf_tf':
  "to_bl (slice1 n w :: 'a::len word) =
    rev (takefill False (LENGTH('a)) (rev (takefill False n (to_bl w))))"
  unfolding slice1_eq_of_bl by (rule word_rev_tf)

lemmas slice1_tf_tf = slice1_tf_tf' [THEN word_bl.Rep_inverse', symmetric]

lemma rev_slice1:
  "n + k = LENGTH('a) + LENGTH('b) \<Longrightarrow>
    slice1 n (word_reverse w :: 'b::len word) =
    word_reverse (slice1 k w :: 'a::len word)"
  apply (unfold word_reverse_eq_of_bl_rev_to_bl slice1_tf_tf)
  apply (rule word_bl.Rep_inverse')
  apply (rule rev_swap [THEN iffD1])
  apply (rule trans [symmetric])
   apply (rule tf_rev)
   apply (simp add: word_bl.Abs_inverse)
  apply (simp add: word_bl.Abs_inverse)
  done

lemma rev_slice:
  "n + k + LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow>
    slice n (word_reverse (w::'b word)) = word_reverse (slice k w :: 'a word)"
  apply (unfold slice_def word_size)
  apply (rule rev_slice1)
  apply arith
  done


subsubsection \<open>Revcast\<close>

definition revcast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>revcast = slice1 LENGTH('b)\<close>

lemma bit_revcast_iff:
  \<open>bit (revcast w :: 'b::len word) n \<longleftrightarrow> LENGTH('b) - LENGTH('a) \<le> n \<and> n < LENGTH('b)
    \<and> bit w (n + (LENGTH('a) - LENGTH('b)) - (LENGTH('b) - LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: revcast_def bit_slice1_iff)

lemma revcast_eq_of_bl:
  \<open>(revcast w :: 'b::len word) = of_bl (takefill False (LENGTH('b)) (to_bl w))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: revcast_def slice1_eq_of_bl)

lemma revcast_slice1 [OF refl]: "rc = revcast w \<Longrightarrow> slice1 (size rc) w = rc"
  by (simp add: revcast_def word_size)

lemmas revcast_no_def [simp] = revcast_eq_of_bl [where w="numeral w", unfolded word_size] for w

lemma to_bl_revcast:
  "to_bl (revcast w :: 'a::len word) = takefill False (LENGTH('a)) (to_bl w)"
  apply (rule nth_equalityI)
  apply simp
  apply (cases \<open>LENGTH('a) \<le> LENGTH('b)\<close>)
   apply (auto simp add: nth_to_bl nth_takefill bit_revcast_iff)
  done

lemma revcast_rev_ucast [OF refl refl refl]:
  "cs = [rc, uc] \<Longrightarrow> rc = revcast (word_reverse w) \<Longrightarrow> uc = ucast w \<Longrightarrow>
    rc = word_reverse uc"
  apply auto
  apply (rule bit_word_eqI)
  apply (cases \<open>LENGTH('a) \<le> LENGTH('b)\<close>)
   apply (simp_all add: bit_revcast_iff bit_word_reverse_iff bit_ucast_iff not_le
     bit_imp_le_length)
  using bit_imp_le_length apply fastforce
  using bit_imp_le_length apply fastforce
  done

lemma revcast_ucast: "revcast w = word_reverse (ucast (word_reverse w))"
  using revcast_rev_ucast [of "word_reverse w"] by simp

lemma ucast_revcast: "ucast w = word_reverse (revcast (word_reverse w))"
  by (fact revcast_rev_ucast [THEN word_rev_gal'])

lemma ucast_rev_revcast: "ucast (word_reverse w) = word_reverse (revcast w)"
  by (fact revcast_ucast [THEN word_rev_gal'])


text "linking revcast and cast via shift"

lemmas wsst_TYs = source_size target_size word_size

lemma revcast_down_uu [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: revcast_eq_of_bl)
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule ucast_down_drop)
   prefer 2
   apply (rule trans, rule drop_shiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_us [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: revcast_eq_of_bl)
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule ucast_down_drop)
   prefer 2
   apply (rule trans, rule drop_sshiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_su [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: revcast_eq_of_bl)
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule scast_down_drop)
   prefer 2
   apply (rule trans, rule drop_shiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_ss [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: revcast_eq_of_bl)
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule scast_down_drop)
   prefer 2
   apply (rule trans, rule drop_sshiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

(* FIXME: should this also be [OF refl] ? *)
lemma cast_down_rev:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> uc w = revcast (w << n)"
  for w :: "'a::len word"
  apply (unfold shiftl_rev)
  apply clarify
  apply (simp add: revcast_rev_ucast)
  apply (rule word_rev_gal')
  apply (rule trans [OF _ revcast_rev_ucast])
  apply (rule revcast_down_uu [symmetric])
  apply (auto simp add: wsst_TYs)
  done

lemma revcast_up [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc + n = target_size rc \<Longrightarrow>
    rc w = (ucast w :: 'a::len word) << n"
  apply (simp add: revcast_eq_of_bl)
  apply (rule word_bl.Rep_inverse')
  apply (simp add: takefill_alt)
  apply (rule bl_shiftl [THEN trans])
  apply (subst ucast_up_app)
   apply (auto simp add: wsst_TYs)
  done

lemmas rc1 = revcast_up [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]
lemmas rc2 = revcast_down_uu [THEN
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]

lemmas ucast_up =
 rc1 [simplified rev_shiftr [symmetric] revcast_ucast [symmetric]]
lemmas ucast_down =
  rc2 [simplified rev_shiftr revcast_ucast [symmetric]]

lemmas sym_notr =
  not_iff [THEN iffD2, THEN not_sym, THEN not_iff [THEN iffD1]]

\<comment> \<open>problem posed by TPHOLs referee:
      criterion for overflow of addition of signed integers\<close>

lemma sofl_test:
  \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (x + y XOR x) AND (x + y XOR y) >> (size x - 1) = 0\<close>
  for x y :: \<open>'a::len word\<close>
proof -
  obtain n where n: \<open>LENGTH('a) = Suc n\<close>
    by (cases \<open>LENGTH('a)\<close>) simp_all
  have *: \<open>sint x + sint y + 2 ^ Suc n > signed_take_bit n (sint x + sint y) \<Longrightarrow> sint x + sint y \<ge> - (2 ^ n)\<close>
    \<open>signed_take_bit n (sint x + sint y) > sint x + sint y - 2 ^ Suc n \<Longrightarrow> 2 ^ n > sint x + sint y\<close>
    using signed_take_bit_greater_eq [of \<open>sint x + sint y\<close> n] signed_take_bit_less_eq [of n \<open>sint x + sint y\<close>]
    by (auto intro: ccontr)
  have \<open>sint x + sint y = sint (x + y) \<longleftrightarrow>
    (sint (x + y) < 0 \<longleftrightarrow> sint x < 0) \<or>
    (sint (x + y) < 0 \<longleftrightarrow> sint y < 0)\<close>
    using sint_range' [of x] sint_range' [of y]
    apply (auto simp add: not_less)
       apply (unfold sint_word_ariths word_sbin.set_iff_norm [symmetric] sints_num)
       apply (auto simp add: signed_take_bit_eq_take_bit_minus take_bit_Suc_from_most n not_less intro!: *)
    done
  then show ?thesis
    apply (simp add: word_size shiftr_word_eq drop_bit_eq_zero_iff_not_bit_last bit_and_iff bit_xor_iff)
    apply (simp add: bit_last_iff)
    done
qed

lemma shiftr_zero_size: "size x \<le> n \<Longrightarrow> x >> n = 0"
  for x :: "'a :: len word"
  by (rule word_eqI) (auto simp add: nth_shiftr dest: test_bit_size)


subsection \<open>Split and cat\<close>

lemmas word_split_bin' = word_split_def
lemmas word_cat_bin' = word_cat_def

lemma word_rsplit_no:
  "(word_rsplit (numeral bin :: 'b::len word) :: 'a word list) =
    map word_of_int (bin_rsplit (LENGTH('a::len))
      (LENGTH('b), bintrunc (LENGTH('b)) (numeral bin)))"
  by (simp add: word_rsplit_def word_ubin.eq_norm)

lemmas word_rsplit_no_cl [simp] = word_rsplit_no
  [unfolded bin_rsplitl_def bin_rsplit_l [symmetric]]

lemma test_bit_cat:
  "wc = word_cat a b \<Longrightarrow> wc !! n = (n < size wc \<and>
    (if n < size b then b !! n else a !! (n - size b)))"
  apply (auto simp: word_cat_bin' test_bit_bin word_ubin.eq_norm nth_bintr bin_nth_cat word_size)
  apply (erule bin_nth_uint_imp)
  done

lemma word_cat_bl: "word_cat a b = of_bl (to_bl a @ to_bl b)"
  by (simp add: of_bl_def to_bl_def word_cat_bin' bl_to_bin_app_cat)

lemma of_bl_append:
  "(of_bl (xs @ ys) :: 'a::len word) = of_bl xs * 2^(length ys) + of_bl ys"
  apply (simp add: of_bl_def bl_to_bin_app_cat bin_cat_num)
  apply (simp add: word_of_int_power_hom [symmetric] word_of_int_hom_syms)
  done

lemma of_bl_False [simp]: "of_bl (False#xs) = of_bl xs"
  by (rule word_eqI) (auto simp: test_bit_of_bl nth_append)

lemma of_bl_True [simp]: "(of_bl (True # xs) :: 'a::len word) = 2^length xs + of_bl xs"
  by (subst of_bl_append [where xs="[True]", simplified]) (simp add: word_1_bl)

lemma of_bl_Cons: "of_bl (x#xs) = of_bool x * 2^length xs + of_bl xs"
  by (cases x) simp_all

lemma split_uint_lem: "bin_split n (uint w) = (a, b) \<Longrightarrow>
    a = bintrunc (LENGTH('a) - n) a \<and> b = bintrunc (LENGTH('a)) b"
  for w :: "'a::len word"
  apply (frule word_ubin.norm_Rep [THEN ssubst])
  apply (drule bin_split_trunc1)
  apply (drule sym [THEN trans])
   apply assumption
  apply safe
  done

lemma word_split_bl':
  "std = size c - size b \<Longrightarrow> (word_split c = (a, b)) \<Longrightarrow>
    (a = of_bl (take std (to_bl c)) \<and> b = of_bl (drop std (to_bl c)))"
  apply (unfold word_split_bin')
  apply safe
   defer
   apply (clarsimp split: prod.splits)
  apply (metis of_bl_drop' ucast_bl ucast_def word_size word_size_bl)
   apply hypsubst_thin
   apply (drule word_ubin.norm_Rep [THEN ssubst])
   apply (simp add: of_bl_def bl2bin_drop word_size
      word_ubin.norm_eq_iff [symmetric] min_def del: word_ubin.norm_Rep)
  apply (clarsimp split: prod.splits)
  apply (cases "LENGTH('a) \<ge> LENGTH('b)")
   apply (simp_all add: not_le)
  defer
   apply (simp add: drop_bit_eq_div lt2p_lem)
  apply (simp add : of_bl_def to_bl_def)
  apply (subst bin_to_bl_drop_bit [symmetric])
   apply (subst diff_add)
    apply (simp_all add: take_bit_drop_bit)
  done

lemma word_split_bl: "std = size c - size b \<Longrightarrow>
    (a = of_bl (take std (to_bl c)) \<and> b = of_bl (drop std (to_bl c))) \<longleftrightarrow>
    word_split c = (a, b)"
  apply (rule iffI)
   defer
   apply (erule (1) word_split_bl')
  apply (case_tac "word_split c")
  apply (auto simp add: word_size)
  apply (frule word_split_bl' [rotated])
   apply (auto simp add: word_size)
  done

lemma word_split_bl_eq:
  "(word_split c :: ('c::len word \<times> 'd::len word)) =
    (of_bl (take (LENGTH('a::len) - LENGTH('d::len)) (to_bl c)),
     of_bl (drop (LENGTH('a) - LENGTH('d)) (to_bl c)))"
  for c :: "'a::len word"
  apply (rule word_split_bl [THEN iffD1])
   apply (unfold word_size)
   apply (rule refl conjI)+
  done

\<comment> \<open>keep quantifiers for use in simplification\<close>
lemma test_bit_split':
  "word_split c = (a, b) \<longrightarrow>
    (\<forall>n m.
      b !! n = (n < size b \<and> c !! n) \<and>
      a !! m = (m < size a \<and> c !! (m + size b)))"
  apply (unfold word_split_bin' test_bit_bin)
  apply (clarify)
  apply (clarsimp simp: word_ubin.eq_norm nth_bintr word_size split: prod.splits)
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq ac_simps bin_nth_uint_imp)
  done

lemma test_bit_split:
  "word_split c = (a, b) \<Longrightarrow>
    (\<forall>n::nat. b !! n \<longleftrightarrow> n < size b \<and> c !! n) \<and>
    (\<forall>m::nat. a !! m \<longleftrightarrow> m < size a \<and> c !! (m + size b))"
  by (simp add: test_bit_split')

lemma test_bit_split_eq:
  "word_split c = (a, b) \<longleftrightarrow>
    ((\<forall>n::nat. b !! n = (n < size b \<and> c !! n)) \<and>
     (\<forall>m::nat. a !! m = (m < size a \<and> c !! (m + size b))))"
  apply (rule_tac iffI)
   apply (rule_tac conjI)
    apply (erule test_bit_split [THEN conjunct1])
   apply (erule test_bit_split [THEN conjunct2])
  apply (case_tac "word_split c")
  apply (frule test_bit_split)
  apply (erule trans)
  apply (fastforce intro!: word_eqI simp add: word_size)
  done

\<comment> \<open>this odd result is analogous to \<open>ucast_id\<close>,
      result to the length given by the result type\<close>

lemma word_cat_id: "word_cat a b = b"
  by (simp add: word_cat_bin' word_ubin.inverse_norm)

\<comment> \<open>limited hom result\<close>
lemma word_cat_hom:
  "LENGTH('a::len) \<le> LENGTH('b::len) + LENGTH('c::len) \<Longrightarrow>
    (word_cat (word_of_int w :: 'b word) (b :: 'c word) :: 'a word) =
    word_of_int (bin_cat w (size b) (uint b))"
  by (auto simp: word_cat_def word_size word_ubin.norm_eq_iff [symmetric]
      word_ubin.eq_norm bintr_cat min.absorb1)

lemma word_cat_split_alt: "size w \<le> size u + size v \<Longrightarrow> word_split w = (u, v) \<Longrightarrow> word_cat u v = w"
  apply (rule word_eqI)
  apply (drule test_bit_split)
  apply (clarsimp simp add : test_bit_cat word_size)
  apply safe
  apply arith
  done

lemmas word_cat_split_size = sym [THEN [2] word_cat_split_alt [symmetric]]


subsubsection \<open>Split and slice\<close>

lemma split_slices: "word_split w = (u, v) \<Longrightarrow> u = slice (size v) w \<and> v = slice 0 w"
  apply (drule test_bit_split)
  apply (rule conjI)
   apply (rule word_eqI, clarsimp simp: nth_slice word_size)+
  done

lemma slice_cat1 [OF refl]:
  "wc = word_cat a b \<Longrightarrow> size wc >= size a + size b \<Longrightarrow> slice (size b) wc = a"
  apply safe
  apply (rule word_eqI)
  apply (simp add: nth_slice test_bit_cat word_size)
  done

lemmas slice_cat2 = trans [OF slice_id word_cat_id]

lemma cat_slices:
  "a = slice n c \<Longrightarrow> b = slice 0 c \<Longrightarrow> n = size b \<Longrightarrow>
    size a + size b >= size c \<Longrightarrow> word_cat a b = c"
  apply safe
  apply (rule word_eqI)
  apply (simp add: nth_slice test_bit_cat word_size)
  apply safe
  apply arith
  done

lemma word_split_cat_alt:
  "w = word_cat u v \<Longrightarrow> size u + size v \<le> size w \<Longrightarrow> word_split w = (u, v)"
  apply (case_tac "word_split w")
  apply (rule trans, assumption)
  apply (drule test_bit_split)
  apply safe
   apply (rule word_eqI, clarsimp simp: test_bit_cat word_size)+
  done

lemmas word_cat_bl_no_bin [simp] =
  word_cat_bl [where a="numeral a" and b="numeral b", unfolded to_bl_numeral]
  for a b (* FIXME: negative numerals, 0 and 1 *)

lemmas word_split_bl_no_bin [simp] =
  word_split_bl_eq [where c="numeral c", unfolded to_bl_numeral] for c

text \<open>
  This odd result arises from the fact that the statement of the
  result implies that the decoded words are of the same type,
  and therefore of the same length, as the original word.\<close>

lemma word_rsplit_same: "word_rsplit w = [w]"
  by (simp add: word_rsplit_def bin_rsplit_all)

lemma word_rsplit_empty_iff_size: "word_rsplit w = [] \<longleftrightarrow> size w = 0"
  by (simp add: word_rsplit_def bin_rsplit_def word_size bin_rsplit_aux_simp_alt Let_def
      split: prod.split)

lemma test_bit_rsplit:
  "sw = word_rsplit w \<Longrightarrow> m < size (hd sw) \<Longrightarrow>
    k < length sw \<Longrightarrow> (rev sw ! k) !! m = w !! (k * size (hd sw) + m)"
  for sw :: "'a::len word list"
  apply (unfold word_rsplit_def word_test_bit_def)
  apply (rule trans)
   apply (rule_tac f = "\<lambda>x. bin_nth x m" in arg_cong)
   apply (rule nth_map [symmetric])
   apply simp
  apply (rule bin_nth_rsplit)
     apply simp_all
  apply (simp add : word_size rev_map)
  apply (rule trans)
   defer
   apply (rule map_ident [THEN fun_cong])
  apply (rule refl [THEN map_cong])
  apply (simp add : word_ubin.eq_norm)
  apply (erule bin_rsplit_size_sign [OF len_gt_0 refl])
  done

lemma word_rcat_bl: "word_rcat wl = of_bl (concat (map to_bl wl))"
  by (auto simp: word_rcat_def to_bl_def' of_bl_def bin_rcat_bl)

lemma size_rcat_lem': "size (concat (map to_bl wl)) = length wl * size (hd wl)"
  by (induct wl) (auto simp: word_size)

lemmas size_rcat_lem = size_rcat_lem' [unfolded word_size]

lemma nth_rcat_lem:
  "n < length (wl::'a word list) * LENGTH('a::len) \<Longrightarrow>
    rev (concat (map to_bl wl)) ! n =
    rev (to_bl (rev wl ! (n div LENGTH('a)))) ! (n mod LENGTH('a))"
  apply (induct wl)
   apply clarsimp
  apply (clarsimp simp add : nth_append size_rcat_lem)
  apply (simp flip: mult_Suc minus_div_mult_eq_mod add: less_Suc_eq_le not_less)
  apply (metis (no_types, lifting) diff_is_0_eq div_le_mono len_not_eq_0 less_Suc_eq less_mult_imp_div_less nonzero_mult_div_cancel_right not_le nth_Cons_0)
  done

lemma test_bit_rcat:
  "sw = size (hd wl) \<Longrightarrow> rc = word_rcat wl \<Longrightarrow> rc !! n =
    (n < size rc \<and> n div sw < size wl \<and> (rev wl) ! (n div sw) !! (n mod sw))"
  for wl :: "'a::len word list"
  apply (unfold word_rcat_bl word_size)
  apply (clarsimp simp add: test_bit_of_bl size_rcat_lem word_size)
  apply (metis div_le_mono len_gt_0 len_not_eq_0 less_mult_imp_div_less mod_less_divisor nonzero_mult_div_cancel_right not_le nth_rcat_lem test_bit_bl word_size)
  done

lemma foldl_eq_foldr: "foldl (+) x xs = foldr (+) (x # xs) 0"
  for x :: "'a::comm_monoid_add"
  by (induct xs arbitrary: x) (auto simp: add.assoc)

lemmas test_bit_cong = arg_cong [where f = "test_bit", THEN fun_cong]

lemma test_bit_rsplit_alt:
  \<open>(word_rsplit w  :: 'b::len word list) ! i !! m \<longleftrightarrow>
    w !! ((length (word_rsplit w :: 'b::len word list) - Suc i) * size (hd (word_rsplit w :: 'b::len word list)) + m)\<close>
  if \<open>i < length (word_rsplit w :: 'b::len word list)\<close> \<open>m < size (hd (word_rsplit w :: 'b::len word list))\<close> \<open>0 < length (word_rsplit w :: 'b::len word list)\<close>
  for w :: \<open>'a::len word\<close>
  apply (rule trans)
   apply (rule test_bit_cong)
   apply (rule rev_nth [of _ \<open>rev (word_rsplit w)\<close>, simplified rev_rev_ident])
  apply simp
   apply (rule that(1))
  apply simp
  apply (rule test_bit_rsplit)
    apply (rule refl)
  apply (rule asm_rl)
   apply (rule that(2))
  apply (rule diff_Suc_less)
  apply (rule that(3))
  done

lemma word_rsplit_len_indep [OF refl refl refl refl]:
  "[u,v] = p \<Longrightarrow> [su,sv] = q \<Longrightarrow> word_rsplit u = su \<Longrightarrow>
    word_rsplit v = sv \<Longrightarrow> length su = length sv"
  by (auto simp: word_rsplit_def bin_rsplit_len_indep)

lemma length_word_rsplit_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) \<le> m \<longleftrightarrow> size w \<le> m * n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len_le)

lemmas length_word_rsplit_lt_size =
  length_word_rsplit_size [unfolded Not_eq_iff linorder_not_less [symmetric]]

lemma length_word_rsplit_exp_size:
  "n = LENGTH('a::len) \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = (size w + n - 1) div n"
  by (auto simp: word_rsplit_def word_size bin_rsplit_len)

lemma length_word_rsplit_even_size:
  "n = LENGTH('a::len) \<Longrightarrow> size w = m * n \<Longrightarrow>
    length (word_rsplit w :: 'a word list) = m"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: length_word_rsplit_exp_size div_nat_eqI)

lemmas length_word_rsplit_exp_size' = refl [THEN length_word_rsplit_exp_size]

\<comment> \<open>alternative proof of \<open>word_rcat_rsplit\<close>\<close>
lemmas tdle = times_div_less_eq_dividend
lemmas dtle = xtrans(4) [OF tdle mult.commute]

lemma word_rcat_rsplit: "word_rcat (word_rsplit w) = w"
  apply (rule word_eqI)
  apply (clarsimp simp: test_bit_rcat word_size)
  apply (subst refl [THEN test_bit_rsplit])
    apply (simp_all add: word_size
      refl [THEN length_word_rsplit_size [simplified not_less [symmetric], simplified]])
   apply safe
   apply (erule xtrans(7), rule dtle)+
  done

lemma size_word_rsplit_rcat_size:
  "word_rcat ws = frcw \<Longrightarrow> size frcw = length ws * LENGTH('a)
    \<Longrightarrow> length (word_rsplit frcw::'a word list) = length ws"
  for ws :: "'a::len word list" and frcw :: "'b::len word"
  by (cases \<open>LENGTH('a)\<close>) (simp_all add: word_size length_word_rsplit_exp_size' div_nat_eqI)

lemma msrevs:
  "0 < n \<Longrightarrow> (k * n + m) div n = m div n + k"
  "(k * n + m) mod n = m mod n"
  for n :: nat
  by (auto simp: add.commute)

lemma word_rsplit_rcat_size [OF refl]:
  "word_rcat ws = frcw \<Longrightarrow>
    size frcw = length ws * LENGTH('a) \<Longrightarrow> word_rsplit frcw = ws"
  for ws :: "'a::len word list"
  apply (frule size_word_rsplit_rcat_size, assumption)
  apply (clarsimp simp add : word_size)
  apply (rule nth_equalityI, assumption)
  apply clarsimp
  apply (rule word_eqI [rule_format])
  apply (rule trans)
   apply (rule test_bit_rsplit_alt)
     apply (clarsimp simp: word_size)+
  apply (rule trans)
   apply (rule test_bit_rcat [OF refl refl])
  apply (simp add: word_size)
  apply (subst rev_nth)
   apply arith
  apply (simp add: le0 [THEN [2] xtrans(7), THEN diff_Suc_less])
  apply safe
  apply (simp add: diff_mult_distrib)
   apply (cases "size ws")
    apply simp_all
  done


subsection \<open>Rotation\<close>

lemmas rotater_0' [simp] = rotater_def [where n = "0", simplified]

lemma bit_word_rotl_iff:
  \<open>bit (word_rotl m w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w ((n + (LENGTH('a) - m mod LENGTH('a))) mod LENGTH('a))\<close>
  for w :: \<open>'a::len word\<close>
proof (cases \<open>n < LENGTH('a)\<close>)
  case False
  then show ?thesis
    by (auto dest: bit_imp_le_length)
next
  case True
  define k where \<open>k = int n - int m\<close>
  then have k: \<open>int n = k + int m\<close>
    by simp
  define l where \<open>l = int LENGTH('a)\<close>
  then have l: \<open>int LENGTH('a) = l\<close> \<open>l > 0\<close>
    by simp_all
  have *: \<open>int (m - n) = int m - int n\<close> if \<open>n \<le> m\<close> for n m
    using that by (simp add: int_minus)
  from \<open>l > 0\<close> have \<open>l = 1 + (k mod l + ((- 1 - k) mod l))\<close>
    using minus_mod_int_eq [of l \<open>k + 1\<close>] by (simp add: algebra_simps)
  then have \<open>int (LENGTH('a) - Suc ((m + LENGTH('a) - Suc n) mod LENGTH('a))) =
    int ((n + LENGTH('a) - m mod LENGTH('a)) mod LENGTH('a))\<close>
    by (simp add: * k l zmod_int Suc_leI trans_le_add2 algebra_simps mod_simps \<open>n < LENGTH('a)\<close>)
  then have \<open>LENGTH('a) - Suc ((m + LENGTH('a) - Suc n) mod LENGTH('a)) =
    (n + LENGTH('a) - m mod LENGTH('a)) mod LENGTH('a)\<close>
    by simp
  with True show ?thesis
    by (simp add: word_rotl_def bit_of_bl_iff rev_nth nth_rotate nth_to_bl)
qed

lemmas word_rot_defs = word_roti_def word_rotr_def word_rotl_def

lemma rotate_eq_mod: "m mod length xs = n mod length xs \<Longrightarrow> rotate m xs = rotate n xs"
  apply (rule box_equals)
    defer
    apply (rule rotate_conv_mod [symmetric])+
  apply simp
  done

lemmas rotate_eqs =
  trans [OF rotate0 [THEN fun_cong] id_apply]
  rotate_rotate [symmetric]
  rotate_id
  rotate_conv_mod
  rotate_eq_mod


subsubsection \<open>Rotation of list to right\<close>

lemma rotate1_rl': "rotater1 (l @ [a]) = a # l"
  by (cases l) (auto simp: rotater1_def)

lemma rotate1_rl [simp] : "rotater1 (rotate1 l) = l"
  apply (unfold rotater1_def)
  apply (cases "l")
   apply (case_tac [2] "list")
    apply auto
  done

lemma rotate1_lr [simp] : "rotate1 (rotater1 l) = l"
  by (cases l) (auto simp: rotater1_def)

lemma rotater1_rev': "rotater1 (rev xs) = rev (rotate1 xs)"
  by (cases "xs") (simp add: rotater1_def, simp add: rotate1_rl')

lemma rotater_rev': "rotater n (rev xs) = rev (rotate n xs)"
  by (induct n) (auto simp: rotater_def intro: rotater1_rev')

lemma rotater_rev: "rotater n ys = rev (rotate n (rev ys))"
  using rotater_rev' [where xs = "rev ys"] by simp

lemma rotater_drop_take:
  "rotater n xs =
    drop (length xs - n mod length xs) xs @
    take (length xs - n mod length xs) xs"
  by (auto simp: rotater_rev rotate_drop_take rev_take rev_drop)

lemma rotater_Suc [simp]: "rotater (Suc n) xs = rotater1 (rotater n xs)"
  unfolding rotater_def by auto

lemma nth_rotater:
  \<open>rotater m xs ! n = xs ! ((n + (length xs - m mod length xs)) mod length xs)\<close> if \<open>n < length xs\<close>
  using that by (simp add: rotater_drop_take nth_append not_less less_diff_conv ac_simps le_mod_geq)

lemma nth_rotater1:
  \<open>rotater1 xs ! n = xs ! ((n + (length xs - 1)) mod length xs)\<close> if \<open>n < length xs\<close>
  using that nth_rotater [of n xs 1] by simp

lemma rotate_inv_plus [rule_format]:
  "\<forall>k. k = m + n \<longrightarrow> rotater k (rotate n xs) = rotater m xs \<and>
    rotate k (rotater n xs) = rotate m xs \<and>
    rotater n (rotate k xs) = rotate m xs \<and>
    rotate n (rotater k xs) = rotater m xs"
  by (induct n) (auto simp: rotater_def rotate_def intro: funpow_swap1 [THEN trans])

lemmas rotate_inv_rel = le_add_diff_inverse2 [symmetric, THEN rotate_inv_plus]

lemmas rotate_inv_eq = order_refl [THEN rotate_inv_rel, simplified]

lemmas rotate_lr [simp] = rotate_inv_eq [THEN conjunct1]
lemmas rotate_rl [simp] = rotate_inv_eq [THEN conjunct2, THEN conjunct1]

lemma rotate_gal: "rotater n xs = ys \<longleftrightarrow> rotate n ys = xs"
  by auto

lemma rotate_gal': "ys = rotater n xs \<longleftrightarrow> xs = rotate n ys"
  by auto

lemma length_rotater [simp]: "length (rotater n xs) = length xs"
  by (simp add : rotater_rev)

lemma bit_word_rotr_iff:
  \<open>bit (word_rotr m w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w ((n + m) mod LENGTH('a))\<close>
  for w :: \<open>'a::len word\<close>
proof (cases \<open>n < LENGTH('a)\<close>)
  case False
  then show ?thesis
    by (auto dest: bit_imp_le_length)
next
  case True
  define k where \<open>k = int n + int m\<close>
  then have k: \<open>int n = k - int m\<close>
    by simp
  define l where \<open>l = int LENGTH('a)\<close>
  then have l: \<open>int LENGTH('a) = l\<close> \<open>l > 0\<close>
    by simp_all
  have *: \<open>int (m - n) = int m - int n\<close> if \<open>n \<le> m\<close> for n m
    using that by (simp add: int_minus)
  have \<open>int ((LENGTH('a)
    - Suc ((LENGTH('a) + LENGTH('a) - Suc (n + m mod LENGTH('a))) mod LENGTH('a)))) =
    int ((n + m) mod LENGTH('a))\<close>
    using True
    apply (simp add: l * zmod_int Suc_leI add_strict_mono)
    apply (subst mod_diff_left_eq [symmetric])
    apply simp
    using l minus_mod_int_eq [of l \<open>int n + int m mod l + 1\<close>] apply simp
    apply (simp add: mod_simps)
    done
  then have \<open>(LENGTH('a)
    - Suc ((LENGTH('a) + LENGTH('a) - Suc (n + m mod LENGTH('a))) mod LENGTH('a))) =
    ((n + m) mod LENGTH('a))\<close>
    by simp
  with True show ?thesis
    by (simp add: word_rotr_def bit_of_bl_iff rev_nth nth_rotater nth_to_bl)
qed

lemma bit_word_roti_iff:
  \<open>bit (word_roti k w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w (nat ((int n + k) mod int LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
proof (cases \<open>k \<ge> 0\<close>)
  case True
  moreover define m where \<open>m = nat k\<close>
  ultimately have \<open>k = int m\<close>
    by simp
  then show ?thesis
    by (simp add: word_roti_def bit_word_rotr_iff nat_mod_distrib nat_add_distrib)
next
  have *: \<open>int (m - n) = int m - int n\<close> if \<open>n \<le> m\<close> for n m
    using that by (simp add: int_minus)
  case False
  moreover define m where \<open>m = nat (- k)\<close>
  ultimately have \<open>k = - int m\<close> \<open>k < 0\<close>
    by simp_all
  moreover have \<open>(int n - int m) mod int LENGTH('a) =
    int ((n + LENGTH('a) - m mod LENGTH('a)) mod LENGTH('a))\<close>
    apply (simp add: zmod_int * trans_le_add2 mod_simps)
    apply (metis mod_add_self2 mod_diff_cong)
    done
  ultimately show ?thesis
    by (simp add: word_roti_def bit_word_rotl_iff nat_mod_distrib)
qed

lemma restrict_to_left: "x = y \<Longrightarrow> x = z \<longleftrightarrow> y = z"
  by simp

lemmas rrs0 = rotate_eqs [THEN restrict_to_left,
  simplified rotate_gal [symmetric] rotate_gal' [symmetric]]
lemmas rrs1 = rrs0 [THEN refl [THEN rev_iffD1]]
lemmas rotater_eqs = rrs1 [simplified length_rotater]
lemmas rotater_0 = rotater_eqs (1)
lemmas rotater_add = rotater_eqs (2)


subsubsection \<open>map, map2, commuting with rotate(r)\<close>

lemma butlast_map: "xs \<noteq> [] \<Longrightarrow> butlast (map f xs) = map f (butlast xs)"
  by (induct xs) auto

lemma rotater1_map: "rotater1 (map f xs) = map f (rotater1 xs)"
  by (cases xs) (auto simp: rotater1_def last_map butlast_map)

lemma rotater_map: "rotater n (map f xs) = map f (rotater n xs)"
  by (induct n) (auto simp: rotater_def rotater1_map)

lemma but_last_zip [rule_format] :
  "\<forall>ys. length xs = length ys \<longrightarrow> xs \<noteq> [] \<longrightarrow>
    last (zip xs ys) = (last xs, last ys) \<and>
    butlast (zip xs ys) = zip (butlast xs) (butlast ys)"
  apply (induct xs)
   apply auto
     apply ((case_tac ys, auto simp: neq_Nil_conv)[1])+
  done

lemma but_last_map2 [rule_format] :
  "\<forall>ys. length xs = length ys \<longrightarrow> xs \<noteq> [] \<longrightarrow>
    last (map2 f xs ys) = f (last xs) (last ys) \<and>
    butlast (map2 f xs ys) = map2 f (butlast xs) (butlast ys)"
  apply (induct xs)
   apply auto
     apply ((case_tac ys, auto simp: neq_Nil_conv)[1])+
  done

lemma rotater1_zip:
  "length xs = length ys \<Longrightarrow>
    rotater1 (zip xs ys) = zip (rotater1 xs) (rotater1 ys)"
  apply (unfold rotater1_def)
  apply (cases xs)
   apply auto
   apply ((case_tac ys, auto simp: neq_Nil_conv but_last_zip)[1])+
  done

lemma rotater1_map2:
  "length xs = length ys \<Longrightarrow>
    rotater1 (map2 f xs ys) = map2 f (rotater1 xs) (rotater1 ys)"
  by (simp add: rotater1_map rotater1_zip)

lemmas lrth =
  box_equals [OF asm_rl length_rotater [symmetric]
                 length_rotater [symmetric],
              THEN rotater1_map2]

lemma rotater_map2:
  "length xs = length ys \<Longrightarrow>
    rotater n (map2 f xs ys) = map2 f (rotater n xs) (rotater n ys)"
  by (induct n) (auto intro!: lrth)

lemma rotate1_map2:
  "length xs = length ys \<Longrightarrow>
    rotate1 (map2 f xs ys) = map2 f (rotate1 xs) (rotate1 ys)"
  by (cases xs; cases ys) auto

lemmas lth = box_equals [OF asm_rl length_rotate [symmetric]
  length_rotate [symmetric], THEN rotate1_map2]

lemma rotate_map2:
  "length xs = length ys \<Longrightarrow>
    rotate n (map2 f xs ys) = map2 f (rotate n xs) (rotate n ys)"
  by (induct n) (auto intro!: lth)


\<comment> \<open>corresponding equalities for word rotation\<close>

lemma to_bl_rotl: "to_bl (word_rotl n w) = rotate n (to_bl w)"
  by (simp add: word_bl.Abs_inverse' word_rotl_def)

lemmas blrs0 = rotate_eqs [THEN to_bl_rotl [THEN trans]]

lemmas word_rotl_eqs =
  blrs0 [simplified word_bl_Rep' word_bl.Rep_inject to_bl_rotl [symmetric]]

lemma to_bl_rotr: "to_bl (word_rotr n w) = rotater n (to_bl w)"
  by (simp add: word_bl.Abs_inverse' word_rotr_def)

lemmas brrs0 = rotater_eqs [THEN to_bl_rotr [THEN trans]]

lemmas word_rotr_eqs =
  brrs0 [simplified word_bl_Rep' word_bl.Rep_inject to_bl_rotr [symmetric]]

declare word_rotr_eqs (1) [simp]
declare word_rotl_eqs (1) [simp]

lemma word_rot_rl [simp]: "word_rotl k (word_rotr k v) = v"
  and word_rot_lr [simp]: "word_rotr k (word_rotl k v) = v"
  by (auto simp add: to_bl_rotr to_bl_rotl word_bl.Rep_inject [symmetric])

lemma word_rot_gal: "word_rotr n v = w \<longleftrightarrow> word_rotl n w = v"
  and word_rot_gal': "w = word_rotr n v \<longleftrightarrow> v = word_rotl n w"
  by (auto simp: to_bl_rotr to_bl_rotl word_bl.Rep_inject [symmetric] dest: sym)

lemma word_rotr_rev: "word_rotr n w = word_reverse (word_rotl n (word_reverse w))"
  by (simp only: word_bl.Rep_inject [symmetric] to_bl_word_rev to_bl_rotr to_bl_rotl rotater_rev)

lemma word_roti_0 [simp]: "word_roti 0 w = w"
  by (auto simp: word_rot_defs)

lemmas abl_cong = arg_cong [where f = "of_bl"]

lemma word_roti_add: "word_roti (m + n) w = word_roti m (word_roti n w)"
proof -
  have rotater_eq_lem: "\<And>m n xs. m = n \<Longrightarrow> rotater m xs = rotater n xs"
    by auto

  have rotate_eq_lem: "\<And>m n xs. m = n \<Longrightarrow> rotate m xs = rotate n xs"
    by auto

  note rpts [symmetric] =
    rotate_inv_plus [THEN conjunct1]
    rotate_inv_plus [THEN conjunct2, THEN conjunct1]
    rotate_inv_plus [THEN conjunct2, THEN conjunct2, THEN conjunct1]
    rotate_inv_plus [THEN conjunct2, THEN conjunct2, THEN conjunct2]

  note rrp = trans [symmetric, OF rotate_rotate rotate_eq_lem]
  note rrrp = trans [symmetric, OF rotater_add [symmetric] rotater_eq_lem]

  show ?thesis
    apply (unfold word_rot_defs)
    apply (simp only: split: if_split)
    apply (safe intro!: abl_cong)
           apply (simp_all only: to_bl_rotl [THEN word_bl.Rep_inverse']
                  to_bl_rotl
                  to_bl_rotr [THEN word_bl.Rep_inverse']
                  to_bl_rotr)
         apply (rule rrp rrrp rpts,
                simp add: nat_add_distrib [symmetric]
                nat_diff_distrib [symmetric])+
    done
qed

lemma word_roti_conv_mod':
  "word_roti n w = word_roti (n mod int (size w)) w"
proof (cases "size w = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then have [simp]: "l mod int (size w) \<ge> 0" for l
    by simp
  then have *: "word_roti (n mod int (size w)) w = word_rotr (nat (n mod int (size w))) w"
    by (simp add: word_roti_def)
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    then show ?thesis
      apply (auto simp add: not_le *)
      apply (auto simp add: word_rot_defs)
      apply (safe intro!: abl_cong)
      apply (rule rotater_eqs)
      apply (simp add: word_size nat_mod_distrib)
      done
  next
    case False
    moreover define k where "k = - n"
    ultimately have n: "n = - k"
      by simp_all
    from False show ?thesis
      apply (auto simp add: not_le *)
      apply (auto simp add: word_rot_defs)
      apply (simp add: n)
      apply (safe intro!: abl_cong)
      apply (simp add: rotater_add [symmetric] rotate_gal [symmetric])
      apply (rule rotater_eqs)
      apply (simp add: word_size [symmetric, of w])
      apply (rule of_nat_eq_0_iff [THEN iffD1])
      apply (auto simp add: nat_add_distrib [symmetric] mod_eq_0_iff_dvd)
      using dvd_nat_abs_iff [of "size w" "- k mod int (size w) + k"]
      apply (simp add: algebra_simps)
      apply (simp add: word_size)
      apply (metis dvd_eq_mod_eq_0 eq_neg_iff_add_eq_0 k_def mod_0 mod_add_right_eq n)
      done
  qed
qed

lemmas word_roti_conv_mod = word_roti_conv_mod' [unfolded word_size]


subsubsection \<open>"Word rotation commutes with bit-wise operations\<close>

\<comment> \<open>using locale to not pollute lemma namespace\<close>
locale word_rotate
begin

lemmas word_rot_defs' = to_bl_rotl to_bl_rotr

lemmas blwl_syms [symmetric] = bl_word_not bl_word_and bl_word_or bl_word_xor

lemmas lbl_lbl = trans [OF word_bl_Rep' word_bl_Rep' [symmetric]]

lemmas ths_map2 [OF lbl_lbl] = rotate_map2 rotater_map2

lemmas ths_map [where xs = "to_bl v"] = rotate_map rotater_map for v

lemmas th1s [simplified word_rot_defs' [symmetric]] = ths_map2 ths_map

lemma word_rot_logs:
  "word_rotl n (NOT v) = NOT (word_rotl n v)"
  "word_rotr n (NOT v) = NOT (word_rotr n v)"
  "word_rotl n (x AND y) = word_rotl n x AND word_rotl n y"
  "word_rotr n (x AND y) = word_rotr n x AND word_rotr n y"
  "word_rotl n (x OR y) = word_rotl n x OR word_rotl n y"
  "word_rotr n (x OR y) = word_rotr n x OR word_rotr n y"
  "word_rotl n (x XOR y) = word_rotl n x XOR word_rotl n y"
  "word_rotr n (x XOR y) = word_rotr n x XOR word_rotr n y"
  by (rule word_bl.Rep_eqD,
      rule word_rot_defs' [THEN trans],
      simp only: blwl_syms [symmetric],
      rule th1s [THEN trans],
      rule refl)+
end

lemmas word_rot_logs = word_rotate.word_rot_logs

lemmas bl_word_rotl_dt = trans [OF to_bl_rotl rotate_drop_take,
  simplified word_bl_Rep']

lemmas bl_word_rotr_dt = trans [OF to_bl_rotr rotater_drop_take,
  simplified word_bl_Rep']

lemma bl_word_roti_dt':
  "n = nat ((- i) mod int (size (w :: 'a::len word))) \<Longrightarrow>
    to_bl (word_roti i w) = drop n (to_bl w) @ take n (to_bl w)"
  apply (unfold word_roti_def)
  apply (simp add: bl_word_rotl_dt bl_word_rotr_dt word_size)
  apply safe
   apply (simp add: zmod_zminus1_eq_if)
   apply safe
    apply (simp add: nat_mult_distrib)
   apply (simp add: nat_diff_distrib [OF pos_mod_sign pos_mod_conj
                                      [THEN conjunct2, THEN order_less_imp_le]]
                    nat_mod_distrib)
  apply (simp add: nat_mod_distrib)
  done

lemmas bl_word_roti_dt = bl_word_roti_dt' [unfolded word_size]

lemmas word_rotl_dt = bl_word_rotl_dt [THEN word_bl.Rep_inverse' [symmetric]]
lemmas word_rotr_dt = bl_word_rotr_dt [THEN word_bl.Rep_inverse' [symmetric]]
lemmas word_roti_dt = bl_word_roti_dt [THEN word_bl.Rep_inverse' [symmetric]]

lemma word_rotx_0 [simp] : "word_rotr i 0 = 0 \<and> word_rotl i 0 = 0"
  by (simp add: word_rotr_dt word_rotl_dt replicate_add [symmetric])

lemma word_roti_0' [simp] : "word_roti n 0 = 0"
  by (auto simp: word_roti_def)

lemmas word_rotr_dt_no_bin' [simp] =
  word_rotr_dt [where w="numeral w", unfolded to_bl_numeral] for w
  (* FIXME: negative numerals, 0 and 1 *)

lemmas word_rotl_dt_no_bin' [simp] =
  word_rotl_dt [where w="numeral w", unfolded to_bl_numeral] for w
  (* FIXME: negative numerals, 0 and 1 *)

declare word_roti_def [simp]


subsection \<open>Maximum machine word\<close>

lemma word_int_cases:
  fixes x :: "'a::len word"
  obtains n where "x = word_of_int n" and "0 \<le> n" and "n < 2^LENGTH('a)"
  by (cases x rule: word_uint.Abs_cases) (simp add: uints_num)

lemma word_nat_cases [cases type: word]:
  fixes x :: "'a::len word"
  obtains n where "x = of_nat n" and "n < 2^LENGTH('a)"
  by (cases x rule: word_unat.Abs_cases) (simp add: unats_def)

lemma max_word_max [intro!]: "n \<le> max_word"
  by (fact word_order.extremum)

lemma word_of_int_2p_len: "word_of_int (2 ^ LENGTH('a)) = (0::'a::len word)"
  by (subst word_uint.Abs_norm [symmetric]) simp

lemma word_pow_0: "(2::'a::len word) ^ LENGTH('a) = 0"
  by (fact word_exp_length_eq_0)

lemma max_word_wrap: "x + 1 = 0 \<Longrightarrow> x = max_word"
  by (simp add: eq_neg_iff_add_eq_0)

lemma max_word_bl: "to_bl (max_word::'a::len word) = replicate LENGTH('a) True"
  by (fact to_bl_n1)

lemma max_test_bit: "(max_word::'a::len word) !! n \<longleftrightarrow> n < LENGTH('a)"
  by (fact nth_minus1)

lemma word_and_max: "x AND max_word = x"
  by (fact word_log_esimps)

lemma word_or_max: "x OR max_word = max_word"
  by (fact word_log_esimps)

lemma word_ao_dist2: "x AND (y OR z) = x AND y OR x AND z"
  for x y z :: "'a::len word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_oa_dist2: "x OR y AND z = (x OR y) AND (x OR z)"
  for x y z :: "'a::len word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_and_not [simp]: "x AND NOT x = 0"
  for x :: "'a::len word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_or_not [simp]: "x OR NOT x = max_word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_xor_and_or: "x XOR y = x AND NOT y OR NOT x AND y"
  for x y :: "'a::len word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma shiftr_x_0 [iff]: "x >> 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftr_bl)

lemma shiftl_x_0 [simp]: "x << 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftl_t2n)

lemma shiftl_1 [simp]: "(1::'a::len word) << n = 2^n"
  by (simp add: shiftl_t2n)

lemma uint_lt_0 [simp]: "uint x < 0 = False"
  by (simp add: linorder_not_less)

lemma shiftr1_1 [simp]: "shiftr1 (1::'a::len word) = 0"
  unfolding shiftr1_def by simp

lemma shiftr_1[simp]: "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (induct n) (auto simp: shiftr_def)

lemma word_less_1 [simp]: "x < 1 \<longleftrightarrow> x = 0"
  for x :: "'a::len word"
  by (simp add: word_less_nat_alt unat_0_iff)

lemma to_bl_mask:
  "to_bl (mask n :: 'a::len word) =
  replicate (LENGTH('a) - n) False @
    replicate (min (LENGTH('a)) n) True"
  by (simp add: mask_bl word_rep_drop min_def)

lemma map_replicate_True:
  "n = length xs \<Longrightarrow>
    map (\<lambda>(x,y). x \<and> y) (zip xs (replicate n True)) = xs"
  by (induct xs arbitrary: n) auto

lemma map_replicate_False:
  "n = length xs \<Longrightarrow> map (\<lambda>(x,y). x \<and> y)
    (zip xs (replicate n False)) = replicate n False"
  by (induct xs arbitrary: n) auto

lemma bl_and_mask:
  fixes w :: "'a::len word"
    and n :: nat
  defines "n' \<equiv> LENGTH('a) - n"
  shows "to_bl (w AND mask n) = replicate n' False @ drop n' (to_bl w)"
proof -
  note [simp] = map_replicate_True map_replicate_False
  have "to_bl (w AND mask n) = map2 (\<and>) (to_bl w) (to_bl (mask n::'a::len word))"
    by (simp add: bl_word_and)
  also have "to_bl w = take n' (to_bl w) @ drop n' (to_bl w)"
    by simp
  also have "map2 (\<and>) \<dots> (to_bl (mask n::'a::len word)) =
      replicate n' False @ drop n' (to_bl w)"
    unfolding to_bl_mask n'_def by (subst zip_append) auto
  finally show ?thesis .
qed

lemma drop_rev_takefill:
  "length xs \<le> n \<Longrightarrow>
    drop (n - length xs) (rev (takefill False n (rev xs))) = xs"
  by (simp add: takefill_alt rev_take)

lemma map_nth_0 [simp]: "map ((!!) (0::'a::len word)) xs = replicate (length xs) False"
  by (induct xs) auto

lemma uint_plus_if_size:
  "uint (x + y) =
    (if uint x + uint y < 2^size x
     then uint x + uint y
     else uint x + uint y - 2^size x)"
  by (simp add: word_arith_wis int_word_uint mod_add_if_z word_size)

lemma unat_plus_if_size:
  "unat (x + y) =
    (if unat x + unat y < 2^size x
     then unat x + unat y
     else unat x + unat y - 2^size x)"
  for x y :: "'a::len word"
  apply (subst word_arith_nat_defs)
  apply (subst unat_of_nat)
  apply (auto simp add: not_less word_size)
  apply (metis not_le unat_plus_if' unat_word_ariths(1))
  done

lemma word_neq_0_conv: "w \<noteq> 0 \<longleftrightarrow> 0 < w"
  for w :: "'a::len word"
  by (simp add: word_gt_0)

lemma max_lt: "unat (max a b div c) = unat (max a b) div unat c"
  for c :: "'a::len word"
  by (fact unat_div)

lemma uint_sub_if_size:
  "uint (x - y) =
    (if uint y \<le> uint x
     then uint x - uint y
     else uint x - uint y + 2^size x)"
  by (simp add: word_arith_wis int_word_uint mod_sub_if_z word_size)

lemma unat_sub: "b \<le> a \<Longrightarrow> unat (a - b) = unat a - unat b"
  by (simp add: unat_def uint_sub_if_size word_le_def nat_diff_distrib)

lemmas word_less_sub1_numberof [simp] = word_less_sub1 [of "numeral w"] for w
lemmas word_le_sub1_numberof [simp] = word_le_sub1 [of "numeral w"] for w

lemma word_of_int_minus: "word_of_int (2^LENGTH('a) - i) = (word_of_int (-i)::'a::len word)"
proof -
  have *: "2^LENGTH('a) - i = -i + 2^LENGTH('a)"
    by simp
  show ?thesis
    apply (subst *)
    apply (subst word_uint.Abs_norm [symmetric], subst mod_add_self2)
    apply simp
    done
qed

lemmas word_of_int_inj =
  word_uint.Abs_inject [unfolded uints_num, simplified]

lemma word_le_less_eq: "x \<le> y \<longleftrightarrow> x = y \<or> x < y"
  for x y :: "'z::len word"
  by (auto simp add: order_class.le_less)

lemma mod_plus_cong:
  fixes b b' :: int
  assumes 1: "b = b'"
    and 2: "x mod b' = x' mod b'"
    and 3: "y mod b' = y' mod b'"
    and 4: "x' + y' = z'"
  shows "(x + y) mod b = z' mod b'"
proof -
  from 1 2[symmetric] 3[symmetric] have "(x + y) mod b = (x' mod b' + y' mod b') mod b'"
    by (simp add: mod_add_eq)
  also have "\<dots> = (x' + y') mod b'"
    by (simp add: mod_add_eq)
  finally show ?thesis
    by (simp add: 4)
qed

lemma mod_minus_cong:
  fixes b b' :: int
  assumes "b = b'"
    and "x mod b' = x' mod b'"
    and "y mod b' = y' mod b'"
    and "x' - y' = z'"
  shows "(x - y) mod b = z' mod b'"
  using assms [symmetric] by (auto intro: mod_diff_cong)

lemma word_induct_less: "P 0 \<Longrightarrow> (\<And>n. n < m \<Longrightarrow> P n \<Longrightarrow> P (1 + n)) \<Longrightarrow> P m"
  for P :: "'a::len word \<Rightarrow> bool"
  apply (cases m)
  apply atomize
  apply (erule rev_mp)+
  apply (rule_tac x=m in spec)
  apply (induct_tac n)
   apply simp
  apply clarsimp
  apply (erule impE)
   apply clarsimp
   apply (erule_tac x=n in allE)
   apply (erule impE)
    apply (simp add: unat_arith_simps)
    apply (clarsimp simp: unat_of_nat)
   apply simp
  apply (erule_tac x="of_nat na" in allE)
  apply (erule impE)
   apply (simp add: unat_arith_simps)
   apply (clarsimp simp: unat_of_nat)
  apply simp
  done

lemma word_induct: "P 0 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (1 + n)) \<Longrightarrow> P m"
  for P :: "'a::len word \<Rightarrow> bool"
  by (erule word_induct_less) simp

lemma word_induct2 [induct type]: "P 0 \<Longrightarrow> (\<And>n. 1 + n \<noteq> 0 \<Longrightarrow> P n \<Longrightarrow> P (1 + n)) \<Longrightarrow> P n"
  for P :: "'b::len word \<Rightarrow> bool"
  apply (rule word_induct)
   apply simp
  apply (case_tac "1 + n = 0")
   apply auto
  done


subsection \<open>Recursion combinator for words\<close>

definition word_rec :: "'a \<Rightarrow> ('b::len word \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b word \<Rightarrow> 'a"
  where "word_rec forZero forSuc n = rec_nat forZero (forSuc \<circ> of_nat) (unat n)"

lemma word_rec_0: "word_rec z s 0 = z"
  by (simp add: word_rec_def)

lemma word_rec_Suc: "1 + n \<noteq> 0 \<Longrightarrow> word_rec z s (1 + n) = s n (word_rec z s n)"
  for n :: "'a::len word"
  apply (auto simp add: word_rec_def unat_word_ariths)
  apply (metis (mono_tags, lifting) old.nat.simps(7) unatSuc word_unat.Rep_inverse word_unat.eq_norm word_unat.td_th)
  done

lemma word_rec_Pred: "n \<noteq> 0 \<Longrightarrow> word_rec z s n = s (n - 1) (word_rec z s (n - 1))"
  apply (rule subst[where t="n" and s="1 + (n - 1)"])
   apply simp
  apply (subst word_rec_Suc)
   apply simp
  apply simp
  done

lemma word_rec_in: "f (word_rec z (\<lambda>_. f) n) = word_rec (f z) (\<lambda>_. f) n"
  by (induct n) (simp_all add: word_rec_0 word_rec_Suc)

lemma word_rec_in2: "f n (word_rec z f n) = word_rec (f 0 z) (f \<circ> (+) 1) n"
  by (induct n) (simp_all add: word_rec_0 word_rec_Suc)

lemma word_rec_twice:
  "m \<le> n \<Longrightarrow> word_rec z f n = word_rec (word_rec z f (n - m)) (f \<circ> (+) (n - m)) m"
  apply (erule rev_mp)
  apply (rule_tac x=z in spec)
  apply (rule_tac x=f in spec)
  apply (induct n)
   apply (simp add: word_rec_0)
  apply clarsimp
  apply (rule_tac t="1 + n - m" and s="1 + (n - m)" in subst)
   apply simp
  apply (case_tac "1 + (n - m) = 0")
   apply (simp add: word_rec_0)
   apply (rule_tac f = "word_rec a b" for a b in arg_cong)
   apply (rule_tac t="m" and s="m + (1 + (n - m))" in subst)
    apply simp
   apply (simp (no_asm_use))
  apply (simp add: word_rec_Suc word_rec_in2)
  apply (erule impE)
   apply uint_arith
  apply (drule_tac x="x \<circ> (+) 1" in spec)
  apply (drule_tac x="x 0 xa" in spec)
  apply simp
  apply (rule_tac t="\<lambda>a. x (1 + (n - m + a))" and s="\<lambda>a. x (1 + (n - m) + a)" in subst)
   apply (clarsimp simp add: fun_eq_iff)
   apply (rule_tac t="(1 + (n - m + xb))" and s="1 + (n - m) + xb" in subst)
    apply simp
   apply (rule refl)
  apply (rule refl)
  done

lemma word_rec_id: "word_rec z (\<lambda>_. id) n = z"
  by (induct n) (auto simp add: word_rec_0 word_rec_Suc)

lemma word_rec_id_eq: "\<forall>m < n. f m = id \<Longrightarrow> word_rec z f n = z"
  apply (erule rev_mp)
  apply (induct n)
   apply (auto simp add: word_rec_0 word_rec_Suc)
   apply (drule spec, erule mp)
   apply uint_arith
  apply (drule_tac x=n in spec, erule impE)
   apply uint_arith
  apply simp
  done

lemma word_rec_max:
  "\<forall>m\<ge>n. m \<noteq> - 1 \<longrightarrow> f m = id \<Longrightarrow> word_rec z f (- 1) = word_rec z f n"
  apply (subst word_rec_twice[where n="-1" and m="-1 - n"])
   apply simp
  apply simp
  apply (rule word_rec_id_eq)
  apply clarsimp
  apply (drule spec, rule mp, erule mp)
   apply (rule word_plus_mono_right2[OF _ order_less_imp_le])
    prefer 2
    apply assumption
   apply simp
  apply (erule contrapos_pn)
  apply simp
  apply (drule arg_cong[where f="\<lambda>x. x - n"])
  apply simp
  done


subsection \<open>More\<close>

lemma test_bit_1' [simp]:
  "(1 :: 'a :: len word) !! n \<longleftrightarrow> 0 < LENGTH('a) \<and> n = 0"
  by simp

lemma mask_0 [simp]:
  "mask 0 = 0"
  by (simp add: Word.mask_def)

lemma shiftl0:
  "x << 0 = (x :: 'a :: len word)"
  by (fact shiftl_x_0)

lemma mask_1: "mask 1 = 1"
  by (simp add: mask_def)

lemma mask_Suc_0: "mask (Suc 0) = 1"
  by (simp add: mask_def)

lemma mask_numeral: "mask (numeral n) = 2 * mask (pred_numeral n) + 1"
  by (simp add: mask_def neg_numeral_class.sub_def numeral_eq_Suc numeral_pow)

lemma bin_last_bintrunc: "bin_last (bintrunc l n) = (l > 0 \<and> bin_last n)"
  by (cases l) simp_all

lemma word_and_1:
  "n AND 1 = (if n !! 0 then 1 else 0)" for n :: "_ word"
  by transfer (rule bin_rl_eqI, simp_all add: bin_rest_trunc bin_last_bintrunc)

lemma bintrunc_shiftl:
  "bintrunc n (m << i) = bintrunc (n - i) m << i"
proof (induction i arbitrary: n)
  case 0
  show ?case
    by simp
next
  case (Suc i)
  then show ?case by (cases n) (simp_all add: take_bit_Suc)
qed

lemma shiftl_transfer [transfer_rule]:
  includes lifting_syntax
  shows "(pcr_word ===> (=) ===> pcr_word) (<<) (<<)"
  by (auto intro!: rel_funI word_eqI simp add: word.pcr_cr_eq cr_word_def word_size nth_shiftl)

lemma uint_shiftl:
  "uint (n << i) = bintrunc (size n) (uint n << i)"
  apply (simp add: word_size shiftl_eq_push_bit shiftl_word_eq)
  apply transfer
  apply (simp add: push_bit_take_bit)
  done


subsection \<open>Misc\<close>

declare bin_to_bl_def [simp]

ML_file \<open>Tools/word_lib.ML\<close>
ML_file \<open>Tools/smt_word.ML\<close>

hide_const (open) Word

end
