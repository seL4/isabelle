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

lemma signed_take_bit_decr_length_iff:
  \<open>signed_take_bit (LENGTH('a::len) - Suc 0) k = signed_take_bit (LENGTH('a) - Suc 0) l
    \<longleftrightarrow> take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by (cases \<open>LENGTH('a)\<close>)
    (simp_all add: signed_take_bit_eq_iff_take_bit_eq)

lift_definition sint :: \<open>'a::len word \<Rightarrow> int\<close>
  \<comment> \<open>treats the most-significant bit as a sign bit\<close>
  is \<open>signed_take_bit (LENGTH('a) - 1)\<close>  
  by (simp add: signed_take_bit_decr_length_iff)

lemma sint_uint [code]:
  \<open>sint w = signed_take_bit (LENGTH('a) - 1) (uint w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer simp

lift_definition unat :: \<open>'a::len word \<Rightarrow> nat\<close>
  is \<open>nat \<circ> take_bit LENGTH('a)\<close>
  by transfer simp

lemma nat_uint_eq [simp]:
  \<open>nat (uint w) = unat w\<close>
  by transfer simp

lemma unat_eq_nat_uint [code]:
  \<open>unat w = nat (uint w)\<close>
  by simp

lift_definition ucast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  is \<open>take_bit LENGTH('a)\<close>
  by simp

lemma ucast_eq [code]:
  \<open>ucast w = word_of_int (uint w)\<close>
  by transfer simp

lift_definition scast :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  is \<open>signed_take_bit (LENGTH('a) - 1)\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma scast_eq [code]:
  \<open>scast w = word_of_int (sint w)\<close>
  by transfer simp

instantiation word :: (len) size
begin

lift_definition size_word :: \<open>'a word \<Rightarrow> nat\<close>
  is \<open>\<lambda>_. LENGTH('a)\<close> ..

instance ..

end

lemma word_size [code]:
  \<open>size w = LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  by (fact size_word.rep_eq)

lemma word_size_gt_0 [iff]: "0 < size w"
  for w :: "'a::len word"
  by (simp add: word_size)

lemmas lens_gt_0 = word_size_gt_0 len_gt_0

lemma lens_not_0 [iff]:
  \<open>size w \<noteq> 0\<close> for  w :: \<open>'a::len word\<close>
  by auto

lift_definition source_size :: \<open>('a::len word \<Rightarrow> 'b) \<Rightarrow> nat\<close>
  is \<open>\<lambda>_. LENGTH('a)\<close> .

lift_definition target_size :: \<open>('a \<Rightarrow> 'b::len word) \<Rightarrow> nat\<close>
  is \<open>\<lambda>_. LENGTH('b)\<close> ..

lift_definition is_up :: \<open>('a::len word \<Rightarrow> 'b::len word) \<Rightarrow> bool\<close>
  is \<open>\<lambda>_. LENGTH('a) \<le> LENGTH('b)\<close> ..

lift_definition is_down :: \<open>('a::len word \<Rightarrow> 'b::len word) \<Rightarrow> bool\<close>
  is \<open>\<lambda>_. LENGTH('a) \<ge> LENGTH('b)\<close> ..

lemma is_up_eq:
  \<open>is_up f \<longleftrightarrow> source_size f \<le> target_size f\<close>
  for f :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  by (simp add: source_size.rep_eq target_size.rep_eq is_up.rep_eq)

lemma is_down_eq:
  \<open>is_down f \<longleftrightarrow> target_size f \<le> source_size f\<close>
  for f :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  by (simp add: source_size.rep_eq target_size.rep_eq is_down.rep_eq)

lift_definition word_int_case :: \<open>(int \<Rightarrow> 'b) \<Rightarrow> 'a::len word \<Rightarrow> 'b\<close>
  is \<open>\<lambda>f. f \<circ> take_bit LENGTH('a)\<close> by simp

lemma word_int_case_eq_uint [code]:
  \<open>word_int_case f w = f (uint w)\<close>
  by transfer simp

translations
  "case x of XCONST of_int y \<Rightarrow> b" \<rightleftharpoons> "CONST word_int_case (\<lambda>y. b) x"
  "case x of (XCONST of_int :: 'a) y \<Rightarrow> b" \<rightharpoonup> "CONST word_int_case (\<lambda>y. b) x"


subsection \<open>Basic code generation setup\<close>

lift_definition Word :: \<open>int \<Rightarrow> 'a::len word\<close>
  is id .

lemma Word_eq_word_of_int [code_post]:
  \<open>Word = word_of_int\<close>
  by (simp add: fun_eq_iff Word.abs_eq)

lemma [code abstype]:
  \<open>Word (uint w) = w\<close>
  by transfer simp

lemma [code abstract]:
  \<open>uint (word_of_int k :: 'a::len word) = take_bit LENGTH('a) k\<close>
  by (fact uint.abs_eq)

instantiation word :: (len) equal
begin

lift_definition equal_word :: \<open>'a word \<Rightarrow> 'a word \<Rightarrow> bool\<close>
  is \<open>\<lambda>k l. take_bit LENGTH('a) k = take_bit LENGTH('a) l\<close>
  by simp

instance
  by (standard; transfer) rule

end

lemma [code]:
  \<open>HOL.equal k l \<longleftrightarrow> HOL.equal (uint k) (uint l)\<close>
  by transfer (simp add: equal)

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

lemma uint_0_eq [simp, code]:
  \<open>uint 0 = 0\<close>
  by transfer simp

quickcheck_generator word
  constructors:
    \<open>0 :: 'a::len word\<close>,
    \<open>numeral :: num \<Rightarrow> 'a::len word\<close>,
    \<open>uminus :: 'a word \<Rightarrow> 'a::len word\<close>

lemma uint_1_eq [simp, code]:
  \<open>uint 1 = 1\<close>
  by transfer simp

lemma word_div_def [code]:
  "a div b = word_of_int (uint a div uint b)"
  by transfer rule

lemma word_mod_def [code]:
  "a mod b = word_of_int (uint a mod uint b)"
  by transfer rule

context
  includes lifting_syntax
  notes power_transfer [transfer_rule]
begin

lemma power_transfer_word [transfer_rule]:
  \<open>(pcr_word ===> (=) ===> pcr_word) (^) (^)\<close>
  by transfer_prover

end


text \<open>Legacy theorems:\<close>

lemma word_arith_wis:
  shows word_add_def [code]: "a + b = word_of_int (uint a + uint b)"
    and word_sub_wi [code]: "a - b = word_of_int (uint a - uint b)"
    and word_mult_def [code]: "a * b = word_of_int (uint a * uint b)"
    and word_minus_def [code]: "- a = word_of_int (- uint a)"
    and word_succ_alt [code]: "word_succ a = word_of_int (uint a + 1)"
    and word_pred_alt [code]: "word_pred a = word_of_int (uint a - 1)"
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

lift_definition word_sle :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> bool\<close>  (\<open>(_/ <=s _)\<close> [50, 51] 50)
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - 1) k \<le> signed_take_bit (LENGTH('a) - 1) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma word_sle_eq [code]:
  \<open>a <=s b \<longleftrightarrow> sint a \<le> sint b\<close>
  by transfer simp
  
lift_definition word_sless :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> bool\<close>  (\<open>(_/ <s _)\<close> [50, 51] 50)
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - 1) k < signed_take_bit (LENGTH('a) - 1) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lemma word_sless_eq:
  \<open>x <s y \<longleftrightarrow> x <=s y \<and> x \<noteq> y\<close>
  by transfer (simp add: signed_take_bit_decr_length_iff less_le)

lemma [code]:
  \<open>a <s b \<longleftrightarrow> sint a < sint b\<close>
  by transfer simp


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
    by (simp add: n_def)
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
  \<open>a = b\<close> if \<open>\<And>n. n < LENGTH('a) \<Longrightarrow> bit a n \<longleftrightarrow> bit b n\<close>
  for a b :: \<open>'a::len word\<close>
  using that by transfer (auto simp add: nat_less_le bit_eq_iff bit_take_bit_iff)

lemma bit_imp_le_length:
  \<open>n < LENGTH('a)\<close> if \<open>bit w n\<close>
    for w :: \<open>'a::len word\<close>
  using that by transfer simp

lemma not_bit_length [simp]:
  \<open>\<not> bit w LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  by transfer simp

lemma uint_take_bit_eq [code]:
  \<open>uint (take_bit n w) = take_bit n (uint w)\<close>
  by transfer (simp add: ac_simps)

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
  by transfer (auto simp add: bit_signed_take_bit_iff min_def le_less not_less)

lemma bit_word_ucast_iff:
  \<open>bit (ucast w :: 'b::len word) n \<longleftrightarrow> n < LENGTH('a) \<and> n < LENGTH('b) \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: bit_take_bit_iff ac_simps)

lemma bit_word_scast_iff:
  \<open>bit (scast w :: 'b::len word) n \<longleftrightarrow>
    n < LENGTH('b) \<and> (bit w n \<or> LENGTH('a) \<le> n \<and> bit w (LENGTH('a) - Suc 0))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (auto simp add: bit_signed_take_bit_iff le_less min_def)

lift_definition shiftl1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  is \<open>(*) 2\<close>
  by (auto simp add: take_bit_eq_mod intro: mod_mult_cong)

lemma shiftl1_eq:
  \<open>shiftl1 w = word_of_int (2 * uint w)\<close>
  by transfer (simp add: take_bit_eq_mod mod_simps)

lemma shiftl1_eq_mult_2:
  \<open>shiftl1 = (*) 2\<close>
  by (rule ext, transfer) simp

lemma bit_shiftl1_iff:
  \<open>bit (shiftl1 w) n \<longleftrightarrow> 0 < n \<and> n < LENGTH('a) \<and> bit w (n - 1)\<close>
    for w :: \<open>'a::len word\<close>
  by (simp add: shiftl1_eq_mult_2 bit_double_iff exp_eq_zero_iff not_le) (simp add: ac_simps)

lift_definition shiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  \<comment> \<open>shift right as unsigned or as signed, ie logical or arithmetic\<close>
  is \<open>\<lambda>k. take_bit LENGTH('a) k div 2\<close> by simp

lemma shiftr1_eq_div_2:
  \<open>shiftr1 w = w div 2\<close>
  by transfer simp

lemma bit_shiftr1_iff:
  \<open>bit (shiftr1 w) n \<longleftrightarrow> bit w (Suc n)\<close>
  by transfer (auto simp flip: bit_Suc simp add: bit_take_bit_iff)

lemma shiftr1_eq:
  \<open>shiftr1 w = word_of_int (bin_rest (uint w))\<close>
  by transfer simp

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

lift_definition mask_word :: \<open>nat \<Rightarrow> 'a word\<close>
  is mask
  .

instance by (standard; transfer)
  (auto simp add: minus_eq_not_minus_1 mask_eq_exp_minus_1
    bit_not_iff bit_and_iff bit_or_iff bit_xor_iff)

end

context
  includes lifting_syntax
begin

lemma set_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word) set_bit set_bit\<close>
  by (unfold set_bit_def) transfer_prover

lemma unset_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word) unset_bit unset_bit\<close>
  by (unfold unset_bit_def) transfer_prover

lemma flip_bit_word_transfer [transfer_rule]:
  \<open>((=) ===> pcr_word ===> pcr_word) flip_bit flip_bit\<close>
  by (unfold flip_bit_def) transfer_prover

end

instantiation word :: (len) semiring_bit_syntax
begin

lift_definition test_bit_word :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> bool\<close>
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

lemma test_bit_word_eq:
  \<open>test_bit = (bit :: 'a word \<Rightarrow> _)\<close>
  by transfer simp

lemma bit_word_iff_drop_bit_and [code]:
  \<open>bit a n \<longleftrightarrow> drop_bit n a AND 1 = 1\<close> for a :: \<open>'a::len word\<close>
  by (simp add: bit_iff_odd_drop_bit odd_iff_mod_2_eq_one and_one_eq)

lemma [code]:
  \<open>test_bit a n \<longleftrightarrow> drop_bit n a AND 1 = 1\<close> for a :: \<open>'a::len word\<close>
  by (simp add: test_bit_word_eq bit_word_iff_drop_bit_and)

lift_definition shiftl_word :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k n. push_bit n k\<close>
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

lemma shiftl_word_eq:
  \<open>w << n = push_bit n w\<close> for w :: \<open>'a::len word\<close>
  by transfer rule

lift_definition shiftr_word :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k n. drop_bit n (take_bit LENGTH('a) k)\<close> by simp
  
lemma shiftr_word_eq:
  \<open>w >> n = drop_bit n w\<close> for w :: \<open>'a::len word\<close>
  by transfer simp

instance
  by (standard; transfer) simp_all

end

lemma shiftl_code [code]:
  \<open>w << n = w * 2 ^ n\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: push_bit_eq_mult)

lemma shiftl1_code [code]:
  \<open>shiftl1 w = w << 1\<close>
  by transfer (simp add: push_bit_eq_mult ac_simps)

lemma uint_shiftr_eq [code]:
  \<open>uint (w >> n) = uint w div 2 ^ n\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp flip: drop_bit_eq_div add: drop_bit_take_bit min_def le_less less_diff_conv)

lemma shiftr1_code [code]:
  \<open>shiftr1 w = w >> 1\<close>
  by transfer (simp add: drop_bit_Suc)

lemma word_test_bit_def: 
  \<open>test_bit a = bin_nth (uint a)\<close>
  by transfer (simp add: fun_eq_iff bit_take_bit_iff)

lemma shiftl_def:
  \<open>w << n = (shiftl1 ^^ n) w\<close>
proof -
  have \<open>push_bit n = (((*) 2 ^^ n) :: int \<Rightarrow> int)\<close> for n
    by (induction n) (simp_all add: fun_eq_iff funpow_swap1, simp add: ac_simps)
  then show ?thesis
    by transfer simp
qed

lemma shiftr_def:
  \<open>w >> n = (shiftr1 ^^ n) w\<close>
proof -
  have \<open>drop_bit n = (((\<lambda>k::int. k div 2) ^^ n))\<close> for n
    by (rule sym, induction n)
       (simp_all add: fun_eq_iff drop_bit_Suc flip: drop_bit_half)
  then show ?thesis
    apply transfer
    apply simp
    apply (metis bintrunc_bintrunc rco_bintr)
    done
qed

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
  \<open>uint (take_bit n w) = (if n < LENGTH('a::len) then take_bit n (uint w) else uint w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: min_def)

lemma [code]:
  \<open>uint (mask n :: 'a::len word) = mask (min LENGTH('a) n)\<close>
  by transfer simp

lemma [code_abbrev]:
  \<open>push_bit n 1 = (2 :: 'a::len word) ^ n\<close>
  by (fact push_bit_of_1)

lemma
  word_not_def [code]: "NOT (a::'a::len word) = word_of_int (NOT (uint a))"
    and word_and_def: "(a::'a word) AND b = word_of_int (uint a AND uint b)"
    and word_or_def: "(a::'a word) OR b = word_of_int (uint a OR uint b)"
    and word_xor_def: "(a::'a word) XOR b = word_of_int (uint a XOR uint b)"
  by (transfer, simp add: take_bit_not_take_bit)+

lemma [code abstract]:
  \<open>uint (v AND w) = uint v AND uint w\<close>
  by transfer simp

lemma [code abstract]:
  \<open>uint (v OR w) = uint v OR uint w\<close>
  by transfer simp

lemma [code abstract]:
  \<open>uint (v XOR w) = uint v XOR uint w\<close>
  by transfer simp

lift_definition setBit :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k n. set_bit n k\<close>
  by (simp add: take_bit_set_bit_eq)

lemma set_Bit_eq:
  \<open>setBit w n = set_bit n w\<close>
  by transfer simp

lemma bit_setBit_iff:
  \<open>bit (setBit w m) n \<longleftrightarrow> (m = n \<and> n < LENGTH('a) \<or> bit w n)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (auto simp add: bit_set_bit_iff)

lift_definition clearBit :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k n. unset_bit n k\<close>
  by (simp add: take_bit_unset_bit_eq)

lemma clear_Bit_eq:
  \<open>clearBit w n = unset_bit n w\<close>
  by transfer simp

lemma bit_clearBit_iff:
  \<open>bit (clearBit w m) n \<longleftrightarrow> m \<noteq> n \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (auto simp add: bit_unset_bit_iff)

definition even_word :: \<open>'a::len word \<Rightarrow> bool\<close>
  where [code_abbrev]: \<open>even_word = even\<close>

lemma even_word_iff [code]:
  \<open>even_word a \<longleftrightarrow> a AND 1 = 0\<close>
  by (simp add: and_one_eq even_iff_mod_2_eq_zero even_word_def)

lemma map_bit_range_eq_if_take_bit_eq:
  \<open>map (bit k) [0..<n] = map (bit l) [0..<n]\<close>
  if \<open>take_bit n k = take_bit n l\<close> for k l :: int
using that proof (induction n arbitrary: k l)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  from Suc.prems have \<open>take_bit n (k div 2) = take_bit n (l div 2)\<close>
    by (simp add: take_bit_Suc)
  then have \<open>map (bit (k div 2)) [0..<n] = map (bit (l div 2)) [0..<n]\<close>
    by (rule Suc.IH)
  moreover have \<open>bit (r div 2) = bit r \<circ> Suc\<close> for r :: int
    by (simp add: fun_eq_iff bit_Suc)
  moreover from Suc.prems have \<open>even k \<longleftrightarrow> even l\<close>
    by (auto simp add: take_bit_Suc elim!: evenE oddE) arith+
  ultimately show ?case
    by (simp only: map_Suc_upt upt_conv_Cons flip: list.map_comp) simp
qed


subsection \<open>More shift operations\<close>

lift_definition sshiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k. take_bit LENGTH('a) (signed_take_bit (LENGTH('a) - 1) k div 2)\<close>
  by (simp flip: signed_take_bit_decr_length_iff)
 
lift_definition sshiftr :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>  (infixl \<open>>>>\<close> 55)
  is \<open>\<lambda>k n. take_bit LENGTH('a) (drop_bit n (signed_take_bit (LENGTH('a) - 1) k))\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition bshiftr1 :: \<open>bool \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>b k. take_bit LENGTH('a) k div 2 + of_bool b * 2 ^ (LENGTH('a) - Suc 0)\<close>
  by (fact arg_cong)

lemma sshiftr1_eq:
  \<open>sshiftr1 w = word_of_int (bin_rest (sint w))\<close>
  by transfer simp

lemma sshiftr_eq:
  \<open>w >>> n = (sshiftr1 ^^ n) w\<close>
proof -
  have *: \<open>(\<lambda>k. take_bit LENGTH('a) (signed_take_bit (LENGTH('a) - Suc 0) k div 2)) ^^ Suc n =
    take_bit LENGTH('a) \<circ> drop_bit (Suc n) \<circ> signed_take_bit (LENGTH('a) - Suc 0)\<close>
    for n
    apply (induction n)
     apply (auto simp add: fun_eq_iff drop_bit_Suc)
    apply (metis (no_types, lifting) Suc_pred funpow_swap1 len_gt_0 sbintrunc_bintrunc sbintrunc_rest)
    done
  show ?thesis
    apply transfer
    apply simp
    subgoal for k n
      apply (cases n)
       apply (simp_all only: *)
       apply simp_all
      done
    done
qed

lemma mask_eq:
  \<open>mask n = (1 << n) - (1 :: 'a::len word)\<close>
  by transfer (simp add: mask_eq_exp_minus_1 push_bit_of_1) 

lemma uint_sshiftr_eq [code]:
  \<open>uint (w >>> n) = take_bit LENGTH('a) (sint w div 2 ^  n)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp flip: drop_bit_eq_div)

lemma sshift1_code [code]:
  \<open>sshiftr1 w = w >>> 1\<close>
  by transfer (simp add: drop_bit_Suc)


subsection \<open>Rotation\<close>

lift_definition word_rotr :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>n k. concat_bit (LENGTH('a) - n mod LENGTH('a))
    (drop_bit (n mod LENGTH('a)) (take_bit LENGTH('a) k))
    (take_bit (n mod LENGTH('a)) k)\<close>
  subgoal for n k l
    apply (simp add: concat_bit_def nat_le_iff less_imp_le
      take_bit_tightened [of \<open>LENGTH('a)\<close> k l \<open>n mod LENGTH('a::len)\<close>])
    done
  done

lift_definition word_rotl :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>n k. concat_bit (n mod LENGTH('a))
    (drop_bit (LENGTH('a) - n mod LENGTH('a)) (take_bit LENGTH('a) k))
    (take_bit (LENGTH('a) - n mod LENGTH('a)) k)\<close>
  subgoal for n k l
    apply (simp add: concat_bit_def nat_le_iff less_imp_le
      take_bit_tightened [of \<open>LENGTH('a)\<close> k l \<open>LENGTH('a) - n mod LENGTH('a::len)\<close>])
    done
  done

lift_definition word_roti :: \<open>int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  is \<open>\<lambda>r k. concat_bit (LENGTH('a) - nat (r mod int LENGTH('a)))
    (drop_bit (nat (r mod int LENGTH('a))) (take_bit LENGTH('a) k))
    (take_bit (nat (r mod int LENGTH('a))) k)\<close>
  subgoal for r k l
    apply (simp add: concat_bit_def nat_le_iff less_imp_le
      take_bit_tightened [of \<open>LENGTH('a)\<close> k l \<open>nat (r mod int LENGTH('a::len))\<close>])
    done
  done

lemma word_rotl_eq_word_rotr [code]:
  \<open>word_rotl n = (word_rotr (LENGTH('a) - n mod LENGTH('a)) :: 'a::len word \<Rightarrow> 'a word)\<close>
  by (rule ext, cases \<open>n mod LENGTH('a) = 0\<close>; transfer) simp_all

lemma word_roti_eq_word_rotr_word_rotl [code]:
  \<open>word_roti i w =
    (if i \<ge> 0 then word_rotr (nat i) w else word_rotl (nat (- i)) w)\<close>
proof (cases \<open>i \<ge> 0\<close>)
  case True
  moreover define n where \<open>n = nat i\<close>
  ultimately have \<open>i = int n\<close>
    by simp
  moreover have \<open>word_roti (int n) = (word_rotr n :: _ \<Rightarrow> 'a word)\<close>
    by (rule ext, transfer) (simp add: nat_mod_distrib)
  ultimately show ?thesis
    by simp
next
  case False
  moreover define n where \<open>n = nat (- i)\<close>
  ultimately have \<open>i = - int n\<close> \<open>n > 0\<close>
    by simp_all
  moreover have \<open>word_roti (- int n) = (word_rotl n :: _ \<Rightarrow> 'a word)\<close>
    by (rule ext, transfer)
      (simp add: zmod_zminus1_eq_if flip: of_nat_mod of_nat_diff)
  ultimately show ?thesis
    by simp
qed

lemma bit_word_rotr_iff:
  \<open>bit (word_rotr m w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w ((n + m) mod LENGTH('a))\<close>
  for w :: \<open>'a::len word\<close>
proof transfer
  fix k :: int and m n :: nat
  define q where \<open>q = m mod LENGTH('a)\<close>
  have \<open>q < LENGTH('a)\<close> 
    by (simp add: q_def)
  then have \<open>q \<le> LENGTH('a)\<close>
    by simp
  have \<open>m mod LENGTH('a) = q\<close>
    by (simp add: q_def)
  moreover have \<open>(n + m) mod LENGTH('a) = (n + q) mod LENGTH('a)\<close>
    by (subst mod_add_right_eq [symmetric]) (simp add: \<open>m mod LENGTH('a) = q\<close>)
  moreover have \<open>n < LENGTH('a) \<and>
    bit (concat_bit (LENGTH('a) - q) (drop_bit q (take_bit LENGTH('a) k)) (take_bit q k)) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit k ((n + q) mod LENGTH('a))\<close>
    using \<open>q < LENGTH('a)\<close>
    by (cases \<open>q + n \<ge> LENGTH('a)\<close>)
     (auto simp add: bit_concat_bit_iff bit_drop_bit_eq
        bit_take_bit_iff le_mod_geq ac_simps)
  ultimately show \<open>n < LENGTH('a) \<and>
    bit (concat_bit (LENGTH('a) - m mod LENGTH('a))
      (drop_bit (m mod LENGTH('a)) (take_bit LENGTH('a) k))
      (take_bit (m mod LENGTH('a)) k)) n
    \<longleftrightarrow> n < LENGTH('a) \<and>
      (n + m) mod LENGTH('a) < LENGTH('a) \<and>
      bit k ((n + m) mod LENGTH('a))\<close>
    by simp
qed

lemma bit_word_rotl_iff:
  \<open>bit (word_rotl m w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w ((n + (LENGTH('a) - m mod LENGTH('a))) mod LENGTH('a))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: word_rotl_eq_word_rotr bit_word_rotr_iff)

lemma bit_word_roti_iff:
  \<open>bit (word_roti k w) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit w (nat ((int n + k) mod int LENGTH('a)))\<close>
  for w :: \<open>'a::len word\<close>
proof transfer
  fix k l :: int and n :: nat
  define m where \<open>m = nat (k mod int LENGTH('a))\<close>
  have \<open>m < LENGTH('a)\<close> 
    by (simp add: nat_less_iff m_def)
  then have \<open>m \<le> LENGTH('a)\<close>
    by simp
  have \<open>k mod int LENGTH('a) = int m\<close>
    by (simp add: nat_less_iff m_def)
  moreover have \<open>(int n + k) mod int LENGTH('a) = int ((n + m) mod LENGTH('a))\<close>
    by (subst mod_add_right_eq [symmetric]) (simp add: of_nat_mod \<open>k mod int LENGTH('a) = int m\<close>)
  moreover have \<open>n < LENGTH('a) \<and>
    bit (concat_bit (LENGTH('a) - m) (drop_bit m (take_bit LENGTH('a) l)) (take_bit m l)) n \<longleftrightarrow>
    n < LENGTH('a) \<and> bit l ((n + m) mod LENGTH('a))\<close>
    using \<open>m < LENGTH('a)\<close>
    by (cases \<open>m + n \<ge> LENGTH('a)\<close>)
     (auto simp add: bit_concat_bit_iff bit_drop_bit_eq
        bit_take_bit_iff nat_less_iff not_le not_less ac_simps
        le_diff_conv le_mod_geq)
  ultimately show \<open>n < LENGTH('a)
    \<and> bit (concat_bit (LENGTH('a) - nat (k mod int LENGTH('a)))
             (drop_bit (nat (k mod int LENGTH('a))) (take_bit LENGTH('a) l))
             (take_bit (nat (k mod int LENGTH('a))) l)) n \<longleftrightarrow>
       n < LENGTH('a) 
    \<and> nat ((int n + k) mod int LENGTH('a)) < LENGTH('a)
    \<and> bit l (nat ((int n + k) mod int LENGTH('a)))\<close>
    by simp
qed

lemma uint_word_rotr_eq [code]:
  \<open>uint (word_rotr n w) = concat_bit (LENGTH('a) - n mod LENGTH('a))
    (drop_bit (n mod LENGTH('a)) (uint w))
    (uint (take_bit (n mod LENGTH('a)) w))\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (simp add: concat_bit_def take_bit_drop_bit push_bit_take_bit min_def)
  using mod_less_divisor not_less apply blast
  done

    
subsection \<open>Split and cat operations\<close>

lift_definition word_cat :: \<open>'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word\<close>
  is \<open>\<lambda>k l. concat_bit LENGTH('b) l (take_bit LENGTH('a) k)\<close>
  by (simp add: bit_eq_iff bit_concat_bit_iff bit_take_bit_iff)

lemma word_cat_eq:
  \<open>(word_cat v w :: 'c::len word) = push_bit LENGTH('b) (ucast v) + ucast w\<close>
  for v :: \<open>'a::len word\<close> and w :: \<open>'b::len word\<close>
  by transfer (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma word_cat_eq' [code]:
  \<open>word_cat a b = word_of_int (concat_bit LENGTH('b) (uint b) (uint a))\<close>
  for a :: \<open>'a::len word\<close> and b :: \<open>'b::len word\<close>
  by transfer simp

lemma bit_word_cat_iff:
  \<open>bit (word_cat v w :: 'c::len word) n \<longleftrightarrow> n < LENGTH('c) \<and> (if n < LENGTH('b) then bit w n else bit v (n - LENGTH('b)))\<close> 
  for v :: \<open>'a::len word\<close> and w :: \<open>'b::len word\<close>
  by transfer (simp add: bit_concat_bit_iff bit_take_bit_iff)

definition word_split :: "'a::len word \<Rightarrow> 'b::len word \<times> 'c::len word"
  where "word_split a =
    (case bin_split (LENGTH('c)) (uint a) of
      (u, v) \<Rightarrow> (word_of_int u, word_of_int v))"

definition word_rcat :: \<open>'a::len word list \<Rightarrow> 'b::len word\<close>
  where \<open>word_rcat = word_of_int \<circ> horner_sum uint (2 ^ LENGTH('a)) \<circ> rev\<close>

lemma word_rcat_eq:
  \<open>word_rcat ws = word_of_int (bin_rcat (LENGTH('a::len)) (map uint ws))\<close>
  for ws :: \<open>'a::len word list\<close>
  apply (simp add: word_rcat_def bin_rcat_def rev_map)
  apply transfer
  apply (simp add: horner_sum_foldr foldr_map comp_def)
  done

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
  by transfer simp

lemma unat_bintrunc_neg [simp]:
  "unat (- numeral bin :: 'a::len word) = nat (bintrunc (LENGTH('a)) (- numeral bin))"
  by transfer simp

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
  by transfer simp

lemma uint_numeral: "uint (numeral b :: 'a::len word) = numeral b mod 2 ^ LENGTH('a)"
  by (simp only: word_numeral_alt int_word_uint)

lemma uint_neg_numeral: "uint (- numeral b :: 'a::len word) = - numeral b mod 2 ^ LENGTH('a)"
  by (simp only: word_neg_numeral_alt int_word_uint)

lemma unat_numeral: "unat (numeral b :: 'a::len word) = numeral b mod 2 ^ LENGTH('a)"
  by transfer (simp add: take_bit_eq_mod nat_mod_distrib nat_power_eq)

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
  by transfer (simp add: take_bit_eq_mod)

lemma word_int_split:
  "P (word_int_case f x) =
    (\<forall>i. x = (word_of_int i :: 'b::len word) \<and> 0 \<le> i \<and> i < 2 ^ LENGTH('b) \<longrightarrow> P (f i))"
  by transfer (auto simp add: take_bit_eq_mod)

lemma word_int_split_asm:
  "P (word_int_case f x) =
    (\<nexists>n. x = (word_of_int n :: 'b::len word) \<and> 0 \<le> n \<and> n < 2 ^ LENGTH('b::len) \<and> \<not> P (f n))"
  by transfer (auto simp add: take_bit_eq_mod)

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
  \<open>bit (ucast a :: 'a::len word) n \<longleftrightarrow> n < LENGTH('a::len) \<and> Parity.bit a n\<close>
  by transfer (simp add: bit_take_bit_iff)

lemma ucast_id [simp]: "ucast w = w"
  by transfer simp

lemma scast_id [simp]: "scast w = w"
  by transfer simp

lemma nth_ucast: "(ucast w::'a::len word) !! n = (w !! n \<and> n < LENGTH('a))"
  by transfer (simp add: bit_take_bit_iff ac_simps)

lemma ucast_mask_eq:
  \<open>ucast (mask n :: 'b word) = mask (min LENGTH('b::len) n)\<close>
  by (simp add: bit_eq_iff) (auto simp add: bit_mask_iff bit_ucast_iff exp_eq_zero_iff)

\<comment> \<open>literal u(s)cast\<close>
lemma ucast_bintr [simp]:
  "ucast (numeral w :: 'a::len word) =
    word_of_int (bintrunc (LENGTH('a)) (numeral w))"
  by transfer simp

(* TODO: neg_numeral *)

lemma scast_sbintr [simp]:
  "scast (numeral w ::'a::len word) =
    word_of_int (sbintrunc (LENGTH('a) - Suc 0) (numeral w))"
  by transfer simp

lemma source_size: "source_size (c::'a::len word \<Rightarrow> _) = LENGTH('a)"
  by transfer simp

lemma target_size: "target_size (c::_ \<Rightarrow> 'b::len word) = LENGTH('b)"
  by transfer simp

lemma is_down: "is_down c \<longleftrightarrow> LENGTH('b) \<le> LENGTH('a)"
  for c :: "'a::len word \<Rightarrow> 'b::len word"
  by transfer simp

lemma is_up: "is_up c \<longleftrightarrow> LENGTH('a) \<le> LENGTH('b)"
  for c :: "'a::len word \<Rightarrow> 'b::len word"
  by transfer simp

lemma is_up_down:
  \<open>is_up c \<longleftrightarrow> is_down d\<close>
  for c :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  and d :: \<open>'b::len word \<Rightarrow> 'a::len word\<close>
  by transfer simp

context
  fixes dummy_types :: \<open>'a::len \<times> 'b::len\<close>
begin

private abbreviation (input) UCAST :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>UCAST == ucast\<close>

private abbreviation (input) SCAST :: \<open>'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>SCAST == scast\<close>

lemma down_cast_same:
  \<open>UCAST = scast\<close> if \<open>is_down UCAST\<close>
  by (rule ext, use that in transfer) (simp add: take_bit_signed_take_bit)

lemma sint_up_scast:
  \<open>sint (SCAST w) = sint w\<close> if \<open>is_up SCAST\<close>
  using that by transfer (simp add: min_def Suc_leI le_diff_iff)

lemma uint_up_ucast:
  \<open>uint (UCAST w) = uint w\<close> if \<open>is_up UCAST\<close>
  using that by transfer (simp add: min_def)

lemma ucast_up_ucast:
  \<open>ucast (UCAST w) = ucast w\<close> if \<open>is_up UCAST\<close>
  using that by transfer (simp add: ac_simps)

lemma ucast_up_ucast_id:
  \<open>ucast (UCAST w) = w\<close> if \<open>is_up UCAST\<close>
  using that by (simp add: ucast_up_ucast)

lemma scast_up_scast:
  \<open>scast (SCAST w) = scast w\<close> if \<open>is_up SCAST\<close>
  using that by transfer (simp add: ac_simps)

lemma scast_up_scast_id:
  \<open>scast (SCAST w) = w\<close> if \<open>is_up SCAST\<close>
  using that by (simp add: scast_up_scast)

lemma isduu:
  \<open>is_up UCAST\<close> if \<open>is_down d\<close>
    for d :: \<open>'b word \<Rightarrow> 'a word\<close>
  using that is_up_down [of UCAST d] by simp

lemma isdus:
  \<open>is_up SCAST\<close> if \<open>is_down d\<close>
    for d :: \<open>'b word \<Rightarrow> 'a word\<close>
  using that is_up_down [of SCAST d] by simp

lemmas ucast_down_ucast_id = isduu [THEN ucast_up_ucast_id]
lemmas scast_down_scast_id = isdus [THEN scast_up_scast_id]

lemma up_ucast_surj:
  \<open>surj (ucast :: 'b word \<Rightarrow> 'a word)\<close> if \<open>is_up UCAST\<close>
  by (rule surjI) (use that in \<open>rule ucast_up_ucast_id\<close>)

lemma up_scast_surj:
  \<open>surj (scast :: 'b word \<Rightarrow> 'a word)\<close> if \<open>is_up SCAST\<close>
  by (rule surjI) (use that in \<open>rule scast_up_scast_id\<close>)

lemma down_ucast_inj:
  \<open>inj_on UCAST A\<close> if \<open>is_down (ucast :: 'b word \<Rightarrow> 'a word)\<close>
  by (rule inj_on_inverseI) (use that in \<open>rule ucast_down_ucast_id\<close>)

lemma down_scast_inj:
  \<open>inj_on SCAST A\<close> if \<open>is_down (scast :: 'b word \<Rightarrow> 'a word)\<close>
  by (rule inj_on_inverseI) (use that in \<open>rule scast_down_scast_id\<close>)
  
lemma ucast_down_wi:
  \<open>UCAST (word_of_int x) = word_of_int x\<close> if \<open>is_down UCAST\<close>
  using that by transfer simp

lemma ucast_down_no:
  \<open>UCAST (numeral bin) = numeral bin\<close> if \<open>is_down UCAST\<close>
  using that by transfer simp

end

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
  by (standard; transfer) (auto simp add: signed_take_bit_decr_length_iff)

interpretation signed: linorder "word_sle" "word_sless"
  by (rule signed_linorder)

lemma udvdI: "0 \<le> n \<Longrightarrow> uint b = n * uint a \<Longrightarrow> a udvd b"
  by (auto simp: udvd_def)

lemmas word_div_no [simp] = word_div_def [of "numeral a" "numeral b"] for a b
lemmas word_mod_no [simp] = word_mod_def [of "numeral a" "numeral b"] for a b
lemmas word_less_no [simp] = word_less_def [of "numeral a" "numeral b"] for a b
lemmas word_le_no [simp] = word_le_def [of "numeral a" "numeral b"] for a b
lemmas word_sless_no [simp] = word_sless_eq [of "numeral a" "numeral b"] for a b
lemmas word_sle_no [simp] = word_sle_eq [of "numeral a" "numeral b"] for a b

lemma word_m1_wi: "- 1 = word_of_int (- 1)"
  by (simp add: word_neg_numeral_alt [of Num.One])

lemma uint_0_iff: "uint x = 0 \<longleftrightarrow> x = 0"
  by (simp add: word_uint_eq_iff)

lemma unat_0_iff: "unat x = 0 \<longleftrightarrow> x = 0"
  by transfer (auto intro: antisym)

lemma unat_0 [simp]: "unat 0 = 0"
  by transfer simp

lemma size_0_same': "size w = 0 \<Longrightarrow> w = v"
  for v w :: "'a::len word"
  by (unfold word_size) simp

lemmas size_0_same = size_0_same' [unfolded word_size]

lemmas unat_eq_0 = unat_0_iff
lemmas unat_eq_zero = unat_0_iff

lemma unat_gt_0: "0 < unat x \<longleftrightarrow> x \<noteq> 0"
  by (auto simp: unat_0_iff [symmetric])

lemma ucast_0 [simp]: "ucast 0 = 0"
  by transfer simp

lemma sint_0 [simp]: "sint 0 = 0"
  by (simp add: sint_uint)

lemma scast_0 [simp]: "scast 0 = 0"
  by transfer simp

lemma sint_n1 [simp] : "sint (- 1) = - 1"
  by transfer simp

lemma scast_n1 [simp]: "scast (- 1) = - 1"
  by transfer simp

lemma uint_1: "uint (1::'a::len word) = 1"
  by (fact uint_1_eq)

lemma unat_1 [simp]: "unat (1::'a::len word) = 1"
  by transfer simp

lemma ucast_1 [simp]: "ucast (1::'a::len word) = 1"
  by transfer simp

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
  by (auto simp add: word_sle_eq word_sless_eq less_le)

lemma word_le_nat_alt: "a \<le> b \<longleftrightarrow> unat a \<le> unat b"
  by transfer (simp add: nat_le_eq_zle)

lemma word_less_nat_alt: "a < b \<longleftrightarrow> unat a < unat b"
  by transfer (auto simp add: less_le [of 0])

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
  supply nat_uint_eq [simp del]
  apply (unfold udvd_def)
  apply safe
   apply (simp add: unat_eq_nat_uint nat_mult_distrib)
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
  \<open>unat (w - 1) = unat w - 1\<close> if \<open>w \<noteq> 0\<close>
proof -
  have "0 \<le> uint w" by (fact uint_nonnegative)
  moreover from that have "0 \<noteq> uint w"
    by (simp add: uint_0_iff)
  ultimately have "1 \<le> uint w"
    by arith
  from uint_lt2p [of w] have "uint w - 1 < 2 ^ LENGTH('a)"
    by arith
  with \<open>1 \<le> uint w\<close> have "(uint w - 1) mod 2 ^ LENGTH('a) = uint w - 1"
    by (auto intro: mod_pos_pos_trivial)
  with \<open>1 \<le> uint w\<close> have "nat ((uint w - 1) mod 2 ^ LENGTH('a)) = nat (uint w) - 1"
    by (auto simp del: nat_uint_eq)
  then show ?thesis
    by (simp only: unat_eq_nat_uint int_word_uint word_arith_wis mod_diff_right_eq)
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
  by transfer (auto simp add: take_bit_eq_mod take_bit_int_less_exp)

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
  apply (standard; transfer)
     apply (simp_all add: unats_def take_bit_int_less_exp take_bit_of_nat take_bit_eq_self)
  apply (simp add: take_bit_eq_mod)
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
  supply nat_uint_eq [simp del]
  apply (unfold word_size)
  apply (simp add: un_ui_le)
  apply (auto simp add: unat_eq_nat_uint uint_sub_if')
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
  by (simp add: uint_div nat_div_distrib flip: nat_uint_eq)

lemma uint_mod:
  \<open>uint (x mod y) = uint x mod uint y\<close>
  by (metis (no_types, lifting) le_less_trans mod_by_0 mod_le_divisor mod_less neq0_conv uint_nat unat_lt2p unat_word_ariths(7) zmod_int)
  
lemma unat_mod:
  \<open>unat (x mod y) = unat x mod unat y\<close>
  by (simp add: uint_mod nat_mod_distrib flip: nat_uint_eq)


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

lemma bit_horner_sum_bit_word_iff:
  \<open>bit (horner_sum of_bool (2 :: 'a::len word) bs) n
    \<longleftrightarrow> n < min LENGTH('a) (length bs) \<and> bs ! n\<close>
  by transfer (simp add: bit_horner_sum_bit_iff)

definition word_reverse :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>word_reverse w = horner_sum of_bool 2 (rev (map (bit w) [0..<LENGTH('a)]))\<close>

lemma bit_word_reverse_iff:
  \<open>bit (word_reverse w) n \<longleftrightarrow> n < LENGTH('a) \<and> bit w (LENGTH('a) - Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  by (cases \<open>n < LENGTH('a)\<close>)
    (simp_all add: word_reverse_def bit_horner_sum_bit_word_iff rev_nth)

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
  by transfer (simp add: bin_sc_eq)
 
lemma clearBit_no [simp]:
  "clearBit (numeral bin) n = word_of_int (bin_sc n False (numeral bin))"
  by transfer (simp add: bin_sc_eq)

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
  by (fact shiftl1.abs_eq)

lemma shiftl1_numeral [simp]: "shiftl1 (numeral w) = numeral (Num.Bit0 w)"
  unfolding word_numeral_alt shiftl1_wi by simp

lemma shiftl1_neg_numeral [simp]: "shiftl1 (- numeral w) = - numeral (Num.Bit0 w)"
  unfolding word_neg_numeral_alt shiftl1_wi by simp

lemma shiftl1_0 [simp] : "shiftl1 0 = 0"
  by transfer simp

lemma shiftl1_def_u: "shiftl1 w = word_of_int (2 * uint w)"
  by (fact shiftl1_eq)

lemma shiftl1_def_s: "shiftl1 w = word_of_int (2 * sint w)"
  by (simp add: shiftl1_def_u wi_hom_syms)

lemma shiftr1_0 [simp]: "shiftr1 0 = 0"
  by transfer simp

lemma sshiftr1_0 [simp]: "sshiftr1 0 = 0"
  by transfer simp

lemma sshiftr1_n1 [simp]: "sshiftr1 (- 1) = - 1"
  by transfer simp

lemma shiftl_0 [simp]: "(0::'a::len word) << n = 0"
  by transfer simp

lemma shiftr_0 [simp]: "(0::'a::len word) >> n = 0"
  by transfer simp

lemma sshiftr_0 [simp]: "0 >>> n = 0"
  by transfer simp

lemma sshiftr_n1 [simp]: "-1 >>> n = -1"
  by transfer simp

lemma nth_shiftl1: "shiftl1 w !! n \<longleftrightarrow> n < size w \<and> n > 0 \<and> w !! (n - 1)"
  by transfer (auto simp add: bit_double_iff)

lemma nth_shiftl': "(w << m) !! n \<longleftrightarrow> n < size w \<and> n >= m \<and> w !! (n - m)"
  for w :: "'a::len word"
  by transfer (auto simp add: bit_push_bit_iff)

lemmas nth_shiftl = nth_shiftl' [unfolded word_size]

lemma nth_shiftr1: "shiftr1 w !! n = w !! Suc n"
  by transfer (auto simp add: bit_take_bit_iff simp flip: bit_Suc)

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
  by transfer simp

lemma bit_sshiftr1_iff:
  \<open>bit (sshiftr1 w) n \<longleftrightarrow> bit w (if n = LENGTH('a) - 1 then LENGTH('a) - 1 else Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_signed_take_bit_iff min_def simp flip: bit_Suc)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma bit_sshiftr_word_iff:
  \<open>bit (w >>> m) n \<longleftrightarrow> bit w (if LENGTH('a) - m \<le> n \<and> n < LENGTH('a) then LENGTH('a) - 1 else (m + n))\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq bit_signed_take_bit_iff min_def not_le simp flip: bit_Suc)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma nth_sshiftr1: "sshiftr1 w !! n = (if n = size w - 1 then w !! n else w !! Suc n)"
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_signed_take_bit_iff min_def simp flip: bit_Suc)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma nth_sshiftr :
  "sshiftr w m !! n =
    (n < size w \<and> (if n + m \<ge> size w then w !! (size w - 1) else w !! (n + m)))"
  apply transfer
  apply (auto simp add: bit_take_bit_iff bit_drop_bit_eq bit_signed_take_bit_iff min_def not_le ac_simps)
  using le_less_Suc_eq apply fastforce
  using le_less_Suc_eq apply fastforce
  done

lemma shiftr1_div_2: "uint (shiftr1 w) = uint w div 2"
  by (fact uint_shiftr1)

lemma sshiftr1_div_2: "sint (sshiftr1 w) = sint w div 2"
  by transfer simp

lemma shiftr_div_2n: "uint (shiftr w n) = uint w div 2 ^ n"
  apply (unfold shiftr_def)
  apply (induct n)
   apply simp
  apply (simp add: shiftr1_div_2 mult.commute zdiv_zmult2_eq [symmetric])
  done

lemma sshiftr_div_2n: "sint (sshiftr w n) = sint w div 2 ^ n"
  apply transfer
  apply (auto simp add: bit_eq_iff bit_signed_take_bit_iff bit_drop_bit_eq min_def simp flip: drop_bit_eq_div)
  done

lemma bit_bshiftr1_iff:
  \<open>bit (bshiftr1 b w) n \<longleftrightarrow> b \<and> n = LENGTH('a) - 1 \<or> bit w (Suc n)\<close>
  for w :: \<open>'a::len word\<close>
  apply transfer
  apply (simp add: bit_take_bit_iff flip: bit_Suc)
    apply (subst disjunctive_add)
   apply (auto simp add: bit_take_bit_iff bit_or_iff bit_exp_iff simp flip: bit_Suc)
  done


subsubsection \<open>shift functions in terms of lists of bools\<close>

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

lemma shiftl_numeral [simp]:
  \<open>numeral k << numeral l = (push_bit (numeral l) (numeral k) :: 'a::len word)\<close>
  by (fact shiftl_word_eq)

lemma shiftl_zero_size: "size x \<le> n \<Longrightarrow> x << n = 0"
  for x :: "'a::len word"
  apply transfer
  apply (simp add: take_bit_push_bit)
  done

\<comment> \<open>note -- the following results use \<open>'a::len word < number_ring\<close>\<close>

lemma shiftl1_2t: "shiftl1 w = 2 * w"
  for w :: "'a::len word"
  by (simp add: shiftl1_eq wi_hom_mult [symmetric])

lemma shiftl1_p: "shiftl1 w = w + w"
  for w :: "'a::len word"
  by (simp add: shiftl1_2t)

lemma shiftl_t2n: "shiftl w n = 2 ^ n * w"
  for w :: "'a::len word"
  by (induct n) (auto simp: shiftl_def shiftl1_2t)

lemma shiftr1_bintr [simp]:
  "(shiftr1 (numeral w) :: 'a::len word) =
    word_of_int (bin_rest (bintrunc (LENGTH('a)) (numeral w)))"
  unfolding shiftr1_eq word_numeral_alt by (simp add: word_ubin.eq_norm)

lemma sshiftr1_sbintr [simp]:
  "(sshiftr1 (numeral w) :: 'a::len word) =
    word_of_int (bin_rest (sbintrunc (LENGTH('a) - 1) (numeral w)))"
  unfolding sshiftr1_eq word_numeral_alt by (simp add: word_sbin.eq_norm)

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


subsubsection \<open>Mask\<close>

lemma minus_1_eq_mask:
  \<open>- 1 = (mask LENGTH('a) :: 'a::len word)\<close>
  by (rule bit_eqI) (simp add: bit_exp_iff bit_mask_iff exp_eq_zero_iff)

lemma mask_eq_decr_exp:
  \<open>mask n = 2 ^ n - (1 :: 'a::len word)\<close>
  by (fact mask_eq_exp_minus_1)

lemma mask_Suc_rec:
  \<open>mask (Suc n) = 2 * mask n + (1 :: 'a::len word)\<close>
  by (simp add: mask_eq_exp_minus_1)

context
begin

qualified lemma bit_mask_iff:
  \<open>bit (mask m :: 'a::len word) n \<longleftrightarrow> n < min LENGTH('a) m\<close>
  by (simp add: bit_mask_iff exp_eq_zero_iff not_le)

end

lemma nth_mask [simp]:
  \<open>(mask n :: 'a::len word) !! i \<longleftrightarrow> i < n \<and> i < size (mask n :: 'a word)\<close>
  by (auto simp add: test_bit_word_eq word_size Word.bit_mask_iff)

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
  apply (simp flip: and_mask_dvd)
  apply transfer
  using dvd_nat_abs_iff [of _ \<open>take_bit LENGTH('a) k\<close> for k]
  apply simp
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

lemma and_mask_less_size: "n < size x \<Longrightarrow> x AND mask n < 2 ^ n"
  for x :: \<open>'a::len word\<close>
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
  for x :: \<open>'a::len word\<close>
  using word_of_int_Ex [where x=x]
  by (auto simp: and_mask_wi' word_of_int_power_hom word.abs_eq_iff bintrunc_mod2p mod_simps)

lemma mask_full [simp]: "mask LENGTH('a) = (- 1 :: 'a::len word)"
  by transfer (simp add: take_bit_minus_one_eq_mask)


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

definition slice :: \<open>nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word\<close>
  where \<open>slice n = slice1 (LENGTH('a) - n)\<close>

lemma bit_slice_iff:
  \<open>bit (slice m w :: 'b::len word) n \<longleftrightarrow> n < min LENGTH('b) (LENGTH('a) - m) \<and> bit w (n + LENGTH('a) - (LENGTH('a) - m))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: slice_def word_size bit_slice1_iff)

lemma slice1_0 [simp] : "slice1 n 0 = 0"
  unfolding slice1_def by simp

lemma slice_0 [simp] : "slice n 0 = 0"
  unfolding slice_def by auto

lemma slice_shiftr: "slice n w = ucast (w >> n)"
  apply (rule bit_word_eqI)
  apply (cases \<open>n \<le> LENGTH('b)\<close>)
   apply (auto simp add: bit_slice_iff bit_ucast_iff bit_shiftr_word_iff ac_simps
    dest: bit_imp_le_length)
  done

lemma nth_slice: "(slice n w :: 'a::len word) !! m = (w !! (m + n) \<and> m < LENGTH('a))"
  by (simp add: slice_shiftr nth_ucast nth_shiftr)

lemma ucast_slice1: "ucast w = slice1 (size w) w"
  apply (simp add: slice1_def)
  apply transfer
  apply simp
  done

lemma ucast_slice: "ucast w = slice 0 w"
  by (simp add: slice_def slice1_def)

lemma slice_id: "slice 0 t = t"
  by (simp only: ucast_slice [symmetric] ucast_id)

lemma rev_slice1:
  \<open>slice1 n (word_reverse w :: 'b::len word) = word_reverse (slice1 k w :: 'a::len word)\<close>
  if \<open>n + k = LENGTH('a) + LENGTH('b)\<close>
proof (rule bit_word_eqI)
  fix m
  assume *: \<open>m < LENGTH('a)\<close>
  from that have **: \<open>LENGTH('b) = n + k - LENGTH('a)\<close>
    by simp
  show \<open>bit (slice1 n (word_reverse w :: 'b word) :: 'a word) m \<longleftrightarrow> bit (word_reverse (slice1 k w :: 'a word)) m\<close>
    apply (simp add: bit_slice1_iff bit_word_reverse_iff)
    using * **
    apply (cases \<open>n \<le> LENGTH('a)\<close>; cases \<open>k \<le> LENGTH('a)\<close>)
       apply auto
    done
qed

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

lemma revcast_slice1 [OF refl]: "rc = revcast w \<Longrightarrow> slice1 (size rc) w = rc"
  by (simp add: revcast_def word_size)

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
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_ucast_iff bit_shiftr_word_iff ac_simps)
  done

lemma revcast_down_us [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = ucast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_ucast_iff bit_sshiftr_word_iff ac_simps)
  done

lemma revcast_down_su [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_scast_iff bit_shiftr_word_iff ac_simps)
  done

lemma revcast_down_ss [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> rc w = scast (w >>> n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_scast_iff bit_sshiftr_word_iff ac_simps)
  done

lemma cast_down_rev [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> uc w = revcast (w << n)"
  for w :: "'a::len word"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_ucast_iff bit_shiftl_word_iff)
  done

lemma revcast_up [OF refl]:
  "rc = revcast \<Longrightarrow> source_size rc + n = target_size rc \<Longrightarrow>
    rc w = (ucast w :: 'a::len word) << n"
  apply (simp add: source_size_def target_size_def)
  apply (rule bit_word_eqI)
  apply (simp add: bit_revcast_iff bit_word_ucast_iff bit_shiftl_word_iff)
  apply auto
  apply (metis add.commute add_diff_cancel_right)
  apply (metis diff_add_inverse2 diff_diff_add)
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
lemmas word_cat_bin' = word_cat_eq

lemma word_rsplit_no:
  "(word_rsplit (numeral bin :: 'b::len word) :: 'a word list) =
    map word_of_int (bin_rsplit (LENGTH('a::len))
      (LENGTH('b), bintrunc (LENGTH('b)) (numeral bin)))"
  by (simp add: word_rsplit_def word_ubin.eq_norm)

lemmas word_rsplit_no_cl [simp] = word_rsplit_no
  [unfolded bin_rsplitl_def bin_rsplit_l [symmetric]]

lemma test_bit_cat [OF refl]:
  "wc = word_cat a b \<Longrightarrow> wc !! n = (n < size wc \<and>
    (if n < size b then b !! n else a !! (n - size b)))"
  apply (simp add: word_size not_less; transfer)
       apply (auto simp add: bit_concat_bit_iff bit_take_bit_iff)
  done

lemma split_uint_lem: "bin_split n (uint w) = (a, b) \<Longrightarrow>
    a = bintrunc (LENGTH('a) - n) a \<and> b = bintrunc (LENGTH('a)) b"
  for w :: "'a::len word"
  apply (frule word_ubin.norm_Rep [THEN ssubst])
  apply (drule bin_split_trunc1)
  apply (drule sym [THEN trans])
   apply assumption
  apply safe
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
  by transfer simp

\<comment> \<open>limited hom result\<close>
lemma word_cat_hom:
  "LENGTH('a::len) \<le> LENGTH('b::len) + LENGTH('c::len) \<Longrightarrow>
    (word_cat (word_of_int w :: 'b word) (b :: 'c word) :: 'a word) =
    word_of_int (bin_cat w (size b) (uint b))"
  apply transfer
  using bintr_cat by auto

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

lemma horner_sum_uint_exp_Cons_eq:
  \<open>horner_sum uint (2 ^ LENGTH('a)) (w # ws) =
    concat_bit LENGTH('a) (uint w) (horner_sum uint (2 ^ LENGTH('a)) ws)\<close>
  for ws :: \<open>'a::len word list\<close>
  by (simp add: concat_bit_eq push_bit_eq_mult)

lemma bit_horner_sum_uint_exp_iff:
  \<open>bit (horner_sum uint (2 ^ LENGTH('a)) ws) n \<longleftrightarrow>
    n div LENGTH('a) < length ws \<and> bit (ws ! (n div LENGTH('a))) (n mod LENGTH('a))\<close>
  for ws :: \<open>'a::len word list\<close>
proof (induction ws arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons w ws)
  then show ?case
    by (cases \<open>n \<ge> LENGTH('a)\<close>)
      (simp_all only: horner_sum_uint_exp_Cons_eq, simp_all add: bit_concat_bit_iff le_div_geq le_mod_geq bit_uint_iff Cons)
qed

lemma test_bit_rcat:
  "sw = size (hd wl) \<Longrightarrow> rc = word_rcat wl \<Longrightarrow> rc !! n =
    (n < size rc \<and> n div sw < size wl \<and> (rev wl) ! (n div sw) !! (n mod sw))"
  for wl :: "'a::len word list"
  by (simp add: word_size word_rcat_def bin_rcat_def foldl_map rev_map bit_horner_sum_uint_exp_iff)
    (simp add: test_bit_eq_bit)

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

lemma word_rotr_word_rotr_eq:
  \<open>word_rotr m (word_rotr n w) = word_rotr (m + n) w\<close>
  by (rule bit_word_eqI) (simp add: bit_word_rotr_iff ac_simps mod_add_right_eq)

lemma word_rot_rl [simp]:
  \<open>word_rotl k (word_rotr k v) = v\<close>
  apply (rule bit_word_eqI)
  apply (simp add: word_rotl_eq_word_rotr word_rotr_word_rotr_eq bit_word_rotr_iff algebra_simps)
  apply (auto dest: bit_imp_le_length)
   apply (metis (no_types, lifting) add.right_neutral add_diff_cancel_right' div_mult_mod_eq mod_add_right_eq mod_add_self2 mod_if mod_mult_self2_is_0)
  apply (metis (no_types, lifting) add.right_neutral add_diff_cancel_right' bit_imp_le_length div_mult_mod_eq mod_add_right_eq mod_add_self2 mod_less mod_mult_self2_is_0)
  done

lemma word_rot_lr [simp]:
  \<open>word_rotr k (word_rotl k v) = v\<close>
  apply (rule bit_word_eqI)
  apply (simp add: word_rotl_eq_word_rotr word_rotr_word_rotr_eq bit_word_rotr_iff algebra_simps)
  apply (auto dest: bit_imp_le_length)
   apply (metis (no_types, lifting) add.right_neutral add_diff_cancel_right' div_mult_mod_eq mod_add_right_eq mod_add_self2 mod_if mod_mult_self2_is_0)
  apply (metis (no_types, lifting) add.right_neutral add_diff_cancel_right' bit_imp_le_length div_mult_mod_eq mod_add_right_eq mod_add_self2 mod_less mod_mult_self2_is_0)
  done

lemma word_rot_gal:
  \<open>word_rotr n v = w \<longleftrightarrow> word_rotl n w = v\<close>
  by auto

lemma word_rot_gal':
  \<open>w = word_rotr n v \<longleftrightarrow> v = word_rotl n w\<close>
  by auto

lemma word_rotr_rev:
  \<open>word_rotr n w = word_reverse (word_rotl n (word_reverse w))\<close>
proof (rule bit_word_eqI)
  fix m
  assume \<open>m < LENGTH('a)\<close>
  moreover have \<open>1 +
    ((int m + int n mod int LENGTH('a)) mod int LENGTH('a) +
     ((int LENGTH('a) * 2) mod int LENGTH('a) - (1 + (int m + int n mod int LENGTH('a)))) mod int LENGTH('a)) =
    int LENGTH('a)\<close>
    apply (cases \<open>(1 + (int m + int n mod int LENGTH('a))) mod
         int LENGTH('a) = 0\<close>)
    using zmod_zminus1_eq_if [of \<open>1 + (int m + int n mod int LENGTH('a))\<close> \<open>int LENGTH('a)\<close>]
    apply simp_all
     apply (auto simp add: algebra_simps)
     apply (simp add: minus_equation_iff [of \<open>int m\<close>])
     apply (drule sym [of _ \<open>int m\<close>])
    apply simp
    apply (metis add.commute add_minus_cancel diff_minus_eq_add len_gt_0 less_imp_of_nat_less less_nat_zero_code mod_mult_self3 of_nat_gt_0 zmod_minus1)
    apply (metis (no_types, hide_lams) Abs_fnat_hom_add less_not_refl mod_Suc of_nat_Suc of_nat_gt_0 of_nat_mod)
    done
  then have \<open>int ((m + n) mod LENGTH('a)) =
    int (LENGTH('a) - Suc ((LENGTH('a) - Suc m + LENGTH('a) - n mod LENGTH('a)) mod LENGTH('a)))\<close>
    using \<open>m < LENGTH('a)\<close>
    by (simp only: of_nat_mod mod_simps)
      (simp add: of_nat_diff of_nat_mod Suc_le_eq add_less_mono algebra_simps mod_simps)
  then have \<open>(m + n) mod LENGTH('a) =
    LENGTH('a) - Suc ((LENGTH('a) - Suc m + LENGTH('a) - n mod LENGTH('a)) mod LENGTH('a))\<close>
    by simp
  ultimately show \<open>bit (word_rotr n w) m \<longleftrightarrow> bit (word_reverse (word_rotl n (word_reverse w))) m\<close>
    by (simp add: word_rotl_eq_word_rotr bit_word_rotr_iff bit_word_reverse_iff)
qed

lemma word_roti_0 [simp]: "word_roti 0 w = w"
  by transfer simp

lemma word_roti_add: "word_roti (m + n) w = word_roti m (word_roti n w)"
  by (rule bit_word_eqI)
    (simp add: bit_word_roti_iff nat_less_iff mod_simps ac_simps)

lemma word_roti_conv_mod':
  "word_roti n w = word_roti (n mod int (size w)) w"
  by transfer simp

lemmas word_roti_conv_mod = word_roti_conv_mod' [unfolded word_size]


subsubsection \<open>"Word rotation commutes with bit-wise operations\<close>

\<comment> \<open>using locale to not pollute lemma namespace\<close>
locale word_rotate
begin

lemma word_rot_logs:
  "word_rotl n (NOT v) = NOT (word_rotl n v)"
  "word_rotr n (NOT v) = NOT (word_rotr n v)"
  "word_rotl n (x AND y) = word_rotl n x AND word_rotl n y"
  "word_rotr n (x AND y) = word_rotr n x AND word_rotr n y"
  "word_rotl n (x OR y) = word_rotl n x OR word_rotl n y"
  "word_rotr n (x OR y) = word_rotr n x OR word_rotr n y"
  "word_rotl n (x XOR y) = word_rotl n x XOR word_rotl n y"
  "word_rotr n (x XOR y) = word_rotr n x XOR word_rotr n y"
         apply (rule bit_word_eqI)
         apply (auto simp add: bit_word_rotl_iff bit_not_iff algebra_simps exp_eq_zero_iff not_le)
        apply (rule bit_word_eqI)
        apply (auto simp add: bit_word_rotr_iff bit_not_iff algebra_simps exp_eq_zero_iff not_le)
       apply (rule bit_word_eqI)
       apply (auto simp add: bit_word_rotl_iff bit_and_iff algebra_simps exp_eq_zero_iff not_le)
      apply (rule bit_word_eqI)
      apply (auto simp add: bit_word_rotr_iff bit_and_iff algebra_simps exp_eq_zero_iff not_le)
     apply (rule bit_word_eqI)
     apply (auto simp add: bit_word_rotl_iff bit_or_iff algebra_simps exp_eq_zero_iff not_le)
    apply (rule bit_word_eqI)
    apply (auto simp add: bit_word_rotr_iff bit_or_iff algebra_simps exp_eq_zero_iff not_le)
   apply (rule bit_word_eqI)
   apply (auto simp add: bit_word_rotl_iff bit_xor_iff algebra_simps exp_eq_zero_iff not_le)
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_word_rotr_iff bit_xor_iff algebra_simps exp_eq_zero_iff not_le)
  done

end

lemmas word_rot_logs = word_rotate.word_rot_logs

lemma word_rotx_0 [simp] : "word_rotr i 0 = 0 \<and> word_rotl i 0 = 0"
  by transfer simp_all

lemma word_roti_0' [simp] : "word_roti n 0 = 0"
  by transfer simp

declare word_roti_eq_word_rotr_word_rotl [simp]


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
  by transfer simp

lemma shiftl_x_0 [simp]: "x << 0 = x"
  for x :: "'a::len word"
  by (simp add: shiftl_t2n)

lemma shiftl_1 [simp]: "(1::'a::len word) << n = 2^n"
  by (simp add: shiftl_t2n)

lemma uint_lt_0 [simp]: "uint x < 0 = False"
  by (simp add: linorder_not_less)

lemma shiftr1_1 [simp]: "shiftr1 (1::'a::len word) = 0"
  by transfer simp

lemma shiftr_1[simp]: "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (induct n) (auto simp: shiftr_def)

lemma word_less_1 [simp]: "x < 1 \<longleftrightarrow> x = 0"
  for x :: "'a::len word"
  by (simp add: word_less_nat_alt unat_0_iff)

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
  apply transfer
  apply (simp flip: nat_diff_distrib)
  apply (metis minus_word.abs_eq uint_sub_lem word_ubin.eq_norm)
  done

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

lemma shiftl0:
  "x << 0 = (x :: 'a :: len word)"
  by (fact shiftl_x_0)

lemma mask_1: "mask 1 = 1"
  by transfer (simp add: min_def mask_Suc_exp)

lemma mask_Suc_0: "mask (Suc 0) = 1"
  using mask_1 by simp

lemma mask_numeral: "mask (numeral n) = 2 * mask (pred_numeral n) + (1 :: 'a::len word)"
  by (simp add: mask_Suc_rec numeral_eq_Suc)

lemma bin_last_bintrunc: "bin_last (bintrunc l n) = (l > 0 \<and> bin_last n)"
  by simp

lemma word_and_1:
  "n AND 1 = (if n !! 0 then 1 else 0)" for n :: "_ word"
  by (rule bit_word_eqI) (auto simp add: bit_and_iff test_bit_eq_bit bit_1_iff intro: gr0I)

lemma bintrunc_shiftl:
  "bintrunc n (m << i) = bintrunc (n - i) m << i"
  by (rule bit_eqI) (auto simp add: bit_take_bit_iff)

lemma uint_shiftl:
  "uint (n << i) = bintrunc (size n) (uint n << i)"
  by transfer (simp add: push_bit_take_bit shiftl_eq_push_bit)


subsection \<open>Misc\<close>

ML_file \<open>Tools/word_lib.ML\<close>
ML_file \<open>Tools/smt_word.ML\<close>

hide_const (open) Word

end
