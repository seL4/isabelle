(*  Title:      HOL/Word/Word.thy
    Author: Jeremy Dawson and Gerwin Klein, NICTA
*)

header {* A type of finite bit strings *}

theory Word
imports
  Type_Length
  Misc_Typedef
  "~~/src/HOL/Library/Boolean_Algebra"
  Bool_List_Representation
uses ("~~/src/HOL/Word/Tools/smt_word.ML")
begin

text {* see @{text "Examples/WordExamples.thy"} for examples *}

subsection {* Type definition *}

typedef (open) 'a word = "{(0::int) ..< 2^len_of TYPE('a::len0)}"
  morphisms uint Abs_word by auto

definition word_of_int :: "int \<Rightarrow> 'a\<Colon>len0 word" where
  -- {* representation of words using unsigned or signed bins, 
        only difference in these is the type class *}
  "word_of_int w = Abs_word (bintrunc (len_of TYPE ('a)) w)" 

lemma uint_word_of_int [code]: "uint (word_of_int w \<Colon> 'a\<Colon>len0 word) = w mod 2 ^ len_of TYPE('a)"
  by (auto simp add: word_of_int_def bintrunc_mod2p intro: Abs_word_inverse)

code_datatype word_of_int

subsection {* Random instance *}

notation fcomp (infixl "\<circ>>" 60)
notation scomp (infixl "\<circ>\<rightarrow>" 60)

instantiation word :: ("{len0, typerep}") random
begin

definition
  "random_word i = Random.range (max i (2 ^ len_of TYPE('a))) \<circ>\<rightarrow> (\<lambda>k. Pair (
     let j = word_of_int (Code_Numeral.int_of k) :: 'a word
     in (j, \<lambda>_::unit. Code_Evaluation.term_of j)))"

instance ..

end

no_notation fcomp (infixl "\<circ>>" 60)
no_notation scomp (infixl "\<circ>\<rightarrow>" 60)


subsection {* Type conversions and casting *}

definition sint :: "'a :: len word => int" where
  -- {* treats the most-significant-bit as a sign bit *}
  sint_uint: "sint w = sbintrunc (len_of TYPE ('a) - 1) (uint w)"

definition unat :: "'a :: len0 word => nat" where
  "unat w = nat (uint w)"

definition uints :: "nat => int set" where
  -- "the sets of integers representing the words"
  "uints n = range (bintrunc n)"

definition sints :: "nat => int set" where
  "sints n = range (sbintrunc (n - 1))"

definition unats :: "nat => nat set" where
  "unats n = {i. i < 2 ^ n}"

definition norm_sint :: "nat => int => int" where
  "norm_sint n w = (w + 2 ^ (n - 1)) mod 2 ^ n - 2 ^ (n - 1)"

definition scast :: "'a :: len word => 'b :: len word" where
  -- "cast a word to a different length"
  "scast w = word_of_int (sint w)"

definition ucast :: "'a :: len0 word => 'b :: len0 word" where
  "ucast w = word_of_int (uint w)"

instantiation word :: (len0) size
begin

definition
  word_size: "size (w :: 'a word) = len_of TYPE('a)"

instance ..

end

definition source_size :: "('a :: len0 word => 'b) => nat" where
  -- "whether a cast (or other) function is to a longer or shorter length"
  "source_size c = (let arb = undefined ; x = c arb in size arb)"  

definition target_size :: "('a => 'b :: len0 word) => nat" where
  "target_size c = size (c undefined)"

definition is_up :: "('a :: len0 word => 'b :: len0 word) => bool" where
  "is_up c \<longleftrightarrow> source_size c <= target_size c"

definition is_down :: "('a :: len0 word => 'b :: len0 word) => bool" where
  "is_down c \<longleftrightarrow> target_size c <= source_size c"

definition of_bl :: "bool list => 'a :: len0 word" where
  "of_bl bl = word_of_int (bl_to_bin bl)"

definition to_bl :: "'a :: len0 word => bool list" where
  "to_bl w = bin_to_bl (len_of TYPE ('a)) (uint w)"

definition word_reverse :: "'a :: len0 word => 'a word" where
  "word_reverse w = of_bl (rev (to_bl w))"

definition word_int_case :: "(int => 'b) => ('a :: len0 word) => 'b" where
  "word_int_case f w = f (uint w)"

syntax
  of_int :: "int => 'a"
translations
  "case x of CONST of_int y => b" == "CONST word_int_case (%y. b) x"

subsection {* Type-definition locale instantiations *}

lemma word_size_gt_0 [iff]: "0 < size (w::'a::len word)"
  by (fact xtr1 [OF word_size len_gt_0])

lemmas lens_gt_0 = word_size_gt_0 len_gt_0
lemmas lens_not_0 [iff] = lens_gt_0 [THEN gr_implies_not0]

lemma uints_num: "uints n = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (simp add: uints_def range_bintrunc)

lemma sints_num: "sints n = {i. - (2 ^ (n - 1)) \<le> i \<and> i < 2 ^ (n - 1)}"
  by (simp add: sints_def range_sbintrunc)

lemma mod_in_reps: "m > 0 \<Longrightarrow> y mod m : {0::int ..< m}"
  by auto

lemma 
  uint_0:"0 <= uint x" and 
  uint_lt: "uint (x::'a::len0 word) < 2 ^ len_of TYPE('a)"
  by (auto simp: uint [simplified])

lemma uint_mod_same:
  "uint x mod 2 ^ len_of TYPE('a) = uint (x::'a::len0 word)"
  by (simp add: int_mod_eq uint_lt uint_0)

lemma td_ext_uint: 
  "td_ext (uint :: 'a word => int) word_of_int (uints (len_of TYPE('a::len0))) 
    (%w::int. w mod 2 ^ len_of TYPE('a))"
  apply (unfold td_ext_def')
  apply (simp add: uints_num word_of_int_def bintrunc_mod2p)
  apply (simp add: uint_mod_same uint_0 uint_lt
                   word.uint_inverse word.Abs_word_inverse int_mod_lem)
  done

lemma int_word_uint:
  "uint (word_of_int x::'a::len0 word) = x mod 2 ^ len_of TYPE('a)"
  by (fact td_ext_uint [THEN td_ext.eq_norm])

interpretation word_uint:
  td_ext "uint::'a::len0 word \<Rightarrow> int" 
         word_of_int 
         "uints (len_of TYPE('a::len0))"
         "\<lambda>w. w mod 2 ^ len_of TYPE('a::len0)"
  by (rule td_ext_uint)
  
lemmas td_uint = word_uint.td_thm

lemmas td_ext_ubin = td_ext_uint 
  [simplified len_gt_0 no_bintr_alt1 [symmetric]]

interpretation word_ubin:
  td_ext "uint::'a::len0 word \<Rightarrow> int" 
         word_of_int 
         "uints (len_of TYPE('a::len0))"
         "bintrunc (len_of TYPE('a::len0))"
  by (rule td_ext_ubin)

lemma split_word_all:
  "(\<And>x::'a::len0 word. PROP P x) \<equiv> (\<And>x. PROP P (word_of_int x))"
proof
  fix x :: "'a word"
  assume "\<And>x. PROP P (word_of_int x)"
  hence "PROP P (word_of_int (uint x))" .
  thus "PROP P x" by simp
qed

subsection  "Arithmetic operations"

definition
  word_succ :: "'a :: len0 word => 'a word"
where
  "word_succ a = word_of_int (Int.succ (uint a))"

definition
  word_pred :: "'a :: len0 word => 'a word"
where
  "word_pred a = word_of_int (Int.pred (uint a))"

instantiation word :: (len0) "{number, Divides.div, comm_monoid_mult, comm_ring}"
begin

definition
  word_0_wi: "0 = word_of_int 0"

definition
  word_1_wi: "1 = word_of_int 1"

definition
  word_add_def: "a + b = word_of_int (uint a + uint b)"

definition
  word_sub_wi: "a - b = word_of_int (uint a - uint b)"

definition
  word_minus_def: "- a = word_of_int (- uint a)"

definition
  word_mult_def: "a * b = word_of_int (uint a * uint b)"

definition
  word_div_def: "a div b = word_of_int (uint a div uint b)"

definition
  word_mod_def: "a mod b = word_of_int (uint a mod uint b)"

definition
  word_number_of_def: "number_of w = word_of_int w"

lemmas word_arith_wis = 
  word_add_def word_mult_def word_minus_def 
  word_succ_def word_pred_def word_0_wi word_1_wi

lemmas arths = 
  bintr_ariths [THEN word_ubin.norm_eq_iff [THEN iffD1], folded word_ubin.eq_norm]

lemma wi_homs: 
  shows
  wi_hom_add: "word_of_int a + word_of_int b = word_of_int (a + b)" and
  wi_hom_mult: "word_of_int a * word_of_int b = word_of_int (a * b)" and
  wi_hom_neg: "- word_of_int a = word_of_int (- a)" and
  wi_hom_succ: "word_succ (word_of_int a) = word_of_int (Int.succ a)" and
  wi_hom_pred: "word_pred (word_of_int a) = word_of_int (Int.pred a)"
  by (auto simp: word_arith_wis arths)

lemmas wi_hom_syms = wi_homs [symmetric]

lemma word_sub_def: "a - b = a + - (b :: 'a :: len0 word)"
  unfolding word_sub_wi diff_minus
  by (simp only : word_uint.Rep_inverse wi_hom_syms)

lemma word_of_int_sub_hom:
  "(word_of_int a) - word_of_int b = word_of_int (a - b)"
  by (simp add: word_sub_wi arths)

lemmas new_word_of_int_homs = 
  word_of_int_sub_hom wi_homs word_0_wi word_1_wi 

lemmas new_word_of_int_hom_syms = new_word_of_int_homs [symmetric]

lemmas word_of_int_hom_syms =
  new_word_of_int_hom_syms [unfolded succ_def pred_def]

lemmas word_of_int_homs =
  new_word_of_int_homs [unfolded succ_def pred_def]

(* FIXME: provide only one copy of these theorems! *)
lemmas word_of_int_add_hom = wi_hom_add
lemmas word_of_int_mult_hom = wi_hom_mult
lemmas word_of_int_minus_hom = wi_hom_neg
lemmas word_of_int_succ_hom = wi_hom_succ [unfolded succ_def]
lemmas word_of_int_pred_hom = wi_hom_pred [unfolded pred_def]
lemmas word_of_int_0_hom = word_0_wi
lemmas word_of_int_1_hom = word_1_wi

instance
  by default (auto simp: split_word_all word_of_int_homs algebra_simps)

end

lemma word_zero_neq_one: "0 < len_of TYPE ('a :: len0) \<Longrightarrow> (0 :: 'a word) ~= 1"
  unfolding word_arith_wis
  by (auto simp add: word_ubin.norm_eq_iff [symmetric] gr0_conv_Suc)

lemmas lenw1_zero_neq_one = len_gt_0 [THEN word_zero_neq_one]

instance word :: (len) comm_ring_1
  by (intro_classes) (simp add: lenw1_zero_neq_one)

lemma word_of_nat: "of_nat n = word_of_int (int n)"
  by (induct n) (auto simp add : word_of_int_hom_syms)

lemma word_of_int: "of_int = word_of_int"
  apply (rule ext)
  apply (case_tac x rule: int_diff_cases)
  apply (simp add: word_of_nat word_of_int_sub_hom)
  done

lemma word_number_of_eq: 
  "number_of w = (of_int w :: 'a :: len word)"
  unfolding word_number_of_def word_of_int by auto

instance word :: (len) number_ring
  by (intro_classes) (simp add : word_number_of_eq)

definition udvd :: "'a::len word => 'a::len word => bool" (infixl "udvd" 50) where
  "a udvd b = (EX n>=0. uint b = n * uint a)"


subsection "Ordering"

instantiation word :: (len0) linorder
begin

definition
  word_le_def: "a \<le> b \<longleftrightarrow> uint a \<le> uint b"

definition
  word_less_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> (y \<Colon> 'a word)"

instance
  by default (auto simp: word_less_def word_le_def)

end

definition word_sle :: "'a :: len word => 'a word => bool" ("(_/ <=s _)" [50, 51] 50) where
  "a <=s b = (sint a <= sint b)"

definition word_sless :: "'a :: len word => 'a word => bool" ("(_/ <s _)" [50, 51] 50) where
  "(x <s y) = (x <=s y & x ~= y)"


subsection "Bit-wise operations"

instantiation word :: (len0) bits
begin

definition
  word_and_def: 
  "(a::'a word) AND b = word_of_int (uint a AND uint b)"

definition
  word_or_def:  
  "(a::'a word) OR b = word_of_int (uint a OR uint b)"

definition
  word_xor_def: 
  "(a::'a word) XOR b = word_of_int (uint a XOR uint b)"

definition
  word_not_def: 
  "NOT (a::'a word) = word_of_int (NOT (uint a))"

definition
  word_test_bit_def: "test_bit a = bin_nth (uint a)"

definition
  word_set_bit_def: "set_bit a n x =
   word_of_int (bin_sc n (If x 1 0) (uint a))"

definition
  word_set_bits_def: "(BITS n. f n) = of_bl (bl_of_nth (len_of TYPE ('a)) f)"

definition
  word_lsb_def: "lsb a \<longleftrightarrow> bin_last (uint a) = 1"

definition shiftl1 :: "'a word \<Rightarrow> 'a word" where
  "shiftl1 w = word_of_int (uint w BIT 0)"

definition shiftr1 :: "'a word \<Rightarrow> 'a word" where
  -- "shift right as unsigned or as signed, ie logical or arithmetic"
  "shiftr1 w = word_of_int (bin_rest (uint w))"

definition
  shiftl_def: "w << n = (shiftl1 ^^ n) w"

definition
  shiftr_def: "w >> n = (shiftr1 ^^ n) w"

instance ..

end

instantiation word :: (len) bitss
begin

definition
  word_msb_def: 
  "msb a \<longleftrightarrow> bin_sign (sint a) = Int.Min"

instance ..

end

lemma [code]:
  "msb a \<longleftrightarrow> bin_sign (sint a) = (- 1 :: int)"
  by (simp only: word_msb_def Min_def)

definition setBit :: "'a :: len0 word => nat => 'a word" where 
  "setBit w n = set_bit w n True"

definition clearBit :: "'a :: len0 word => nat => 'a word" where
  "clearBit w n = set_bit w n False"


subsection "Shift operations"

definition sshiftr1 :: "'a :: len word => 'a word" where 
  "sshiftr1 w = word_of_int (bin_rest (sint w))"

definition bshiftr1 :: "bool => 'a :: len word => 'a word" where
  "bshiftr1 b w = of_bl (b # butlast (to_bl w))"

definition sshiftr :: "'a :: len word => nat => 'a word" (infixl ">>>" 55) where
  "w >>> n = (sshiftr1 ^^ n) w"

definition mask :: "nat => 'a::len word" where
  "mask n = (1 << n) - 1"

definition revcast :: "'a :: len0 word => 'b :: len0 word" where
  "revcast w =  of_bl (takefill False (len_of TYPE('b)) (to_bl w))"

definition slice1 :: "nat => 'a :: len0 word => 'b :: len0 word" where
  "slice1 n w = of_bl (takefill False n (to_bl w))"

definition slice :: "nat => 'a :: len0 word => 'b :: len0 word" where
  "slice n w = slice1 (size w - n) w"


subsection "Rotation"

definition rotater1 :: "'a list => 'a list" where
  "rotater1 ys = 
    (case ys of [] => [] | x # xs => last ys # butlast ys)"

definition rotater :: "nat => 'a list => 'a list" where
  "rotater n = rotater1 ^^ n"

definition word_rotr :: "nat => 'a :: len0 word => 'a :: len0 word" where
  "word_rotr n w = of_bl (rotater n (to_bl w))"

definition word_rotl :: "nat => 'a :: len0 word => 'a :: len0 word" where
  "word_rotl n w = of_bl (rotate n (to_bl w))"

definition word_roti :: "int => 'a :: len0 word => 'a :: len0 word" where
  "word_roti i w = (if i >= 0 then word_rotr (nat i) w
                    else word_rotl (nat (- i)) w)"


subsection "Split and cat operations"

definition word_cat :: "'a :: len0 word => 'b :: len0 word => 'c :: len0 word" where
  "word_cat a b = word_of_int (bin_cat (uint a) (len_of TYPE ('b)) (uint b))"

definition word_split :: "'a :: len0 word => ('b :: len0 word) * ('c :: len0 word)" where
  "word_split a = 
   (case bin_split (len_of TYPE ('c)) (uint a) of 
     (u, v) => (word_of_int u, word_of_int v))"

definition word_rcat :: "'a :: len0 word list => 'b :: len0 word" where
  "word_rcat ws = 
  word_of_int (bin_rcat (len_of TYPE ('a)) (map uint ws))"

definition word_rsplit :: "'a :: len0 word => 'b :: len word list" where
  "word_rsplit w = 
  map word_of_int (bin_rsplit (len_of TYPE ('b)) (len_of TYPE ('a), uint w))"

definition max_word :: "'a::len word" -- "Largest representable machine integer." where
  "max_word = word_of_int (2 ^ len_of TYPE('a) - 1)"

primrec of_bool :: "bool \<Rightarrow> 'a::len word" where
  "of_bool False = 0"
| "of_bool True = 1"

(* FIXME: only provide one theorem name *)
lemmas of_nth_def = word_set_bits_def

lemma sint_sbintrunc': 
  "sint (word_of_int bin :: 'a word) = 
    (sbintrunc (len_of TYPE ('a :: len) - 1) bin)"
  unfolding sint_uint 
  by (auto simp: word_ubin.eq_norm sbintrunc_bintrunc_lt)

lemma uint_sint: 
  "uint w = bintrunc (len_of TYPE('a)) (sint (w :: 'a :: len word))"
  unfolding sint_uint by (auto simp: bintrunc_sbintrunc_le)

lemma bintr_uint': 
  "n >= size w \<Longrightarrow> bintrunc n (uint w) = uint w"
  apply (unfold word_size)
  apply (subst word_ubin.norm_Rep [symmetric]) 
  apply (simp only: bintrunc_bintrunc_min word_size)
  apply (simp add: min_max.inf_absorb2)
  done

lemma wi_bintr': 
  "wb = word_of_int bin \<Longrightarrow> n >= size wb \<Longrightarrow> 
    word_of_int (bintrunc n bin) = wb"
  unfolding word_size
  by (clarsimp simp add: word_ubin.norm_eq_iff [symmetric] min_max.inf_absorb1)

lemmas bintr_uint = bintr_uint' [unfolded word_size]
lemmas wi_bintr = wi_bintr' [unfolded word_size]

lemma td_ext_sbin: 
  "td_ext (sint :: 'a word => int) word_of_int (sints (len_of TYPE('a::len))) 
    (sbintrunc (len_of TYPE('a) - 1))"
  apply (unfold td_ext_def' sint_uint)
  apply (simp add : word_ubin.eq_norm)
  apply (cases "len_of TYPE('a)")
   apply (auto simp add : sints_def)
  apply (rule sym [THEN trans])
  apply (rule word_ubin.Abs_norm)
  apply (simp only: bintrunc_sbintrunc)
  apply (drule sym)
  apply simp
  done

lemmas td_ext_sint = td_ext_sbin 
  [simplified len_gt_0 no_sbintr_alt2 Suc_pred' [symmetric]]

(* We do sint before sbin, before sint is the user version
   and interpretations do not produce thm duplicates. I.e. 
   we get the name word_sint.Rep_eqD, but not word_sbin.Req_eqD,
   because the latter is the same thm as the former *)
interpretation word_sint:
  td_ext "sint ::'a::len word => int" 
          word_of_int 
          "sints (len_of TYPE('a::len))"
          "%w. (w + 2^(len_of TYPE('a::len) - 1)) mod 2^len_of TYPE('a::len) -
               2 ^ (len_of TYPE('a::len) - 1)"
  by (rule td_ext_sint)

interpretation word_sbin:
  td_ext "sint ::'a::len word => int" 
          word_of_int 
          "sints (len_of TYPE('a::len))"
          "sbintrunc (len_of TYPE('a::len) - 1)"
  by (rule td_ext_sbin)

lemmas int_word_sint = td_ext_sint [THEN td_ext.eq_norm]

lemmas td_sint = word_sint.td

lemma word_number_of_alt [code_unfold_post]:
  "number_of b = word_of_int (number_of b)"
  by (simp add: number_of_eq word_number_of_def)

lemma word_no_wi: "number_of = word_of_int"
  by (auto simp: word_number_of_def)

lemma to_bl_def': 
  "(to_bl :: 'a :: len0 word => bool list) =
    bin_to_bl (len_of TYPE('a)) o uint"
  by (auto simp: to_bl_def)

lemmas word_reverse_no_def [simp] = word_reverse_def [of "number_of w"] for w

lemma uints_mod: "uints n = range (\<lambda>w. w mod 2 ^ n)"
  by (fact uints_def [unfolded no_bintr_alt1])

lemma uint_bintrunc [simp]:
  "uint (number_of bin :: 'a word) =
    number_of (bintrunc (len_of TYPE ('a :: len0)) bin)"
  unfolding word_number_of_def number_of_eq
  by (auto intro: word_ubin.eq_norm) 

lemma sint_sbintrunc [simp]:
  "sint (number_of bin :: 'a word) =
    number_of (sbintrunc (len_of TYPE ('a :: len) - 1) bin)" 
  unfolding word_number_of_def number_of_eq
  by (subst word_sbin.eq_norm) simp

lemma unat_bintrunc [simp]:
  "unat (number_of bin :: 'a :: len0 word) =
    number_of (bintrunc (len_of TYPE('a)) bin)"
  unfolding unat_def nat_number_of_def 
  by (simp only: uint_bintrunc)

lemma size_0_eq: "size (w :: 'a :: len0 word) = 0 \<Longrightarrow> v = w"
  apply (unfold word_size)
  apply (rule word_uint.Rep_eqD)
  apply (rule box_equals)
    defer
    apply (rule word_ubin.norm_Rep)+
  apply simp
  done

lemma uint_ge_0 [iff]: "0 \<le> uint (x::'a::len0 word)"
  using word_uint.Rep [of x] by (simp add: uints_num)

lemma uint_lt2p [iff]: "uint (x::'a::len0 word) < 2 ^ len_of TYPE('a)"
  using word_uint.Rep [of x] by (simp add: uints_num)

lemma sint_ge: "- (2 ^ (len_of TYPE('a) - 1)) \<le> sint (x::'a::len word)"
  using word_sint.Rep [of x] by (simp add: sints_num)

lemma sint_lt: "sint (x::'a::len word) < 2 ^ (len_of TYPE('a) - 1)"
  using word_sint.Rep [of x] by (simp add: sints_num)

lemma sign_uint_Pls [simp]: 
  "bin_sign (uint x) = Int.Pls"
  by (simp add: sign_Pls_ge_0 number_of_eq)

lemma uint_m2p_neg: "uint (x::'a::len0 word) - 2 ^ len_of TYPE('a) < 0"
  by (simp only: diff_less_0_iff_less uint_lt2p)

lemma uint_m2p_not_non_neg:
  "\<not> 0 \<le> uint (x::'a::len0 word) - 2 ^ len_of TYPE('a)"
  by (simp only: not_le uint_m2p_neg)

lemma lt2p_lem:
  "len_of TYPE('a) <= n \<Longrightarrow> uint (w :: 'a :: len0 word) < 2 ^ n"
  by (rule xtr8 [OF _ uint_lt2p]) simp

lemma uint_le_0_iff [simp]: "uint x \<le> 0 \<longleftrightarrow> uint x = 0"
  by (fact uint_ge_0 [THEN leD, THEN linorder_antisym_conv1])

lemma uint_nat: "uint w = int (unat w)"
  unfolding unat_def by auto

lemma uint_number_of:
  "uint (number_of b :: 'a :: len0 word) = number_of b mod 2 ^ len_of TYPE('a)"
  unfolding word_number_of_alt
  by (simp only: int_word_uint)

lemma unat_number_of: 
  "bin_sign b = Int.Pls \<Longrightarrow> 
  unat (number_of b::'a::len0 word) = number_of b mod 2 ^ len_of TYPE ('a)"
  apply (unfold unat_def)
  apply (clarsimp simp only: uint_number_of)
  apply (rule nat_mod_distrib [THEN trans])
    apply (erule sign_Pls_ge_0 [THEN iffD1])
   apply (simp_all add: nat_power_eq)
  done

lemma sint_number_of: "sint (number_of b :: 'a :: len word) = (number_of b + 
    2 ^ (len_of TYPE('a) - 1)) mod 2 ^ len_of TYPE('a) -
    2 ^ (len_of TYPE('a) - 1)"
  unfolding word_number_of_alt by (rule int_word_sint)

lemma word_of_int_bin [simp] : 
  "(word_of_int (number_of bin) :: 'a :: len0 word) = (number_of bin)"
  unfolding word_number_of_alt by auto

lemma word_int_case_wi: 
  "word_int_case f (word_of_int i :: 'b word) = 
    f (i mod 2 ^ len_of TYPE('b::len0))"
  unfolding word_int_case_def by (simp add: word_uint.eq_norm)

lemma word_int_split: 
  "P (word_int_case f x) = 
    (ALL i. x = (word_of_int i :: 'b :: len0 word) & 
      0 <= i & i < 2 ^ len_of TYPE('b) --> P (f i))"
  unfolding word_int_case_def
  by (auto simp: word_uint.eq_norm int_mod_eq')

lemma word_int_split_asm: 
  "P (word_int_case f x) = 
    (~ (EX n. x = (word_of_int n :: 'b::len0 word) &
      0 <= n & n < 2 ^ len_of TYPE('b::len0) & ~ P (f n)))"
  unfolding word_int_case_def
  by (auto simp: word_uint.eq_norm int_mod_eq')

lemmas uint_range' = word_uint.Rep [unfolded uints_num mem_Collect_eq]
lemmas sint_range' = word_sint.Rep [unfolded One_nat_def sints_num mem_Collect_eq]

lemma uint_range_size: "0 <= uint w & uint w < 2 ^ size w"
  unfolding word_size by (rule uint_range')

lemma sint_range_size:
  "- (2 ^ (size w - Suc 0)) <= sint w & sint w < 2 ^ (size w - Suc 0)"
  unfolding word_size by (rule sint_range')

lemma sint_above_size: "2 ^ (size (w::'a::len word) - 1) \<le> x \<Longrightarrow> sint w < x"
  unfolding word_size by (rule less_le_trans [OF sint_lt])

lemma sint_below_size:
  "x \<le> - (2 ^ (size (w::'a::len word) - 1)) \<Longrightarrow> x \<le> sint w"
  unfolding word_size by (rule order_trans [OF _ sint_ge])

lemma test_bit_eq_iff: "(test_bit (u::'a::len0 word) = test_bit v) = (u = v)"
  unfolding word_test_bit_def by (simp add: bin_nth_eq_iff)

lemma test_bit_size [rule_format] : "(w::'a::len0 word) !! n --> n < size w"
  apply (unfold word_test_bit_def)
  apply (subst word_ubin.norm_Rep [symmetric])
  apply (simp only: nth_bintr word_size)
  apply fast
  done

lemma word_eqI [rule_format] : 
  fixes u :: "'a::len0 word"
  shows "(ALL n. n < size u --> u !! n = v !! n) \<Longrightarrow> u = v"
  apply (rule test_bit_eq_iff [THEN iffD1])
  apply (rule ext)
  apply (erule allE)
  apply (erule impCE)
   prefer 2
   apply assumption
  apply (auto dest!: test_bit_size simp add: word_size)
  done

lemma word_eqD: "(u::'a::len0 word) = v \<Longrightarrow> u !! x = v !! x"
  by simp

lemma test_bit_bin': "w !! n = (n < size w & bin_nth (uint w) n)"
  unfolding word_test_bit_def word_size
  by (simp add: nth_bintr [symmetric])

lemmas test_bit_bin = test_bit_bin' [unfolded word_size]

lemma bin_nth_uint_imp': "bin_nth (uint w) n --> n < size w"
  apply (unfold word_size)
  apply (rule impI)
  apply (rule nth_bintr [THEN iffD1, THEN conjunct1])
  apply (subst word_ubin.norm_Rep)
  apply assumption
  done

lemma bin_nth_sint': 
  "n >= size w --> bin_nth (sint w) n = bin_nth (sint w) (size w - 1)"
  apply (rule impI)
  apply (subst word_sbin.norm_Rep [symmetric])
  apply (simp add : nth_sbintr word_size)
  apply auto
  done

lemmas bin_nth_uint_imp = bin_nth_uint_imp' [rule_format, unfolded word_size]
lemmas bin_nth_sint = bin_nth_sint' [rule_format, unfolded word_size]

(* type definitions theorem for in terms of equivalent bool list *)
lemma td_bl: 
  "type_definition (to_bl :: 'a::len0 word => bool list) 
                   of_bl  
                   {bl. length bl = len_of TYPE('a)}"
  apply (unfold type_definition_def of_bl_def to_bl_def)
  apply (simp add: word_ubin.eq_norm)
  apply safe
  apply (drule sym)
  apply simp
  done

interpretation word_bl:
  type_definition "to_bl :: 'a::len0 word => bool list"
                  of_bl  
                  "{bl. length bl = len_of TYPE('a::len0)}"
  by (rule td_bl)

lemmas word_bl_Rep' = word_bl.Rep [simplified, iff]

lemma word_size_bl: "size w = size (to_bl w)"
  unfolding word_size by auto

lemma to_bl_use_of_bl:
  "(to_bl w = bl) = (w = of_bl bl \<and> length bl = length (to_bl w))"
  by (fastforce elim!: word_bl.Abs_inverse [simplified])

lemma to_bl_word_rev: "to_bl (word_reverse w) = rev (to_bl w)"
  unfolding word_reverse_def by (simp add: word_bl.Abs_inverse)

lemma word_rev_rev [simp] : "word_reverse (word_reverse w) = w"
  unfolding word_reverse_def by (simp add : word_bl.Abs_inverse)

lemma word_rev_gal: "word_reverse w = u \<Longrightarrow> word_reverse u = w"
  by auto

lemma word_rev_gal': "u = word_reverse w \<Longrightarrow> w = word_reverse u"
  by simp

lemma length_bl_gt_0 [iff]: "0 < length (to_bl (x::'a::len word))"
  unfolding word_bl_Rep' by (rule len_gt_0)

lemma bl_not_Nil [iff]: "to_bl (x::'a::len word) \<noteq> []"
  by (fact length_bl_gt_0 [unfolded length_greater_0_conv])

lemma length_bl_neq_0 [iff]: "length (to_bl (x::'a::len word)) \<noteq> 0"
  by (fact length_bl_gt_0 [THEN gr_implies_not0])

lemma hd_bl_sign_sint: "hd (to_bl w) = (bin_sign (sint w) = Int.Min)"
  apply (unfold to_bl_def sint_uint)
  apply (rule trans [OF _ bl_sbin_sign])
  apply simp
  done

lemma of_bl_drop': 
  "lend = length bl - len_of TYPE ('a :: len0) \<Longrightarrow> 
    of_bl (drop lend bl) = (of_bl bl :: 'a word)"
  apply (unfold of_bl_def)
  apply (clarsimp simp add : trunc_bl2bin [symmetric])
  done

lemma of_bl_no: "of_bl bl = number_of (bl_to_bin bl)"
  by (fact of_bl_def [folded word_number_of_def])

lemma test_bit_of_bl:  
  "(of_bl bl::'a::len0 word) !! n = (rev bl ! n \<and> n < len_of TYPE('a) \<and> n < length bl)"
  apply (unfold of_bl_def word_test_bit_def)
  apply (auto simp add: word_size word_ubin.eq_norm nth_bintr bin_nth_of_bl)
  done

lemma no_of_bl: 
  "(number_of bin ::'a::len0 word) = of_bl (bin_to_bl (len_of TYPE ('a)) bin)"
  unfolding word_size of_bl_no by (simp add : word_number_of_def)

lemma uint_bl: "to_bl w = bin_to_bl (size w) (uint w)"
  unfolding word_size to_bl_def by auto

lemma to_bl_bin: "bl_to_bin (to_bl w) = uint w"
  unfolding uint_bl by (simp add : word_size)

lemma to_bl_of_bin: 
  "to_bl (word_of_int bin::'a::len0 word) = bin_to_bl (len_of TYPE('a)) bin"
  unfolding uint_bl by (clarsimp simp add: word_ubin.eq_norm word_size)

lemma to_bl_no_bin [simp]:
  "to_bl (number_of bin::'a::len0 word) = bin_to_bl (len_of TYPE('a)) bin"
  by (fact to_bl_of_bin [folded word_number_of_def])

lemma to_bl_to_bin [simp] : "bl_to_bin (to_bl w) = uint w"
  unfolding uint_bl by (simp add : word_size)
  
lemmas uint_bl_bin [simp] = trans [OF bin_bl_bin word_ubin.norm_Rep]

(* FIXME: the next two lemmas should be unnecessary, because the lhs
terms should never occur in practice *)
lemma num_AB_u [simp]: "number_of (uint x) = x"
  unfolding word_number_of_def by (rule word_uint.Rep_inverse)

lemma num_AB_s [simp]: "number_of (sint x) = x"
  unfolding word_number_of_def by (rule word_sint.Rep_inverse)

(* naturals *)
lemma uints_unats: "uints n = int ` unats n"
  apply (unfold unats_def uints_num)
  apply safe
  apply (rule_tac image_eqI)
  apply (erule_tac nat_0_le [symmetric])
  apply auto
  apply (erule_tac nat_less_iff [THEN iffD2])
  apply (rule_tac [2] zless_nat_eq_int_zless [THEN iffD1])
  apply (auto simp add : nat_power_eq int_power)
  done

lemma unats_uints: "unats n = nat ` uints n"
  by (auto simp add : uints_unats image_iff)

lemmas bintr_num = word_ubin.norm_eq_iff [symmetric, folded word_number_of_def]
lemmas sbintr_num = word_sbin.norm_eq_iff [symmetric, folded word_number_of_def]

lemmas num_of_bintr = word_ubin.Abs_norm [folded word_number_of_def]
lemmas num_of_sbintr = word_sbin.Abs_norm [folded word_number_of_def]
    
(* don't add these to simpset, since may want bintrunc n w to be simplified;
  may want these in reverse, but loop as simp rules, so use following *)

lemma num_of_bintr':
  "bintrunc (len_of TYPE('a :: len0)) a = b \<Longrightarrow> 
    number_of a = (number_of b :: 'a word)"
  apply safe
  apply (rule_tac num_of_bintr [symmetric])
  done

lemma num_of_sbintr':
  "sbintrunc (len_of TYPE('a :: len) - 1) a = b \<Longrightarrow> 
    number_of a = (number_of b :: 'a word)"
  apply safe
  apply (rule_tac num_of_sbintr [symmetric])
  done

lemmas num_abs_bintr = sym [THEN trans, OF num_of_bintr word_number_of_def]
lemmas num_abs_sbintr = sym [THEN trans, OF num_of_sbintr word_number_of_def]
  
(** cast - note, no arg for new length, as it's determined by type of result,
  thus in "cast w = w, the type means cast to length of w! **)

lemma ucast_id: "ucast w = w"
  unfolding ucast_def by auto

lemma scast_id: "scast w = w"
  unfolding scast_def by auto

lemma ucast_bl: "ucast w = of_bl (to_bl w)"
  unfolding ucast_def of_bl_def uint_bl
  by (auto simp add : word_size)

lemma nth_ucast: 
  "(ucast w::'a::len0 word) !! n = (w !! n & n < len_of TYPE('a))"
  apply (unfold ucast_def test_bit_bin)
  apply (simp add: word_ubin.eq_norm nth_bintr word_size) 
  apply (fast elim!: bin_nth_uint_imp)
  done

(* for literal u(s)cast *)

lemma ucast_bintr [simp]: 
  "ucast (number_of w ::'a::len0 word) = 
   number_of (bintrunc (len_of TYPE('a)) w)"
  unfolding ucast_def by simp

lemma scast_sbintr [simp]: 
  "scast (number_of w ::'a::len word) = 
   number_of (sbintrunc (len_of TYPE('a) - Suc 0) w)"
  unfolding scast_def by simp

lemmas source_size = source_size_def [unfolded Let_def word_size]
lemmas target_size = target_size_def [unfolded Let_def word_size]
lemmas is_down = is_down_def [unfolded source_size target_size]
lemmas is_up = is_up_def [unfolded source_size target_size]

lemmas is_up_down = trans [OF is_up is_down [symmetric]]

lemma down_cast_same': "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc = scast"
  apply (unfold is_down)
  apply safe
  apply (rule ext)
  apply (unfold ucast_def scast_def uint_sint)
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply simp
  done

lemma word_rev_tf': 
  "r = to_bl (of_bl bl) \<Longrightarrow> r = rev (takefill False (length r) (rev bl))"
  unfolding of_bl_def uint_bl
  by (clarsimp simp add: bl_bin_bl_rtf word_ubin.eq_norm word_size)

lemmas word_rev_tf = refl [THEN word_rev_tf', unfolded word_bl_Rep']

lemmas word_rep_drop = word_rev_tf [simplified takefill_alt,
  simplified, simplified rev_take, simplified]

lemma to_bl_ucast: 
  "to_bl (ucast (w::'b::len0 word) ::'a::len0 word) = 
   replicate (len_of TYPE('a) - len_of TYPE('b)) False @
   drop (len_of TYPE('b) - len_of TYPE('a)) (to_bl w)"
  apply (unfold ucast_bl)
  apply (rule trans)
   apply (rule word_rep_drop)
  apply simp
  done

lemma ucast_up_app': 
  "uc = ucast \<Longrightarrow> source_size uc + n = target_size uc \<Longrightarrow> 
    to_bl (uc w) = replicate n False @ (to_bl w)"
  by (auto simp add : source_size target_size to_bl_ucast)

lemma ucast_down_drop': 
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> 
    to_bl (uc w) = drop n (to_bl w)"
  by (auto simp add : source_size target_size to_bl_ucast)

lemma scast_down_drop': 
  "sc = scast \<Longrightarrow> source_size sc = target_size sc + n \<Longrightarrow> 
    to_bl (sc w) = drop n (to_bl w)"
  apply (subgoal_tac "sc = ucast")
   apply safe
   apply simp
   apply (erule refl [THEN ucast_down_drop'])
  apply (rule refl [THEN down_cast_same', symmetric])
  apply (simp add : source_size target_size is_down)
  done

lemma sint_up_scast': 
  "sc = scast \<Longrightarrow> is_up sc \<Longrightarrow> sint (sc w) = sint w"
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

lemma uint_up_ucast':
  "uc = ucast \<Longrightarrow> is_up uc \<Longrightarrow> uint (uc w) = uint w"
  apply (unfold is_up)
  apply safe
  apply (rule bin_eqI)
  apply (fold word_test_bit_def)
  apply (auto simp add: nth_ucast)
  apply (auto simp add: test_bit_bin)
  done
    
lemmas down_cast_same = refl [THEN down_cast_same']
lemmas ucast_up_app = refl [THEN ucast_up_app']
lemmas ucast_down_drop = refl [THEN ucast_down_drop']
lemmas scast_down_drop = refl [THEN scast_down_drop']
lemmas uint_up_ucast = refl [THEN uint_up_ucast']
lemmas sint_up_scast = refl [THEN sint_up_scast']

lemma ucast_up_ucast': "uc = ucast \<Longrightarrow> is_up uc \<Longrightarrow> ucast (uc w) = ucast w"
  apply (simp (no_asm) add: ucast_def)
  apply (clarsimp simp add: uint_up_ucast)
  done
    
lemma scast_up_scast': "sc = scast \<Longrightarrow> is_up sc \<Longrightarrow> scast (sc w) = scast w"
  apply (simp (no_asm) add: scast_def)
  apply (clarsimp simp add: sint_up_scast)
  done
    
lemma ucast_of_bl_up': 
  "w = of_bl bl \<Longrightarrow> size bl <= size w \<Longrightarrow> ucast w = of_bl bl"
  by (auto simp add : nth_ucast word_size test_bit_of_bl intro!: word_eqI)

lemmas ucast_up_ucast = refl [THEN ucast_up_ucast']
lemmas scast_up_scast = refl [THEN scast_up_scast']
lemmas ucast_of_bl_up = refl [THEN ucast_of_bl_up']

lemmas ucast_up_ucast_id = trans [OF ucast_up_ucast ucast_id]
lemmas scast_up_scast_id = trans [OF scast_up_scast scast_id]

lemmas isduu = is_up_down [where c = "ucast", THEN iffD2]
lemmas isdus = is_up_down [where c = "scast", THEN iffD2]
lemmas ucast_down_ucast_id = isduu [THEN ucast_up_ucast_id]
lemmas scast_down_scast_id = isdus [THEN ucast_up_ucast_id]

lemma up_ucast_surj:
  "is_up (ucast :: 'b::len0 word => 'a::len0 word) \<Longrightarrow> 
   surj (ucast :: 'a word => 'b word)"
  by (rule surjI, erule ucast_up_ucast_id)

lemma up_scast_surj:
  "is_up (scast :: 'b::len word => 'a::len word) \<Longrightarrow> 
   surj (scast :: 'a word => 'b word)"
  by (rule surjI, erule scast_up_scast_id)

lemma down_scast_inj:
  "is_down (scast :: 'b::len word => 'a::len word) \<Longrightarrow> 
   inj_on (ucast :: 'a word => 'b word) A"
  by (rule inj_on_inverseI, erule scast_down_scast_id)

lemma down_ucast_inj:
  "is_down (ucast :: 'b::len0 word => 'a::len0 word) \<Longrightarrow> 
   inj_on (ucast :: 'a word => 'b word) A"
  by (rule inj_on_inverseI, erule ucast_down_ucast_id)

lemma of_bl_append_same: "of_bl (X @ to_bl w) = w"
  by (rule word_bl.Rep_eqD) (simp add: word_rep_drop)
  
lemma ucast_down_no': 
  "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc (number_of bin) = number_of bin"
  apply (unfold word_number_of_def is_down)
  apply (clarsimp simp add: ucast_def word_ubin.eq_norm)
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply (erule bintrunc_bintrunc_ge)
  done
    
lemmas ucast_down_no = ucast_down_no' [OF refl]

lemma ucast_down_bl': "uc = ucast \<Longrightarrow> is_down uc \<Longrightarrow> uc (of_bl bl) = of_bl bl"
  unfolding of_bl_no by clarify (erule ucast_down_no)
    
lemmas ucast_down_bl = ucast_down_bl' [OF refl]

lemmas slice_def' = slice_def [unfolded word_size]
lemmas test_bit_def' = word_test_bit_def [THEN fun_cong]

lemmas word_log_defs = word_and_def word_or_def word_xor_def word_not_def
lemmas word_log_bin_defs = word_log_defs

text {* Executable equality *}

instantiation word :: (len0) equal
begin

definition equal_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "equal_word k l \<longleftrightarrow> HOL.equal (uint k) (uint l)"

instance proof
qed (simp add: equal equal_word_def)

end


subsection {* Word Arithmetic *}

lemma word_less_alt: "(a < b) = (uint a < uint b)"
  unfolding word_less_def word_le_def
  by (auto simp del: word_uint.Rep_inject 
           simp: word_uint.Rep_inject [symmetric])

lemma signed_linorder: "class.linorder word_sle word_sless"
proof
qed (unfold word_sle_def word_sless_def, auto)

interpretation signed: linorder "word_sle" "word_sless"
  by (rule signed_linorder)

lemma udvdI: 
  "0 \<le> n \<Longrightarrow> uint b = n * uint a \<Longrightarrow> a udvd b"
  by (auto simp: udvd_def)

lemmas word_div_no [simp] = word_div_def [of "number_of a" "number_of b"] for a b

lemmas word_mod_no [simp] = word_mod_def [of "number_of a" "number_of b"] for a b

lemmas word_less_no [simp] = word_less_def [of "number_of a" "number_of b"] for a b

lemmas word_le_no [simp] = word_le_def [of "number_of a" "number_of b"] for a b

lemmas word_sless_no [simp] = word_sless_def [of "number_of a" "number_of b"] for a b

lemmas word_sle_no [simp] = word_sle_def [of "number_of a" "number_of b"] for a b

(* following two are available in class number_ring, 
  but convenient to have them here here;
  note - the number_ring versions, numeral_0_eq_0 and numeral_1_eq_1
  are in the default simpset, so to use the automatic simplifications for
  (eg) sint (number_of bin) on sint 1, must do
  (simp add: word_1_no del: numeral_1_eq_1) 
  *)
lemmas word_0_wi_Pls = word_0_wi [folded Pls_def]
lemmas word_0_no = word_0_wi_Pls [folded word_no_wi]

lemma int_one_bin: "(1 :: int) = (Int.Pls BIT 1)"
  unfolding Pls_def Bit_def by auto

lemma word_1_no: 
  "(1 :: 'a :: len0 word) = number_of (Int.Pls BIT 1)"
  unfolding word_1_wi word_number_of_def int_one_bin by auto

lemma word_m1_wi: "-1 = word_of_int -1" 
  by (rule word_number_of_alt)

lemma word_m1_wi_Min: "-1 = word_of_int Int.Min"
  by (simp add: word_m1_wi number_of_eq)

lemma word_0_bl [simp]: "of_bl [] = 0" 
  unfolding word_0_wi of_bl_def by (simp add : Pls_def)

lemma word_1_bl: "of_bl [True] = 1" 
  unfolding word_1_wi of_bl_def
  by (simp add : bl_to_bin_def Bit_def Pls_def)

lemma uint_eq_0 [simp] : "(uint 0 = 0)" 
  unfolding word_0_wi
  by (simp add: word_ubin.eq_norm Pls_def [symmetric])

lemma of_bl_0 [simp] : "of_bl (replicate n False) = 0"
  by (simp add : word_0_wi of_bl_def bl_to_bin_rep_False Pls_def)

lemma to_bl_0 [simp]:
  "to_bl (0::'a::len0 word) = replicate (len_of TYPE('a)) False"
  unfolding uint_bl
  by (simp add : word_size bin_to_bl_Pls Pls_def [symmetric])

lemma uint_0_iff: "(uint x = 0) = (x = 0)"
  by (auto intro!: word_uint.Rep_eqD)

lemma unat_0_iff: "(unat x = 0) = (x = 0)"
  unfolding unat_def by (auto simp add : nat_eq_iff uint_0_iff)

lemma unat_0 [simp]: "unat 0 = 0"
  unfolding unat_def by auto

lemma size_0_same': "size w = 0 \<Longrightarrow> w = (v :: 'a :: len0 word)"
  apply (unfold word_size)
  apply (rule box_equals)
    defer
    apply (rule word_uint.Rep_inverse)+
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply simp
  done

lemmas size_0_same = size_0_same' [folded word_size]

lemmas unat_eq_0 = unat_0_iff
lemmas unat_eq_zero = unat_0_iff

lemma unat_gt_0: "(0 < unat x) = (x ~= 0)"
by (auto simp: unat_0_iff [symmetric])

lemma ucast_0 [simp] : "ucast 0 = 0"
unfolding ucast_def
by simp (simp add: word_0_wi)

lemma sint_0 [simp] : "sint 0 = 0"
unfolding sint_uint
by (simp add: Pls_def [symmetric])

lemma scast_0 [simp] : "scast 0 = 0"
apply (unfold scast_def)
apply simp
apply (simp add: word_0_wi)
done

lemma sint_n1 [simp] : "sint -1 = -1"
apply (unfold word_m1_wi_Min)
apply (simp add: word_sbin.eq_norm)
apply (unfold Min_def number_of_eq)
apply simp
done

lemma scast_n1 [simp] : "scast -1 = -1"
  apply (unfold scast_def sint_n1)
  apply (unfold word_number_of_alt)
  apply (rule refl)
  done

lemma uint_1 [simp] : "uint (1 :: 'a :: len word) = 1"
  unfolding word_1_wi
  by (simp add: word_ubin.eq_norm int_one_bin bintrunc_minus_simps)

lemma unat_1 [simp] : "unat (1 :: 'a :: len word) = 1"
  by (unfold unat_def uint_1) auto

lemma ucast_1 [simp] : "ucast (1 :: 'a :: len word) = 1"
  unfolding ucast_def word_1_wi
  by (simp add: word_ubin.eq_norm int_one_bin bintrunc_minus_simps)

(* now, to get the weaker results analogous to word_div/mod_def *)

lemmas word_arith_alts = 
  word_sub_wi [unfolded succ_def pred_def]
  word_arith_wis [unfolded succ_def pred_def]

lemmas word_succ_alt = word_arith_alts (5)
lemmas word_pred_alt = word_arith_alts (6)

subsection  "Transferring goals from words to ints"

lemma word_ths:  
  shows
  word_succ_p1:   "word_succ a = a + 1" and
  word_pred_m1:   "word_pred a = a - 1" and
  word_pred_succ: "word_pred (word_succ a) = a" and
  word_succ_pred: "word_succ (word_pred a) = a" and
  word_mult_succ: "word_succ a * b = b + a * b"
  by (rule word_uint.Abs_cases [of b],
      rule word_uint.Abs_cases [of a],
      simp add: pred_def succ_def add_commute mult_commute 
                ring_distribs new_word_of_int_homs)+

lemmas uint_cong = arg_cong [where f = uint]

lemmas uint_word_ariths = 
  word_arith_alts [THEN trans [OF uint_cong int_word_uint]]

lemmas uint_word_arith_bintrs = uint_word_ariths [folded bintrunc_mod2p]

(* similar expressions for sint (arith operations) *)
lemmas sint_word_ariths = uint_word_arith_bintrs
  [THEN uint_sint [symmetric, THEN trans],
  unfolded uint_sint bintr_arith1s bintr_ariths 
    len_gt_0 [THEN bin_sbin_eq_iff'] word_sbin.norm_Rep]

lemmas uint_div_alt = word_div_def [THEN trans [OF uint_cong int_word_uint]]
lemmas uint_mod_alt = word_mod_def [THEN trans [OF uint_cong int_word_uint]]

lemma word_pred_0_n1: "word_pred 0 = word_of_int -1"
  unfolding word_pred_def uint_eq_0 pred_def by simp

lemma word_pred_0_Min: "word_pred 0 = word_of_int Int.Min"
  by (simp add: word_pred_0_n1 number_of_eq)

lemma word_m1_Min: "- 1 = word_of_int Int.Min"
  unfolding Min_def by (simp only: word_of_int_hom_syms)

lemma succ_pred_no [simp]:
  "word_succ (number_of bin) = number_of (Int.succ bin) & 
    word_pred (number_of bin) = number_of (Int.pred bin)"
  unfolding word_number_of_def by (simp add : new_word_of_int_homs)

lemma word_sp_01 [simp] : 
  "word_succ -1 = 0 & word_succ 0 = 1 & word_pred 0 = -1 & word_pred 1 = 0"
  by (unfold word_0_no word_1_no) auto

(* alternative approach to lifting arithmetic equalities *)
lemma word_of_int_Ex:
  "\<exists>y. x = word_of_int y"
  by (rule_tac x="uint x" in exI) simp


subsection "Order on fixed-length words"

lemma word_zero_le [simp] :
  "0 <= (y :: 'a :: len0 word)"
  unfolding word_le_def by auto
  
lemma word_m1_ge [simp] : "word_pred 0 >= y"
  unfolding word_le_def
  by (simp only : word_pred_0_n1 word_uint.eq_norm m1mod2k) auto

lemmas word_n1_ge [simp]  = word_m1_ge [simplified word_sp_01]

lemmas word_not_simps [simp] = 
  word_zero_le [THEN leD] word_m1_ge [THEN leD] word_n1_ge [THEN leD]

lemma word_gt_0: "0 < y = (0 ~= (y :: 'a :: len0 word))"
  unfolding word_less_def by auto

lemmas word_gt_0_no [simp] = word_gt_0 [of "number_of y"] for y

lemma word_sless_alt: "(a <s b) = (sint a < sint b)"
  unfolding word_sle_def word_sless_def
  by (auto simp add: less_le)

lemma word_le_nat_alt: "(a <= b) = (unat a <= unat b)"
  unfolding unat_def word_le_def
  by (rule nat_le_eq_zle [symmetric]) simp

lemma word_less_nat_alt: "(a < b) = (unat a < unat b)"
  unfolding unat_def word_less_alt
  by (rule nat_less_eq_zless [symmetric]) simp
  
lemma wi_less: 
  "(word_of_int n < (word_of_int m :: 'a :: len0 word)) = 
    (n mod 2 ^ len_of TYPE('a) < m mod 2 ^ len_of TYPE('a))"
  unfolding word_less_alt by (simp add: word_uint.eq_norm)

lemma wi_le: 
  "(word_of_int n <= (word_of_int m :: 'a :: len0 word)) = 
    (n mod 2 ^ len_of TYPE('a) <= m mod 2 ^ len_of TYPE('a))"
  unfolding word_le_def by (simp add: word_uint.eq_norm)

lemma udvd_nat_alt: "a udvd b = (EX n>=0. unat b = n * unat a)"
  apply (unfold udvd_def)
  apply safe
   apply (simp add: unat_def nat_mult_distrib)
  apply (simp add: uint_nat int_mult)
  apply (rule exI)
  apply safe
   prefer 2
   apply (erule notE)
   apply (rule refl)
  apply force
  done

lemma udvd_iff_dvd: "x udvd y <-> unat x dvd unat y"
  unfolding dvd_def udvd_nat_alt by force

lemmas unat_mono = word_less_nat_alt [THEN iffD1]

lemma no_no [simp] : "number_of (number_of b) = number_of b"
  by (simp add: number_of_eq)

lemma unat_minus_one: "x ~= 0 \<Longrightarrow> unat (x - 1) = unat x - 1"
  apply (unfold unat_def)
  apply (simp only: int_word_uint word_arith_alts rdmods)
  apply (subgoal_tac "uint x >= 1")
   prefer 2
   apply (drule contrapos_nn)
    apply (erule word_uint.Rep_inverse' [symmetric])
   apply (insert uint_ge_0 [of x])[1]
   apply arith
  apply (rule box_equals)
    apply (rule nat_diff_distrib)
     prefer 2
     apply assumption
    apply simp
   apply (subst mod_pos_pos_trivial)
     apply arith
    apply (insert uint_lt2p [of x])[1]
    apply arith
   apply (rule refl)
  apply simp
  done
    
lemma measure_unat: "p ~= 0 \<Longrightarrow> unat (p - 1) < unat p"
  by (simp add: unat_minus_one) (simp add: unat_0_iff [symmetric])
  
lemmas uint_add_ge0 [simp] = add_nonneg_nonneg [OF uint_ge_0 uint_ge_0]
lemmas uint_mult_ge0 [simp] = mult_nonneg_nonneg [OF uint_ge_0 uint_ge_0]

lemma uint_sub_lt2p [simp]: 
  "uint (x :: 'a :: len0 word) - uint (y :: 'b :: len0 word) < 
    2 ^ len_of TYPE('a)"
  using uint_ge_0 [of y] uint_lt2p [of x] by arith


subsection "Conditions for the addition (etc) of two words to overflow"

lemma uint_add_lem: 
  "(uint x + uint y < 2 ^ len_of TYPE('a)) = 
    (uint (x + y :: 'a :: len0 word) = uint x + uint y)"
  by (unfold uint_word_ariths) (auto intro!: trans [OF _ int_mod_lem])

lemma uint_mult_lem: 
  "(uint x * uint y < 2 ^ len_of TYPE('a)) = 
    (uint (x * y :: 'a :: len0 word) = uint x * uint y)"
  by (unfold uint_word_ariths) (auto intro!: trans [OF _ int_mod_lem])

lemma uint_sub_lem: 
  "(uint x >= uint y) = (uint (x - y) = uint x - uint y)"
  by (unfold uint_word_ariths) (auto intro!: trans [OF _ int_mod_lem])

lemma uint_add_le: "uint (x + y) <= uint x + uint y"
  unfolding uint_word_ariths by (auto simp: mod_add_if_z)

lemma uint_sub_ge: "uint (x - y) >= uint x - uint y"
  unfolding uint_word_ariths by (auto simp: mod_sub_if_z)

lemmas uint_sub_if' = trans [OF uint_word_ariths(1) mod_sub_if_z, simplified]
lemmas uint_plus_if' = trans [OF uint_word_ariths(2) mod_add_if_z, simplified]


subsection {* Definition of uint\_arith *}

lemma word_of_int_inverse:
  "word_of_int r = a \<Longrightarrow> 0 <= r \<Longrightarrow> r < 2 ^ len_of TYPE('a) \<Longrightarrow> 
   uint (a::'a::len0 word) = r"
  apply (erule word_uint.Abs_inverse' [rotated])
  apply (simp add: uints_num)
  done

lemma uint_split:
  fixes x::"'a::len0 word"
  shows "P (uint x) = 
         (ALL i. word_of_int i = x & 0 <= i & i < 2^len_of TYPE('a) --> P i)"
  apply (fold word_int_case_def)
  apply (auto dest!: word_of_int_inverse simp: int_word_uint int_mod_eq'
              split: word_int_split)
  done

lemma uint_split_asm:
  fixes x::"'a::len0 word"
  shows "P (uint x) = 
         (~(EX i. word_of_int i = x & 0 <= i & i < 2^len_of TYPE('a) & ~ P i))"
  by (auto dest!: word_of_int_inverse 
           simp: int_word_uint int_mod_eq'
           split: uint_split)

lemmas uint_splits = uint_split uint_split_asm

lemmas uint_arith_simps = 
  word_le_def word_less_alt
  word_uint.Rep_inject [symmetric] 
  uint_sub_if' uint_plus_if'

(* use this to stop, eg, 2 ^ len_of TYPE (32) being simplified *)
lemma power_False_cong: "False \<Longrightarrow> a ^ b = c ^ d" 
  by auto

(* uint_arith_tac: reduce to arithmetic on int, try to solve by arith *)
ML {*
fun uint_arith_ss_of ss = 
  ss addsimps @{thms uint_arith_simps}
     delsimps @{thms word_uint.Rep_inject}
     |> fold Splitter.add_split @{thms split_if_asm}
     |> fold Simplifier.add_cong @{thms power_False_cong}

fun uint_arith_tacs ctxt = 
  let
    fun arith_tac' n t =
      Arith_Data.verbose_arith_tac ctxt n t
        handle Cooper.COOPER _ => Seq.empty;
  in 
    [ clarify_tac ctxt 1,
      full_simp_tac (uint_arith_ss_of (simpset_of ctxt)) 1,
      ALLGOALS (full_simp_tac (HOL_ss |> fold Splitter.add_split @{thms uint_splits}
                                      |> fold Simplifier.add_cong @{thms power_False_cong})),
      rewrite_goals_tac @{thms word_size}, 
      ALLGOALS  (fn n => REPEAT (resolve_tac [allI, impI] n) THEN      
                         REPEAT (etac conjE n) THEN
                         REPEAT (dtac @{thm word_of_int_inverse} n 
                                 THEN atac n 
                                 THEN atac n)),
      TRYALL arith_tac' ]
  end

fun uint_arith_tac ctxt = SELECT_GOAL (EVERY (uint_arith_tacs ctxt))
*}

method_setup uint_arith = 
  {* Scan.succeed (SIMPLE_METHOD' o uint_arith_tac) *}
  "solving word arithmetic via integers and arith"


subsection "More on overflows and monotonicity"

lemma no_plus_overflow_uint_size: 
  "((x :: 'a :: len0 word) <= x + y) = (uint x + uint y < 2 ^ size x)"
  unfolding word_size by uint_arith

lemmas no_olen_add = no_plus_overflow_uint_size [unfolded word_size]

lemma no_ulen_sub: "((x :: 'a :: len0 word) >= x - y) = (uint y <= uint x)"
  by uint_arith

lemma no_olen_add':
  fixes x :: "'a::len0 word"
  shows "(x \<le> y + x) = (uint y + uint x < 2 ^ len_of TYPE('a))"
  by (simp add: add_ac no_olen_add)

lemmas olen_add_eqv = trans [OF no_olen_add no_olen_add' [symmetric]]

lemmas uint_plus_simple_iff = trans [OF no_olen_add uint_add_lem]
lemmas uint_plus_simple = uint_plus_simple_iff [THEN iffD1]
lemmas uint_minus_simple_iff = trans [OF no_ulen_sub uint_sub_lem]
lemmas uint_minus_simple_alt = uint_sub_lem [folded word_le_def]
lemmas word_sub_le_iff = no_ulen_sub [folded word_le_def]
lemmas word_sub_le = word_sub_le_iff [THEN iffD2]

lemma word_less_sub1: 
  "(x :: 'a :: len word) ~= 0 \<Longrightarrow> (1 < x) = (0 < x - 1)"
  by uint_arith

lemma word_le_sub1: 
  "(x :: 'a :: len word) ~= 0 \<Longrightarrow> (1 <= x) = (0 <= x - 1)"
  by uint_arith

lemma sub_wrap_lt: 
  "((x :: 'a :: len0 word) < x - z) = (x < z)"
  by uint_arith

lemma sub_wrap: 
  "((x :: 'a :: len0 word) <= x - z) = (z = 0 | x < z)"
  by uint_arith

lemma plus_minus_not_NULL_ab: 
  "(x :: 'a :: len0 word) <= ab - c \<Longrightarrow> c <= ab \<Longrightarrow> c ~= 0 \<Longrightarrow> x + c ~= 0"
  by uint_arith

lemma plus_minus_no_overflow_ab: 
  "(x :: 'a :: len0 word) <= ab - c \<Longrightarrow> c <= ab \<Longrightarrow> x <= x + c" 
  by uint_arith

lemma le_minus': 
  "(a :: 'a :: len0 word) + c <= b \<Longrightarrow> a <= a + c \<Longrightarrow> c <= b - a"
  by uint_arith

lemma le_plus': 
  "(a :: 'a :: len0 word) <= b \<Longrightarrow> c <= b - a \<Longrightarrow> a + c <= b"
  by uint_arith

lemmas le_plus = le_plus' [rotated]

lemmas le_minus = leD [THEN thin_rl, THEN le_minus']

lemma word_plus_mono_right: 
  "(y :: 'a :: len0 word) <= z \<Longrightarrow> x <= x + z \<Longrightarrow> x + y <= x + z"
  by uint_arith

lemma word_less_minus_cancel: 
  "y - x < z - x \<Longrightarrow> x <= z \<Longrightarrow> (y :: 'a :: len0 word) < z"
  by uint_arith

lemma word_less_minus_mono_left: 
  "(y :: 'a :: len0 word) < z \<Longrightarrow> x <= y \<Longrightarrow> y - x < z - x"
  by uint_arith

lemma word_less_minus_mono:  
  "a < c \<Longrightarrow> d < b \<Longrightarrow> a - b < a \<Longrightarrow> c - d < c 
  \<Longrightarrow> a - b < c - (d::'a::len word)"
  by uint_arith

lemma word_le_minus_cancel: 
  "y - x <= z - x \<Longrightarrow> x <= z \<Longrightarrow> (y :: 'a :: len0 word) <= z"
  by uint_arith

lemma word_le_minus_mono_left: 
  "(y :: 'a :: len0 word) <= z \<Longrightarrow> x <= y \<Longrightarrow> y - x <= z - x"
  by uint_arith

lemma word_le_minus_mono:  
  "a <= c \<Longrightarrow> d <= b \<Longrightarrow> a - b <= a \<Longrightarrow> c - d <= c 
  \<Longrightarrow> a - b <= c - (d::'a::len word)"
  by uint_arith

lemma plus_le_left_cancel_wrap: 
  "(x :: 'a :: len0 word) + y' < x \<Longrightarrow> x + y < x \<Longrightarrow> (x + y' < x + y) = (y' < y)"
  by uint_arith

lemma plus_le_left_cancel_nowrap: 
  "(x :: 'a :: len0 word) <= x + y' \<Longrightarrow> x <= x + y \<Longrightarrow> 
    (x + y' < x + y) = (y' < y)" 
  by uint_arith

lemma word_plus_mono_right2: 
  "(a :: 'a :: len0 word) <= a + b \<Longrightarrow> c <= b \<Longrightarrow> a <= a + c"
  by uint_arith

lemma word_less_add_right: 
  "(x :: 'a :: len0 word) < y - z \<Longrightarrow> z <= y \<Longrightarrow> x + z < y"
  by uint_arith

lemma word_less_sub_right: 
  "(x :: 'a :: len0 word) < y + z \<Longrightarrow> y <= x \<Longrightarrow> x - y < z"
  by uint_arith

lemma word_le_plus_either: 
  "(x :: 'a :: len0 word) <= y | x <= z \<Longrightarrow> y <= y + z \<Longrightarrow> x <= y + z"
  by uint_arith

lemma word_less_nowrapI: 
  "(x :: 'a :: len0 word) < z - k \<Longrightarrow> k <= z \<Longrightarrow> 0 < k \<Longrightarrow> x < x + k"
  by uint_arith

lemma inc_le: "(i :: 'a :: len word) < m \<Longrightarrow> i + 1 <= m"
  by uint_arith

lemma inc_i: 
  "(1 :: 'a :: len word) <= i \<Longrightarrow> i < m \<Longrightarrow> 1 <= (i + 1) & i + 1 <= m"
  by uint_arith

lemma udvd_incr_lem:
  "up < uq \<Longrightarrow> up = ua + n * uint K \<Longrightarrow> 
    uq = ua + n' * uint K \<Longrightarrow> up + uint K <= uq"
  apply clarsimp
  apply (drule less_le_mult)
  apply safe
  done

lemma udvd_incr': 
  "p < q \<Longrightarrow> uint p = ua + n * uint K \<Longrightarrow> 
    uint q = ua + n' * uint K \<Longrightarrow> p + K <= q" 
  apply (unfold word_less_alt word_le_def)
  apply (drule (2) udvd_incr_lem)
  apply (erule uint_add_le [THEN order_trans])
  done

lemma udvd_decr': 
  "p < q \<Longrightarrow> uint p = ua + n * uint K \<Longrightarrow> 
    uint q = ua + n' * uint K \<Longrightarrow> p <= q - K"
  apply (unfold word_less_alt word_le_def)
  apply (drule (2) udvd_incr_lem)
  apply (drule le_diff_eq [THEN iffD2])
  apply (erule order_trans)
  apply (rule uint_sub_ge)
  done

lemmas udvd_incr_lem0 = udvd_incr_lem [where ua=0, simplified]
lemmas udvd_incr0 = udvd_incr' [where ua=0, simplified]
lemmas udvd_decr0 = udvd_decr' [where ua=0, simplified]

lemma udvd_minus_le': 
  "xy < k \<Longrightarrow> z udvd xy \<Longrightarrow> z udvd k \<Longrightarrow> xy <= k - z"
  apply (unfold udvd_def)
  apply clarify
  apply (erule (2) udvd_decr0)
  done

ML {* Delsimprocs [@{simproc linordered_ring_less_cancel_factor}] *}

lemma udvd_incr2_K: 
  "p < a + s \<Longrightarrow> a <= a + s \<Longrightarrow> K udvd s \<Longrightarrow> K udvd p - a \<Longrightarrow> a <= p \<Longrightarrow> 
    0 < K \<Longrightarrow> p <= p + K & p + K <= a + s"
  apply (unfold udvd_def)
  apply clarify
  apply (simp add: uint_arith_simps split: split_if_asm)
   prefer 2 
   apply (insert uint_range' [of s])[1]
   apply arith
  apply (drule add_commute [THEN xtr1])
  apply (simp add: diff_less_eq [symmetric])
  apply (drule less_le_mult)
   apply arith
  apply simp
  done

ML {* Addsimprocs [@{simproc linordered_ring_less_cancel_factor}] *}

(* links with rbl operations *)
lemma word_succ_rbl:
  "to_bl w = bl \<Longrightarrow> to_bl (word_succ w) = (rev (rbl_succ (rev bl)))"
  apply (unfold word_succ_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_succ)
  done

lemma word_pred_rbl:
  "to_bl w = bl \<Longrightarrow> to_bl (word_pred w) = (rev (rbl_pred (rev bl)))"
  apply (unfold word_pred_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_pred)
  done

lemma word_add_rbl:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow> 
    to_bl (v + w) = (rev (rbl_add (rev vbl) (rev wbl)))"
  apply (unfold word_add_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_add)
  done

lemma word_mult_rbl:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow> 
    to_bl (v * w) = (rev (rbl_mult (rev vbl) (rev wbl)))"
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
  by (auto simp: rev_swap [symmetric] word_succ_rbl 
                 word_pred_rbl word_mult_rbl word_add_rbl)


subsection "Arithmetic type class instantiations"

(* note that iszero_def is only for class comm_semiring_1_cancel,
   which requires word length >= 1, ie 'a :: len word *) 
lemma zero_bintrunc:
  "iszero (number_of x :: 'a :: len word) = 
    (bintrunc (len_of TYPE('a)) x = Int.Pls)"
  apply (unfold iszero_def word_0_wi word_no_wi)
  apply (rule word_ubin.norm_eq_iff [symmetric, THEN trans])
  apply (simp add : Pls_def [symmetric])
  done

lemmas word_le_0_iff [simp] =
  word_zero_le [THEN leD, THEN linorder_antisym_conv1]

lemma word_of_int_nat: 
  "0 <= x \<Longrightarrow> word_of_int x = of_nat (nat x)"
  by (simp add: of_nat_nat word_of_int)

lemma iszero_word_no [simp] : 
  "iszero (number_of bin :: 'a :: len word) = 
    iszero (number_of (bintrunc (len_of TYPE('a)) bin) :: int)"
  apply (simp add: zero_bintrunc number_of_is_id)
  apply (unfold iszero_def Pls_def)
  apply (rule refl)
  done
    

subsection "Word and nat"

lemma td_ext_unat':
  "n = len_of TYPE ('a :: len) \<Longrightarrow> 
    td_ext (unat :: 'a word => nat) of_nat 
    (unats n) (%i. i mod 2 ^ n)"
  apply (unfold td_ext_def' unat_def word_of_nat unats_uints)
  apply (auto intro!: imageI simp add : word_of_int_hom_syms)
  apply (erule word_uint.Abs_inverse [THEN arg_cong])
  apply (simp add: int_word_uint nat_mod_distrib nat_power_eq)
  done

lemmas td_ext_unat = refl [THEN td_ext_unat']
lemmas unat_of_nat = td_ext_unat [THEN td_ext.eq_norm]

interpretation word_unat:
  td_ext "unat::'a::len word => nat" 
         of_nat 
         "unats (len_of TYPE('a::len))"
         "%i. i mod 2 ^ len_of TYPE('a::len)"
  by (rule td_ext_unat)

lemmas td_unat = word_unat.td_thm

lemmas unat_lt2p [iff] = word_unat.Rep [unfolded unats_def mem_Collect_eq]

lemma unat_le: "y <= unat (z :: 'a :: len word) \<Longrightarrow> y : unats (len_of TYPE ('a))"
  apply (unfold unats_def)
  apply clarsimp
  apply (rule xtrans, rule unat_lt2p, assumption) 
  done

lemma word_nchotomy:
  "ALL w. EX n. (w :: 'a :: len word) = of_nat n & n < 2 ^ len_of TYPE ('a)"
  apply (rule allI)
  apply (rule word_unat.Abs_cases)
  apply (unfold unats_def)
  apply auto
  done

lemma of_nat_eq:
  fixes w :: "'a::len word"
  shows "(of_nat n = w) = (\<exists>q. n = unat w + q * 2 ^ len_of TYPE('a))"
  apply (rule trans)
   apply (rule word_unat.inverse_norm)
  apply (rule iffI)
   apply (rule mod_eqD)
   apply simp
  apply clarsimp
  done

lemma of_nat_eq_size: 
  "(of_nat n = w) = (EX q. n = unat w + q * 2 ^ size w)"
  unfolding word_size by (rule of_nat_eq)

lemma of_nat_0:
  "(of_nat m = (0::'a::len word)) = (\<exists>q. m = q * 2 ^ len_of TYPE('a))"
  by (simp add: of_nat_eq)

lemma of_nat_2p [simp]:
  "of_nat (2 ^ len_of TYPE('a)) = (0::'a::len word)"
  by (fact mult_1 [symmetric, THEN iffD2 [OF of_nat_0 exI]])

lemma of_nat_gt_0: "of_nat k ~= 0 \<Longrightarrow> 0 < k"
  by (cases k) auto

lemma of_nat_neq_0: 
  "0 < k \<Longrightarrow> k < 2 ^ len_of TYPE ('a :: len) \<Longrightarrow> of_nat k ~= (0 :: 'a word)"
  by (clarsimp simp add : of_nat_0)

lemma Abs_fnat_hom_add:
  "of_nat a + of_nat b = of_nat (a + b)"
  by simp

lemma Abs_fnat_hom_mult:
  "of_nat a * of_nat b = (of_nat (a * b) :: 'a :: len word)"
  by (simp add: word_of_nat word_of_int_mult_hom zmult_int)

lemma Abs_fnat_hom_Suc:
  "word_succ (of_nat a) = of_nat (Suc a)"
  by (simp add: word_of_nat word_of_int_succ_hom add_ac)

lemma Abs_fnat_hom_0: "(0::'a::len word) = of_nat 0"
  by (simp add: word_of_nat word_0_wi)

lemma Abs_fnat_hom_1: "(1::'a::len word) = of_nat (Suc 0)"
  by (simp add: word_of_nat word_1_wi)

lemmas Abs_fnat_homs = 
  Abs_fnat_hom_add Abs_fnat_hom_mult Abs_fnat_hom_Suc 
  Abs_fnat_hom_0 Abs_fnat_hom_1

lemma word_arith_nat_add:
  "a + b = of_nat (unat a + unat b)" 
  by simp

lemma word_arith_nat_mult:
  "a * b = of_nat (unat a * unat b)"
  by (simp add: Abs_fnat_hom_mult [symmetric])
    
lemma word_arith_nat_Suc:
  "word_succ a = of_nat (Suc (unat a))"
  by (subst Abs_fnat_hom_Suc [symmetric]) simp

lemma word_arith_nat_div:
  "a div b = of_nat (unat a div unat b)"
  by (simp add: word_div_def word_of_nat zdiv_int uint_nat)

lemma word_arith_nat_mod:
  "a mod b = of_nat (unat a mod unat b)"
  by (simp add: word_mod_def word_of_nat zmod_int uint_nat)

lemmas word_arith_nat_defs =
  word_arith_nat_add word_arith_nat_mult
  word_arith_nat_Suc Abs_fnat_hom_0
  Abs_fnat_hom_1 word_arith_nat_div
  word_arith_nat_mod 

lemmas unat_cong = arg_cong [where f = unat]
  
lemmas unat_word_ariths = word_arith_nat_defs
  [THEN trans [OF unat_cong unat_of_nat]]

lemmas word_sub_less_iff = word_sub_le_iff
  [simplified linorder_not_less [symmetric], simplified]

lemma unat_add_lem: 
  "(unat x + unat y < 2 ^ len_of TYPE('a)) = 
    (unat (x + y :: 'a :: len word) = unat x + unat y)"
  unfolding unat_word_ariths
  by (auto intro!: trans [OF _ nat_mod_lem])

lemma unat_mult_lem: 
  "(unat x * unat y < 2 ^ len_of TYPE('a)) = 
    (unat (x * y :: 'a :: len word) = unat x * unat y)"
  unfolding unat_word_ariths
  by (auto intro!: trans [OF _ nat_mod_lem])

lemmas unat_plus_if' = trans [OF unat_word_ariths(1) mod_nat_add, simplified]

lemma le_no_overflow: 
  "x <= b \<Longrightarrow> a <= a + b \<Longrightarrow> x <= a + (b :: 'a :: len0 word)"
  apply (erule order_trans)
  apply (erule olen_add_eqv [THEN iffD1])
  done

lemmas un_ui_le = trans [OF word_le_nat_alt [symmetric] word_le_def]

lemma unat_sub_if_size:
  "unat (x - y) = (if unat y <= unat x 
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

lemma unat_div: "unat ((x :: 'a :: len word) div y) = unat x div unat y"
  apply (simp add : unat_word_ariths)
  apply (rule unat_lt2p [THEN xtr7, THEN nat_mod_eq'])
  apply (rule div_le_dividend)
  done

lemma unat_mod: "unat ((x :: 'a :: len word) mod y) = unat x mod unat y"
  apply (clarsimp simp add : unat_word_ariths)
  apply (cases "unat y")
   prefer 2
   apply (rule unat_lt2p [THEN xtr7, THEN nat_mod_eq'])
   apply (rule mod_le_divisor)
   apply auto
  done

lemma uint_div: "uint ((x :: 'a :: len word) div y) = uint x div uint y"
  unfolding uint_nat by (simp add : unat_div zdiv_int)

lemma uint_mod: "uint ((x :: 'a :: len word) mod y) = uint x mod uint y"
  unfolding uint_nat by (simp add : unat_mod zmod_int)


subsection {* Definition of unat\_arith tactic *}

lemma unat_split:
  fixes x::"'a::len word"
  shows "P (unat x) = 
         (ALL n. of_nat n = x & n < 2^len_of TYPE('a) --> P n)"
  by (auto simp: unat_of_nat)

lemma unat_split_asm:
  fixes x::"'a::len word"
  shows "P (unat x) = 
         (~(EX n. of_nat n = x & n < 2^len_of TYPE('a) & ~ P n))"
  by (auto simp: unat_of_nat)

lemmas of_nat_inverse = 
  word_unat.Abs_inverse' [rotated, unfolded unats_def, simplified]

lemmas unat_splits = unat_split unat_split_asm

lemmas unat_arith_simps =
  word_le_nat_alt word_less_nat_alt
  word_unat.Rep_inject [symmetric]
  unat_sub_if' unat_plus_if' unat_div unat_mod

(* unat_arith_tac: tactic to reduce word arithmetic to nat, 
   try to solve via arith *)
ML {*
fun unat_arith_ss_of ss = 
  ss addsimps @{thms unat_arith_simps}
     delsimps @{thms word_unat.Rep_inject}
     |> fold Splitter.add_split @{thms split_if_asm}
     |> fold Simplifier.add_cong @{thms power_False_cong}

fun unat_arith_tacs ctxt =   
  let
    fun arith_tac' n t =
      Arith_Data.verbose_arith_tac ctxt n t
        handle Cooper.COOPER _ => Seq.empty;
  in 
    [ clarify_tac ctxt 1,
      full_simp_tac (unat_arith_ss_of (simpset_of ctxt)) 1,
      ALLGOALS (full_simp_tac (HOL_ss |> fold Splitter.add_split @{thms unat_splits}
                                      |> fold Simplifier.add_cong @{thms power_False_cong})),
      rewrite_goals_tac @{thms word_size}, 
      ALLGOALS  (fn n => REPEAT (resolve_tac [allI, impI] n) THEN      
                         REPEAT (etac conjE n) THEN
                         REPEAT (dtac @{thm of_nat_inverse} n THEN atac n)),
      TRYALL arith_tac' ] 
  end

fun unat_arith_tac ctxt = SELECT_GOAL (EVERY (unat_arith_tacs ctxt))
*}

method_setup unat_arith = 
  {* Scan.succeed (SIMPLE_METHOD' o unat_arith_tac) *}
  "solving word arithmetic via natural numbers and arith"

lemma no_plus_overflow_unat_size: 
  "((x :: 'a :: len word) <= x + y) = (unat x + unat y < 2 ^ size x)" 
  unfolding word_size by unat_arith

lemmas no_olen_add_nat = no_plus_overflow_unat_size [unfolded word_size]

lemmas unat_plus_simple = trans [OF no_olen_add_nat unat_add_lem]

lemma word_div_mult: 
  "(0 :: 'a :: len word) < y \<Longrightarrow> unat x * unat y < 2 ^ len_of TYPE('a) \<Longrightarrow> 
    x * y div y = x"
  apply unat_arith
  apply clarsimp
  apply (subst unat_mult_lem [THEN iffD1])
  apply auto
  done

lemma div_lt': "(i :: 'a :: len word) <= k div x \<Longrightarrow> 
    unat i * unat x < 2 ^ len_of TYPE('a)"
  apply unat_arith
  apply clarsimp
  apply (drule mult_le_mono1)
  apply (erule order_le_less_trans)
  apply (rule xtr7 [OF unat_lt2p div_mult_le])
  done

lemmas div_lt'' = order_less_imp_le [THEN div_lt']

lemma div_lt_mult: "(i :: 'a :: len word) < k div x \<Longrightarrow> 0 < x \<Longrightarrow> i * x < k"
  apply (frule div_lt'' [THEN unat_mult_lem [THEN iffD1]])
  apply (simp add: unat_arith_simps)
  apply (drule (1) mult_less_mono1)
  apply (erule order_less_le_trans)
  apply (rule div_mult_le)
  done

lemma div_le_mult: 
  "(i :: 'a :: len word) <= k div x \<Longrightarrow> 0 < x \<Longrightarrow> i * x <= k"
  apply (frule div_lt' [THEN unat_mult_lem [THEN iffD1]])
  apply (simp add: unat_arith_simps)
  apply (drule mult_le_mono1)
  apply (erule order_trans)
  apply (rule div_mult_le)
  done

lemma div_lt_uint': 
  "(i :: 'a :: len word) <= k div x \<Longrightarrow> uint i * uint x < 2 ^ len_of TYPE('a)"
  apply (unfold uint_nat)
  apply (drule div_lt')
  apply (simp add: zmult_int zless_nat_eq_int_zless [symmetric] 
                   nat_power_eq)
  done

lemmas div_lt_uint'' = order_less_imp_le [THEN div_lt_uint']

lemma word_le_exists': 
  "(x :: 'a :: len0 word) <= y \<Longrightarrow> 
    (EX z. y = x + z & uint x + uint z < 2 ^ len_of TYPE('a))"
  apply (rule exI)
  apply (rule conjI)
  apply (rule zadd_diff_inverse)
  apply uint_arith
  done

lemmas plus_minus_not_NULL = order_less_imp_le [THEN plus_minus_not_NULL_ab]

lemmas plus_minus_no_overflow =
  order_less_imp_le [THEN plus_minus_no_overflow_ab]
  
lemmas mcs = word_less_minus_cancel word_less_minus_mono_left
  word_le_minus_cancel word_le_minus_mono_left

lemmas word_l_diffs = mcs [where y = "w + x", unfolded add_diff_cancel] for w x
lemmas word_diff_ls = mcs [where z = "w + x", unfolded add_diff_cancel] for w x
lemmas word_plus_mcs = word_diff_ls [where y = "v + x", unfolded add_diff_cancel] for v x

lemmas le_unat_uoi = unat_le [THEN word_unat.Abs_inverse]

lemmas thd = refl [THEN [2] split_div_lemma [THEN iffD2], THEN conjunct1]

lemma thd1:
  "a div b * b \<le> (a::nat)"
  using gt_or_eq_0 [of b]
  apply (rule disjE)
   apply (erule xtr4 [OF thd mult_commute])
  apply clarsimp
  done

lemmas uno_simps [THEN le_unat_uoi] = mod_le_divisor div_le_dividend thd1 

lemma word_mod_div_equality:
  "(n div b) * b + (n mod b) = (n :: 'a :: len word)"
  apply (unfold word_less_nat_alt word_arith_nat_defs)
  apply (cut_tac y="unat b" in gt_or_eq_0)
  apply (erule disjE)
   apply (simp add: mod_div_equality uno_simps)
  apply simp
  done

lemma word_div_mult_le: "a div b * b <= (a::'a::len word)"
  apply (unfold word_le_nat_alt word_arith_nat_defs)
  apply (cut_tac y="unat b" in gt_or_eq_0)
  apply (erule disjE)
   apply (simp add: div_mult_le uno_simps)
  apply simp
  done

lemma word_mod_less_divisor: "0 < n \<Longrightarrow> m mod n < (n :: 'a :: len word)"
  apply (simp only: word_less_nat_alt word_arith_nat_defs)
  apply (clarsimp simp add : uno_simps)
  done

lemma word_of_int_power_hom: 
  "word_of_int a ^ n = (word_of_int (a ^ n) :: 'a :: len word)"
  by (induct n) (simp_all add: word_of_int_hom_syms)

lemma word_arith_power_alt: 
  "a ^ n = (word_of_int (uint a ^ n) :: 'a :: len word)"
  by (simp add : word_of_int_power_hom [symmetric])

lemma of_bl_length_less: 
  "length x = k \<Longrightarrow> k < len_of TYPE('a) \<Longrightarrow> (of_bl x :: 'a :: len word) < 2 ^ k"
  apply (unfold of_bl_no [unfolded word_number_of_def]
                word_less_alt word_number_of_alt)
  apply safe
  apply (simp (no_asm) add: word_of_int_power_hom word_uint.eq_norm 
                       del: word_of_int_bin)
  apply (simp add: mod_pos_pos_trivial)
  apply (subst mod_pos_pos_trivial)
    apply (rule bl_to_bin_ge0)
   apply (rule order_less_trans)
    apply (rule bl_to_bin_lt2p)
   apply simp
  apply (rule bl_to_bin_lt2p)    
  done


subsection "Cardinality, finiteness of set of words"

instance word :: (len0) finite
  by (default, simp add: type_definition.univ [OF type_definition_word])

lemma card_word: "CARD('a::len0 word) = 2 ^ len_of TYPE('a)"
  by (simp add: type_definition.card [OF type_definition_word] nat_power_eq)

lemma card_word_size: 
  "card (UNIV :: 'a :: len0 word set) = (2 ^ size (x :: 'a word))"
unfolding word_size by (rule card_word)


subsection {* Bitwise Operations on Words *}

lemmas bin_log_bintrs = bin_trunc_not bin_trunc_xor bin_trunc_and bin_trunc_or
  
(* following definitions require both arithmetic and bit-wise word operations *)

(* to get word_no_log_defs from word_log_defs, using bin_log_bintrs *)
lemmas wils1 = bin_log_bintrs [THEN word_ubin.norm_eq_iff [THEN iffD1],
  folded word_ubin.eq_norm, THEN eq_reflection]

(* the binary operations only *)
lemmas word_log_binary_defs = 
  word_and_def word_or_def word_xor_def

lemmas word_no_log_defs [simp] = 
  word_not_def  [where a="number_of a", 
                 unfolded word_no_wi wils1, folded word_no_wi]
  word_log_binary_defs [where a="number_of a" and b="number_of b",
                        unfolded word_no_wi wils1, folded word_no_wi]
  for a b

lemmas word_wi_log_defs = word_no_log_defs [unfolded word_no_wi]

lemma uint_or: "uint (x OR y) = (uint x) OR (uint y)"
  by (simp add: word_or_def word_wi_log_defs word_ubin.eq_norm
                bin_trunc_ao(2) [symmetric])

lemma uint_and: "uint (x AND y) = (uint x) AND (uint y)"
  by (simp add: word_and_def word_wi_log_defs word_ubin.eq_norm
                bin_trunc_ao(1) [symmetric]) 

lemma word_ops_nth_size:
  "n < size (x::'a::len0 word) \<Longrightarrow> 
    (x OR y) !! n = (x !! n | y !! n) & 
    (x AND y) !! n = (x !! n & y !! n) & 
    (x XOR y) !! n = (x !! n ~= y !! n) & 
    (NOT x) !! n = (~ x !! n)"
  unfolding word_size word_test_bit_def word_log_defs
  by (clarsimp simp add : word_ubin.eq_norm nth_bintr bin_nth_ops)

lemma word_ao_nth:
  fixes x :: "'a::len0 word"
  shows "(x OR y) !! n = (x !! n | y !! n) & 
         (x AND y) !! n = (x !! n & y !! n)"
  apply (cases "n < size x")
   apply (drule_tac y = "y" in word_ops_nth_size)
   apply simp
  apply (simp add : test_bit_bin word_size)
  done

(* get from commutativity, associativity etc of int_and etc
  to same for word_and etc *)

lemmas bwsimps = 
  word_of_int_homs(2) 
  word_0_wi_Pls
  word_m1_wi_Min
  word_wi_log_defs

lemma word_bw_assocs:
  fixes x :: "'a::len0 word"
  shows
  "(x AND y) AND z = x AND y AND z"
  "(x OR y) OR z = x OR y OR z"
  "(x XOR y) XOR z = x XOR y XOR z"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
        word_of_int_Ex [where x=z]
  by (auto simp: bwsimps bbw_assocs)
  
lemma word_bw_comms:
  fixes x :: "'a::len0 word"
  shows
  "x AND y = y AND x"
  "x OR y = y OR x"
  "x XOR y = y XOR x"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
  by (auto simp: bwsimps bin_ops_comm)
  
lemma word_bw_lcs:
  fixes x :: "'a::len0 word"
  shows
  "y AND x AND z = x AND y AND z"
  "y OR x OR z = x OR y OR z"
  "y XOR x XOR z = x XOR y XOR z"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
        word_of_int_Ex [where x=z]
  by (auto simp: bwsimps)

lemma word_log_esimps [simp]:
  fixes x :: "'a::len0 word"
  shows
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
  using word_of_int_Ex [where x=x] 
  by (auto simp: bwsimps)

lemma word_not_dist:
  fixes x :: "'a::len0 word"
  shows
  "NOT (x OR y) = NOT x AND NOT y"
  "NOT (x AND y) = NOT x OR NOT y"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
  by (auto simp: bwsimps bbw_not_dist)

lemma word_bw_same:
  fixes x :: "'a::len0 word"
  shows
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  using word_of_int_Ex [where x=x] 
  by (auto simp: bwsimps)

lemma word_ao_absorbs [simp]:
  fixes x :: "'a::len0 word"
  shows
  "x AND (y OR x) = x"
  "x OR y AND x = x"
  "x AND (x OR y) = x"
  "y AND x OR x = x"
  "(y OR x) AND x = x"
  "x OR x AND y = x"
  "(x OR y) AND x = x"
  "x AND y OR x = x"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
  by (auto simp: bwsimps)

lemma word_not_not [simp]:
  "NOT NOT (x::'a::len0 word) = x"
  using word_of_int_Ex [where x=x] 
  by (auto simp: bwsimps)

lemma word_ao_dist:
  fixes x :: "'a::len0 word"
  shows "(x OR y) AND z = x AND z OR y AND z"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
        word_of_int_Ex [where x=z]   
  by (auto simp: bwsimps bbw_ao_dist)

lemma word_oa_dist:
  fixes x :: "'a::len0 word"
  shows "x AND y OR z = (x OR z) AND (y OR z)"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
        word_of_int_Ex [where x=z]   
  by (auto simp: bwsimps bbw_oa_dist)

lemma word_add_not [simp]: 
  fixes x :: "'a::len0 word"
  shows "x + NOT x = -1"
  using word_of_int_Ex [where x=x] 
  by (auto simp: bwsimps bin_add_not)

lemma word_plus_and_or [simp]:
  fixes x :: "'a::len0 word"
  shows "(x AND y) + (x OR y) = x + y"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
  by (auto simp: bwsimps plus_and_or)

lemma leoa:   
  fixes x :: "'a::len0 word"
  shows "(w = (x OR y)) \<Longrightarrow> (y = (w AND y))" by auto
lemma leao: 
  fixes x' :: "'a::len0 word"
  shows "(w' = (x' AND y')) \<Longrightarrow> (x' = (x' OR w'))" by auto 

lemmas word_ao_equiv = leao [COMP leoa [COMP iffI]]

lemma le_word_or2: "x <= x OR (y::'a::len0 word)"
  unfolding word_le_def uint_or
  by (auto intro: le_int_or) 

lemmas le_word_or1 = xtr3 [OF word_bw_comms (2) le_word_or2]
lemmas word_and_le1 = xtr3 [OF word_ao_absorbs (4) [symmetric] le_word_or2]
lemmas word_and_le2 = xtr3 [OF word_ao_absorbs (8) [symmetric] le_word_or2]

lemma bl_word_not: "to_bl (NOT w) = map Not (to_bl w)" 
  unfolding to_bl_def word_log_defs bl_not_bin
  by (simp add: word_ubin.eq_norm)

lemma bl_word_xor: "to_bl (v XOR w) = map2 op ~= (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs bl_xor_bin
  by (simp add: word_ubin.eq_norm)

lemma bl_word_or: "to_bl (v OR w) = map2 op | (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs bl_or_bin
  by (simp add: word_ubin.eq_norm)

lemma bl_word_and: "to_bl (v AND w) = map2 op & (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs bl_and_bin
  by (simp add: word_ubin.eq_norm)

lemma word_lsb_alt: "lsb (w::'a::len0 word) = test_bit w 0"
  by (auto simp: word_test_bit_def word_lsb_def)

lemma word_lsb_1_0 [simp]: "lsb (1::'a::len word) & ~ lsb (0::'b::len0 word)"
  unfolding word_lsb_def uint_eq_0 uint_1 by simp

lemma word_lsb_last: "lsb (w::'a::len word) = last (to_bl w)"
  apply (unfold word_lsb_def uint_bl bin_to_bl_def) 
  apply (rule_tac bin="uint w" in bin_exhaust)
  apply (cases "size w")
   apply auto
   apply (auto simp add: bin_to_bl_aux_alt)
  done

lemma word_lsb_int: "lsb w = (uint w mod 2 = 1)"
  unfolding word_lsb_def bin_last_def by auto

lemma word_msb_sint: "msb w = (sint w < 0)" 
  unfolding word_msb_def
  by (simp add : sign_Min_lt_0 number_of_is_id)
  
lemma word_msb_no': 
  "w = number_of bin \<Longrightarrow> msb (w::'a::len word) = bin_nth bin (size w - 1)"
  unfolding word_msb_def word_number_of_def
  by (clarsimp simp add: word_sbin.eq_norm word_size bin_sign_lem)

lemma word_msb_no [simp]:
  "msb (number_of bin :: 'a::len word) = bin_nth bin (len_of TYPE('a) - 1)"
  by (rule refl [THEN word_msb_no', unfolded word_size])

lemma word_msb_nth': "msb (w::'a::len word) = bin_nth (uint w) (size w - 1)"
  apply (unfold word_size)
  apply (rule trans [OF _ word_msb_no])
  apply (simp add : word_number_of_def)
  done

lemmas word_msb_nth = word_msb_nth' [unfolded word_size]

lemma word_msb_alt: "msb (w::'a::len word) = hd (to_bl w)"
  apply (unfold word_msb_nth uint_bl)
  apply (subst hd_conv_nth)
  apply (rule length_greater_0_conv [THEN iffD1])
   apply simp
  apply (simp add : nth_bin_to_bl word_size)
  done

lemma word_set_nth [simp]:
  "set_bit w n (test_bit w n) = (w::'a::len0 word)"
  unfolding word_test_bit_def word_set_bit_def by auto

lemma bin_nth_uint':
  "bin_nth (uint w) n = (rev (bin_to_bl (size w) (uint w)) ! n & n < size w)"
  apply (unfold word_size)
  apply (safe elim!: bin_nth_uint_imp)
   apply (frule bin_nth_uint_imp)
   apply (fast dest!: bin_nth_bl)+
  done

lemmas bin_nth_uint = bin_nth_uint' [unfolded word_size]

lemma test_bit_bl: "w !! n = (rev (to_bl w) ! n & n < size w)"
  unfolding to_bl_def word_test_bit_def word_size
  by (rule bin_nth_uint)

lemma to_bl_nth: "n < size w \<Longrightarrow> to_bl w ! n = w !! (size w - Suc n)"
  apply (unfold test_bit_bl)
  apply clarsimp
  apply (rule trans)
   apply (rule nth_rev_alt)
   apply (auto simp add: word_size)
  done

lemma test_bit_set: 
  fixes w :: "'a::len0 word"
  shows "(set_bit w n x) !! n = (n < size w & x)"
  unfolding word_size word_test_bit_def word_set_bit_def
  by (clarsimp simp add : word_ubin.eq_norm nth_bintr)

lemma test_bit_set_gen: 
  fixes w :: "'a::len0 word"
  shows "test_bit (set_bit w n x) m = 
         (if m = n then n < size w & x else test_bit w m)"
  apply (unfold word_size word_test_bit_def word_set_bit_def)
  apply (clarsimp simp add: word_ubin.eq_norm nth_bintr bin_nth_sc_gen)
  apply (auto elim!: test_bit_size [unfolded word_size]
              simp add: word_test_bit_def [symmetric])
  done

lemma of_bl_rep_False: "of_bl (replicate n False @ bs) = of_bl bs"
  unfolding of_bl_def bl_to_bin_rep_F by auto
  
lemma msb_nth':
  fixes w :: "'a::len word"
  shows "msb w = w !! (size w - 1)"
  unfolding word_msb_nth' word_test_bit_def by simp

lemmas msb_nth = msb_nth' [unfolded word_size]

lemmas msb0 = len_gt_0 [THEN diff_Suc_less, THEN word_ops_nth_size [unfolded word_size]]
lemmas msb1 = msb0 [where i = 0]
lemmas word_ops_msb = msb1 [unfolded msb_nth [symmetric, unfolded One_nat_def]]

lemmas lsb0 = len_gt_0 [THEN word_ops_nth_size [unfolded word_size]]
lemmas word_ops_lsb = lsb0 [unfolded word_lsb_alt]

lemma td_ext_nth':
  "n = size (w::'a::len0 word) \<Longrightarrow> ofn = set_bits \<Longrightarrow> [w, ofn g] = l \<Longrightarrow> 
    td_ext test_bit ofn {f. ALL i. f i --> i < n} (%h i. h i & i < n)"
  apply (unfold word_size td_ext_def')
  apply (safe del: subset_antisym)
     apply (rule_tac [3] ext)
     apply (rule_tac [4] ext)
     apply (unfold word_size of_nth_def test_bit_bl)
     apply safe
       defer
       apply (clarsimp simp: word_bl.Abs_inverse)+
  apply (rule word_bl.Rep_inverse')
  apply (rule sym [THEN trans])
  apply (rule bl_of_nth_nth)
  apply simp
  apply (rule bl_of_nth_inj)
  apply (clarsimp simp add : test_bit_bl word_size)
  done

lemmas td_ext_nth = td_ext_nth' [OF refl refl refl, unfolded word_size]

interpretation test_bit:
  td_ext "op !! :: 'a::len0 word => nat => bool"
         set_bits
         "{f. \<forall>i. f i \<longrightarrow> i < len_of TYPE('a::len0)}"
         "(\<lambda>h i. h i \<and> i < len_of TYPE('a::len0))"
  by (rule td_ext_nth)

lemmas td_nth = test_bit.td_thm

lemma word_set_set_same [simp]:
  fixes w :: "'a::len0 word"
  shows "set_bit (set_bit w n x) n y = set_bit w n y" 
  by (rule word_eqI) (simp add : test_bit_set_gen word_size)
    
lemma word_set_set_diff: 
  fixes w :: "'a::len0 word"
  assumes "m ~= n"
  shows "set_bit (set_bit w m x) n y = set_bit (set_bit w n y) m x" 
  by (rule word_eqI) (clarsimp simp add: test_bit_set_gen word_size assms)
    
lemma test_bit_no': 
  fixes w :: "'a::len0 word"
  shows "w = number_of bin \<Longrightarrow> test_bit w n = (n < size w & bin_nth bin n)"
  unfolding word_test_bit_def word_number_of_def word_size
  by (simp add : nth_bintr [symmetric] word_ubin.eq_norm)

lemma test_bit_no [simp]:
  "(number_of bin :: 'a::len0 word) !! n \<equiv> n < len_of TYPE('a) \<and> bin_nth bin n"
  by (rule refl [THEN test_bit_no', unfolded word_size, THEN eq_reflection])

lemma nth_0 [simp]: "~ (0::'a::len0 word) !! n"
  unfolding test_bit_no word_0_no by auto

lemma nth_sint: 
  fixes w :: "'a::len word"
  defines "l \<equiv> len_of TYPE ('a)"
  shows "bin_nth (sint w) n = (if n < l - 1 then w !! n else w !! (l - 1))"
  unfolding sint_uint l_def
  by (clarsimp simp add: nth_sbintr word_test_bit_def [symmetric])

lemma word_lsb_no [simp]:
  "lsb (number_of bin :: 'a :: len word) = (bin_last bin = 1)"
  unfolding word_lsb_alt test_bit_no by auto

lemma word_set_no [simp]:
  "set_bit (number_of bin::'a::len0 word) n b = 
    number_of (bin_sc n (if b then 1 else 0) bin)"
  apply (unfold word_set_bit_def word_number_of_def [symmetric])
  apply (rule word_eqI)
  apply (clarsimp simp: word_size bin_nth_sc_gen number_of_is_id 
                        nth_bintr)
  done

lemma setBit_no [simp]:
  "setBit (number_of bin) n = number_of (bin_sc n 1 bin) "
  by (simp add: setBit_def)

lemma clearBit_no [simp]:
  "clearBit (number_of bin) n = number_of (bin_sc n 0 bin)"
  by (simp add: clearBit_def)

lemma to_bl_n1: 
  "to_bl (-1::'a::len0 word) = replicate (len_of TYPE ('a)) True"
  apply (rule word_bl.Abs_inverse')
   apply simp
  apply (rule word_eqI)
  apply (clarsimp simp add: word_size)
  apply (auto simp add: word_bl.Abs_inverse test_bit_bl word_size)
  done

lemma word_msb_n1 [simp]: "msb (-1::'a::len word)"
  unfolding word_msb_alt to_bl_n1 by simp

lemma word_set_nth_iff: 
  "(set_bit w n b = w) = (w !! n = b | n >= size (w::'a::len0 word))"
  apply (rule iffI)
   apply (rule disjCI)
   apply (drule word_eqD)
   apply (erule sym [THEN trans])
   apply (simp add: test_bit_set)
  apply (erule disjE)
   apply clarsimp
  apply (rule word_eqI)
  apply (clarsimp simp add : test_bit_set_gen)
  apply (drule test_bit_size)
  apply force
  done

lemma test_bit_2p': 
  "w = word_of_int (2 ^ n) \<Longrightarrow> 
    w !! m = (m = n & m < size (w :: 'a :: len word))"
  unfolding word_test_bit_def word_size
  by (auto simp add: word_ubin.eq_norm nth_bintr nth_2p_bin)

lemmas test_bit_2p = refl [THEN test_bit_2p', unfolded word_size]

lemma nth_w2p:
  "((2\<Colon>'a\<Colon>len word) ^ n) !! m \<longleftrightarrow> m = n \<and> m < len_of TYPE('a\<Colon>len)"
  unfolding test_bit_2p [symmetric] word_of_int [symmetric]
  by (simp add:  of_int_power)

lemma uint_2p: 
  "(0::'a::len word) < 2 ^ n \<Longrightarrow> uint (2 ^ n::'a::len word) = 2 ^ n"
  apply (unfold word_arith_power_alt)
  apply (case_tac "len_of TYPE ('a)")
   apply clarsimp
  apply (case_tac "nat")
   apply clarsimp
   apply (case_tac "n")
    apply (clarsimp simp add : word_1_wi [symmetric])
   apply (clarsimp simp add : word_0_wi [symmetric])
  apply (drule word_gt_0 [THEN iffD1])
  apply (safe intro!: word_eqI bin_nth_lem ext)
     apply (auto simp add: test_bit_2p nth_2p_bin word_test_bit_def [symmetric])
  done

lemma word_of_int_2p: "(word_of_int (2 ^ n) :: 'a :: len word) = 2 ^ n" 
  apply (unfold word_arith_power_alt)
  apply (case_tac "len_of TYPE ('a)")
   apply clarsimp
  apply (case_tac "nat")
   apply (rule word_ubin.norm_eq_iff [THEN iffD1]) 
   apply (rule box_equals) 
     apply (rule_tac [2] bintr_ariths (1))+ 
   apply (clarsimp simp add : number_of_is_id)
  apply simp 
  done

lemma bang_is_le: "x !! m \<Longrightarrow> 2 ^ m <= (x :: 'a :: len word)" 
  apply (rule xtr3) 
  apply (rule_tac [2] y = "x" in le_word_or2)
  apply (rule word_eqI)
  apply (auto simp add: word_ao_nth nth_w2p word_size)
  done

lemma word_clr_le: 
  fixes w :: "'a::len0 word"
  shows "w >= set_bit w n False"
  apply (unfold word_set_bit_def word_le_def word_ubin.eq_norm)
  apply simp
  apply (rule order_trans)
   apply (rule bintr_bin_clr_le)
  apply simp
  done

lemma word_set_ge: 
  fixes w :: "'a::len word"
  shows "w <= set_bit w n True"
  apply (unfold word_set_bit_def word_le_def word_ubin.eq_norm)
  apply simp
  apply (rule order_trans [OF _ bintr_bin_set_ge])
  apply simp
  done


subsection {* Shifting, Rotating, and Splitting Words *}

lemma shiftl1_number [simp] :
  "shiftl1 (number_of w) = number_of (w BIT 0)"
  apply (unfold shiftl1_def word_number_of_def)
  apply (simp add: word_ubin.norm_eq_iff [symmetric] word_ubin.eq_norm
              del: BIT_simps)
  apply (subst refl [THEN bintrunc_BIT_I, symmetric])
  apply (subst bintrunc_bintrunc_min)
  apply simp
  done

lemma shiftl1_0 [simp] : "shiftl1 0 = 0"
  unfolding word_0_no shiftl1_number by auto

lemmas shiftl1_def_u = shiftl1_def [folded word_number_of_def]

lemma shiftl1_def_s: "shiftl1 w = number_of (sint w BIT 0)"
  by (rule trans [OF _ shiftl1_number]) simp

lemma shiftr1_0 [simp] : "shiftr1 0 = 0"
  unfolding shiftr1_def 
  by simp (simp add: word_0_wi)

lemma sshiftr1_0 [simp] : "sshiftr1 0 = 0"
  apply (unfold sshiftr1_def)
  apply simp
  apply (simp add : word_0_wi)
  done

lemma sshiftr1_n1 [simp] : "sshiftr1 -1 = -1"
  unfolding sshiftr1_def by auto

lemma shiftl_0 [simp] : "(0::'a::len0 word) << n = 0"
  unfolding shiftl_def by (induct n) auto

lemma shiftr_0 [simp] : "(0::'a::len0 word) >> n = 0"
  unfolding shiftr_def by (induct n) auto

lemma sshiftr_0 [simp] : "0 >>> n = 0"
  unfolding sshiftr_def by (induct n) auto

lemma sshiftr_n1 [simp] : "-1 >>> n = -1"
  unfolding sshiftr_def by (induct n) auto

lemma nth_shiftl1: "shiftl1 w !! n = (n < size w & n > 0 & w !! (n - 1))"
  apply (unfold shiftl1_def word_test_bit_def)
  apply (simp add: nth_bintr word_ubin.eq_norm word_size)
  apply (cases n)
   apply auto
  done

lemma nth_shiftl' [rule_format]:
  "ALL n. ((w::'a::len0 word) << m) !! n = (n < size w & n >= m & w !! (n - m))"
  apply (unfold shiftl_def)
  apply (induct "m")
   apply (force elim!: test_bit_size)
  apply (clarsimp simp add : nth_shiftl1 word_size)
  apply arith
  done

lemmas nth_shiftl = nth_shiftl' [unfolded word_size] 

lemma nth_shiftr1: "shiftr1 w !! n = w !! Suc n"
  apply (unfold shiftr1_def word_test_bit_def)
  apply (simp add: nth_bintr word_ubin.eq_norm)
  apply safe
  apply (drule bin_nth.Suc [THEN iffD2, THEN bin_nth_uint_imp])
  apply simp
  done

lemma nth_shiftr: 
  "\<And>n. ((w::'a::len0 word) >> m) !! n = w !! (n + m)"
  apply (unfold shiftr_def)
  apply (induct "m")
   apply (auto simp add : nth_shiftr1)
  done
   
(* see paper page 10, (1), (2), shiftr1_def is of the form of (1),
  where f (ie bin_rest) takes normal arguments to normal results,
  thus we get (2) from (1) *)

lemma uint_shiftr1: "uint (shiftr1 w) = bin_rest (uint w)" 
  apply (unfold shiftr1_def word_ubin.eq_norm bin_rest_trunc_i)
  apply (subst bintr_uint [symmetric, OF order_refl])
  apply (simp only : bintrunc_bintrunc_l)
  apply simp 
  done

lemma nth_sshiftr1: 
  "sshiftr1 w !! n = (if n = size w - 1 then w !! n else w !! Suc n)"
  apply (unfold sshiftr1_def word_test_bit_def)
  apply (simp add: nth_bintr word_ubin.eq_norm
                   bin_nth.Suc [symmetric] word_size 
             del: bin_nth.simps)
  apply (simp add: nth_bintr uint_sint del : bin_nth.simps)
  apply (auto simp add: bin_nth_sint)
  done

lemma nth_sshiftr [rule_format] : 
  "ALL n. sshiftr w m !! n = (n < size w & 
    (if n + m >= size w then w !! (size w - 1) else w !! (n + m)))"
  apply (unfold sshiftr_def)
  apply (induct_tac "m")
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
  apply (unfold shiftr1_def bin_rest_def)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num pos_imp_zdiv_nonneg_iff)
  apply (rule xtr7)
   prefer 2
   apply (rule zdiv_le_dividend)
    apply auto
  done

lemma sshiftr1_div_2: "sint (sshiftr1 w) = sint w div 2"
  apply (unfold sshiftr1_def bin_rest_def [symmetric])
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
  apply (induct "n")
   apply simp
  apply (simp add: shiftr1_div_2 mult_commute
                   zdiv_zmult2_eq [symmetric])
  done

lemma sshiftr_div_2n: "sint (sshiftr w n) = sint w div 2 ^ n"
  apply (unfold sshiftr_def)
  apply (induct "n")
   apply simp
  apply (simp add: sshiftr1_div_2 mult_commute
                   zdiv_zmult2_eq [symmetric])
  done

subsubsection "shift functions in terms of lists of bools"

lemmas bshiftr1_no_bin [simp] = 
  bshiftr1_def [where w="number_of w", unfolded to_bl_no_bin] for w

lemma bshiftr1_bl: "to_bl (bshiftr1 b w) = b # butlast (to_bl w)"
  unfolding bshiftr1_def by (rule word_bl.Abs_inverse) simp

lemma shiftl1_of_bl: "shiftl1 (of_bl bl) = of_bl (bl @ [False])"
  unfolding uint_bl of_bl_no 
  by (simp add: bl_to_bin_aux_append bl_to_bin_def)

lemma shiftl1_bl: "shiftl1 (w::'a::len0 word) = of_bl (to_bl w @ [False])"
proof -
  have "shiftl1 w = shiftl1 (of_bl (to_bl w))" by simp
  also have "\<dots> = of_bl (to_bl w @ [False])" by (rule shiftl1_of_bl)
  finally show ?thesis .
qed

lemma bl_shiftl1:
  "to_bl (shiftl1 (w :: 'a :: len word)) = tl (to_bl w) @ [False]"
  apply (simp add: shiftl1_bl word_rep_drop drop_Suc drop_Cons')
  apply (fast intro!: Suc_leI)
  done

(* Generalized version of bl_shiftl1. Maybe this one should replace it? *)
lemma bl_shiftl1':
  "to_bl (shiftl1 w) = tl (to_bl w @ [False])"
  unfolding shiftl1_bl
  by (simp add: word_rep_drop drop_Suc del: drop_append)

lemma shiftr1_bl: "shiftr1 w = of_bl (butlast (to_bl w))"
  apply (unfold shiftr1_def uint_bl of_bl_def)
  apply (simp add: butlast_rest_bin word_size)
  apply (simp add: bin_rest_trunc [symmetric, unfolded One_nat_def])
  done

lemma bl_shiftr1: 
  "to_bl (shiftr1 (w :: 'a :: len word)) = False # butlast (to_bl w)"
  unfolding shiftr1_bl
  by (simp add : word_rep_drop len_gt_0 [THEN Suc_leI])

(* Generalized version of bl_shiftr1. Maybe this one should replace it? *)
lemma bl_shiftr1':
  "to_bl (shiftr1 w) = butlast (False # to_bl w)"
  apply (rule word_bl.Abs_inverse')
  apply (simp del: butlast.simps)
  apply (simp add: shiftr1_bl of_bl_def)
  done

lemma shiftl1_rev: 
  "shiftl1 w = word_reverse (shiftr1 (word_reverse w))"
  apply (unfold word_reverse_def)
  apply (rule word_bl.Rep_inverse' [symmetric])
  apply (simp add: bl_shiftl1' bl_shiftr1' word_bl.Abs_inverse)
  apply (cases "to_bl w")
   apply auto
  done

lemma shiftl_rev: 
  "shiftl w n = word_reverse (shiftr (word_reverse w) n)"
  apply (unfold shiftl_def shiftr_def)
  apply (induct "n")
   apply (auto simp add : shiftl1_rev)
  done

lemmas rev_shiftl =
  shiftl_rev [where w = "word_reverse w", simplified] for w

lemmas shiftr_rev = rev_shiftl [THEN word_rev_gal']
lemmas rev_shiftr = shiftl_rev [THEN word_rev_gal']

lemma bl_sshiftr1:
  "to_bl (sshiftr1 (w :: 'a :: len word)) = hd (to_bl w) # butlast (to_bl w)"
  apply (unfold sshiftr1_def uint_bl word_size)
  apply (simp add: butlast_rest_bin word_ubin.eq_norm)
  apply (simp add: sint_uint)
  apply (rule nth_equalityI)
   apply clarsimp
  apply clarsimp
  apply (case_tac i)
   apply (simp_all add: hd_conv_nth length_0_conv [symmetric]
                        nth_bin_to_bl bin_nth.Suc [symmetric] 
                        nth_sbintr 
                   del: bin_nth.Suc)
   apply force
  apply (rule impI)
  apply (rule_tac f = "bin_nth (uint w)" in arg_cong)
  apply simp
  done

lemma drop_shiftr: 
  "drop n (to_bl ((w :: 'a :: len word) >> n)) = take (size w - n) (to_bl w)" 
  apply (unfold shiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: drop_Suc bl_shiftr1 butlast_drop [symmetric])
   apply (rule butlast_take [THEN trans])
  apply (auto simp: word_size)
  done

lemma drop_sshiftr: 
  "drop n (to_bl ((w :: 'a :: len word) >>> n)) = take (size w - n) (to_bl w)"
  apply (unfold sshiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: drop_Suc bl_sshiftr1 butlast_drop [symmetric])
   apply (rule butlast_take [THEN trans])
  apply (auto simp: word_size)
  done

lemma take_shiftr:
  "n \<le> size w \<Longrightarrow> take n (to_bl (w >> n)) = replicate n False"
  apply (unfold shiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: bl_shiftr1' length_0_conv [symmetric] word_size)
   apply (rule take_butlast [THEN trans])
  apply (auto simp: word_size)
  done

lemma take_sshiftr' [rule_format] :
  "n <= size (w :: 'a :: len word) --> hd (to_bl (w >>> n)) = hd (to_bl w) & 
    take n (to_bl (w >>> n)) = replicate n (hd (to_bl w))" 
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
  unfolding shiftl_def
  by (induct n) (auto simp: shiftl1_of_bl replicate_app_Cons_same)

lemma shiftl_bl:
  "(w::'a::len0 word) << (n::nat) = of_bl (to_bl w @ replicate n False)"
proof -
  have "w << n = of_bl (to_bl w) << n" by simp
  also have "\<dots> = of_bl (to_bl w @ replicate n False)" by (rule shiftl_of_bl)
  finally show ?thesis .
qed

lemmas shiftl_number [simp] = shiftl_def [where w="number_of w"] for w

lemma bl_shiftl:
  "to_bl (w << n) = drop n (to_bl w) @ replicate (min (size w) n) False"
  by (simp add: shiftl_bl word_rep_drop word_size)

lemma shiftl_zero_size: 
  fixes x :: "'a::len0 word"
  shows "size x <= n \<Longrightarrow> x << n = 0"
  apply (unfold word_size)
  apply (rule word_eqI)
  apply (clarsimp simp add: shiftl_bl word_size test_bit_of_bl nth_append)
  done

(* note - the following results use 'a :: len word < number_ring *)

lemma shiftl1_2t: "shiftl1 (w :: 'a :: len word) = 2 * w"
  apply (simp add: shiftl1_def_u)
  apply (simp only:  double_number_of_Bit0 [symmetric])
  apply simp
  done

lemma shiftl1_p: "shiftl1 (w :: 'a :: len word) = w + w"
  apply (simp add: shiftl1_def_u)
  apply (simp only: double_number_of_Bit0 [symmetric])
  apply simp
  done

lemma shiftl_t2n: "shiftl (w :: 'a :: len word) n = 2 ^ n * w"
  unfolding shiftl_def 
  by (induct n) (auto simp: shiftl1_2t)

lemma shiftr1_bintr [simp]:
  "(shiftr1 (number_of w) :: 'a :: len0 word) = 
    number_of (bin_rest (bintrunc (len_of TYPE ('a)) w))" 
  unfolding shiftr1_def word_number_of_def
  by (simp add : word_ubin.eq_norm)

lemma sshiftr1_sbintr [simp] :
  "(sshiftr1 (number_of w) :: 'a :: len word) = 
    number_of (bin_rest (sbintrunc (len_of TYPE ('a) - 1) w))" 
  unfolding sshiftr1_def word_number_of_def
  by (simp add : word_sbin.eq_norm)

lemma shiftr_no': 
  "w = number_of bin \<Longrightarrow> 
  (w::'a::len0 word) >> n = number_of ((bin_rest ^^ n) (bintrunc (size w) bin))"
  apply clarsimp
  apply (rule word_eqI)
  apply (auto simp: nth_shiftr nth_rest_power_bin nth_bintr word_size)
  done

lemma sshiftr_no': 
  "w = number_of bin \<Longrightarrow> w >>> n = number_of ((bin_rest ^^ n) 
    (sbintrunc (size w - 1) bin))"
  apply clarsimp
  apply (rule word_eqI)
  apply (auto simp: nth_sshiftr nth_rest_power_bin nth_sbintr word_size)
   apply (subgoal_tac "na + n = len_of TYPE('a) - Suc 0", simp, simp)+
  done

lemmas sshiftr_no [simp] = 
  sshiftr_no' [where w = "number_of w", OF refl, unfolded word_size] for w

lemmas shiftr_no [simp] = 
  shiftr_no' [where w = "number_of w", OF refl, unfolded word_size] for w

lemma shiftr1_bl_of': 
  "us = shiftr1 (of_bl bl) \<Longrightarrow> length bl <= size us \<Longrightarrow> 
    us = of_bl (butlast bl)"
  by (clarsimp simp: shiftr1_def of_bl_def word_size butlast_rest_bl2bin 
                     word_ubin.eq_norm trunc_bl2bin)

lemmas shiftr1_bl_of = refl [THEN shiftr1_bl_of', unfolded word_size]

lemma shiftr_bl_of' [rule_format]: 
  "us = of_bl bl >> n \<Longrightarrow> length bl <= size us --> 
   us = of_bl (take (length bl - n) bl)"
  apply (unfold shiftr_def)
  apply hypsubst
  apply (unfold word_size)
  apply (induct n)
   apply clarsimp
  apply clarsimp
  apply (subst shiftr1_bl_of)
   apply simp
  apply (simp add: butlast_take)
  done

lemmas shiftr_bl_of = refl [THEN shiftr_bl_of', unfolded word_size]

lemmas shiftr_bl = word_bl_Rep' [THEN eq_imp_le, THEN shiftr_bl_of,
  simplified word_size, simplified, THEN eq_reflection]

lemma msb_shift': "msb (w::'a::len word) <-> (w >> (size w - 1)) ~= 0"
  apply (unfold shiftr_bl word_msb_alt)
  apply (simp add: word_size Suc_le_eq take_Suc)
  apply (cases "hd (to_bl w)")
   apply (auto simp: word_1_bl
                     of_bl_rep_False [where n=1 and bs="[]", simplified])
  done

lemmas msb_shift = msb_shift' [unfolded word_size]

lemma align_lem_or [rule_format] :
  "ALL x m. length x = n + m --> length y = n + m --> 
    drop m x = replicate n False --> take m y = replicate m False --> 
    map2 op | x y = take m x @ drop m y"
  apply (induct_tac y)
   apply force
  apply clarsimp
  apply (case_tac x, force)
  apply (case_tac m, auto)
  apply (drule sym)
  apply auto
  apply (induct_tac list, auto)
  done

lemma align_lem_and [rule_format] :
  "ALL x m. length x = n + m --> length y = n + m --> 
    drop m x = replicate n False --> take m y = replicate m False --> 
    map2 op & x y = replicate (n + m) False"
  apply (induct_tac y)
   apply force
  apply clarsimp
  apply (case_tac x, force)
  apply (case_tac m, auto)
  apply (drule sym)
  apply auto
  apply (induct_tac list, auto)
  done

lemma aligned_bl_add_size':
  "size x - n = m \<Longrightarrow> n <= size x \<Longrightarrow> drop m (to_bl x) = replicate n False \<Longrightarrow>
    take m (to_bl y) = replicate m False \<Longrightarrow> 
    to_bl (x + y) = take m (to_bl x) @ drop m (to_bl y)"
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

lemmas aligned_bl_add_size = refl [THEN aligned_bl_add_size']

subsubsection "Mask"

lemma nth_mask': "m = mask n \<Longrightarrow> test_bit m i = (i < n & i < size m)"
  apply (unfold mask_def test_bit_bl)
  apply (simp only: word_1_bl [symmetric] shiftl_of_bl)
  apply (clarsimp simp add: word_size)
  apply (simp only: of_bl_no mask_lem number_of_succ add_diff_cancel2)
  apply (fold of_bl_no)
  apply (simp add: word_1_bl)
  apply (rule test_bit_of_bl [THEN trans, unfolded test_bit_bl word_size])
  apply auto
  done

lemmas nth_mask [simp] = refl [THEN nth_mask']

lemma mask_bl: "mask n = of_bl (replicate n True)"
  by (auto simp add : test_bit_of_bl word_size intro: word_eqI)

lemma mask_bin: "mask n = number_of (bintrunc n Int.Min)"
  by (auto simp add: nth_bintr word_size intro: word_eqI)

lemma and_mask_bintr: "w AND mask n = number_of (bintrunc n (uint w))"
  apply (rule word_eqI)
  apply (simp add: nth_bintr word_size word_ops_nth_size)
  apply (auto simp add: test_bit_bin)
  done

lemma and_mask_no: "number_of i AND mask n = number_of (bintrunc n i)" 
  by (auto simp add : nth_bintr word_size word_ops_nth_size intro: word_eqI)

lemmas and_mask_wi = and_mask_no [unfolded word_number_of_def] 

lemma bl_and_mask':
  "to_bl (w AND mask n :: 'a :: len word) = 
    replicate (len_of TYPE('a) - n) False @ 
    drop (len_of TYPE('a) - n) (to_bl w)"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp add: to_bl_nth word_size)
  apply (simp add: word_size word_ops_nth_size)
  apply (auto simp add: word_size test_bit_bl nth_append nth_rev)
  done

lemmas and_mask_mod_2p = 
  and_mask_bintr [unfolded word_number_of_alt no_bintr_alt]

lemma and_mask_lt_2p: "uint (w AND mask n) < 2 ^ n"
  apply (simp add : and_mask_bintr no_bintr_alt)
  apply (rule xtr8)
   prefer 2
   apply (rule pos_mod_bound)
  apply auto
  done

lemmas eq_mod_iff = trans [symmetric, OF int_mod_lem eq_sym_conv]

lemma mask_eq_iff: "(w AND mask n) = w <-> uint w < 2 ^ n"
  apply (simp add: and_mask_bintr word_number_of_def)
  apply (simp add: word_ubin.inverse_norm)
  apply (simp add: eq_mod_iff bintrunc_mod2p min_def)
  apply (fast intro!: lt2p_lem)
  done

lemma and_mask_dvd: "2 ^ n dvd uint w = (w AND mask n = 0)"
  apply (simp add: dvd_eq_mod_eq_0 and_mask_mod_2p)
  apply (simp add: word_uint.norm_eq_iff [symmetric] word_of_int_homs)
  apply (subst word_uint.norm_Rep [symmetric])
  apply (simp only: bintrunc_bintrunc_min bintrunc_mod2p [symmetric] min_def)
  apply auto
  done

lemma and_mask_dvd_nat: "2 ^ n dvd unat w = (w AND mask n = 0)"
  apply (unfold unat_def)
  apply (rule trans [OF _ and_mask_dvd])
  apply (unfold dvd_def) 
  apply auto 
  apply (drule uint_ge_0 [THEN nat_int.Abs_inverse' [simplified], symmetric])
  apply (simp add : int_mult int_power)
  apply (simp add : nat_mult_distrib nat_power_eq)
  done

lemma word_2p_lem: 
  "n < size w \<Longrightarrow> w < 2 ^ n = (uint (w :: 'a :: len word) < 2 ^ n)"
  apply (unfold word_size word_less_alt word_number_of_alt)
  apply (clarsimp simp add: word_of_int_power_hom word_uint.eq_norm 
                            int_mod_eq'
                  simp del: word_of_int_bin)
  done

lemma less_mask_eq: "x < 2 ^ n \<Longrightarrow> x AND mask n = (x :: 'a :: len word)"
  apply (unfold word_less_alt word_number_of_alt)
  apply (clarsimp simp add: and_mask_mod_2p word_of_int_power_hom 
                            word_uint.eq_norm
                  simp del: word_of_int_bin)
  apply (drule xtr8 [rotated])
  apply (rule int_mod_le)
  apply (auto simp add : mod_pos_pos_trivial)
  done

lemmas mask_eq_iff_w2p = trans [OF mask_eq_iff word_2p_lem [symmetric]]

lemmas and_mask_less' = iffD2 [OF word_2p_lem and_mask_lt_2p, simplified word_size]

lemma and_mask_less_size: "n < size x \<Longrightarrow> x AND mask n < 2^n"
  unfolding word_size by (erule and_mask_less')

lemma word_mod_2p_is_mask':
  "c = 2 ^ n \<Longrightarrow> c > 0 \<Longrightarrow> x mod c = (x :: 'a :: len word) AND mask n" 
  by (clarsimp simp add: word_mod_def uint_2p and_mask_mod_2p) 

lemmas word_mod_2p_is_mask = refl [THEN word_mod_2p_is_mask'] 

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
  by (auto simp: and_mask_wi bintr_ariths bintr_arith1s new_word_of_int_homs)

lemma mask_power_eq:
  "(x AND mask n) ^ k AND mask n = x ^ k AND mask n"
  using word_of_int_Ex [where x=x]
  by (clarsimp simp: and_mask_wi word_of_int_power_hom bintr_ariths)


subsubsection "Revcast"

lemmas revcast_def' = revcast_def [simplified]
lemmas revcast_def'' = revcast_def' [simplified word_size]
lemmas revcast_no_def [simp] = revcast_def' [where w="number_of w", unfolded word_size] for w

lemma to_bl_revcast: 
  "to_bl (revcast w :: 'a :: len0 word) = 
   takefill False (len_of TYPE ('a)) (to_bl w)"
  apply (unfold revcast_def' word_size)
  apply (rule word_bl.Abs_inverse)
  apply simp
  done

lemma revcast_rev_ucast': 
  "cs = [rc, uc] \<Longrightarrow> rc = revcast (word_reverse w) \<Longrightarrow> uc = ucast w \<Longrightarrow> 
    rc = word_reverse uc"
  apply (unfold ucast_def revcast_def' Let_def word_reverse_def)
  apply (clarsimp simp add : to_bl_of_bin takefill_bintrunc)
  apply (simp add : word_bl.Abs_inverse word_size)
  done

lemmas revcast_rev_ucast = revcast_rev_ucast' [OF refl refl refl]

lemmas revcast_ucast = revcast_rev_ucast
  [where w = "word_reverse w", simplified word_rev_rev] for w

lemmas ucast_revcast = revcast_rev_ucast [THEN word_rev_gal']
lemmas ucast_rev_revcast = revcast_ucast [THEN word_rev_gal']


-- "linking revcast and cast via shift"

lemmas wsst_TYs = source_size target_size word_size

lemma revcast_down_uu': 
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> 
    rc (w :: 'a :: len word) = ucast (w >> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule ucast_down_drop)
   prefer 2
   apply (rule trans, rule drop_shiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_us': 
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> 
    rc (w :: 'a :: len word) = ucast (w >>> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule ucast_down_drop)
   prefer 2
   apply (rule trans, rule drop_sshiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_su': 
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> 
    rc (w :: 'a :: len word) = scast (w >> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule scast_down_drop)
   prefer 2
   apply (rule trans, rule drop_shiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_ss': 
  "rc = revcast \<Longrightarrow> source_size rc = target_size rc + n \<Longrightarrow> 
    rc (w :: 'a :: len word) = scast (w >>> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule scast_down_drop)
   prefer 2
   apply (rule trans, rule drop_sshiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemmas revcast_down_uu = refl [THEN revcast_down_uu']
lemmas revcast_down_us = refl [THEN revcast_down_us']
lemmas revcast_down_su = refl [THEN revcast_down_su']
lemmas revcast_down_ss = refl [THEN revcast_down_ss']

lemma cast_down_rev: 
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow> 
    uc w = revcast ((w :: 'a :: len word) << n)"
  apply (unfold shiftl_rev)
  apply clarify
  apply (simp add: revcast_rev_ucast)
  apply (rule word_rev_gal')
  apply (rule trans [OF _ revcast_rev_ucast])
  apply (rule revcast_down_uu [symmetric])
  apply (auto simp add: wsst_TYs)
  done

lemma revcast_up': 
  "rc = revcast \<Longrightarrow> source_size rc + n = target_size rc \<Longrightarrow> 
    rc w = (ucast w :: 'a :: len word) << n" 
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (simp add: takefill_alt)
  apply (rule bl_shiftl [THEN trans])
  apply (subst ucast_up_app)
  apply (auto simp add: wsst_TYs)
  done

lemmas revcast_up = refl [THEN revcast_up']

lemmas rc1 = revcast_up [THEN 
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]
lemmas rc2 = revcast_down_uu [THEN 
  revcast_rev_ucast [symmetric, THEN trans, THEN word_rev_gal, symmetric]]

lemmas ucast_up =
 rc1 [simplified rev_shiftr [symmetric] revcast_ucast [symmetric]]
lemmas ucast_down = 
  rc2 [simplified rev_shiftr revcast_ucast [symmetric]]


subsubsection "Slices"

lemma slice1_no_bin [simp]:
  "slice1 n (number_of w :: 'b word) = of_bl (takefill False n (bin_to_bl (len_of TYPE('b :: len0)) w))"
  by (simp add: slice1_def)

lemma slice_no_bin [simp]:
  "slice n (number_of w :: 'b word) = of_bl (takefill False (len_of TYPE('b :: len0) - n)
    (bin_to_bl (len_of TYPE('b :: len0)) w))"
  by (simp add: slice_def word_size)

lemma slice1_0 [simp] : "slice1 n 0 = 0"
  unfolding slice1_def by simp

lemma slice_0 [simp] : "slice n 0 = 0"
  unfolding slice_def by auto

lemma slice_take': "slice n w = of_bl (take (size w - n) (to_bl w))"
  unfolding slice_def' slice1_def
  by (simp add : takefill_alt word_size)

lemmas slice_take = slice_take' [unfolded word_size]

-- "shiftr to a word of the same size is just slice, 
    slice is just shiftr then ucast"
lemmas shiftr_slice = trans [OF shiftr_bl [THEN meta_eq_to_obj_eq] slice_take [symmetric]]

lemma slice_shiftr: "slice n w = ucast (w >> n)"
  apply (unfold slice_take shiftr_bl)
  apply (rule ucast_of_bl_up [symmetric])
  apply (simp add: word_size)
  done

lemma nth_slice: 
  "(slice n w :: 'a :: len0 word) !! m = 
   (w !! (m + n) & m < len_of TYPE ('a))"
  unfolding slice_shiftr 
  by (simp add : nth_ucast nth_shiftr)

lemma slice1_down_alt': 
  "sl = slice1 n w \<Longrightarrow> fs = size sl \<Longrightarrow> fs + k = n \<Longrightarrow> 
    to_bl sl = takefill False fs (drop k (to_bl w))"
  unfolding slice1_def word_size of_bl_def uint_bl
  by (clarsimp simp: word_ubin.eq_norm bl_bin_bl_rep_drop drop_takefill)

lemma slice1_up_alt': 
  "sl = slice1 n w \<Longrightarrow> fs = size sl \<Longrightarrow> fs = n + k \<Longrightarrow> 
    to_bl sl = takefill False fs (replicate k False @ (to_bl w))"
  apply (unfold slice1_def word_size of_bl_def uint_bl)
  apply (clarsimp simp: word_ubin.eq_norm bl_bin_bl_rep_drop 
                        takefill_append [symmetric])
  apply (rule_tac f = "%k. takefill False (len_of TYPE('a))
    (replicate k False @ bin_to_bl (len_of TYPE('b)) (uint w))" in arg_cong)
  apply arith
  done
    
lemmas sd1 = slice1_down_alt' [OF refl refl, unfolded word_size]
lemmas su1 = slice1_up_alt' [OF refl refl, unfolded word_size]
lemmas slice1_down_alt = le_add_diff_inverse [THEN sd1]
lemmas slice1_up_alts = 
  le_add_diff_inverse [symmetric, THEN su1] 
  le_add_diff_inverse2 [symmetric, THEN su1]

lemma ucast_slice1: "ucast w = slice1 (size w) w"
  unfolding slice1_def ucast_bl
  by (simp add : takefill_same' word_size)

lemma ucast_slice: "ucast w = slice 0 w"
  unfolding slice_def by (simp add : ucast_slice1)

lemmas slice_id = trans [OF ucast_slice [symmetric] ucast_id]

lemma revcast_slice1': 
  "rc = revcast w \<Longrightarrow> slice1 (size rc) w = rc"
  unfolding slice1_def revcast_def' by (simp add : word_size)

lemmas revcast_slice1 = refl [THEN revcast_slice1']

lemma slice1_tf_tf': 
  "to_bl (slice1 n w :: 'a :: len0 word) = 
   rev (takefill False (len_of TYPE('a)) (rev (takefill False n (to_bl w))))"
  unfolding slice1_def by (rule word_rev_tf)

lemmas slice1_tf_tf = slice1_tf_tf' [THEN word_bl.Rep_inverse', symmetric]

lemma rev_slice1:
  "n + k = len_of TYPE('a) + len_of TYPE('b) \<Longrightarrow> 
  slice1 n (word_reverse w :: 'b :: len0 word) = 
  word_reverse (slice1 k w :: 'a :: len0 word)"
  apply (unfold word_reverse_def slice1_tf_tf)
  apply (rule word_bl.Rep_inverse')
  apply (rule rev_swap [THEN iffD1])
  apply (rule trans [symmetric])
  apply (rule tf_rev)
   apply (simp add: word_bl.Abs_inverse)
  apply (simp add: word_bl.Abs_inverse)
  done

lemma rev_slice': 
  "res = slice n (word_reverse w) \<Longrightarrow> n + k + size res = size w \<Longrightarrow> 
    res = word_reverse (slice k w)"
  apply (unfold slice_def word_size)
  apply clarify
  apply (rule rev_slice1)
  apply arith
  done

lemmas rev_slice = refl [THEN rev_slice', unfolded word_size]

lemmas sym_notr = 
  not_iff [THEN iffD2, THEN not_sym, THEN not_iff [THEN iffD1]]

-- {* problem posed by TPHOLs referee:
      criterion for overflow of addition of signed integers *}

lemma sofl_test:
  "(sint (x :: 'a :: len word) + sint y = sint (x + y)) = 
     ((((x+y) XOR x) AND ((x+y) XOR y)) >> (size x - 1) = 0)"
  apply (unfold word_size)
  apply (cases "len_of TYPE('a)", simp) 
  apply (subst msb_shift [THEN sym_notr])
  apply (simp add: word_ops_msb)
  apply (simp add: word_msb_sint)
  apply safe
       apply simp_all
     apply (unfold sint_word_ariths)
     apply (unfold word_sbin.set_iff_norm [symmetric] sints_num)
     apply safe
        apply (insert sint_range' [where x=x])
        apply (insert sint_range' [where x=y])
        defer 
        apply (simp (no_asm), arith)
       apply (simp (no_asm), arith)
      defer
      defer
      apply (simp (no_asm), arith)
     apply (simp (no_asm), arith)
    apply (rule notI [THEN notnotD],
           drule leI not_leE,
           drule sbintrunc_inc sbintrunc_dec,      
           simp)+
  done


subsection "Split and cat"

lemmas word_split_bin' = word_split_def
lemmas word_cat_bin' = word_cat_def

lemma word_rsplit_no:
  "(word_rsplit (number_of bin :: 'b :: len0 word) :: 'a word list) = 
    map number_of (bin_rsplit (len_of TYPE('a :: len)) 
      (len_of TYPE('b), bintrunc (len_of TYPE('b)) bin))"
  apply (unfold word_rsplit_def word_no_wi)
  apply (simp add: word_ubin.eq_norm)
  done

lemmas word_rsplit_no_cl [simp] = word_rsplit_no
  [unfolded bin_rsplitl_def bin_rsplit_l [symmetric]]

lemma test_bit_cat:
  "wc = word_cat a b \<Longrightarrow> wc !! n = (n < size wc & 
    (if n < size b then b !! n else a !! (n - size b)))"
  apply (unfold word_cat_bin' test_bit_bin)
  apply (auto simp add : word_ubin.eq_norm nth_bintr bin_nth_cat word_size)
  apply (erule bin_nth_uint_imp)
  done

lemma word_cat_bl: "word_cat a b = of_bl (to_bl a @ to_bl b)"
  apply (unfold of_bl_def to_bl_def word_cat_bin')
  apply (simp add: bl_to_bin_app_cat)
  done

lemma of_bl_append:
  "(of_bl (xs @ ys) :: 'a :: len word) = of_bl xs * 2^(length ys) + of_bl ys"
  apply (unfold of_bl_def)
  apply (simp add: bl_to_bin_app_cat bin_cat_num)
  apply (simp add: word_of_int_power_hom [symmetric] new_word_of_int_hom_syms)
  done

lemma of_bl_False [simp]:
  "of_bl (False#xs) = of_bl xs"
  by (rule word_eqI)
     (auto simp add: test_bit_of_bl nth_append)

lemma of_bl_True [simp]:
  "(of_bl (True#xs)::'a::len word) = 2^length xs + of_bl xs"
  by (subst of_bl_append [where xs="[True]", simplified])
     (simp add: word_1_bl)

lemma of_bl_Cons:
  "of_bl (x#xs) = of_bool x * 2^length xs + of_bl xs"
  by (cases x) simp_all

lemma split_uint_lem: "bin_split n (uint (w :: 'a :: len0 word)) = (a, b) \<Longrightarrow> 
  a = bintrunc (len_of TYPE('a) - n) a & b = bintrunc (len_of TYPE('a)) b"
  apply (frule word_ubin.norm_Rep [THEN ssubst])
  apply (drule bin_split_trunc1)
  apply (drule sym [THEN trans])
  apply assumption
  apply safe
  done

lemma word_split_bl': 
  "std = size c - size b \<Longrightarrow> (word_split c = (a, b)) \<Longrightarrow> 
    (a = of_bl (take std (to_bl c)) & b = of_bl (drop std (to_bl c)))"
  apply (unfold word_split_bin')
  apply safe
   defer
   apply (clarsimp split: prod.splits)
   apply (drule word_ubin.norm_Rep [THEN ssubst])
   apply (drule split_bintrunc)
   apply (simp add : of_bl_def bl2bin_drop word_size
       word_ubin.norm_eq_iff [symmetric] min_def del : word_ubin.norm_Rep)    
  apply (clarsimp split: prod.splits)
  apply (frule split_uint_lem [THEN conjunct1])
  apply (unfold word_size)
  apply (cases "len_of TYPE('a) >= len_of TYPE('b)")
   defer
   apply (simp add: word_0_wi_Pls)
  apply (simp add : of_bl_def to_bl_def)
  apply (subst bin_split_take1 [symmetric])
    prefer 2
    apply assumption
   apply simp
  apply (erule thin_rl)
  apply (erule arg_cong [THEN trans])
  apply (simp add : word_ubin.norm_eq_iff [symmetric])
  done

lemma word_split_bl: "std = size c - size b \<Longrightarrow> 
    (a = of_bl (take std (to_bl c)) & b = of_bl (drop std (to_bl c))) <-> 
    word_split c = (a, b)"
  apply (rule iffI)
   defer
   apply (erule (1) word_split_bl')
  apply (case_tac "word_split c")
  apply (auto simp add : word_size)
  apply (frule word_split_bl' [rotated])
  apply (auto simp add : word_size)
  done

lemma word_split_bl_eq:
   "(word_split (c::'a::len word) :: ('c :: len0 word * 'd :: len0 word)) =
      (of_bl (take (len_of TYPE('a::len) - len_of TYPE('d::len0)) (to_bl c)),
       of_bl (drop (len_of TYPE('a) - len_of TYPE('d)) (to_bl c)))"
  apply (rule word_split_bl [THEN iffD1])
  apply (unfold word_size)
  apply (rule refl conjI)+
  done

-- "keep quantifiers for use in simplification"
lemma test_bit_split':
  "word_split c = (a, b) --> (ALL n m. b !! n = (n < size b & c !! n) & 
    a !! m = (m < size a & c !! (m + size b)))"
  apply (unfold word_split_bin' test_bit_bin)
  apply (clarify)
  apply (clarsimp simp: word_ubin.eq_norm nth_bintr word_size split: prod.splits)
  apply (drule bin_nth_split)
  apply safe
       apply (simp_all add: add_commute)
   apply (erule bin_nth_uint_imp)+
  done

lemma test_bit_split:
  "word_split c = (a, b) \<Longrightarrow>
    (\<forall>n\<Colon>nat. b !! n \<longleftrightarrow> n < size b \<and> c !! n) \<and> (\<forall>m\<Colon>nat. a !! m \<longleftrightarrow> m < size a \<and> c !! (m + size b))"
  by (simp add: test_bit_split')

lemma test_bit_split_eq: "word_split c = (a, b) <-> 
  ((ALL n::nat. b !! n = (n < size b & c !! n)) &
    (ALL m::nat. a !! m = (m < size a & c !! (m + size b))))"
  apply (rule_tac iffI)
   apply (rule_tac conjI)
    apply (erule test_bit_split [THEN conjunct1])
   apply (erule test_bit_split [THEN conjunct2])
  apply (case_tac "word_split c")
  apply (frule test_bit_split)
  apply (erule trans)
  apply (fastforce intro ! : word_eqI simp add : word_size)
  done

-- {* this odd result is analogous to @{text "ucast_id"}, 
      result to the length given by the result type *}

lemma word_cat_id: "word_cat a b = b"
  unfolding word_cat_bin' by (simp add: word_ubin.inverse_norm)

-- "limited hom result"
lemma word_cat_hom:
  "len_of TYPE('a::len0) <= len_of TYPE('b::len0) + len_of TYPE ('c::len0)
  \<Longrightarrow>
  (word_cat (word_of_int w :: 'b word) (b :: 'c word) :: 'a word) = 
  word_of_int (bin_cat w (size b) (uint b))"
  apply (unfold word_cat_def word_size) 
  apply (clarsimp simp add: word_ubin.norm_eq_iff [symmetric]
      word_ubin.eq_norm bintr_cat min_max.inf_absorb1)
  done

lemma word_cat_split_alt:
  "size w <= size u + size v \<Longrightarrow> word_split w = (u, v) \<Longrightarrow> word_cat u v = w"
  apply (rule word_eqI)
  apply (drule test_bit_split)
  apply (clarsimp simp add : test_bit_cat word_size)
  apply safe
  apply arith
  done

lemmas word_cat_split_size = sym [THEN [2] word_cat_split_alt [symmetric]]


subsubsection "Split and slice"

lemma split_slices: 
  "word_split w = (u, v) \<Longrightarrow> u = slice (size v) w & v = slice 0 w"
  apply (drule test_bit_split)
  apply (rule conjI)
   apply (rule word_eqI, clarsimp simp: nth_slice word_size)+
  done

lemma slice_cat1':
  "wc = word_cat a b \<Longrightarrow> size wc >= size a + size b \<Longrightarrow> slice (size b) wc = a"
  apply safe
  apply (rule word_eqI)
  apply (simp add: nth_slice test_bit_cat word_size)
  done

lemmas slice_cat1 = refl [THEN slice_cat1']
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
  "w = word_cat u v \<Longrightarrow> size u + size v <= size w \<Longrightarrow> word_split w = (u, v)"
  apply (case_tac "word_split ?w")
  apply (rule trans, assumption)
  apply (drule test_bit_split)
  apply safe
   apply (rule word_eqI, clarsimp simp: test_bit_cat word_size)+
  done

lemmas word_cat_bl_no_bin [simp] =
  word_cat_bl [where a="number_of a" 
                 and b="number_of b", 
               unfolded to_bl_no_bin]
  for a b

lemmas word_split_bl_no_bin [simp] =
  word_split_bl_eq [where c="number_of c", unfolded to_bl_no_bin] for c

-- {* this odd result arises from the fact that the statement of the
      result implies that the decoded words are of the same type, 
      and therefore of the same length, as the original word *}

lemma word_rsplit_same: "word_rsplit w = [w]"
  unfolding word_rsplit_def by (simp add : bin_rsplit_all)

lemma word_rsplit_empty_iff_size:
  "(word_rsplit w = []) = (size w = 0)" 
  unfolding word_rsplit_def bin_rsplit_def word_size
  by (simp add: bin_rsplit_aux_simp_alt Let_def split: Product_Type.split_split)

lemma test_bit_rsplit:
  "sw = word_rsplit w \<Longrightarrow> m < size (hd sw :: 'a :: len word) \<Longrightarrow> 
    k < length sw \<Longrightarrow> (rev sw ! k) !! m = (w !! (k * size (hd sw) + m))"
  apply (unfold word_rsplit_def word_test_bit_def)
  apply (rule trans)
   apply (rule_tac f = "%x. bin_nth x m" in arg_cong)
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
  unfolding word_rcat_def to_bl_def' of_bl_def
  by (clarsimp simp add : bin_rcat_bl)

lemma size_rcat_lem':
  "size (concat (map to_bl wl)) = length wl * size (hd wl)"
  unfolding word_size by (induct wl) auto

lemmas size_rcat_lem = size_rcat_lem' [unfolded word_size]

lemmas td_gal_lt_len = len_gt_0 [THEN td_gal_lt]

lemma nth_rcat_lem' [rule_format] :
  "sw = size (hd wl  :: 'a :: len word) \<Longrightarrow> (ALL n. n < size wl * sw --> 
    rev (concat (map to_bl wl)) ! n = 
    rev (to_bl (rev wl ! (n div sw))) ! (n mod sw))"
  apply (unfold word_size)
  apply (induct "wl")
   apply clarsimp
  apply (clarsimp simp add : nth_append size_rcat_lem)
  apply (simp (no_asm_use) only:  mult_Suc [symmetric] 
         td_gal_lt_len less_Suc_eq_le mod_div_equality')
  apply clarsimp
  done

lemmas nth_rcat_lem = refl [THEN nth_rcat_lem', unfolded word_size]

lemma test_bit_rcat:
  "sw = size (hd wl :: 'a :: len word) \<Longrightarrow> rc = word_rcat wl \<Longrightarrow> rc !! n = 
    (n < size rc & n div sw < size wl & (rev wl) ! (n div sw) !! (n mod sw))"
  apply (unfold word_rcat_bl word_size)
  apply (clarsimp simp add : 
    test_bit_of_bl size_rcat_lem word_size td_gal_lt_len)
  apply safe
   apply (auto simp add : 
    test_bit_bl word_size td_gal_lt_len [THEN iffD2, THEN nth_rcat_lem])
  done

lemma foldl_eq_foldr [rule_format] :
  "ALL x. foldl op + x xs = foldr op + (x # xs) (0 :: 'a :: comm_monoid_add)" 
  by (induct xs) (auto simp add : add_assoc)

lemmas test_bit_cong = arg_cong [where f = "test_bit", THEN fun_cong]

lemmas test_bit_rsplit_alt = 
  trans [OF nth_rev_alt [THEN test_bit_cong] 
  test_bit_rsplit [OF refl asm_rl diff_Suc_less]]

-- "lazy way of expressing that u and v, and su and sv, have same types"
lemma word_rsplit_len_indep':
  "[u,v] = p \<Longrightarrow> [su,sv] = q \<Longrightarrow> word_rsplit u = su \<Longrightarrow> 
    word_rsplit v = sv \<Longrightarrow> length su = length sv"
  apply (unfold word_rsplit_def)
  apply (auto simp add : bin_rsplit_len_indep)
  done

lemmas word_rsplit_len_indep = word_rsplit_len_indep' [OF refl refl refl refl]

lemma length_word_rsplit_size: 
  "n = len_of TYPE ('a :: len) \<Longrightarrow> 
    (length (word_rsplit w :: 'a word list) <= m) = (size w <= m * n)"
  apply (unfold word_rsplit_def word_size)
  apply (clarsimp simp add : bin_rsplit_len_le)
  done

lemmas length_word_rsplit_lt_size = 
  length_word_rsplit_size [unfolded Not_eq_iff linorder_not_less [symmetric]]

lemma length_word_rsplit_exp_size: 
  "n = len_of TYPE ('a :: len) \<Longrightarrow> 
    length (word_rsplit w :: 'a word list) = (size w + n - 1) div n"
  unfolding word_rsplit_def by (clarsimp simp add : word_size bin_rsplit_len)

lemma length_word_rsplit_even_size: 
  "n = len_of TYPE ('a :: len) \<Longrightarrow> size w = m * n \<Longrightarrow> 
    length (word_rsplit w :: 'a word list) = m"
  by (clarsimp simp add : length_word_rsplit_exp_size given_quot_alt)

lemmas length_word_rsplit_exp_size' = refl [THEN length_word_rsplit_exp_size]

(* alternative proof of word_rcat_rsplit *)
lemmas tdle = iffD2 [OF split_div_lemma refl, THEN conjunct1] 
lemmas dtle = xtr4 [OF tdle mult_commute]

lemma word_rcat_rsplit: "word_rcat (word_rsplit w) = w"
  apply (rule word_eqI)
  apply (clarsimp simp add : test_bit_rcat word_size)
  apply (subst refl [THEN test_bit_rsplit])
    apply (simp_all add: word_size 
      refl [THEN length_word_rsplit_size [simplified not_less [symmetric], simplified]])
   apply safe
   apply (erule xtr7, rule len_gt_0 [THEN dtle])+
  done

lemma size_word_rsplit_rcat_size':
  "word_rcat (ws :: 'a :: len word list) = frcw \<Longrightarrow> 
    size frcw = length ws * len_of TYPE ('a) \<Longrightarrow> 
    size (hd [word_rsplit frcw, ws]) = size ws" 
  apply (clarsimp simp add : word_size length_word_rsplit_exp_size')
  apply (fast intro: given_quot_alt)
  done

lemmas size_word_rsplit_rcat_size = 
  size_word_rsplit_rcat_size' [simplified]

lemma msrevs:
  fixes n::nat
  shows "0 < n \<Longrightarrow> (k * n + m) div n = m div n + k"
  and   "(k * n + m) mod n = m mod n"
  by (auto simp: add_commute)

lemma word_rsplit_rcat_size':
  "word_rcat (ws :: 'a :: len word list) = frcw \<Longrightarrow> 
    size frcw = length ws * len_of TYPE ('a) \<Longrightarrow> word_rsplit frcw = ws" 
  apply (frule size_word_rsplit_rcat_size, assumption)
  apply (clarsimp simp add : word_size)
  apply (rule nth_equalityI, assumption)
  apply clarsimp
  apply (rule word_eqI)
  apply (rule trans)
   apply (rule test_bit_rsplit_alt)
     apply (clarsimp simp: word_size)+
  apply (rule trans)
  apply (rule test_bit_rcat [OF refl refl])
  apply (simp add: word_size msrevs)
  apply (subst nth_rev)
   apply arith
  apply (simp add: le0 [THEN [2] xtr7, THEN diff_Suc_less])
  apply safe
  apply (simp add: diff_mult_distrib)
  apply (rule mpl_lem)
  apply (cases "size ws")
   apply simp_all
  done

lemmas word_rsplit_rcat_size = refl [THEN word_rsplit_rcat_size']


subsection "Rotation"

lemmas rotater_0' [simp] = rotater_def [where n = "0", simplified]

lemmas word_rot_defs = word_roti_def word_rotr_def word_rotl_def

lemma rotate_eq_mod: 
  "m mod length xs = n mod length xs \<Longrightarrow> rotate m xs = rotate n xs"
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


subsubsection "Rotation of list to right"

lemma rotate1_rl': "rotater1 (l @ [a]) = a # l"
  unfolding rotater1_def by (cases l) auto

lemma rotate1_rl [simp] : "rotater1 (rotate1 l) = l"
  apply (unfold rotater1_def)
  apply (cases "l")
  apply (case_tac [2] "list")
  apply auto
  done

lemma rotate1_lr [simp] : "rotate1 (rotater1 l) = l"
  unfolding rotater1_def by (cases l) auto

lemma rotater1_rev': "rotater1 (rev xs) = rev (rotate1 xs)"
  apply (cases "xs")
  apply (simp add : rotater1_def)
  apply (simp add : rotate1_rl')
  done
  
lemma rotater_rev': "rotater n (rev xs) = rev (rotate n xs)"
  unfolding rotater_def by (induct n) (auto intro: rotater1_rev')

lemmas rotater_rev = rotater_rev' [where xs = "rev ys", simplified] for ys

lemma rotater_drop_take: 
  "rotater n xs = 
   drop (length xs - n mod length xs) xs @
   take (length xs - n mod length xs) xs"
  by (clarsimp simp add : rotater_rev rotate_drop_take rev_take rev_drop)

lemma rotater_Suc [simp] : 
  "rotater (Suc n) xs = rotater1 (rotater n xs)"
  unfolding rotater_def by auto

lemma rotate_inv_plus [rule_format] :
  "ALL k. k = m + n --> rotater k (rotate n xs) = rotater m xs & 
    rotate k (rotater n xs) = rotate m xs & 
    rotater n (rotate k xs) = rotate m xs & 
    rotate n (rotater k xs) = rotater m xs"
  unfolding rotater_def rotate_def
  by (induct n) (auto intro: funpow_swap1 [THEN trans])
  
lemmas rotate_inv_rel = le_add_diff_inverse2 [symmetric, THEN rotate_inv_plus]

lemmas rotate_inv_eq = order_refl [THEN rotate_inv_rel, simplified]

lemmas rotate_lr [simp] = rotate_inv_eq [THEN conjunct1]
lemmas rotate_rl [simp] = rotate_inv_eq [THEN conjunct2, THEN conjunct1]

lemma rotate_gal: "(rotater n xs = ys) = (rotate n ys = xs)"
  by auto

lemma rotate_gal': "(ys = rotater n xs) = (xs = rotate n ys)"
  by auto

lemma length_rotater [simp]: 
  "length (rotater n xs) = length xs"
  by (simp add : rotater_rev)

lemma restrict_to_left:
  assumes "x = y"
  shows "(x = z) = (y = z)"
  using assms by simp

lemmas rrs0 = rotate_eqs [THEN restrict_to_left, 
  simplified rotate_gal [symmetric] rotate_gal' [symmetric]]
lemmas rrs1 = rrs0 [THEN refl [THEN rev_iffD1]]
lemmas rotater_eqs = rrs1 [simplified length_rotater]
lemmas rotater_0 = rotater_eqs (1)
lemmas rotater_add = rotater_eqs (2)


subsubsection "map, map2, commuting with rotate(r)"

lemma last_map: "xs ~= [] \<Longrightarrow> last (map f xs) = f (last xs)"
  by (induct xs) auto

lemma butlast_map:
  "xs ~= [] \<Longrightarrow> butlast (map f xs) = map f (butlast xs)"
  by (induct xs) auto

lemma rotater1_map: "rotater1 (map f xs) = map f (rotater1 xs)" 
  unfolding rotater1_def
  by (cases xs) (auto simp add: last_map butlast_map)

lemma rotater_map:
  "rotater n (map f xs) = map f (rotater n xs)" 
  unfolding rotater_def
  by (induct n) (auto simp add : rotater1_map)

lemma but_last_zip [rule_format] :
  "ALL ys. length xs = length ys --> xs ~= [] --> 
    last (zip xs ys) = (last xs, last ys) & 
    butlast (zip xs ys) = zip (butlast xs) (butlast ys)" 
  apply (induct "xs")
  apply auto
     apply ((case_tac ys, auto simp: neq_Nil_conv)[1])+
  done

lemma but_last_map2 [rule_format] :
  "ALL ys. length xs = length ys --> xs ~= [] --> 
    last (map2 f xs ys) = f (last xs) (last ys) & 
    butlast (map2 f xs ys) = map2 f (butlast xs) (butlast ys)" 
  apply (induct "xs")
  apply auto
     apply (unfold map2_def)
     apply ((case_tac ys, auto simp: neq_Nil_conv)[1])+
  done

lemma rotater1_zip:
  "length xs = length ys \<Longrightarrow> 
    rotater1 (zip xs ys) = zip (rotater1 xs) (rotater1 ys)" 
  apply (unfold rotater1_def)
  apply (cases "xs")
   apply auto
   apply ((case_tac ys, auto simp: neq_Nil_conv but_last_zip)[1])+
  done

lemma rotater1_map2:
  "length xs = length ys \<Longrightarrow> 
    rotater1 (map2 f xs ys) = map2 f (rotater1 xs) (rotater1 ys)" 
  unfolding map2_def by (simp add: rotater1_map rotater1_zip)

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
  apply (unfold map2_def)
  apply (cases xs)
   apply (cases ys, auto simp add : rotate1_def)+
  done

lemmas lth = box_equals [OF asm_rl length_rotate [symmetric] 
  length_rotate [symmetric], THEN rotate1_map2]

lemma rotate_map2: 
  "length xs = length ys \<Longrightarrow> 
    rotate n (map2 f xs ys) = map2 f (rotate n xs) (rotate n ys)" 
  by (induct n) (auto intro!: lth)


-- "corresponding equalities for word rotation"

lemma to_bl_rotl: 
  "to_bl (word_rotl n w) = rotate n (to_bl w)"
  by (simp add: word_bl.Abs_inverse' word_rotl_def)

lemmas blrs0 = rotate_eqs [THEN to_bl_rotl [THEN trans]]

lemmas word_rotl_eqs =
  blrs0 [simplified word_bl_Rep' word_bl.Rep_inject to_bl_rotl [symmetric]]

lemma to_bl_rotr: 
  "to_bl (word_rotr n w) = rotater n (to_bl w)"
  by (simp add: word_bl.Abs_inverse' word_rotr_def)

lemmas brrs0 = rotater_eqs [THEN to_bl_rotr [THEN trans]]

lemmas word_rotr_eqs =
  brrs0 [simplified word_bl_Rep' word_bl.Rep_inject to_bl_rotr [symmetric]]

declare word_rotr_eqs (1) [simp]
declare word_rotl_eqs (1) [simp]

lemma
  word_rot_rl [simp]:
  "word_rotl k (word_rotr k v) = v" and
  word_rot_lr [simp]:
  "word_rotr k (word_rotl k v) = v"
  by (auto simp add: to_bl_rotr to_bl_rotl word_bl.Rep_inject [symmetric])

lemma
  word_rot_gal:
  "(word_rotr n v = w) = (word_rotl n w = v)" and
  word_rot_gal':
  "(w = word_rotr n v) = (v = word_rotl n w)"
  by (auto simp: to_bl_rotr to_bl_rotl word_bl.Rep_inject [symmetric] 
           dest: sym)

lemma word_rotr_rev:
  "word_rotr n w = word_reverse (word_rotl n (word_reverse w))"
  by (simp add: word_bl.Rep_inject [symmetric] to_bl_word_rev
                to_bl_rotr to_bl_rotl rotater_rev)
  
lemma word_roti_0 [simp]: "word_roti 0 w = w"
  by (unfold word_rot_defs) auto

lemmas abl_cong = arg_cong [where f = "of_bl"]

lemma word_roti_add: 
  "word_roti (m + n) w = word_roti m (word_roti n w)"
proof -
  have rotater_eq_lem: 
    "\<And>m n xs. m = n \<Longrightarrow> rotater m xs = rotater n xs"
    by auto

  have rotate_eq_lem: 
    "\<And>m n xs. m = n \<Longrightarrow> rotate m xs = rotate n xs"
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
  apply (simp only: split: split_if)
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
    
lemma word_roti_conv_mod': "word_roti n w = word_roti (n mod int (size w)) w"
  apply (unfold word_rot_defs)
  apply (cut_tac y="size w" in gt_or_eq_0)
  apply (erule disjE)
   apply simp_all
  apply (safe intro!: abl_cong)
   apply (rule rotater_eqs)
   apply (simp add: word_size nat_mod_distrib)
  apply (simp add: rotater_add [symmetric] rotate_gal [symmetric])
  apply (rule rotater_eqs)
  apply (simp add: word_size nat_mod_distrib)
  apply (rule int_eq_0_conv [THEN iffD1])
  apply (simp only: zmod_int of_nat_add)
  apply (simp add: rdmods)
  done

lemmas word_roti_conv_mod = word_roti_conv_mod' [unfolded word_size]


subsubsection "Word rotation commutes with bit-wise operations"

(* using locale to not pollute lemma namespace *)
locale word_rotate 
begin

lemmas word_rot_defs' = to_bl_rotl to_bl_rotr

lemmas blwl_syms [symmetric] = bl_word_not bl_word_and bl_word_or bl_word_xor

lemmas lbl_lbl = trans [OF word_bl_Rep' word_bl_Rep' [symmetric]]

lemmas ths_map2 [OF lbl_lbl] = rotate_map2 rotater_map2

lemmas ths_map [where xs = "to_bl v"] = rotate_map rotater_map for v

lemmas th1s [simplified word_rot_defs' [symmetric]] = ths_map2 ths_map

lemma word_rot_logs:
  "word_rotl n (NOT v) = NOT word_rotl n v"
  "word_rotr n (NOT v) = NOT word_rotr n v"
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
  "n = nat ((- i) mod int (size (w :: 'a :: len word))) \<Longrightarrow> 
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

lemma word_rotx_0 [simp] : "word_rotr i 0 = 0 & word_rotl i 0 = 0"
  by (simp add : word_rotr_dt word_rotl_dt replicate_add [symmetric])

lemma word_roti_0' [simp] : "word_roti n 0 = 0"
  unfolding word_roti_def by auto

lemmas word_rotr_dt_no_bin' [simp] = 
  word_rotr_dt [where w="number_of w", unfolded to_bl_no_bin] for w

lemmas word_rotl_dt_no_bin' [simp] = 
  word_rotl_dt [where w="number_of w", unfolded to_bl_no_bin] for w

declare word_roti_def [simp]


subsection {* Miscellaneous  *}

lemma word_int_cases:
  "\<lbrakk>\<And>n. \<lbrakk>(x ::'a::len0 word) = word_of_int n; 0 \<le> n; n < 2^len_of TYPE('a)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (cases x rule: word_uint.Abs_cases) (simp add: uints_num)

lemma word_nat_cases [cases type: word]:
  "\<lbrakk>\<And>n. \<lbrakk>(x ::'a::len word) = of_nat n; n < 2^len_of TYPE('a)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (cases x rule: word_unat.Abs_cases) (simp add: unats_def)

lemma max_word_eq:
  "(max_word::'a::len word) = 2^len_of TYPE('a) - 1"
  by (simp add: max_word_def word_of_int_hom_syms word_of_int_2p)

lemma max_word_max [simp,intro!]:
  "n \<le> max_word"
  by (cases n rule: word_int_cases)
     (simp add: max_word_def word_le_def int_word_uint int_mod_eq')
  
lemma word_of_int_2p_len: 
  "word_of_int (2 ^ len_of TYPE('a)) = (0::'a::len0 word)"
  by (subst word_uint.Abs_norm [symmetric]) 
     (simp add: word_of_int_hom_syms)

lemma word_pow_0:
  "(2::'a::len word) ^ len_of TYPE('a) = 0"
proof -
  have "word_of_int (2 ^ len_of TYPE('a)) = (0::'a word)"
    by (rule word_of_int_2p_len)
  thus ?thesis by (simp add: word_of_int_2p)
qed

lemma max_word_wrap: "x + 1 = 0 \<Longrightarrow> x = max_word"
  apply (simp add: max_word_eq)
  apply uint_arith
  apply auto
  apply (simp add: word_pow_0)
  done

lemma max_word_minus: 
  "max_word = (-1::'a::len word)"
proof -
  have "-1 + 1 = (0::'a word)" by simp
  thus ?thesis by (rule max_word_wrap [symmetric])
qed

lemma max_word_bl [simp]:
  "to_bl (max_word::'a::len word) = replicate (len_of TYPE('a)) True"
  by (subst max_word_minus to_bl_n1)+ simp

lemma max_test_bit [simp]:
  "(max_word::'a::len word) !! n = (n < len_of TYPE('a))"
  by (auto simp add: test_bit_bl word_size)

lemma word_and_max [simp]:
  "x AND max_word = x"
  by (rule word_eqI) (simp add: word_ops_nth_size word_size)

lemma word_or_max [simp]:
  "x OR max_word = max_word"
  by (rule word_eqI) (simp add: word_ops_nth_size word_size)

lemma word_ao_dist2:
  "x AND (y OR z) = x AND y OR x AND (z::'a::len0 word)"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_oa_dist2:
  "x OR y AND z = (x OR y) AND (x OR (z::'a::len0 word))"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_and_not [simp]:
  "x AND NOT x = (0::'a::len0 word)"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_or_not [simp]:
  "x OR NOT x = max_word"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

lemma word_boolean:
  "boolean (op AND) (op OR) bitNOT 0 max_word"
  apply (rule boolean.intro)
           apply (rule word_bw_assocs)
          apply (rule word_bw_assocs)
         apply (rule word_bw_comms)
        apply (rule word_bw_comms)
       apply (rule word_ao_dist2)
      apply (rule word_oa_dist2)
     apply (rule word_and_max)
    apply (rule word_log_esimps)
   apply (rule word_and_not)
  apply (rule word_or_not)
  done

interpretation word_bool_alg:
  boolean "op AND" "op OR" bitNOT 0 max_word
  by (rule word_boolean)

lemma word_xor_and_or:
  "x XOR y = x AND NOT y OR NOT x AND (y::'a::len0 word)"
  by (rule word_eqI) (auto simp add: word_ops_nth_size word_size)

interpretation word_bool_alg:
  boolean_xor "op AND" "op OR" bitNOT 0 max_word "op XOR"
  apply (rule boolean_xor.intro)
   apply (rule word_boolean)
  apply (rule boolean_xor_axioms.intro)
  apply (rule word_xor_and_or)
  done

lemma shiftr_x_0 [iff]:
  "(x::'a::len0 word) >> 0 = x"
  by (simp add: shiftr_bl)

lemma shiftl_x_0 [simp]: 
  "(x :: 'a :: len word) << 0 = x"
  by (simp add: shiftl_t2n)

lemma shiftl_1 [simp]:
  "(1::'a::len word) << n = 2^n"
  by (simp add: shiftl_t2n)

lemma uint_lt_0 [simp]:
  "uint x < 0 = False"
  by (simp add: linorder_not_less)

lemma shiftr1_1 [simp]: 
  "shiftr1 (1::'a::len word) = 0"
  by (simp add: shiftr1_def word_0_wi)

lemma shiftr_1[simp]: 
  "(1::'a::len word) >> n = (if n = 0 then 1 else 0)"
  by (induct n) (auto simp: shiftr_def)

lemma word_less_1 [simp]: 
  "((x::'a::len word) < 1) = (x = 0)"
  by (simp add: word_less_nat_alt unat_0_iff)

lemma to_bl_mask:
  "to_bl (mask n :: 'a::len word) = 
  replicate (len_of TYPE('a) - n) False @ 
    replicate (min (len_of TYPE('a)) n) True"
  by (simp add: mask_bl word_rep_drop min_def)

lemma map_replicate_True:
  "n = length xs \<Longrightarrow>
    map (\<lambda>(x,y). x & y) (zip xs (replicate n True)) = xs"
  by (induct xs arbitrary: n) auto

lemma map_replicate_False:
  "n = length xs \<Longrightarrow> map (\<lambda>(x,y). x & y)
    (zip xs (replicate n False)) = replicate n False"
  by (induct xs arbitrary: n) auto

lemma bl_and_mask:
  fixes w :: "'a::len word"
  fixes n
  defines "n' \<equiv> len_of TYPE('a) - n"
  shows "to_bl (w AND mask n) =  replicate n' False @ drop n' (to_bl w)"
proof - 
  note [simp] = map_replicate_True map_replicate_False
  have "to_bl (w AND mask n) = 
        map2 op & (to_bl w) (to_bl (mask n::'a::len word))"
    by (simp add: bl_word_and)
  also
  have "to_bl w = take n' (to_bl w) @ drop n' (to_bl w)" by simp
  also
  have "map2 op & \<dots> (to_bl (mask n::'a::len word)) = 
        replicate n' False @ drop n' (to_bl w)"
    unfolding to_bl_mask n'_def map2_def
    by (subst zip_append) auto
  finally
  show ?thesis .
qed

lemma drop_rev_takefill:
  "length xs \<le> n \<Longrightarrow>
    drop (n - length xs) (rev (takefill False n (rev xs))) = xs"
  by (simp add: takefill_alt rev_take)

lemma map_nth_0 [simp]:
  "map (op !! (0::'a::len0 word)) xs = replicate (length xs) False"
  by (induct xs) auto

lemma uint_plus_if_size:
  "uint (x + y) = 
  (if uint x + uint y < 2^size x then 
      uint x + uint y 
   else 
      uint x + uint y - 2^size x)" 
  by (simp add: word_arith_alts int_word_uint mod_add_if_z 
                word_size)

lemma unat_plus_if_size:
  "unat (x + (y::'a::len word)) = 
  (if unat x + unat y < 2^size x then 
      unat x + unat y 
   else 
      unat x + unat y - 2^size x)" 
  apply (subst word_arith_nat_defs)
  apply (subst unat_of_nat)
  apply (simp add:  mod_nat_add word_size)
  done

lemma word_neq_0_conv:
  fixes w :: "'a :: len word"
  shows "(w \<noteq> 0) = (0 < w)"
proof -
  have "0 \<le> w" by (rule word_zero_le)
  thus ?thesis by (auto simp add: word_less_def)
qed

lemma max_lt:
  "unat (max a b div c) = unat (max a b) div unat (c:: 'a :: len word)"
  apply (subst word_arith_nat_defs)
  apply (subst word_unat.eq_norm)
  apply (subst mod_if)
  apply clarsimp
  apply (erule notE)
  apply (insert div_le_dividend [of "unat (max a b)" "unat c"])
  apply (erule order_le_less_trans)
  apply (insert unat_lt2p [of "max a b"])
  apply simp
  done

lemma uint_sub_if_size:
  "uint (x - y) = 
  (if uint y \<le> uint x then 
      uint x - uint y 
   else 
      uint x - uint y + 2^size x)"
  by (simp add: word_arith_alts int_word_uint mod_sub_if_z 
                word_size)

lemma unat_sub:
  "b <= a \<Longrightarrow> unat (a - b) = unat a - unat b"
  by (simp add: unat_def uint_sub_if_size word_le_def nat_diff_distrib)

lemmas word_less_sub1_numberof [simp] = word_less_sub1 [of "number_of w"] for w
lemmas word_le_sub1_numberof [simp] = word_le_sub1 [of "number_of w"] for w
  
lemma word_of_int_minus: 
  "word_of_int (2^len_of TYPE('a) - i) = (word_of_int (-i)::'a::len word)"
proof -
  have x: "2^len_of TYPE('a) - i = -i + 2^len_of TYPE('a)" by simp
  show ?thesis
    apply (subst x)
    apply (subst word_uint.Abs_norm [symmetric], subst mod_add_self2)
    apply simp
    done
qed
  
lemmas word_of_int_inj = 
  word_uint.Abs_inject [unfolded uints_num, simplified]

lemma word_le_less_eq:
  "(x ::'z::len word) \<le> y = (x = y \<or> x < y)"
  by (auto simp add: word_less_def)

lemma mod_plus_cong:
  assumes 1: "(b::int) = b'"
      and 2: "x mod b' = x' mod b'"
      and 3: "y mod b' = y' mod b'"
      and 4: "x' + y' = z'"
  shows "(x + y) mod b = z' mod b'"
proof -
  from 1 2[symmetric] 3[symmetric] have "(x + y) mod b = (x' mod b' + y' mod b') mod b'"
    by (simp add: mod_add_eq[symmetric])
  also have "\<dots> = (x' + y') mod b'"
    by (simp add: mod_add_eq[symmetric])
  finally show ?thesis by (simp add: 4)
qed

lemma mod_minus_cong:
  assumes 1: "(b::int) = b'"
      and 2: "x mod b' = x' mod b'"
      and 3: "y mod b' = y' mod b'"
      and 4: "x' - y' = z'"
  shows "(x - y) mod b = z' mod b'"
  using assms
  apply (subst zmod_zsub_left_eq)
  apply (subst zmod_zsub_right_eq)
  apply (simp add: zmod_zsub_left_eq [symmetric] zmod_zsub_right_eq [symmetric])
  done

lemma word_induct_less: 
  "\<lbrakk>P (0::'a::len word); \<And>n. \<lbrakk>n < m; P n\<rbrakk> \<Longrightarrow> P (1 + n)\<rbrakk> \<Longrightarrow> P m"
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
  
lemma word_induct: 
  "\<lbrakk>P (0::'a::len word); \<And>n. P n \<Longrightarrow> P (1 + n)\<rbrakk> \<Longrightarrow> P m"
  by (erule word_induct_less, simp)

lemma word_induct2 [induct type]: 
  "\<lbrakk>P 0; \<And>n. \<lbrakk>1 + n \<noteq> 0; P n\<rbrakk> \<Longrightarrow> P (1 + n)\<rbrakk> \<Longrightarrow> P (n::'b::len word)"
  apply (rule word_induct, simp)
  apply (case_tac "1+n = 0", auto)
  done

definition word_rec :: "'a \<Rightarrow> ('b::len word \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b word \<Rightarrow> 'a" where
  "word_rec forZero forSuc n = nat_rec forZero (forSuc \<circ> of_nat) (unat n)"

lemma word_rec_0: "word_rec z s 0 = z"
  by (simp add: word_rec_def)

lemma word_rec_Suc: 
  "1 + n \<noteq> (0::'a::len word) \<Longrightarrow> word_rec z s (1 + n) = s n (word_rec z s n)"
  apply (simp add: word_rec_def unat_word_ariths)
  apply (subst nat_mod_eq')
   apply (cut_tac x=n in unat_lt2p)
   apply (drule Suc_mono)
   apply (simp add: less_Suc_eq_le)
   apply (simp only: order_less_le, simp)
   apply (erule contrapos_pn, simp)
   apply (drule arg_cong[where f=of_nat])
   apply simp
   apply (subst (asm) word_unat.Rep_inverse[of n])
   apply simp
  apply simp
  done

lemma word_rec_Pred: 
  "n \<noteq> 0 \<Longrightarrow> word_rec z s n = s (n - 1) (word_rec z s (n - 1))"
  apply (rule subst[where t="n" and s="1 + (n - 1)"])
   apply simp
  apply (subst word_rec_Suc)
   apply simp
  apply simp
  done

lemma word_rec_in: 
  "f (word_rec z (\<lambda>_. f) n) = word_rec (f z) (\<lambda>_. f) n"
  by (induct n) (simp_all add: word_rec_0 word_rec_Suc)

lemma word_rec_in2: 
  "f n (word_rec z f n) = word_rec (f 0 z) (f \<circ> op + 1) n"
  by (induct n) (simp_all add: word_rec_0 word_rec_Suc)

lemma word_rec_twice: 
  "m \<le> n \<Longrightarrow> word_rec z f n = word_rec (word_rec z f (n - m)) (f \<circ> op + (n - m)) m"
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
 apply (rule_tac f = "word_rec ?a ?b" in arg_cong)
 apply (rule_tac t="m" and s="m + (1 + (n - m))" in subst)
  apply simp
 apply (simp (no_asm_use))
apply (simp add: word_rec_Suc word_rec_in2)
apply (erule impE)
 apply uint_arith
apply (drule_tac x="x \<circ> op + 1" in spec)
apply (drule_tac x="x 0 xa" in spec)
apply simp
apply (rule_tac t="\<lambda>a. x (1 + (n - m + a))" and s="\<lambda>a. x (1 + (n - m) + a)"
       in subst)
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
  "\<forall>m\<ge>n. m \<noteq> -1 \<longrightarrow> f m = id \<Longrightarrow> word_rec z f -1 = word_rec z f n"
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

lemma unatSuc: 
  "1 + n \<noteq> (0::'a::len word) \<Longrightarrow> unat (1 + n) = Suc (unat n)"
  by unat_arith


lemma word_no_1 [simp]: "(Numeral1::'a::len0 word) = 1"
  by (fact word_1_no [symmetric, unfolded BIT_simps])

lemma word_no_0 [simp]: "(Numeral0::'a::len0 word) = 0"
  by (fact word_0_no [symmetric])

declare bin_to_bl_def [simp]


use "~~/src/HOL/Word/Tools/smt_word.ML"

setup {* SMT_Word.setup *}

end
