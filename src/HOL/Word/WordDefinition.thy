(* 
  ID:     $Id$
  Author: Jeremy Dawson and Gerwin Klein, NICTA
  
  Basic definition of word type and basic theorems following from 
  the definition of the word type 
*) 

header {* Definition of Word Type *}

theory WordDefinition imports Size BinBoolList TdThs begin

typedef (open word) 'a word
  = "{(0::int) ..< 2^len_of TYPE('a::len0)}" by auto

instance word :: (len0) number ..
instance word :: (type) minus ..
instance word :: (type) plus ..
instance word :: (type) one ..
instance word :: (type) zero ..
instance word :: (type) times ..
instance word :: (type) Divides.div ..
instance word :: (type) power ..
instance word :: (type) ord ..
instance word :: (type) size ..
instance word :: (type) inverse ..
instance word :: (type) bit ..


subsection "Type conversions and casting"

constdefs
  -- {* representation of words using unsigned or signed bins, 
        only difference in these is the type class *}
  word_of_int :: "int => 'a :: len0 word"
  "word_of_int w == Abs_word (bintrunc (len_of TYPE ('a)) w)" 

  -- {* uint and sint cast a word to an integer,
        uint treats the word as unsigned,
        sint treats the most-significant-bit as a sign bit *}
  uint :: "'a :: len0 word => int"
  "uint w == Rep_word w"
  sint :: "'a :: len word => int"
  sint_uint: "sint w == sbintrunc (len_of TYPE ('a) - 1) (uint w)"
  unat :: "'a :: len0 word => nat"
  "unat w == nat (uint w)"

  -- "the sets of integers representing the words"
  uints :: "nat => int set"
  "uints n == range (bintrunc n)"
  sints :: "nat => int set"
  "sints n == range (sbintrunc (n - 1))"
  unats :: "nat => nat set"
  "unats n == {i. i < 2 ^ n}"
  norm_sint :: "nat => int => int"
  "norm_sint n w == (w + 2 ^ (n - 1)) mod 2 ^ n - 2 ^ (n - 1)"

constdefs
  of_bl :: "bool list => 'a :: len0 word" 
  "of_bl bl == word_of_int (bl_to_bin bl)"
  to_bl :: "'a :: len0 word => bool list"
  "to_bl w == 
  bin_to_bl (len_of TYPE ('a)) (uint w)"

  word_reverse :: "'a :: len0 word => 'a word"
  "word_reverse w == of_bl (rev (to_bl w))"

defs (overloaded)
  word_size: "size (w :: 'a :: len0 word) == len_of TYPE('a)"
  word_number_of_def: "number_of w == word_of_int w"

constdefs
  word_int_case :: "(int => 'b) => ('a :: len0 word) => 'b"
  "word_int_case f w == f (uint w)"

syntax
  of_int :: "int => 'a"
translations
  "case x of of_int y => b" == "word_int_case (%y. b) x"


subsection  "Arithmetic operations"

defs (overloaded)
  word_1_wi: "(1 :: ('a :: len0) word) == word_of_int 1"
  word_0_wi: "(0 :: ('a :: len0) word) == word_of_int 0"

  word_le_def: "a <= b == uint a <= uint b"
  word_less_def: "x < y == x <= y & x ~= (y :: 'a :: len0 word)"

constdefs
  word_succ :: "'a :: len0 word => 'a word"
  "word_succ a == word_of_int (Numeral.succ (uint a))"

  word_pred :: "'a :: len0 word => 'a word"
  "word_pred a == word_of_int (Numeral.pred (uint a))"

  udvd :: "'a::len word => 'a::len word => bool" (infixl "udvd" 50)
  "a udvd b == EX n>=0. uint b = n * uint a"

  word_sle :: "'a :: len word => 'a word => bool" ("(_/ <=s _)" [50, 51] 50)
  "a <=s b == sint a <= sint b"

  word_sless :: "'a :: len word => 'a word => bool" ("(_/ <s _)" [50, 51] 50)
  "(x <s y) == (x <=s y & x ~= y)"

consts
  word_power :: "'a :: len0 word => nat => 'a word"
primrec
  "word_power a 0 = 1"
  "word_power a (Suc n) = a * word_power a n"

defs (overloaded)
  word_pow: "power == word_power"
  word_add_def: "a + b == word_of_int (uint a + uint b)"
  word_sub_wi: "a - b == word_of_int (uint a - uint b)"
  word_minus_def: "- a == word_of_int (- uint a)"
  word_mult_def: "a * b == word_of_int (uint a * uint b)"
  word_div_def: "a div b == word_of_int (uint a div uint b)"
  word_mod_def: "a mod b == word_of_int (uint a mod uint b)"


subsection "Bit-wise operations"

defs (overloaded)
  word_and_def: 
  "(a::'a::len0 word) AND b == word_of_int (uint a AND uint b)"

  word_or_def:  
  "(a::'a::len0 word) OR b == word_of_int (uint a OR uint b)"

  word_xor_def: 
  "(a::'a::len0 word) XOR b == word_of_int (uint a XOR uint b)"

  word_not_def: 
  "NOT (a::'a::len0 word) == word_of_int (NOT (uint a))"

  word_test_bit_def: 
  "test_bit (a::'a::len0 word) == bin_nth (uint a)"

  word_set_bit_def: 
  "set_bit (a::'a::len0 word) n x == 
   word_of_int (bin_sc n (If x bit.B1 bit.B0) (uint a))"

  word_set_bits_def:  
  "(BITS n. f n)::'a::len0 word == of_bl (bl_of_nth (len_of TYPE ('a)) f)"

  word_lsb_def: 
  "lsb (a::'a::len0 word) == bin_last (uint a) = bit.B1"

  word_msb_def: 
  "msb (a::'a::len word) == bin_sign (sint a) = Numeral.Min"


constdefs
  setBit :: "'a :: len0 word => nat => 'a word" 
  "setBit w n == set_bit w n True"

  clearBit :: "'a :: len0 word => nat => 'a word" 
  "clearBit w n == set_bit w n False"


constdefs
  -- "Largest representable machine integer."
  max_word :: "'a::len word"
  "max_word \<equiv> word_of_int (2^len_of TYPE('a) - 1)"

consts 
  of_bool :: "bool \<Rightarrow> 'a::len word"
primrec
  "of_bool False = 0"
  "of_bool True = 1"



lemmas of_nth_def = word_set_bits_def

lemmas word_size_gt_0 [iff] = 
  xtr1 [OF word_size [THEN meta_eq_to_obj_eq] len_gt_0, standard]
lemmas lens_gt_0 = word_size_gt_0 len_gt_0
lemmas lens_not_0 [iff] = lens_gt_0 [THEN gr_implies_not0, standard]

lemma uints_num: "uints n = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (simp add: uints_def range_bintrunc)

lemma sints_num: "sints n = {i. - (2 ^ (n - 1)) \<le> i \<and> i < 2 ^ (n - 1)}"
  by (simp add: sints_def range_sbintrunc)

lemmas atLeastLessThan_alt = atLeastLessThan_def [unfolded 
  atLeast_def lessThan_def Collect_conj_eq [symmetric]]
  
lemma mod_in_reps: "m > 0 ==> y mod m : {0::int ..< m}"
  unfolding atLeastLessThan_alt by auto

lemma 
  Rep_word_0:"0 <= Rep_word x" and 
  Rep_word_lt: "Rep_word (x::'a::len0 word) < 2 ^ len_of TYPE('a)"
  by (auto simp: Rep_word [simplified])

lemma Rep_word_mod_same:
  "Rep_word x mod 2 ^ len_of TYPE('a) = Rep_word (x::'a::len0 word)"
  by (simp add: int_mod_eq Rep_word_lt Rep_word_0)

lemma td_ext_uint: 
  "td_ext (uint :: 'a word => int) word_of_int (uints (len_of TYPE('a::len0))) 
    (%w::int. w mod 2 ^ len_of TYPE('a))"
  apply (unfold td_ext_def')
  apply (simp add: uints_num uint_def word_of_int_def bintrunc_mod2p)
  apply (simp add: Rep_word_mod_same Rep_word_0 Rep_word_lt
                   word.Rep_word_inverse word.Abs_word_inverse int_mod_lem)
  done

lemmas int_word_uint = td_ext_uint [THEN td_ext.eq_norm, standard]

interpretation word_uint: 
  td_ext ["uint::'a::len0 word \<Rightarrow> int" 
          word_of_int 
          "uints (len_of TYPE('a::len0))"
          "\<lambda>w. w mod 2 ^ len_of TYPE('a::len0)"]
  by (rule td_ext_uint)
  
lemmas td_uint = word_uint.td_thm

lemmas td_ext_ubin = td_ext_uint 
  [simplified len_gt_0 no_bintr_alt1 [symmetric]]

interpretation word_ubin:
  td_ext ["uint::'a::len0 word \<Rightarrow> int" 
          word_of_int 
          "uints (len_of TYPE('a::len0))"
          "bintrunc (len_of TYPE('a::len0))"]
  by (rule td_ext_ubin)

lemma sint_sbintrunc': 
  "sint (word_of_int bin :: 'a word) = 
    (sbintrunc (len_of TYPE ('a :: len) - 1) bin)"
  unfolding sint_uint 
  by (auto simp: word_ubin.eq_norm sbintrunc_bintrunc_lt)

lemma uint_sint: 
  "uint w = bintrunc (len_of TYPE('a)) (sint (w :: 'a :: len word))"
  unfolding sint_uint by (auto simp: bintrunc_sbintrunc_le)

lemma bintr_uint': 
  "n >= size w ==> bintrunc n (uint w) = uint w"
  apply (unfold word_size)
  apply (subst word_ubin.norm_Rep [symmetric]) 
  apply (simp only: bintrunc_bintrunc_min word_size min_def)
  apply simp
  done

lemma wi_bintr': 
  "wb = word_of_int bin ==> n >= size wb ==> 
    word_of_int (bintrunc n bin) = wb"
  unfolding word_size
  by (clarsimp simp add : word_ubin.norm_eq_iff [symmetric] min_def)

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
  td_ext ["sint ::'a::len word => int" 
          word_of_int 
          "sints (len_of TYPE('a::len))"
          "%w. (w + 2^(len_of TYPE('a::len) - 1)) mod 2^len_of TYPE('a::len) -
               2 ^ (len_of TYPE('a::len) - 1)"]
  by (rule td_ext_sint)

interpretation word_sbin:
  td_ext ["sint ::'a::len word => int" 
          word_of_int 
          "sints (len_of TYPE('a::len))"
          "sbintrunc (len_of TYPE('a::len) - 1)"]
  by (rule td_ext_sbin)

lemmas int_word_sint = td_ext_sint [THEN td_ext.eq_norm, standard]

lemmas td_sint = word_sint.td

lemma word_number_of_alt: "number_of b == word_of_int (number_of b)"
  unfolding word_number_of_def by (simp add: number_of_eq)

lemma word_no_wi: "number_of = word_of_int"
  by (auto simp: word_number_of_def intro: ext)

lemma to_bl_def': 
  "(to_bl :: 'a :: len0 word => bool list) =
    bin_to_bl (len_of TYPE('a)) o uint"
  by (auto simp: to_bl_def intro: ext)

lemmas word_reverse_no_def [simp] = word_reverse_def [of "number_of ?w"]

lemmas uints_mod = uints_def [unfolded no_bintr_alt1]

lemma uint_bintrunc: "uint (number_of bin :: 'a word) = 
    number_of (bintrunc (len_of TYPE ('a :: len0)) bin)"
  unfolding word_number_of_def number_of_eq
  by (auto intro: word_ubin.eq_norm) 

lemma sint_sbintrunc: "sint (number_of bin :: 'a word) = 
    number_of (sbintrunc (len_of TYPE ('a :: len) - 1) bin)" 
  unfolding word_number_of_def number_of_eq
  by (auto intro!: word_sbin.eq_norm simp del: one_is_Suc_zero)

lemma unat_bintrunc: 
  "unat (number_of bin :: 'a :: len0 word) =
    number_of (bintrunc (len_of TYPE('a)) bin)"
  unfolding unat_def nat_number_of_def 
  by (simp only: uint_bintrunc)

(* WARNING - these may not always be helpful *)
declare 
  uint_bintrunc [simp] 
  sint_sbintrunc [simp] 
  unat_bintrunc [simp]

lemma size_0_eq: "size (w :: 'a :: len0 word) = 0 ==> v = w"
  apply (unfold word_size)
  apply (rule word_uint.Rep_eqD)
  apply (rule box_equals)
    defer
    apply (rule word_ubin.norm_Rep)+
  apply simp
  done

lemmas uint_lem = word_uint.Rep [unfolded uints_num mem_Collect_eq]
lemmas sint_lem = word_sint.Rep [unfolded sints_num mem_Collect_eq]
lemmas uint_ge_0 [iff] = uint_lem [THEN conjunct1, standard]
lemmas uint_lt2p [iff] = uint_lem [THEN conjunct2, standard]
lemmas sint_ge = sint_lem [THEN conjunct1, standard]
lemmas sint_lt = sint_lem [THEN conjunct2, standard]

lemma sign_uint_Pls [simp]: 
  "bin_sign (uint x) = Numeral.Pls"
  by (simp add: sign_Pls_ge_0 number_of_eq)

lemmas uint_m2p_neg = iffD2 [OF diff_less_0_iff_less uint_lt2p, standard]
lemmas uint_m2p_not_non_neg = 
  iffD2 [OF linorder_not_le uint_m2p_neg, standard]

lemma lt2p_lem:
  "len_of TYPE('a) <= n ==> uint (w :: 'a :: len0 word) < 2 ^ n"
  by (rule xtr8 [OF _ uint_lt2p]) simp

lemmas uint_le_0_iff [simp] = 
  uint_ge_0 [THEN leD, THEN linorder_antisym_conv1, standard]

lemma uint_nat: "uint w == int (unat w)"
  unfolding unat_def by auto

lemma uint_number_of:
  "uint (number_of b :: 'a :: len0 word) = number_of b mod 2 ^ len_of TYPE('a)"
  unfolding word_number_of_alt
  by (simp only: int_word_uint)

lemma unat_number_of: 
  "bin_sign b = Numeral.Pls ==> 
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
  
lemmas uint_range' =
  word_uint.Rep [unfolded uints_num mem_Collect_eq, standard]
lemmas sint_range' = word_sint.Rep [unfolded One_nat_def
  sints_num mem_Collect_eq, standard]

lemma uint_range_size: "0 <= uint w & uint w < 2 ^ size w"
  unfolding word_size by (rule uint_range')

lemma sint_range_size:
  "- (2 ^ (size w - Suc 0)) <= sint w & sint w < 2 ^ (size w - Suc 0)"
  unfolding word_size by (rule sint_range')

lemmas sint_above_size = sint_range_size
  [THEN conjunct2, THEN [2] xtr8, folded One_nat_def, standard]

lemmas sint_below_size = sint_range_size
  [THEN conjunct1, THEN [2] order_trans, folded One_nat_def, standard]

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
  shows "(ALL n. n < size u --> u !! n = v !! n) ==> u = v"
  apply (rule test_bit_eq_iff [THEN iffD1])
  apply (rule ext)
  apply (erule allE)
  apply (erule impCE)
   prefer 2
   apply assumption
  apply (auto dest!: test_bit_size simp add: word_size)
  done

lemmas word_eqD = test_bit_eq_iff [THEN iffD2, THEN fun_cong, standard]

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
  type_definition ["to_bl :: 'a::len0 word => bool list"
                   of_bl  
                   "{bl. length bl = len_of TYPE('a::len0)}"]
  by (rule td_bl)

lemma word_size_bl: "size w == size (to_bl w)"
  unfolding word_size by auto

lemma to_bl_use_of_bl:
  "(to_bl w = bl) = (w = of_bl bl \<and> length bl = length (to_bl w))"
  by (fastsimp elim!: word_bl.Abs_inverse [simplified])

lemma to_bl_word_rev: "to_bl (word_reverse w) = rev (to_bl w)"
  unfolding word_reverse_def by (simp add: word_bl.Abs_inverse)

lemma word_rev_rev [simp] : "word_reverse (word_reverse w) = w"
  unfolding word_reverse_def by (simp add : word_bl.Abs_inverse)

lemma word_rev_gal: "word_reverse w = u ==> word_reverse u = w"
  by auto

lemmas word_rev_gal' = sym [THEN word_rev_gal, symmetric, standard]

lemmas length_bl_gt_0 [iff] = xtr1 [OF word_bl.Rep' len_gt_0, standard]
lemmas bl_not_Nil [iff] = 
  length_bl_gt_0 [THEN length_greater_0_conv [THEN iffD1], standard]
lemmas length_bl_neq_0 [iff] = length_bl_gt_0 [THEN gr_implies_not0]

lemma hd_bl_sign_sint: "hd (to_bl w) = (bin_sign (sint w) = Numeral.Min)"
  apply (unfold to_bl_def sint_uint)
  apply (rule trans [OF _ bl_sbin_sign])
  apply simp
  done

lemma of_bl_drop': 
  "lend = length bl - len_of TYPE ('a :: len0) ==> 
    of_bl (drop lend bl) = (of_bl bl :: 'a word)"
  apply (unfold of_bl_def)
  apply (clarsimp simp add : trunc_bl2bin [symmetric])
  done

lemmas of_bl_no = of_bl_def [folded word_number_of_def]

lemma test_bit_of_bl:  
  "(of_bl bl::'a::len0 word) !! n = (rev bl ! n \<and> n < len_of TYPE('a) \<and> n < length bl)"
  apply (unfold of_bl_def word_test_bit_def)
  apply (auto simp add: word_size word_ubin.eq_norm nth_bintr bin_nth_of_bl)
  done

lemma no_of_bl: 
  "(number_of bin ::'a::len0 word) = of_bl (bin_to_bl (len_of TYPE ('a)) bin)"
  unfolding word_size of_bl_no by (simp add : word_number_of_def)

lemma uint_bl: "to_bl w == bin_to_bl (size w) (uint w)"
  unfolding word_size to_bl_def by auto

lemma to_bl_bin: "bl_to_bin (to_bl w) = uint w"
  unfolding uint_bl by (simp add : word_size)

lemma to_bl_of_bin: 
  "to_bl (word_of_int bin::'a::len0 word) = bin_to_bl (len_of TYPE('a)) bin"
  unfolding uint_bl by (clarsimp simp add: word_ubin.eq_norm word_size)

lemmas to_bl_no_bin [simp] = to_bl_of_bin [folded word_number_of_def]

lemma to_bl_to_bin [simp] : "bl_to_bin (to_bl w) = uint w"
  unfolding uint_bl by (simp add : word_size)
  
lemmas uint_bl_bin [simp] = trans [OF bin_bl_bin word_ubin.norm_Rep, standard]

lemmas num_AB_u [simp] = word_uint.Rep_inverse 
  [unfolded o_def word_number_of_def [symmetric], standard]
lemmas num_AB_s [simp] = word_sint.Rep_inverse 
  [unfolded o_def word_number_of_def [symmetric], standard]

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
  apply (auto simp add : uints_unats image_iff)
  done

lemmas bintr_num = word_ubin.norm_eq_iff 
  [symmetric, folded word_number_of_def, standard]
lemmas sbintr_num = word_sbin.norm_eq_iff 
  [symmetric, folded word_number_of_def, standard]

lemmas num_of_bintr = word_ubin.Abs_norm [folded word_number_of_def, standard]
lemmas num_of_sbintr = word_sbin.Abs_norm [folded word_number_of_def, standard];
    
(* don't add these to simpset, since may want bintrunc n w to be simplified;
  may want these in reverse, but loop as simp rules, so use following *)

lemma num_of_bintr':
  "bintrunc (len_of TYPE('a :: len0)) a = b ==> 
    number_of a = (number_of b :: 'a word)"
  apply safe
  apply (rule_tac num_of_bintr [symmetric])
  done

lemma num_of_sbintr':
  "sbintrunc (len_of TYPE('a :: len) - 1) a = b ==> 
    number_of a = (number_of b :: 'a word)"
  apply safe
  apply (rule_tac num_of_sbintr [symmetric])
  done

lemmas num_abs_bintr = sym [THEN trans,
  OF num_of_bintr word_number_of_def [THEN meta_eq_to_obj_eq], standard]
lemmas num_abs_sbintr = sym [THEN trans,
  OF num_of_sbintr word_number_of_def [THEN meta_eq_to_obj_eq], standard]

lemma word_rev_tf': 
  "r = to_bl (of_bl bl) ==> r = rev (takefill False (length r) (rev bl))"
  unfolding of_bl_def uint_bl
  by (clarsimp simp add: bl_bin_bl_rtf word_ubin.eq_norm word_size)

lemmas word_rev_tf = refl [THEN word_rev_tf', unfolded word_bl.Rep', standard]

lemmas word_rep_drop = word_rev_tf [simplified takefill_alt,
  simplified, simplified rev_take, simplified]

lemma of_bl_append_same: "of_bl (X @ to_bl w) = w"
  by (rule word_bl.Rep_eqD) (simp add: word_rep_drop)

lemmas test_bit_def' = word_test_bit_def [THEN meta_eq_to_obj_eq, THEN fun_cong]

lemmas word_log_defs = word_and_def word_or_def word_xor_def word_not_def
lemmas word_log_bin_defs = word_log_defs


subsection {* Casting words to different lengths *}

constdefs
  -- "cast a word to a different length"
  scast :: "'a :: len word => 'b :: len word"
  "scast w == word_of_int (sint w)"
  ucast :: "'a :: len0 word => 'b :: len0 word"
  "ucast w == word_of_int (uint w)"

  -- "whether a cast (or other) function is to a longer or shorter length"
  source_size :: "('a :: len0 word => 'b) => nat"
  "source_size c == let arb = arbitrary ; x = c arb in size arb"  
  target_size :: "('a => 'b :: len0 word) => nat"
  "target_size c == size (c arbitrary)"
  is_up :: "('a :: len0 word => 'b :: len0 word) => bool"
  "is_up c == source_size c <= target_size c"
  is_down :: "('a :: len0 word => 'b :: len0 word) => bool"
  "is_down c == target_size c <= source_size c"

(** cast - note, no arg for new length, as it's determined by type of result,
  thus in "cast w = w, the type means cast to length of w! **)

lemma ucast_id: "ucast w = w"
  unfolding ucast_def by auto

lemma scast_id: "scast w = w"
  unfolding scast_def by auto

lemma ucast_bl: "ucast w == of_bl (to_bl w)"
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

lemmas is_up_down = 
  trans [OF is_up [THEN meta_eq_to_obj_eq] 
            is_down [THEN meta_eq_to_obj_eq, symmetric], 
         standard]

lemma down_cast_same': "uc = ucast ==> is_down uc ==> uc = scast"
  apply (unfold is_down)
  apply safe
  apply (rule ext)
  apply (unfold ucast_def scast_def uint_sint)
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply simp
  done

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
  "uc = ucast ==> source_size uc + n = target_size uc ==> 
    to_bl (uc w) = replicate n False @ (to_bl w)"
  apply (auto simp add : source_size target_size to_bl_ucast)
  apply (rule_tac f = "%n. replicate n False" in arg_cong)
  apply simp
  done

lemma ucast_down_drop': 
  "uc = ucast ==> source_size uc = target_size uc + n ==> 
    to_bl (uc w) = drop n (to_bl w)"
  by (auto simp add : source_size target_size to_bl_ucast)

lemma scast_down_drop': 
  "sc = scast ==> source_size sc = target_size sc + n ==> 
    to_bl (sc w) = drop n (to_bl w)"
  apply (subgoal_tac "sc = ucast")
   apply safe
   apply simp
   apply (erule refl [THEN ucast_down_drop'])
  apply (rule refl [THEN down_cast_same', symmetric])
  apply (simp add : source_size target_size is_down)
  done

lemma sint_up_scast': 
  "sc = scast ==> is_up sc ==> sint (sc w) = sint w"
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
  "uc = ucast ==> is_up uc ==> uint (uc w) = uint w"
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

lemma ucast_up_ucast': "uc = ucast ==> is_up uc ==> ucast (uc w) = ucast w"
  apply (simp (no_asm) add: ucast_def)
  apply (clarsimp simp add: uint_up_ucast)
  done
    
lemma scast_up_scast': "sc = scast ==> is_up sc ==> scast (sc w) = scast w"
  apply (simp (no_asm) add: scast_def)
  apply (clarsimp simp add: sint_up_scast)
  done
    
lemma ucast_of_bl_up': 
  "w = of_bl bl ==> size bl <= size w ==> ucast w = of_bl bl"
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
  "is_up (ucast :: 'b::len0 word => 'a::len0 word) ==> 
   surj (ucast :: 'a word => 'b word)"
  by (rule surjI, erule ucast_up_ucast_id)

lemma up_scast_surj:
  "is_up (scast :: 'b::len word => 'a::len word) ==> 
   surj (scast :: 'a word => 'b word)"
  by (rule surjI, erule scast_up_scast_id)

lemma down_scast_inj:
  "is_down (scast :: 'b::len word => 'a::len word) ==> 
   inj_on (ucast :: 'a word => 'b word) A"
  by (rule inj_on_inverseI, erule scast_down_scast_id)

lemma down_ucast_inj:
  "is_down (ucast :: 'b::len0 word => 'a::len0 word) ==> 
   inj_on (ucast :: 'a word => 'b word) A"
  by (rule inj_on_inverseI, erule ucast_down_ucast_id)

  
lemma ucast_down_no': 
  "uc = ucast ==> is_down uc ==> uc (number_of bin) = number_of bin"
  apply (unfold word_number_of_def is_down)
  apply (clarsimp simp add: ucast_def word_ubin.eq_norm)
  apply (rule word_ubin.norm_eq_iff [THEN iffD1])
  apply (erule bintrunc_bintrunc_ge)
  done
    
lemmas ucast_down_no = ucast_down_no' [OF refl]

lemma ucast_down_bl': "uc = ucast ==> is_down uc ==> uc (of_bl bl) = of_bl bl"
  unfolding of_bl_no by clarify (erule ucast_down_no)
    
lemmas ucast_down_bl = ucast_down_bl' [OF refl]

end
