(* 
    ID:         $Id$
    Author:     Jeremy Dawson and Gerwin Klein, NICTA
*) 

header {* Bool Lists and Words *}

theory WordBoolList imports BinBoolList WordBitwise begin

constdefs
  of_bl :: "bool list => 'a :: len0 word" 
  "of_bl bl == word_of_int (bl_to_bin bl)"
  to_bl :: "'a :: len0 word => bool list"
  "to_bl w == 
  bin_to_bl (len_of TYPE ('a)) (uint w)"

  word_reverse :: "'a :: len0 word => 'a word"
  "word_reverse w == of_bl (rev (to_bl w))"

defs (overloaded)
  word_set_bits_def:  
  "(BITS n. f n)::'a::len0 word == of_bl (bl_of_nth (len_of TYPE ('a)) f)"

lemmas of_nth_def = word_set_bits_def

lemma to_bl_def': 
  "(to_bl :: 'a :: len0 word => bool list) =
    bin_to_bl (len_of TYPE('a)) o uint"
  by (auto simp: to_bl_def intro: ext)

lemmas word_reverse_no_def [simp] = word_reverse_def [of "number_of ?w"]

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

lemma word_rev_tf': 
  "r = to_bl (of_bl bl) ==> r = rev (takefill False (length r) (rev bl))"
  unfolding of_bl_def uint_bl
  by (clarsimp simp add: bl_bin_bl_rtf word_ubin.eq_norm word_size)

lemmas word_rev_tf = refl [THEN word_rev_tf', unfolded word_bl.Rep', standard]

lemmas word_rep_drop = word_rev_tf [simplified takefill_alt,
  simplified, simplified rev_take, simplified]

lemma of_bl_append_same: "of_bl (X @ to_bl w) = w"
  by (rule word_bl.Rep_eqD) (simp add: word_rep_drop)

lemma ucast_bl: "ucast w == of_bl (to_bl w)"
  unfolding ucast_def of_bl_def uint_bl
  by (auto simp add : word_size)

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

lemmas ucast_up_app = refl [THEN ucast_up_app']
lemmas ucast_down_drop = refl [THEN ucast_down_drop']
lemmas scast_down_drop = refl [THEN scast_down_drop']

lemma ucast_of_bl_up': 
  "w = of_bl bl ==> size bl <= size w ==> ucast w = of_bl bl"
  by (auto simp add : nth_ucast word_size test_bit_of_bl intro!: word_eqI)

lemmas ucast_of_bl_up = refl [THEN ucast_of_bl_up']

lemma ucast_down_bl': "uc = ucast ==> is_down uc ==> uc (of_bl bl) = of_bl bl"
  unfolding of_bl_no by clarify (erule ucast_down_no)
    
lemmas ucast_down_bl = ucast_down_bl' [OF refl]

lemma word_0_bl: "of_bl [] = 0" 
  unfolding word_0_wi of_bl_def by (simp add : Pls_def)

lemma word_1_bl: "of_bl [True] = 1" 
  unfolding word_1_wi of_bl_def
  by (simp add : bl_to_bin_def Bit_def Pls_def)

lemma of_bl_0 [simp] : "of_bl (replicate n False) = 0"
  by (simp add : word_0_wi of_bl_def bl_to_bin_rep_False Pls_def)

lemma to_bl_0: 
  "to_bl (0::'a::len0 word) = replicate (len_of TYPE('a)) False"
  unfolding uint_bl
  by (simp add : word_size bin_to_bl_Pls Pls_def [symmetric])

(* links with rbl operations *)
lemma word_succ_rbl:
  "to_bl w = bl ==> to_bl (word_succ w) = (rev (rbl_succ (rev bl)))"
  apply (unfold word_succ_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_succ)
  done

lemma word_pred_rbl:
  "to_bl w = bl ==> to_bl (word_pred w) = (rev (rbl_pred (rev bl)))"
  apply (unfold word_pred_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_pred)
  done

lemma word_add_rbl:
  "to_bl v = vbl ==> to_bl w = wbl ==> 
    to_bl (v + w) = (rev (rbl_add (rev vbl) (rev wbl)))"
  apply (unfold word_add_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_add)
  done

lemma word_mult_rbl:
  "to_bl v = vbl ==> to_bl w = wbl ==> 
    to_bl (v * w) = (rev (rbl_mult (rev vbl) (rev wbl)))"
  apply (unfold word_mult_def)
  apply clarify
  apply (simp add: to_bl_of_bin)
  apply (simp add: to_bl_def rbl_mult)
  done

lemma rtb_rbl_ariths:
  "rev (to_bl w) = ys \<Longrightarrow> rev (to_bl (word_succ w)) = rbl_succ ys"

  "rev (to_bl w) = ys \<Longrightarrow> rev (to_bl (word_pred w)) = rbl_pred ys"

  "[| rev (to_bl v) = ys; rev (to_bl w) = xs |] 
  ==> rev (to_bl (v * w)) = rbl_mult ys xs"

  "[| rev (to_bl v) = ys; rev (to_bl w) = xs |] 
  ==> rev (to_bl (v + w)) = rbl_add ys xs"
  by (auto simp: rev_swap [symmetric] word_succ_rbl 
                 word_pred_rbl word_mult_rbl word_add_rbl)

lemma of_bl_length_less: 
  "length x = k ==> k < len_of TYPE('a) ==> (of_bl x :: 'a :: len word) < 2 ^ k"
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

subsection "Bitwise operations on bool lists"

lemma bl_word_not: "to_bl (NOT w) = map Not (to_bl w)" 
  unfolding to_bl_def word_log_defs
  by (simp add: bl_not_bin number_of_is_id word_no_wi [symmetric])

lemma bl_word_xor: "to_bl (v XOR w) = app2 op ~= (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs bl_xor_bin
  by (simp add: number_of_is_id word_no_wi [symmetric])

lemma bl_word_or: "to_bl (v OR w) = app2 op | (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs
  by (simp add: bl_or_bin number_of_is_id word_no_wi [symmetric])

lemma bl_word_and: "to_bl (v AND w) = app2 op & (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs
  by (simp add: bl_and_bin number_of_is_id word_no_wi [symmetric])

lemma word_lsb_last: "lsb (w::'a::len word) = last (to_bl w)"
  apply (unfold word_lsb_def uint_bl bin_to_bl_def) 
  apply (rule_tac bin="uint w" in bin_exhaust)
  apply (cases "size w")
   apply auto
   apply (auto simp add: bin_to_bl_aux_alt)
  done

lemma word_msb_alt: "msb (w::'a::len word) = hd (to_bl w)"
  apply (unfold word_msb_nth uint_bl)
  apply (subst hd_conv_nth)
  apply (rule length_greater_0_conv [THEN iffD1])
   apply simp
  apply (simp add : nth_bin_to_bl word_size)
  done

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

lemma to_bl_nth: "n < size w ==> to_bl w ! n = w !! (size w - Suc n)"
  apply (unfold test_bit_bl)
  apply clarsimp
  apply (rule trans)
   apply (rule nth_rev_alt)
   apply (auto simp add: word_size)
  done

lemma of_bl_rep_False: "of_bl (replicate n False @ bs) = of_bl bs"
  unfolding of_bl_def bl_to_bin_rep_F by auto
  
lemma td_ext_nth':
  "n = size (w::'a::len0 word) ==> ofn = set_bits ==> [w, ofn g] = l ==> 
    td_ext test_bit ofn {f. ALL i. f i --> i < n} (%h i. h i & i < n)"
  apply (unfold word_size td_ext_def')
  apply safe
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
  td_ext ["op !! :: 'a::len0 word => nat => bool"
          set_bits
          "{f. \<forall>i. f i \<longrightarrow> i < len_of TYPE('a::len0)}"
          "(\<lambda>h i. h i \<and> i < len_of TYPE('a::len0))"]
  by (rule td_ext_nth)

declare test_bit.Rep' [simp del]
declare test_bit.Rep' [rule del]

lemmas td_nth = test_bit.td_thm

lemma to_bl_n1: 
  "to_bl (-1::'a::len0 word) = replicate (len_of TYPE ('a)) True"
  apply (rule word_bl.Abs_inverse')
   apply simp
  apply (rule word_eqI)
  apply (clarsimp simp add: word_size test_bit_no)
  apply (auto simp add: word_bl.Abs_inverse test_bit_bl word_size)
  done

end