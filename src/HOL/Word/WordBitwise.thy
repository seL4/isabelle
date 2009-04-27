(* 
    Author:     Jeremy Dawson and Gerwin Klein, NICTA

  contains theorems to do with bit-wise (logical) operations on words
*)

header {* Bitwise Operations on Words *}

theory WordBitwise
imports WordArith
begin

lemmas bin_log_bintrs = bin_trunc_not bin_trunc_xor bin_trunc_and bin_trunc_or
  
(* following definitions require both arithmetic and bit-wise word operations *)

(* to get word_no_log_defs from word_log_defs, using bin_log_bintrs *)
lemmas wils1 = bin_log_bintrs [THEN word_ubin.norm_eq_iff [THEN iffD1],
  folded word_ubin.eq_norm, THEN eq_reflection, standard]

(* the binary operations only *)
lemmas word_log_binary_defs = 
  word_and_def word_or_def word_xor_def

lemmas word_no_log_defs [simp] = 
  word_not_def  [where a="number_of a", 
                 unfolded word_no_wi wils1, folded word_no_wi, standard]
  word_log_binary_defs [where a="number_of a" and b="number_of b",
                        unfolded word_no_wi wils1, folded word_no_wi, standard]

lemmas word_wi_log_defs = word_no_log_defs [unfolded word_no_wi]

lemma uint_or: "uint (x OR y) = (uint x) OR (uint y)"
  by (simp add: word_or_def word_no_wi [symmetric] number_of_is_id
                bin_trunc_ao(2) [symmetric])

lemma uint_and: "uint (x AND y) = (uint x) AND (uint y)"
  by (simp add: word_and_def number_of_is_id word_no_wi [symmetric]
                bin_trunc_ao(1) [symmetric]) 

lemma word_ops_nth_size:
  "n < size (x::'a::len0 word) ==> 
    (x OR y) !! n = (x !! n | y !! n) & 
    (x AND y) !! n = (x !! n & y !! n) & 
    (x XOR y) !! n = (x !! n ~= y !! n) & 
    (NOT x) !! n = (~ x !! n)"
  unfolding word_size word_no_wi word_test_bit_def word_log_defs
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
  by (auto simp: bwsimps bbw_ao_dist simp del: bin_ops_comm)

lemma word_oa_dist:
  fixes x :: "'a::len0 word"
  shows "x AND y OR z = (x OR z) AND (y OR z)"
  using word_of_int_Ex [where x=x] 
        word_of_int_Ex [where x=y] 
        word_of_int_Ex [where x=z]   
  by (auto simp: bwsimps bbw_oa_dist simp del: bin_ops_comm)

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
  shows "(w = (x OR y)) ==> (y = (w AND y))" by auto
lemma leao: 
  fixes x' :: "'a::len0 word"
  shows "(w' = (x' AND y')) ==> (x' = (x' OR w'))" by auto 

lemmas word_ao_equiv = leao [COMP leoa [COMP iffI]]

lemma le_word_or2: "x <= x OR (y::'a::len0 word)"
  unfolding word_le_def uint_or
  by (auto intro: le_int_or) 

lemmas le_word_or1 = xtr3 [OF word_bw_comms (2) le_word_or2, standard]
lemmas word_and_le1 =
  xtr3 [OF word_ao_absorbs (4) [symmetric] le_word_or2, standard]
lemmas word_and_le2 =
  xtr3 [OF word_ao_absorbs (8) [symmetric] le_word_or2, standard]

lemma bl_word_not: "to_bl (NOT w) = map Not (to_bl w)" 
  unfolding to_bl_def word_log_defs
  by (simp add: bl_not_bin number_of_is_id word_no_wi [symmetric])

lemma bl_word_xor: "to_bl (v XOR w) = map2 op ~= (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs bl_xor_bin
  by (simp add: number_of_is_id word_no_wi [symmetric])

lemma bl_word_or: "to_bl (v OR w) = map2 op | (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs
  by (simp add: bl_or_bin number_of_is_id word_no_wi [symmetric])

lemma bl_word_and: "to_bl (v AND w) = map2 op & (to_bl v) (to_bl w)" 
  unfolding to_bl_def word_log_defs
  by (simp add: bl_and_bin number_of_is_id word_no_wi [symmetric])

lemma word_lsb_alt: "lsb (w::'a::len0 word) = test_bit w 0"
  by (auto simp: word_test_bit_def word_lsb_def)

lemma word_lsb_1_0: "lsb (1::'a::len word) & ~ lsb (0::'b::len0 word)"
  unfolding word_lsb_def word_1_no word_0_no by auto

lemma word_lsb_last: "lsb (w::'a::len word) = last (to_bl w)"
  apply (unfold word_lsb_def uint_bl bin_to_bl_def) 
  apply (rule_tac bin="uint w" in bin_exhaust)
  apply (cases "size w")
   apply auto
   apply (auto simp add: bin_to_bl_aux_alt)
  done

lemma word_lsb_int: "lsb w = (uint w mod 2 = 1)"
  unfolding word_lsb_def bin_last_mod by auto

lemma word_msb_sint: "msb w = (sint w < 0)" 
  unfolding word_msb_def
  by (simp add : sign_Min_lt_0 number_of_is_id)
  
lemma word_msb_no': 
  "w = number_of bin ==> msb (w::'a::len word) = bin_nth bin (size w - 1)"
  unfolding word_msb_def word_number_of_def
  by (clarsimp simp add: word_sbin.eq_norm word_size bin_sign_lem)

lemmas word_msb_no = refl [THEN word_msb_no', unfolded word_size]

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

lemma word_set_nth:
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

lemma to_bl_nth: "n < size w ==> to_bl w ! n = w !! (size w - Suc n)"
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

lemmas msb0 = len_gt_0 [THEN diff_Suc_less, THEN
  word_ops_nth_size [unfolded word_size], standard]
lemmas msb1 = msb0 [where i = 0]
lemmas word_ops_msb = msb1 [unfolded msb_nth [symmetric, unfolded One_nat_def]]

lemmas lsb0 = len_gt_0 [THEN word_ops_nth_size [unfolded word_size], standard]
lemmas word_ops_lsb = lsb0 [unfolded word_lsb_alt]

lemma td_ext_nth':
  "n = size (w::'a::len0 word) ==> ofn = set_bits ==> [w, ofn g] = l ==> 
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

declare test_bit.Rep' [simp del]
declare test_bit.Rep' [rule del]

lemmas td_nth = test_bit.td_thm

lemma word_set_set_same: 
  fixes w :: "'a::len0 word"
  shows "set_bit (set_bit w n x) n y = set_bit w n y" 
  by (rule word_eqI) (simp add : test_bit_set_gen word_size)
    
lemma word_set_set_diff: 
  fixes w :: "'a::len0 word"
  assumes "m ~= n"
  shows "set_bit (set_bit w m x) n y = set_bit (set_bit w n y) m x" 
  by (rule word_eqI) (clarsimp simp add : test_bit_set_gen word_size prems)
    
lemma test_bit_no': 
  fixes w :: "'a::len0 word"
  shows "w = number_of bin ==> test_bit w n = (n < size w & bin_nth bin n)"
  unfolding word_test_bit_def word_number_of_def word_size
  by (simp add : nth_bintr [symmetric] word_ubin.eq_norm)

lemmas test_bit_no = 
  refl [THEN test_bit_no', unfolded word_size, THEN eq_reflection, standard]

lemma nth_0: "~ (0::'a::len0 word) !! n"
  unfolding test_bit_no word_0_no by auto

lemma nth_sint: 
  fixes w :: "'a::len word"
  defines "l \<equiv> len_of TYPE ('a)"
  shows "bin_nth (sint w) n = (if n < l - 1 then w !! n else w !! (l - 1))"
  unfolding sint_uint l_def
  by (clarsimp simp add: nth_sbintr word_test_bit_def [symmetric])

lemma word_lsb_no: 
  "lsb (number_of bin :: 'a :: len word) = (bin_last bin = bit.B1)"
  unfolding word_lsb_alt test_bit_no by auto

lemma word_set_no: 
  "set_bit (number_of bin::'a::len0 word) n b = 
    number_of (bin_sc n (if b then bit.B1 else bit.B0) bin)"
  apply (unfold word_set_bit_def word_number_of_def [symmetric])
  apply (rule word_eqI)
  apply (clarsimp simp: word_size bin_nth_sc_gen number_of_is_id 
                        test_bit_no nth_bintr)
  done

lemmas setBit_no = setBit_def [THEN trans [OF meta_eq_to_obj_eq word_set_no],
  simplified if_simps, THEN eq_reflection, standard]
lemmas clearBit_no = clearBit_def [THEN trans [OF meta_eq_to_obj_eq word_set_no],
  simplified if_simps, THEN eq_reflection, standard]

lemma to_bl_n1: 
  "to_bl (-1::'a::len0 word) = replicate (len_of TYPE ('a)) True"
  apply (rule word_bl.Abs_inverse')
   apply simp
  apply (rule word_eqI)
  apply (clarsimp simp add: word_size test_bit_no)
  apply (auto simp add: word_bl.Abs_inverse test_bit_bl word_size)
  done

lemma word_msb_n1: "msb (-1::'a::len word)"
  unfolding word_msb_alt word_msb_alt to_bl_n1 by simp

declare word_set_set_same [simp] word_set_nth [simp]
  test_bit_no [simp] word_set_no [simp] nth_0 [simp]
  setBit_no [simp] clearBit_no [simp]
  word_lsb_no [simp] word_msb_no [simp] word_msb_n1 [simp] word_lsb_1_0 [simp]

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
  "w = word_of_int (2 ^ n) ==> 
    w !! m = (m = n & m < size (w :: 'a :: len word))"
  unfolding word_test_bit_def word_size
  by (auto simp add: word_ubin.eq_norm nth_bintr nth_2p_bin)

lemmas test_bit_2p = refl [THEN test_bit_2p', unfolded word_size]

lemma nth_w2p:
  "((2\<Colon>'a\<Colon>len word) ^ n) !! m \<longleftrightarrow> m = n \<and> m < len_of TYPE('a\<Colon>len)"
  unfolding test_bit_2p [symmetric] word_of_int [symmetric]
  by (simp add:  of_int_power)

lemma uint_2p: 
  "(0::'a::len word) < 2 ^ n ==> uint (2 ^ n::'a::len word) = 2 ^ n"
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

lemma bang_is_le: "x !! m ==> 2 ^ m <= (x :: 'a :: len word)" 
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

end

