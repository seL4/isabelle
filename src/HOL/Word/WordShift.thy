(* 
    Author:     Jeremy Dawson and Gerwin Klein, NICTA

  contains theorems to do with shifting, rotating, splitting words
*)

header {* Shifting, Rotating, and Splitting Words *}

theory WordShift
imports WordBitwise
begin

subsection "Bit shifting"

lemma shiftl1_number [simp] :
  "shiftl1 (number_of w) = number_of (w BIT bit.B0)"
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

lemma shiftl1_def_s: "shiftl1 w = number_of (sint w BIT bit.B0)"
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
  apply (unfold shiftr1_def bin_rest_div)
  apply (rule word_uint.Abs_inverse)
  apply (simp add: uints_num pos_imp_zdiv_nonneg_iff)
  apply (rule xtr7)
   prefer 2
   apply (rule zdiv_le_dividend)
    apply auto
  done

lemma sshiftr1_div_2: "sint (sshiftr1 w) = sint w div 2"
  apply (unfold sshiftr1_def bin_rest_div [symmetric])
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
  bshiftr1_def [where w="number_of w", unfolded to_bl_no_bin, standard]

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

lemma shiftr1_bl: "shiftr1 w = of_bl (butlast (to_bl w))"
  apply (unfold shiftr1_def uint_bl of_bl_def)
  apply (simp add: butlast_rest_bin word_size)
  apply (simp add: bin_rest_trunc [symmetric, unfolded One_nat_def])
  done

lemma bl_shiftr1: 
  "to_bl (shiftr1 (w :: 'a :: len word)) = False # butlast (to_bl w)"
  unfolding shiftr1_bl
  by (simp add : word_rep_drop len_gt_0 [THEN Suc_leI])


(* relate the two above : TODO - remove the :: len restriction on
  this theorem and others depending on it *)
lemma shiftl1_rev: 
  "shiftl1 (w :: 'a :: len word) = word_reverse (shiftr1 (word_reverse w))"
  apply (unfold word_reverse_def)
  apply (rule word_bl.Rep_inverse' [symmetric])
  apply (simp add: bl_shiftl1 bl_shiftr1 word_bl.Abs_inverse)
  apply (cases "to_bl w")
   apply auto
  done

lemma shiftl_rev: 
  "shiftl (w :: 'a :: len word) n = word_reverse (shiftr (word_reverse w) n)"
  apply (unfold shiftl_def shiftr_def)
  apply (induct "n")
   apply (auto simp add : shiftl1_rev)
  done

lemmas rev_shiftl =
  shiftl_rev [where w = "word_reverse w", simplified, standard]

lemmas shiftr_rev = rev_shiftl [THEN word_rev_gal', standard]
lemmas rev_shiftr = shiftl_rev [THEN word_rev_gal', standard]

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

lemma take_shiftr [rule_format] :
  "n <= size (w :: 'a :: len word) --> take n (to_bl (w >> n)) = 
    replicate n False" 
  apply (unfold shiftr_def)
  apply (induct n)
   prefer 2
   apply (simp add: bl_shiftr1)
   apply (rule impI)
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

lemmas hd_sshiftr = take_sshiftr' [THEN conjunct1, standard]
lemmas take_sshiftr = take_sshiftr' [THEN conjunct2, standard]

lemma atd_lem: "take n xs = t ==> drop n xs = d ==> xs = t @ d"
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

lemmas shiftl_number [simp] = shiftl_def [where w="number_of w", standard]

lemma bl_shiftl:
  "to_bl (w << n) = drop n (to_bl w) @ replicate (min (size w) n) False"
  by (simp add: shiftl_bl word_rep_drop word_size min_def)

lemma shiftl_zero_size: 
  fixes x :: "'a::len0 word"
  shows "size x <= n ==> x << n = 0"
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
  by (induct n) (auto simp: shiftl1_2t power_Suc)

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
  "w = number_of bin ==> 
  (w::'a::len0 word) >> n = number_of ((bin_rest ^ n) (bintrunc (size w) bin))"
  apply clarsimp
  apply (rule word_eqI)
  apply (auto simp: nth_shiftr nth_rest_power_bin nth_bintr word_size)
  done

lemma sshiftr_no': 
  "w = number_of bin ==> w >>> n = number_of ((bin_rest ^ n) 
    (sbintrunc (size w - 1) bin))"
  apply clarsimp
  apply (rule word_eqI)
  apply (auto simp: nth_sshiftr nth_rest_power_bin nth_sbintr word_size)
   apply (subgoal_tac "na + n = len_of TYPE('a) - Suc 0", simp, simp)+
  done

lemmas sshiftr_no [simp] = 
  sshiftr_no' [where w = "number_of w", OF refl, unfolded word_size, standard]

lemmas shiftr_no [simp] = 
  shiftr_no' [where w = "number_of w", OF refl, unfolded word_size, standard]

lemma shiftr1_bl_of': 
  "us = shiftr1 (of_bl bl) ==> length bl <= size us ==> 
    us = of_bl (butlast bl)"
  by (clarsimp simp: shiftr1_def of_bl_def word_size butlast_rest_bl2bin 
                     word_ubin.eq_norm trunc_bl2bin)

lemmas shiftr1_bl_of = refl [THEN shiftr1_bl_of', unfolded word_size]

lemma shiftr_bl_of' [rule_format]: 
  "us = of_bl bl >> n ==> length bl <= size us --> 
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

lemmas shiftr_bl = word_bl.Rep' [THEN eq_imp_le, THEN shiftr_bl_of,
  simplified word_size, simplified, THEN eq_reflection, standard]

lemma msb_shift': "msb (w::'a::len word) <-> (w >> (size w - 1)) ~= 0"
  apply (unfold shiftr_bl word_msb_alt)
  apply (simp add: word_size Suc_le_eq take_Suc)
  apply (cases "hd (to_bl w)")
   apply (auto simp: word_1_bl word_0_bl 
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
  "size x - n = m ==> n <= size x ==> drop m (to_bl x) = replicate n False ==>
    take m (to_bl y) = replicate m False ==> 
    to_bl (x + y) = take m (to_bl x) @ drop m (to_bl y)"
  apply (subgoal_tac "x AND y = 0")
   prefer 2
   apply (rule word_bl.Rep_eqD)
   apply (simp add: bl_word_and to_bl_0)
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

lemma nth_mask': "m = mask n ==> test_bit m i = (i < n & i < size m)"
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

lemma bl_and_mask:
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
  "n < size w ==> w < 2 ^ n = (uint (w :: 'a :: len word) < 2 ^ n)"
  apply (unfold word_size word_less_alt word_number_of_alt)
  apply (clarsimp simp add: word_of_int_power_hom word_uint.eq_norm 
                            int_mod_eq'
                  simp del: word_of_int_bin)
  done

lemma less_mask_eq: "x < 2 ^ n ==> x AND mask n = (x :: 'a :: len word)"
  apply (unfold word_less_alt word_number_of_alt)
  apply (clarsimp simp add: and_mask_mod_2p word_of_int_power_hom 
                            word_uint.eq_norm
                  simp del: word_of_int_bin)
  apply (drule xtr8 [rotated])
  apply (rule int_mod_le)
  apply (auto simp add : mod_pos_pos_trivial)
  done

lemmas mask_eq_iff_w2p =
  trans [OF mask_eq_iff word_2p_lem [symmetric], standard]

lemmas and_mask_less' = 
  iffD2 [OF word_2p_lem and_mask_lt_2p, simplified word_size, standard]

lemma and_mask_less_size: "n < size x ==> x AND mask n < 2^n"
  unfolding word_size by (erule and_mask_less')

lemma word_mod_2p_is_mask':
  "c = 2 ^ n ==> c > 0 ==> x mod c = (x :: 'a :: len word) AND mask n" 
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
lemmas revcast_no_def [simp] =
  revcast_def' [where w="number_of w", unfolded word_size, standard]

lemma to_bl_revcast: 
  "to_bl (revcast w :: 'a :: len0 word) = 
   takefill False (len_of TYPE ('a)) (to_bl w)"
  apply (unfold revcast_def' word_size)
  apply (rule word_bl.Abs_inverse)
  apply simp
  done

lemma revcast_rev_ucast': 
  "cs = [rc, uc] ==> rc = revcast (word_reverse w) ==> uc = ucast w ==> 
    rc = word_reverse uc"
  apply (unfold ucast_def revcast_def' Let_def word_reverse_def)
  apply (clarsimp simp add : to_bl_of_bin takefill_bintrunc)
  apply (simp add : word_bl.Abs_inverse word_size)
  done

lemmas revcast_rev_ucast = revcast_rev_ucast' [OF refl refl refl]

lemmas revcast_ucast = revcast_rev_ucast
  [where w = "word_reverse w", simplified word_rev_rev, standard]

lemmas ucast_revcast = revcast_rev_ucast [THEN word_rev_gal', standard]
lemmas ucast_rev_revcast = revcast_ucast [THEN word_rev_gal', standard]


-- "linking revcast and cast via shift"

lemmas wsst_TYs = source_size target_size word_size

lemma revcast_down_uu': 
  "rc = revcast ==> source_size rc = target_size rc + n ==> 
    rc (w :: 'a :: len word) = ucast (w >> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule ucast_down_drop)
   prefer 2
   apply (rule trans, rule drop_shiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_us': 
  "rc = revcast ==> source_size rc = target_size rc + n ==> 
    rc (w :: 'a :: len word) = ucast (w >>> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule ucast_down_drop)
   prefer 2
   apply (rule trans, rule drop_sshiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_su': 
  "rc = revcast ==> source_size rc = target_size rc + n ==> 
    rc (w :: 'a :: len word) = scast (w >> n)"
  apply (simp add: revcast_def')
  apply (rule word_bl.Rep_inverse')
  apply (rule trans, rule scast_down_drop)
   prefer 2
   apply (rule trans, rule drop_shiftr)
   apply (auto simp: takefill_alt wsst_TYs)
  done

lemma revcast_down_ss': 
  "rc = revcast ==> source_size rc = target_size rc + n ==> 
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
  "uc = ucast ==> source_size uc = target_size uc + n ==> 
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
  "rc = revcast ==> source_size rc + n = target_size rc ==> 
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

lemmas slice1_no_bin [simp] =
  slice1_def [where w="number_of w", unfolded to_bl_no_bin, standard]

lemmas slice_no_bin [simp] = 
   trans [OF slice_def [THEN meta_eq_to_obj_eq] 
             slice1_no_bin [THEN meta_eq_to_obj_eq], 
          unfolded word_size, standard]

lemma slice1_0 [simp] : "slice1 n 0 = 0"
  unfolding slice1_def by (simp add : to_bl_0)

lemma slice_0 [simp] : "slice n 0 = 0"
  unfolding slice_def by auto

lemma slice_take': "slice n w = of_bl (take (size w - n) (to_bl w))"
  unfolding slice_def' slice1_def
  by (simp add : takefill_alt word_size)

lemmas slice_take = slice_take' [unfolded word_size]

-- "shiftr to a word of the same size is just slice, 
    slice is just shiftr then ucast"
lemmas shiftr_slice = trans
  [OF shiftr_bl [THEN meta_eq_to_obj_eq] slice_take [symmetric], standard]

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
  "sl = slice1 n w ==> fs = size sl ==> fs + k = n ==> 
    to_bl sl = takefill False fs (drop k (to_bl w))"
  unfolding slice1_def word_size of_bl_def uint_bl
  by (clarsimp simp: word_ubin.eq_norm bl_bin_bl_rep_drop drop_takefill)

lemma slice1_up_alt': 
  "sl = slice1 n w ==> fs = size sl ==> fs = n + k ==> 
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
  "rc = revcast w ==> slice1 (size rc) w = rc"
  unfolding slice1_def revcast_def' by (simp add : word_size)

lemmas revcast_slice1 = refl [THEN revcast_slice1']

lemma slice1_tf_tf': 
  "to_bl (slice1 n w :: 'a :: len0 word) = 
   rev (takefill False (len_of TYPE('a)) (rev (takefill False n (to_bl w))))"
  unfolding slice1_def by (rule word_rev_tf)

lemmas slice1_tf_tf = slice1_tf_tf'
  [THEN word_bl.Rep_inverse', symmetric, standard]

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
  "res = slice n (word_reverse w) ==> n + k + size res = size w ==> 
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

lemmas word_split_bin' = word_split_def [THEN meta_eq_to_obj_eq, standard]
lemmas word_cat_bin' = word_cat_def [THEN meta_eq_to_obj_eq, standard]

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
  "wc = word_cat a b ==> wc !! n = (n < size wc & 
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

lemma of_bl_True: 
  "(of_bl (True#xs)::'a::len word) = 2^length xs + of_bl xs"
  by (subst of_bl_append [where xs="[True]", simplified])
     (simp add: word_1_bl)

lemma of_bl_Cons:
  "of_bl (x#xs) = of_bool x * 2^length xs + of_bl xs"
  by (cases x) (simp_all add: of_bl_True)

lemma split_uint_lem: "bin_split n (uint (w :: 'a :: len0 word)) = (a, b) ==> 
  a = bintrunc (len_of TYPE('a) - n) a & b = bintrunc (len_of TYPE('a)) b"
  apply (frule word_ubin.norm_Rep [THEN ssubst])
  apply (drule bin_split_trunc1)
  apply (drule sym [THEN trans])
  apply assumption
  apply safe
  done

lemma word_split_bl': 
  "std = size c - size b ==> (word_split c = (a, b)) ==> 
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
   apply (simp add: word_0_bl word_0_wi_Pls)
  apply (simp add : of_bl_def to_bl_def)
  apply (subst bin_split_take1 [symmetric])
    prefer 2
    apply assumption
   apply simp
  apply (erule thin_rl)
  apply (erule arg_cong [THEN trans])
  apply (simp add : word_ubin.norm_eq_iff [symmetric])
  done

lemma word_split_bl: "std = size c - size b ==> 
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

lemmas test_bit_split = 
  test_bit_split' [THEN mp, simplified all_simps, standard]

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
  apply (fastsimp intro ! : word_eqI simp add : word_size)
  done

-- {* this odd result is analogous to @{text "ucast_id"}, 
      result to the length given by the result type *}

lemma word_cat_id: "word_cat a b = b"
  unfolding word_cat_bin' by (simp add: word_ubin.inverse_norm)

-- "limited hom result"
lemma word_cat_hom:
  "len_of TYPE('a::len0) <= len_of TYPE('b::len0) + len_of TYPE ('c::len0)
  ==>
  (word_cat (word_of_int w :: 'b word) (b :: 'c word) :: 'a word) = 
  word_of_int (bin_cat w (size b) (uint b))"
  apply (unfold word_cat_def word_size) 
  apply (clarsimp simp add : word_ubin.norm_eq_iff [symmetric]
      word_ubin.eq_norm bintr_cat min_def)
  apply arith
  done

lemma word_cat_split_alt:
  "size w <= size u + size v ==> word_split w = (u, v) ==> word_cat u v = w"
  apply (rule word_eqI)
  apply (drule test_bit_split)
  apply (clarsimp simp add : test_bit_cat word_size)
  apply safe
  apply arith
  done

lemmas word_cat_split_size = 
  sym [THEN [2] word_cat_split_alt [symmetric], standard]


subsubsection "Split and slice"

lemma split_slices: 
  "word_split w = (u, v) ==> u = slice (size v) w & v = slice 0 w"
  apply (drule test_bit_split)
  apply (rule conjI)
   apply (rule word_eqI, clarsimp simp: nth_slice word_size)+
  done

lemma slice_cat1':
  "wc = word_cat a b ==> size wc >= size a + size b ==> slice (size b) wc = a"
  apply safe
  apply (rule word_eqI)
  apply (simp add: nth_slice test_bit_cat word_size)
  done

lemmas slice_cat1 = refl [THEN slice_cat1']
lemmas slice_cat2 = trans [OF slice_id word_cat_id]

lemma cat_slices:
  "a = slice n c ==> b = slice 0 c ==> n = size b ==>
    size a + size b >= size c ==> word_cat a b = c"
  apply safe
  apply (rule word_eqI)
  apply (simp add: nth_slice test_bit_cat word_size)
  apply safe
  apply arith
  done

lemma word_split_cat_alt:
  "w = word_cat u v ==> size u + size v <= size w ==> word_split w = (u, v)"
  apply (case_tac "word_split ?w")
  apply (rule trans, assumption)
  apply (drule test_bit_split)
  apply safe
   apply (rule word_eqI, clarsimp simp: test_bit_cat word_size)+
  done

lemmas word_cat_bl_no_bin [simp] =
  word_cat_bl [where a="number_of a" 
                 and b="number_of b", 
               unfolded to_bl_no_bin, standard]

lemmas word_split_bl_no_bin [simp] =
  word_split_bl_eq [where c="number_of c", unfolded to_bl_no_bin, standard]

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
  "sw = word_rsplit w ==> m < size (hd sw :: 'a :: len word) ==> 
    k < length sw ==> (rev sw ! k) !! m = (w !! (k * size (hd sw) + m))"
  apply (unfold word_rsplit_def word_test_bit_def)
  apply (rule trans)
   apply (rule_tac f = "%x. bin_nth x m" in arg_cong)
   apply (rule nth_map [symmetric])
   apply simp
  apply (rule bin_nth_rsplit)
     apply simp_all
  apply (simp add : word_size rev_map map_compose [symmetric])
  apply (rule trans)
   defer
   apply (rule map_ident [THEN fun_cong])
  apply (rule refl [THEN map_cong])
  apply (simp add : word_ubin.eq_norm)
  apply (erule bin_rsplit_size_sign [OF len_gt_0 refl])
  done

lemma word_rcat_bl: "word_rcat wl == of_bl (concat (map to_bl wl))"
  unfolding word_rcat_def to_bl_def' of_bl_def
  by (clarsimp simp add : bin_rcat_bl map_compose)

lemma size_rcat_lem':
  "size (concat (map to_bl wl)) = length wl * size (hd wl)"
  unfolding word_size by (induct wl) auto

lemmas size_rcat_lem = size_rcat_lem' [unfolded word_size]

lemmas td_gal_lt_len = len_gt_0 [THEN td_gal_lt, standard]

lemma nth_rcat_lem' [rule_format] :
  "sw = size (hd wl  :: 'a :: len word) ==> (ALL n. n < size wl * sw --> 
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
  "sw = size (hd wl :: 'a :: len word) ==> rc = word_rcat wl ==> rc !! n = 
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
  "[u,v] = p ==> [su,sv] = q ==> word_rsplit u = su ==> 
    word_rsplit v = sv ==> length su = length sv"
  apply (unfold word_rsplit_def)
  apply (auto simp add : bin_rsplit_len_indep)
  done

lemmas word_rsplit_len_indep = word_rsplit_len_indep' [OF refl refl refl refl]

lemma length_word_rsplit_size: 
  "n = len_of TYPE ('a :: len) ==> 
    (length (word_rsplit w :: 'a word list) <= m) = (size w <= m * n)"
  apply (unfold word_rsplit_def word_size)
  apply (clarsimp simp add : bin_rsplit_len_le)
  done

lemmas length_word_rsplit_lt_size = 
  length_word_rsplit_size [unfolded Not_eq_iff linorder_not_less [symmetric]]

lemma length_word_rsplit_exp_size: 
  "n = len_of TYPE ('a :: len) ==> 
    length (word_rsplit w :: 'a word list) = (size w + n - 1) div n"
  unfolding word_rsplit_def by (clarsimp simp add : word_size bin_rsplit_len)

lemma length_word_rsplit_even_size: 
  "n = len_of TYPE ('a :: len) ==> size w = m * n ==> 
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
  "word_rcat (ws :: 'a :: len word list) = frcw ==> 
    size frcw = length ws * len_of TYPE ('a) ==> 
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
  "word_rcat (ws :: 'a :: len word list) = frcw ==> 
    size frcw = length ws * len_of TYPE ('a) ==> word_rsplit frcw = ws" 
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
  apply (simp add : word_size msrevs)
  apply (subst nth_rev)
   apply arith
  apply (simp add : le0 [THEN [2] xtr7, THEN diff_Suc_less])
  apply safe
  apply (simp add : diff_mult_distrib)
  apply (rule mpl_lem)
  apply (cases "size ws")
   apply simp_all
  done

lemmas word_rsplit_rcat_size = refl [THEN word_rsplit_rcat_size']


subsection "Rotation"

lemmas rotater_0' [simp] = rotater_def [where n = "0", simplified]

lemmas word_rot_defs = word_roti_def word_rotr_def word_rotl_def

lemma rotate_eq_mod: 
  "m mod length xs = n mod length xs ==> rotate m xs = rotate n xs"
  apply (rule box_equals)
    defer
    apply (rule rotate_conv_mod [symmetric])+
  apply simp
  done

lemmas rotate_eqs [standard] = 
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

lemmas rotater_rev = rotater_rev' [where xs = "rev ys", simplified, standard]

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

lemmas rotate_lr [simp] = rotate_inv_eq [THEN conjunct1, standard]
lemmas rotate_rl [simp] =
  rotate_inv_eq [THEN conjunct2, THEN conjunct1, standard]

lemma rotate_gal: "(rotater n xs = ys) = (rotate n ys = xs)"
  by auto

lemma rotate_gal': "(ys = rotater n xs) = (xs = rotate n ys)"
  by auto

lemma length_rotater [simp]: 
  "length (rotater n xs) = length xs"
  by (simp add : rotater_rev)

lemmas rrs0 = rotate_eqs [THEN restrict_to_left, 
  simplified rotate_gal [symmetric] rotate_gal' [symmetric], standard]
lemmas rrs1 = rrs0 [THEN refl [THEN rev_iffD1]]
lemmas rotater_eqs = rrs1 [simplified length_rotater, standard]
lemmas rotater_0 = rotater_eqs (1)
lemmas rotater_add = rotater_eqs (2)


subsubsection "map, map2, commuting with rotate(r)"

lemma last_map: "xs ~= [] ==> last (map f xs) = f (last xs)"
  by (induct xs) auto

lemma butlast_map:
  "xs ~= [] ==> butlast (map f xs) = map f (butlast xs)"
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
  "length xs = length ys ==> 
    rotater1 (zip xs ys) = zip (rotater1 xs) (rotater1 ys)" 
  apply (unfold rotater1_def)
  apply (cases "xs")
   apply auto
   apply ((case_tac ys, auto simp: neq_Nil_conv but_last_zip)[1])+
  done

lemma rotater1_map2:
  "length xs = length ys ==> 
    rotater1 (map2 f xs ys) = map2 f (rotater1 xs) (rotater1 ys)" 
  unfolding map2_def by (simp add: rotater1_map rotater1_zip)

lemmas lrth = 
  box_equals [OF asm_rl length_rotater [symmetric] 
                 length_rotater [symmetric], 
              THEN rotater1_map2]

lemma rotater_map2: 
  "length xs = length ys ==> 
    rotater n (map2 f xs ys) = map2 f (rotater n xs) (rotater n ys)" 
  by (induct n) (auto intro!: lrth)

lemma rotate1_map2:
  "length xs = length ys ==> 
    rotate1 (map2 f xs ys) = map2 f (rotate1 xs) (rotate1 ys)" 
  apply (unfold map2_def)
  apply (cases xs)
   apply (cases ys, auto simp add : rotate1_def)+
  done

lemmas lth = box_equals [OF asm_rl length_rotate [symmetric] 
  length_rotate [symmetric], THEN rotate1_map2]

lemma rotate_map2: 
  "length xs = length ys ==> 
    rotate n (map2 f xs ys) = map2 f (rotate n xs) (rotate n ys)" 
  by (induct n) (auto intro!: lth)


-- "corresponding equalities for word rotation"

lemma to_bl_rotl: 
  "to_bl (word_rotl n w) = rotate n (to_bl w)"
  by (simp add: word_bl.Abs_inverse' word_rotl_def)

lemmas blrs0 = rotate_eqs [THEN to_bl_rotl [THEN trans]]

lemmas word_rotl_eqs =
  blrs0 [simplified word_bl.Rep' word_bl.Rep_inject to_bl_rotl [symmetric]]

lemma to_bl_rotr: 
  "to_bl (word_rotr n w) = rotater n (to_bl w)"
  by (simp add: word_bl.Abs_inverse' word_rotr_def)

lemmas brrs0 = rotater_eqs [THEN to_bl_rotr [THEN trans]]

lemmas word_rotr_eqs =
  brrs0 [simplified word_bl.Rep' word_bl.Rep_inject to_bl_rotr [symmetric]]

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
    "\<And>m n xs. m = n ==> rotater m xs = rotater n xs"
    by auto

  have rotate_eq_lem: 
    "\<And>m n xs. m = n ==> rotate m xs = rotate n xs"
    by auto

  note rpts [symmetric, standard] = 
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
  apply (simp only: zmod_int zadd_int [symmetric])
  apply (simp add: rdmods)
  done

lemmas word_roti_conv_mod = word_roti_conv_mod' [unfolded word_size]


subsubsection "Word rotation commutes with bit-wise operations"

(* using locale to not pollute lemma namespace *)
locale word_rotate 

context word_rotate
begin

lemmas word_rot_defs' = to_bl_rotl to_bl_rotr

lemmas blwl_syms [symmetric] = bl_word_not bl_word_and bl_word_or bl_word_xor

lemmas lbl_lbl = trans [OF word_bl.Rep' word_bl.Rep' [symmetric]]

lemmas ths_map2 [OF lbl_lbl] = rotate_map2 rotater_map2

lemmas ths_map [where xs = "to_bl v", standard] = rotate_map rotater_map

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
  simplified word_bl.Rep', standard]

lemmas bl_word_rotr_dt = trans [OF to_bl_rotr rotater_drop_take,
  simplified word_bl.Rep', standard]

lemma bl_word_roti_dt': 
  "n = nat ((- i) mod int (size (w :: 'a :: len word))) ==> 
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

lemmas word_rotl_dt = bl_word_rotl_dt 
  [THEN word_bl.Rep_inverse' [symmetric], standard] 
lemmas word_rotr_dt = bl_word_rotr_dt 
  [THEN word_bl.Rep_inverse' [symmetric], standard]
lemmas word_roti_dt = bl_word_roti_dt 
  [THEN word_bl.Rep_inverse' [symmetric], standard]

lemma word_rotx_0 [simp] : "word_rotr i 0 = 0 & word_rotl i 0 = 0"
  by (simp add : word_rotr_dt word_rotl_dt to_bl_0 replicate_add [symmetric])

lemma word_roti_0' [simp] : "word_roti n 0 = 0"
  unfolding word_roti_def by auto

lemmas word_rotr_dt_no_bin' [simp] = 
  word_rotr_dt [where w="number_of w", unfolded to_bl_no_bin, standard]

lemmas word_rotl_dt_no_bin' [simp] = 
  word_rotl_dt [where w="number_of w", unfolded to_bl_no_bin, standard]

declare word_roti_def [simp]

end

