(* 
    Author:     Jeremy Dawson and Gerwin Klein, NICTA

  contains arithmetic theorems for word, instantiations to
  arithmetic type classes and tactics for reducing word arithmetic
  to linear arithmetic on int or nat
*) 

header {* Word Arithmetic *}

theory WordArith
imports WordDefinition
begin

lemma word_less_alt: "(a < b) = (uint a < uint b)"
  unfolding word_less_def word_le_def
  by (auto simp del: word_uint.Rep_inject 
           simp: word_uint.Rep_inject [symmetric])

lemma signed_linorder: "linorder word_sle word_sless"
proof
qed (unfold word_sle_def word_sless_def, auto)

interpretation signed: linorder "word_sle" "word_sless"
  by (rule signed_linorder)

lemmas word_arith_wis = 
  word_add_def word_mult_def word_minus_def 
  word_succ_def word_pred_def word_0_wi word_1_wi

lemma udvdI: 
  "0 \<le> n ==> uint b = n * uint a ==> a udvd b"
  by (auto simp: udvd_def)

lemmas word_div_no [simp] = 
  word_div_def [of "number_of a" "number_of b", standard]

lemmas word_mod_no [simp] = 
  word_mod_def [of "number_of a" "number_of b", standard]

lemmas word_less_no [simp] = 
  word_less_def [of "number_of a" "number_of b", standard]

lemmas word_le_no [simp] = 
  word_le_def [of "number_of a" "number_of b", standard]

lemmas word_sless_no [simp] = 
  word_sless_def [of "number_of a" "number_of b", standard]

lemmas word_sle_no [simp] = 
  word_sle_def [of "number_of a" "number_of b", standard]

(* following two are available in class number_ring, 
  but convenient to have them here here;
  note - the number_ring versions, numeral_0_eq_0 and numeral_1_eq_1
  are in the default simpset, so to use the automatic simplifications for
  (eg) sint (number_of bin) on sint 1, must do
  (simp add: word_1_no del: numeral_1_eq_1) 
  *)
lemmas word_0_wi_Pls = word_0_wi [folded Pls_def]
lemmas word_0_no = word_0_wi_Pls [folded word_no_wi]

lemma int_one_bin: "(1 :: int) == (Int.Pls BIT bit.B1)"
  unfolding Pls_def Bit_def by auto

lemma word_1_no: 
  "(1 :: 'a :: len0 word) == number_of (Int.Pls BIT bit.B1)"
  unfolding word_1_wi word_number_of_def int_one_bin by auto

lemma word_m1_wi: "-1 == word_of_int -1" 
  by (rule word_number_of_alt)

lemma word_m1_wi_Min: "-1 = word_of_int Int.Min"
  by (simp add: word_m1_wi number_of_eq)

lemma word_0_bl: "of_bl [] = 0" 
  unfolding word_0_wi of_bl_def by (simp add : Pls_def)

lemma word_1_bl: "of_bl [True] = 1" 
  unfolding word_1_wi of_bl_def
  by (simp add : bl_to_bin_def Bit_def Pls_def)

lemma uint_0 [simp] : "(uint 0 = 0)" 
  unfolding word_0_wi
  by (simp add: word_ubin.eq_norm Pls_def [symmetric])

lemma of_bl_0 [simp] : "of_bl (replicate n False) = 0"
  by (simp add : word_0_wi of_bl_def bl_to_bin_rep_False Pls_def)

lemma to_bl_0: 
  "to_bl (0::'a::len0 word) = replicate (len_of TYPE('a)) False"
  unfolding uint_bl
  by (simp add : word_size bin_to_bl_Pls Pls_def [symmetric])

lemma uint_0_iff: "(uint x = 0) = (x = 0)"
  by (auto intro!: word_uint.Rep_eqD)

lemma unat_0_iff: "(unat x = 0) = (x = 0)"
  unfolding unat_def by (auto simp add : nat_eq_iff uint_0_iff)

lemma unat_0 [simp]: "unat 0 = 0"
  unfolding unat_def by auto

lemma size_0_same': "size w = 0 ==> w = (v :: 'a :: len0 word)"
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

(* abstraction preserves the operations
  (the definitions tell this for bins in range uint) *)

lemmas arths = 
  bintr_ariths [THEN word_ubin.norm_eq_iff [THEN iffD1],
                folded word_ubin.eq_norm, standard]

lemma wi_homs: 
  shows
  wi_hom_add: "word_of_int a + word_of_int b = word_of_int (a + b)" and
  wi_hom_mult: "word_of_int a * word_of_int b = word_of_int (a * b)" and
  wi_hom_neg: "- word_of_int a = word_of_int (- a)" and
  wi_hom_succ: "word_succ (word_of_int a) = word_of_int (Int.succ a)" and
  wi_hom_pred: "word_pred (word_of_int a) = word_of_int (Int.pred a)"
  by (auto simp: word_arith_wis arths)

lemmas wi_hom_syms = wi_homs [symmetric]

lemma word_sub_def: "a - b == a + - (b :: 'a :: len0 word)"
  unfolding word_sub_wi diff_def
  by (simp only : word_uint.Rep_inverse wi_hom_syms)
    
lemmas word_diff_minus = word_sub_def [THEN meta_eq_to_obj_eq, standard]

lemma word_of_int_sub_hom:
  "(word_of_int a) - word_of_int b = word_of_int (a - b)"
  unfolding word_sub_def diff_def by (simp only : wi_homs)

lemmas new_word_of_int_homs = 
  word_of_int_sub_hom wi_homs word_0_wi word_1_wi 

lemmas new_word_of_int_hom_syms = new_word_of_int_homs [symmetric, standard]

lemmas word_of_int_hom_syms =
  new_word_of_int_hom_syms [unfolded succ_def pred_def]

lemmas word_of_int_homs =
  new_word_of_int_homs [unfolded succ_def pred_def]

lemmas word_of_int_add_hom = word_of_int_homs (2)
lemmas word_of_int_mult_hom = word_of_int_homs (3)
lemmas word_of_int_minus_hom = word_of_int_homs (4)
lemmas word_of_int_succ_hom = word_of_int_homs (5)
lemmas word_of_int_pred_hom = word_of_int_homs (6)
lemmas word_of_int_0_hom = word_of_int_homs (7)
lemmas word_of_int_1_hom = word_of_int_homs (8)

(* now, to get the weaker results analogous to word_div/mod_def *)

lemmas word_arith_alts = 
  word_sub_wi [unfolded succ_def pred_def, standard]
  word_arith_wis [unfolded succ_def pred_def, standard]

lemmas word_sub_alt = word_arith_alts (1)
lemmas word_add_alt = word_arith_alts (2)
lemmas word_mult_alt = word_arith_alts (3)
lemmas word_minus_alt = word_arith_alts (4)
lemmas word_succ_alt = word_arith_alts (5)
lemmas word_pred_alt = word_arith_alts (6)
lemmas word_0_alt = word_arith_alts (7)
lemmas word_1_alt = word_arith_alts (8)

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
  word_arith_alts [THEN trans [OF uint_cong int_word_uint], standard]

lemmas uint_word_arith_bintrs = uint_word_ariths [folded bintrunc_mod2p]

(* similar expressions for sint (arith operations) *)
lemmas sint_word_ariths = uint_word_arith_bintrs
  [THEN uint_sint [symmetric, THEN trans],
  unfolded uint_sint bintr_arith1s bintr_ariths 
    len_gt_0 [THEN bin_sbin_eq_iff'] word_sbin.norm_Rep, standard]

lemmas uint_div_alt = word_div_def
  [THEN trans [OF uint_cong int_word_uint], standard]
lemmas uint_mod_alt = word_mod_def
  [THEN trans [OF uint_cong int_word_uint], standard]

lemma word_pred_0_n1: "word_pred 0 = word_of_int -1"
  unfolding word_pred_def number_of_eq
  by (simp add : pred_def word_no_wi)

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

lemma word_arith_eqs:
  fixes a :: "'a::len0 word"
  fixes b :: "'a::len0 word"
  shows
  word_add_0: "0 + a = a" and
  word_add_0_right: "a + 0 = a" and
  word_mult_1: "1 * a = a" and
  word_mult_1_right: "a * 1 = a" and
  word_add_commute: "a + b = b + a" and
  word_add_assoc: "a + b + c = a + (b + c)" and
  word_add_left_commute: "a + (b + c) = b + (a + c)" and
  word_mult_commute: "a * b = b * a" and
  word_mult_assoc: "a * b * c = a * (b * c)" and
  word_mult_left_commute: "a * (b * c) = b * (a * c)" and
  word_left_distrib: "(a + b) * c = a * c + b * c" and
  word_right_distrib: "a * (b + c) = a * b + a * c" and
  word_left_minus: "- a + a = 0" and
  word_diff_0_right: "a - 0 = a" and
  word_diff_self: "a - a = 0"
  using word_of_int_Ex [of a] 
        word_of_int_Ex [of b] 
        word_of_int_Ex [of c]
  by (auto simp: word_of_int_hom_syms [symmetric]
                 zadd_0_right add_commute add_assoc add_left_commute
                 mult_commute mult_assoc mult_left_commute
                 left_distrib right_distrib)
  
lemmas word_add_ac = word_add_commute word_add_assoc word_add_left_commute
lemmas word_mult_ac = word_mult_commute word_mult_assoc word_mult_left_commute
  
lemmas word_plus_ac0 = word_add_0 word_add_0_right word_add_ac
lemmas word_times_ac1 = word_mult_1 word_mult_1_right word_mult_ac


subsection "Order on fixed-length words"

lemma word_order_trans: "x <= y ==> y <= z ==> x <= (z :: 'a :: len0 word)"
  unfolding word_le_def by auto

lemma word_order_refl: "z <= (z :: 'a :: len0 word)"
  unfolding word_le_def by auto

lemma word_order_antisym: "x <= y ==> y <= x ==> x = (y :: 'a :: len0 word)"
  unfolding word_le_def by (auto intro!: word_uint.Rep_eqD)

lemma word_order_linear:
  "y <= x | x <= (y :: 'a :: len0 word)"
  unfolding word_le_def by auto

lemma word_zero_le [simp] :
  "0 <= (y :: 'a :: len0 word)"
  unfolding word_le_def by auto
  
instance word :: (len0) semigroup_add
  by intro_classes (simp add: word_add_assoc)

instance word :: (len0) linorder
  by intro_classes (auto simp: word_less_def word_le_def)

instance word :: (len0) ring
  by intro_classes
     (auto simp: word_arith_eqs word_diff_minus 
                 word_diff_self [unfolded word_diff_minus])

lemma word_m1_ge [simp] : "word_pred 0 >= y"
  unfolding word_le_def
  by (simp only : word_pred_0_n1 word_uint.eq_norm m1mod2k) auto

lemmas word_n1_ge [simp]  = word_m1_ge [simplified word_sp_01]

lemmas word_not_simps [simp] = 
  word_zero_le [THEN leD] word_m1_ge [THEN leD] word_n1_ge [THEN leD]

lemma word_gt_0: "0 < y = (0 ~= (y :: 'a :: len0 word))"
  unfolding word_less_def by auto

lemmas word_gt_0_no [simp] = word_gt_0 [of "number_of y", standard]

lemma word_sless_alt: "(a <s b) == (sint a < sint b)"
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

lemmas unat_mono = word_less_nat_alt [THEN iffD1, standard]

lemma word_zero_neq_one: "0 < len_of TYPE ('a :: len0) ==> (0 :: 'a word) ~= 1";
  unfolding word_arith_wis
  by (auto simp add: word_ubin.norm_eq_iff [symmetric] gr0_conv_Suc)

lemmas lenw1_zero_neq_one = len_gt_0 [THEN word_zero_neq_one]

lemma no_no [simp] : "number_of (number_of b) = number_of b"
  by (simp add: number_of_eq)

lemma unat_minus_one: "x ~= 0 ==> unat (x - 1) = unat x - 1"
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
    
lemma measure_unat: "p ~= 0 ==> unat (p - 1) < unat p"
  by (simp add: unat_minus_one) (simp add: unat_0_iff [symmetric])
  
lemmas uint_add_ge0 [simp] =
  add_nonneg_nonneg [OF uint_ge_0 uint_ge_0, standard]
lemmas uint_mult_ge0 [simp] =
  mult_nonneg_nonneg [OF uint_ge_0 uint_ge_0, standard]

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

lemmas uint_sub_if' =
  trans [OF uint_word_ariths(1) mod_sub_if_z, simplified, standard]
lemmas uint_plus_if' =
  trans [OF uint_word_ariths(2) mod_add_if_z, simplified, standard]


subsection {* Definition of uint\_arith *}

lemma word_of_int_inverse:
  "word_of_int r = a ==> 0 <= r ==> r < 2 ^ len_of TYPE('a) ==> 
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
lemma power_False_cong: "False ==> a ^ b = c ^ d" 
  by auto

(* uint_arith_tac: reduce to arithmetic on int, try to solve by arith *)
ML {*
fun uint_arith_ss_of ss = 
  ss addsimps @{thms uint_arith_simps}
     delsimps @{thms word_uint.Rep_inject}
     addsplits @{thms split_if_asm} 
     addcongs @{thms power_False_cong}

fun uint_arith_tacs ctxt = 
  let
    fun arith_tac' n t = Arith_Data.verbose_arith_tac ctxt n t handle COOPER => Seq.empty;
    val cs = local_claset_of ctxt;
    val ss = local_simpset_of ctxt;
  in 
    [ clarify_tac cs 1,
      full_simp_tac (uint_arith_ss_of ss) 1,
      ALLGOALS (full_simp_tac (HOL_ss addsplits @{thms uint_splits} 
                                      addcongs @{thms power_False_cong})),
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
  by (simp add: word_add_ac add_ac no_olen_add)

lemmas olen_add_eqv = trans [OF no_olen_add no_olen_add' [symmetric], standard]

lemmas uint_plus_simple_iff = trans [OF no_olen_add uint_add_lem, standard]
lemmas uint_plus_simple = uint_plus_simple_iff [THEN iffD1, standard]
lemmas uint_minus_simple_iff = trans [OF no_ulen_sub uint_sub_lem, standard]
lemmas uint_minus_simple_alt = uint_sub_lem [folded word_le_def]
lemmas word_sub_le_iff = no_ulen_sub [folded word_le_def]
lemmas word_sub_le = word_sub_le_iff [THEN iffD2, standard]

lemma word_less_sub1: 
  "(x :: 'a :: len word) ~= 0 ==> (1 < x) = (0 < x - 1)"
  by uint_arith

lemma word_le_sub1: 
  "(x :: 'a :: len word) ~= 0 ==> (1 <= x) = (0 <= x - 1)"
  by uint_arith

lemma sub_wrap_lt: 
  "((x :: 'a :: len0 word) < x - z) = (x < z)"
  by uint_arith

lemma sub_wrap: 
  "((x :: 'a :: len0 word) <= x - z) = (z = 0 | x < z)"
  by uint_arith

lemma plus_minus_not_NULL_ab: 
  "(x :: 'a :: len0 word) <= ab - c ==> c <= ab ==> c ~= 0 ==> x + c ~= 0"
  by uint_arith

lemma plus_minus_no_overflow_ab: 
  "(x :: 'a :: len0 word) <= ab - c ==> c <= ab ==> x <= x + c" 
  by uint_arith

lemma le_minus': 
  "(a :: 'a :: len0 word) + c <= b ==> a <= a + c ==> c <= b - a"
  by uint_arith

lemma le_plus': 
  "(a :: 'a :: len0 word) <= b ==> c <= b - a ==> a + c <= b"
  by uint_arith

lemmas le_plus = le_plus' [rotated]

lemmas le_minus = leD [THEN thin_rl, THEN le_minus', standard]

lemma word_plus_mono_right: 
  "(y :: 'a :: len0 word) <= z ==> x <= x + z ==> x + y <= x + z"
  by uint_arith

lemma word_less_minus_cancel: 
  "y - x < z - x ==> x <= z ==> (y :: 'a :: len0 word) < z"
  by uint_arith

lemma word_less_minus_mono_left: 
  "(y :: 'a :: len0 word) < z ==> x <= y ==> y - x < z - x"
  by uint_arith

lemma word_less_minus_mono:  
  "a < c ==> d < b ==> a - b < a ==> c - d < c 
  ==> a - b < c - (d::'a::len word)"
  by uint_arith

lemma word_le_minus_cancel: 
  "y - x <= z - x ==> x <= z ==> (y :: 'a :: len0 word) <= z"
  by uint_arith

lemma word_le_minus_mono_left: 
  "(y :: 'a :: len0 word) <= z ==> x <= y ==> y - x <= z - x"
  by uint_arith

lemma word_le_minus_mono:  
  "a <= c ==> d <= b ==> a - b <= a ==> c - d <= c 
  ==> a - b <= c - (d::'a::len word)"
  by uint_arith

lemma plus_le_left_cancel_wrap: 
  "(x :: 'a :: len0 word) + y' < x ==> x + y < x ==> (x + y' < x + y) = (y' < y)"
  by uint_arith

lemma plus_le_left_cancel_nowrap: 
  "(x :: 'a :: len0 word) <= x + y' ==> x <= x + y ==> 
    (x + y' < x + y) = (y' < y)" 
  by uint_arith

lemma word_plus_mono_right2: 
  "(a :: 'a :: len0 word) <= a + b ==> c <= b ==> a <= a + c"
  by uint_arith

lemma word_less_add_right: 
  "(x :: 'a :: len0 word) < y - z ==> z <= y ==> x + z < y"
  by uint_arith

lemma word_less_sub_right: 
  "(x :: 'a :: len0 word) < y + z ==> y <= x ==> x - y < z"
  by uint_arith

lemma word_le_plus_either: 
  "(x :: 'a :: len0 word) <= y | x <= z ==> y <= y + z ==> x <= y + z"
  by uint_arith

lemma word_less_nowrapI: 
  "(x :: 'a :: len0 word) < z - k ==> k <= z ==> 0 < k ==> x < x + k"
  by uint_arith

lemma inc_le: "(i :: 'a :: len word) < m ==> i + 1 <= m"
  by uint_arith

lemma inc_i: 
  "(1 :: 'a :: len word) <= i ==> i < m ==> 1 <= (i + 1) & i + 1 <= m"
  by uint_arith

lemma udvd_incr_lem:
  "up < uq ==> up = ua + n * uint K ==> 
    uq = ua + n' * uint K ==> up + uint K <= uq"
  apply clarsimp
  apply (drule less_le_mult)
  apply safe
  done

lemma udvd_incr': 
  "p < q ==> uint p = ua + n * uint K ==> 
    uint q = ua + n' * uint K ==> p + K <= q" 
  apply (unfold word_less_alt word_le_def)
  apply (drule (2) udvd_incr_lem)
  apply (erule uint_add_le [THEN order_trans])
  done

lemma udvd_decr': 
  "p < q ==> uint p = ua + n * uint K ==> 
    uint q = ua + n' * uint K ==> p <= q - K"
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
  "xy < k ==> z udvd xy ==> z udvd k ==> xy <= k - z"
  apply (unfold udvd_def)
  apply clarify
  apply (erule (2) udvd_decr0)
  done

ML{*Delsimprocs cancel_factors*}
lemma udvd_incr2_K: 
  "p < a + s ==> a <= a + s ==> K udvd s ==> K udvd p - a ==> a <= p ==> 
    0 < K ==> p <= p + K & p + K <= a + s"
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
ML{*Delsimprocs cancel_factors*}

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


subsection "Arithmetic type class instantiations"

instance word :: (len0) comm_monoid_add ..

instance word :: (len0) comm_monoid_mult
  apply (intro_classes)
   apply (simp add: word_mult_commute)
  apply (simp add: word_mult_1)
  done

instance word :: (len0) recpower ..

instance word :: (len0) comm_semiring 
  by (intro_classes) (simp add : word_left_distrib)

instance word :: (len0) ab_group_add ..

instance word :: (len0) comm_ring ..

instance word :: (len) comm_semiring_1 
  by (intro_classes) (simp add: lenw1_zero_neq_one)

instance word :: (len) recpower ..

instance word :: (len) comm_ring_1 ..

instance word :: (len0) comm_semiring_0 ..

instance word :: (len0) order ..

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

lemma word_of_nat: "of_nat n = word_of_int (int n)"
  by (induct n) (auto simp add : word_of_int_hom_syms)

lemma word_of_int: "of_int = word_of_int"
  apply (rule ext)
  apply (unfold of_int_def)
  apply (rule contentsI)
  apply safe
  apply (simp_all add: word_of_nat word_of_int_homs)
   defer
   apply (rule Rep_Integ_ne [THEN nonemptyE])
   apply (rule bexI)
    prefer 2
    apply assumption
   apply (auto simp add: RI_eq_diff)
  done

lemma word_of_int_nat: 
  "0 <= x ==> word_of_int x = of_nat (nat x)"
  by (simp add: of_nat_nat word_of_int)

lemma word_number_of_eq: 
  "number_of w = (of_int w :: 'a :: len word)"
  unfolding word_number_of_def word_of_int by auto

instance word :: (len) number_ring
  by (intro_classes) (simp add : word_number_of_eq)

lemma iszero_word_no [simp] : 
  "iszero (number_of bin :: 'a :: len word) = 
    iszero (number_of (bintrunc (len_of TYPE('a)) bin) :: int)"
  apply (simp add: zero_bintrunc number_of_is_id)
  apply (unfold iszero_def Pls_def)
  apply (rule refl)
  done
    

subsection "Word and nat"

lemma td_ext_unat':
  "n = len_of TYPE ('a :: len) ==> 
    td_ext (unat :: 'a word => nat) of_nat 
    (unats n) (%i. i mod 2 ^ n)"
  apply (unfold td_ext_def' unat_def word_of_nat unats_uints)
  apply (auto intro!: imageI simp add : word_of_int_hom_syms)
  apply (erule word_uint.Abs_inverse [THEN arg_cong])
  apply (simp add: int_word_uint nat_mod_distrib nat_power_eq)
  done

lemmas td_ext_unat = refl [THEN td_ext_unat']
lemmas unat_of_nat = td_ext_unat [THEN td_ext.eq_norm, standard]

interpretation word_unat:
  td_ext "unat::'a::len word => nat" 
         of_nat 
         "unats (len_of TYPE('a::len))"
         "%i. i mod 2 ^ len_of TYPE('a::len)"
  by (rule td_ext_unat)

lemmas td_unat = word_unat.td_thm

lemmas unat_lt2p [iff] = word_unat.Rep [unfolded unats_def mem_Collect_eq]

lemma unat_le: "y <= unat (z :: 'a :: len word) ==> y : unats (len_of TYPE ('a))"
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

lemmas of_nat_2p = mult_1 [symmetric, THEN iffD2 [OF of_nat_0 exI]]

lemma of_nat_gt_0: "of_nat k ~= 0 ==> 0 < k"
  by (cases k) auto

lemma of_nat_neq_0: 
  "0 < k ==> k < 2 ^ len_of TYPE ('a :: len) ==> of_nat k ~= (0 :: 'a word)"
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

lemmas unat_cong = arg_cong [where f = "unat"]
  
lemmas unat_word_ariths = word_arith_nat_defs
  [THEN trans [OF unat_cong unat_of_nat], standard]

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

lemmas unat_plus_if' = 
  trans [OF unat_word_ariths(1) mod_nat_add, simplified, standard]

lemma le_no_overflow: 
  "x <= b ==> a <= a + b ==> x <= a + (b :: 'a :: len0 word)"
  apply (erule order_trans)
  apply (erule olen_add_eqv [THEN iffD1])
  done

lemmas un_ui_le = trans 
  [OF word_le_nat_alt [symmetric] 
      word_le_def, 
   standard]

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
     addsplits @{thms split_if_asm}
     addcongs @{thms power_False_cong}

fun unat_arith_tacs ctxt =   
  let
    fun arith_tac' n t = Arith_Data.verbose_arith_tac ctxt n t handle COOPER => Seq.empty;
    val cs = local_claset_of ctxt;
    val ss = local_simpset_of ctxt;
  in 
    [ clarify_tac cs 1,
      full_simp_tac (unat_arith_ss_of ss) 1,
      ALLGOALS (full_simp_tac (HOL_ss addsplits @{thms unat_splits} 
                                       addcongs @{thms power_False_cong})),
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

lemma unat_sub: "b <= a ==> unat (a - b) = unat a - unat (b :: 'a :: len word)"
  by unat_arith

lemmas no_olen_add_nat = no_plus_overflow_unat_size [unfolded word_size]

lemmas unat_plus_simple = trans [OF no_olen_add_nat unat_add_lem, standard]

lemma word_div_mult: 
  "(0 :: 'a :: len word) < y ==> unat x * unat y < 2 ^ len_of TYPE('a) ==> 
    x * y div y = x"
  apply unat_arith
  apply clarsimp
  apply (subst unat_mult_lem [THEN iffD1])
  apply auto
  done

lemma div_lt': "(i :: 'a :: len word) <= k div x ==> 
    unat i * unat x < 2 ^ len_of TYPE('a)"
  apply unat_arith
  apply clarsimp
  apply (drule mult_le_mono1)
  apply (erule order_le_less_trans)
  apply (rule xtr7 [OF unat_lt2p div_mult_le])
  done

lemmas div_lt'' = order_less_imp_le [THEN div_lt']

lemma div_lt_mult: "(i :: 'a :: len word) < k div x ==> 0 < x ==> i * x < k"
  apply (frule div_lt'' [THEN unat_mult_lem [THEN iffD1]])
  apply (simp add: unat_arith_simps)
  apply (drule (1) mult_less_mono1)
  apply (erule order_less_le_trans)
  apply (rule div_mult_le)
  done

lemma div_le_mult: 
  "(i :: 'a :: len word) <= k div x ==> 0 < x ==> i * x <= k"
  apply (frule div_lt' [THEN unat_mult_lem [THEN iffD1]])
  apply (simp add: unat_arith_simps)
  apply (drule mult_le_mono1)
  apply (erule order_trans)
  apply (rule div_mult_le)
  done

lemma div_lt_uint': 
  "(i :: 'a :: len word) <= k div x ==> uint i * uint x < 2 ^ len_of TYPE('a)"
  apply (unfold uint_nat)
  apply (drule div_lt')
  apply (simp add: zmult_int zless_nat_eq_int_zless [symmetric] 
                   nat_power_eq)
  done

lemmas div_lt_uint'' = order_less_imp_le [THEN div_lt_uint']

lemma word_le_exists': 
  "(x :: 'a :: len0 word) <= y ==> 
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

lemmas word_l_diffs = mcs [where y = "w + x", unfolded add_diff_cancel, standard]
lemmas word_diff_ls = mcs [where z = "w + x", unfolded add_diff_cancel, standard]
lemmas word_plus_mcs = word_diff_ls 
  [where y = "v + x", unfolded add_diff_cancel, standard]

lemmas le_unat_uoi = unat_le [THEN word_unat.Abs_inverse]

lemmas thd = refl [THEN [2] split_div_lemma [THEN iffD2], THEN conjunct1]

lemma thd1:
  "a div b * b \<le> (a::nat)"
  using gt_or_eq_0 [of b]
  apply (rule disjE)
   apply (erule xtr4 [OF thd mult_commute])
  apply clarsimp
  done

lemmas uno_simps [THEN le_unat_uoi, standard] =
  mod_le_divisor div_le_dividend thd1 

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

lemma word_mod_less_divisor: "0 < n ==> m mod n < (n :: 'a :: len word)"
  apply (simp only: word_less_nat_alt word_arith_nat_defs)
  apply (clarsimp simp add : uno_simps)
  done

lemma word_of_int_power_hom: 
  "word_of_int a ^ n = (word_of_int (a ^ n) :: 'a :: len word)"
  by (induct n) (simp_all add : word_of_int_hom_syms power_Suc)

lemma word_arith_power_alt: 
  "a ^ n = (word_of_int (uint a ^ n) :: 'a :: len word)"
  by (simp add : word_of_int_power_hom [symmetric])

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


subsection "Cardinality, finiteness of set of words"

lemmas card_lessThan' = card_lessThan [unfolded lessThan_def]

lemmas card_eq = word_unat.Abs_inj_on [THEN card_image,
  unfolded word_unat.image, unfolded unats_def, standard]

lemmas card_word = trans [OF card_eq card_lessThan', standard]

lemma finite_word_UNIV: "finite (UNIV :: 'a :: len word set)"
apply (rule contrapos_np)
 prefer 2
 apply (erule card_infinite)
apply (simp add: card_word)
done

lemma card_word_size: 
  "card (UNIV :: 'a :: len word set) = (2 ^ size (x :: 'a word))"
unfolding word_size by (rule card_word)

end 
