(*  Title:      HOL/Word/WordBitwise.thy
    Authors:    Thomas Sewell, NICTA and Sascha Boehme, TU Muenchen
*)


theory WordBitwise

imports Word

begin

text {* Helper constants used in defining addition *}

definition
  xor3 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
 "xor3 a b c = (a = (b = c))"

definition
  carry :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
 "carry a b c = ((a \<and> (b \<or> c)) \<or> (b \<and> c))"

lemma carry_simps:
  "carry True a b = (a \<or> b)"
  "carry a True b = (a \<or> b)"
  "carry a b True = (a \<or> b)"
  "carry False a b = (a \<and> b)"
  "carry a False b = (a \<and> b)"
  "carry a b False = (a \<and> b)"
  by (auto simp add: carry_def)

lemma xor3_simps:
  "xor3 True a b = (a = b)"
  "xor3 a True b = (a = b)"
  "xor3 a b True = (a = b)"
  "xor3 False a b = (a \<noteq> b)"
  "xor3 a False b = (a \<noteq> b)"
  "xor3 a b False = (a \<noteq> b)"
  by (simp_all add: xor3_def)

text {* Breaking up word equalities into equalities on their
bit lists. Equalities are generated and manipulated in the
reverse order to to_bl. *}

lemma word_eq_rbl_eq:
  "(x = y) = (rev (to_bl x) = rev (to_bl y))"
  by simp

lemma rbl_word_or:
  "rev (to_bl (x OR y)) = map2 op \<or> (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: map2_def zip_rev bl_word_or rev_map)

lemma rbl_word_and:
  "rev (to_bl (x AND y)) = map2 op \<and> (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: map2_def zip_rev bl_word_and rev_map)

lemma rbl_word_xor:
  "rev (to_bl (x XOR y)) = map2 op \<noteq> (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: map2_def zip_rev bl_word_xor rev_map)

lemma rbl_word_not:
  "rev (to_bl (NOT x)) = map Not (rev (to_bl x))"
  by (simp add: bl_word_not rev_map)

lemma bl_word_sub:
  "to_bl (x - y) = to_bl (x + (- y))"
  by (simp add: diff_def)

lemma rbl_word_1:
  "rev (to_bl (1 :: ('a :: len0) word))
     = takefill False (len_of TYPE('a)) [True]"
  apply (rule_tac s="rev (to_bl (word_succ (0 :: 'a word)))" in trans)
   apply simp
  apply (simp only: rtb_rbl_ariths(1)[OF refl])
  apply simp
  apply (case_tac "len_of TYPE('a)")
   apply simp
  apply (simp add: takefill_alt)
  done

lemma rbl_word_if:
  "rev (to_bl (if P then x else y))
      = map2 (If P) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: map2_def split_def)

lemma rbl_add_carry_Cons:
  "(if car then rbl_succ else id) (rbl_add (x # xs) (y # ys))
        = xor3 x y car # (if carry x y car then rbl_succ else id)
             (rbl_add xs ys)"
  by (simp add: carry_def xor3_def)

lemma rbl_add_suc_carry_fold:
  "length xs = length ys \<Longrightarrow>
   \<forall>car. (if car then rbl_succ else id) (rbl_add xs ys)
        = (foldr (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car))
                 (zip xs ys) (\<lambda>_. [])) car"
  apply (erule list_induct2)
   apply simp
  apply (simp only: rbl_add_carry_Cons)
  apply simp
  done

lemma to_bl_plus_carry:
  "to_bl (x + y)
     = rev (foldr (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car))
                 (rev (zip (to_bl x) (to_bl y))) (\<lambda>_. []) False)"
  using rbl_add_suc_carry_fold[where xs="rev (to_bl x)" and ys="rev (to_bl y)"]
  apply (simp add: word_add_rbl[OF refl refl])
  apply (drule_tac x=False in spec)
  apply (simp add: zip_rev)
  done

definition
 "rbl_plus cin xs ys = foldr
       (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car))
       (zip xs ys) (\<lambda>_. []) cin"

lemma rbl_plus_simps:
  "rbl_plus cin (x # xs) (y # ys)
      = xor3 x y cin # rbl_plus (carry x y cin) xs ys"
  "rbl_plus cin [] ys = []"
  "rbl_plus cin xs [] = []"
  by (simp_all add: rbl_plus_def)

lemma rbl_word_plus:
  "rev (to_bl (x + y)) = rbl_plus False (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: rbl_plus_def to_bl_plus_carry zip_rev)

definition
 "rbl_succ2 b xs = (if b then rbl_succ xs else xs)"

lemma rbl_succ2_simps:
  "rbl_succ2 b [] = []"
  "rbl_succ2 b (x # xs) = (b \<noteq> x) # rbl_succ2 (x \<and> b) xs"
  by (simp_all add: rbl_succ2_def)

lemma twos_complement:
  "- x = word_succ (NOT x)"
  using arg_cong[OF word_add_not[where x=x], where f="\<lambda>a. a - x + 1"]
  by (simp add: word_succ_p1 word_sp_01[unfolded word_succ_p1]
           del: word_add_not)

lemma rbl_word_neg:
  "rev (to_bl (- x)) = rbl_succ2 True (map Not (rev (to_bl x)))"
  by (simp add: twos_complement word_succ_rbl[OF refl]
                bl_word_not rev_map rbl_succ2_def)

lemma rbl_word_cat:
  "rev (to_bl (word_cat x y :: ('a :: len0) word))
     = takefill False (len_of TYPE('a)) (rev (to_bl y) @ rev (to_bl x))"
  by (simp add: word_cat_bl word_rev_tf)

lemma rbl_word_slice:
  "rev (to_bl (slice n w :: ('a :: len0) word))
     = takefill False (len_of TYPE('a)) (drop n (rev (to_bl w)))"
  apply (simp add: slice_take word_rev_tf rev_take)
  apply (cases "n < len_of TYPE('b)", simp_all)
  done

lemma rbl_word_ucast:
  "rev (to_bl (ucast x :: ('a :: len0) word))
     = takefill False (len_of TYPE('a)) (rev (to_bl x))"
  apply (simp add: to_bl_ucast takefill_alt)
  apply (simp add: rev_drop)
  apply (case_tac "len_of TYPE('a) < len_of TYPE('b)")
   apply simp_all
  done

lemma rbl_shiftl:
  "rev (to_bl (w << n)) = takefill False (size w)
     (replicate n False @ rev (to_bl w))"
  by (simp add: bl_shiftl takefill_alt word_size rev_drop)

lemma rbl_shiftr:
  "rev (to_bl (w >> n)) = takefill False (size w)
     (drop n (rev (to_bl w)))"
  by (simp add: shiftr_slice rbl_word_slice word_size)

definition
 "drop_nonempty v n xs
     = (if n < length xs then drop n xs else [last (v # xs)])"

lemma drop_nonempty_simps:
  "drop_nonempty v (Suc n) (x # xs) = drop_nonempty x n xs"
  "drop_nonempty v 0 (x # xs) = (x # xs)"
  "drop_nonempty v n [] = [v]"
  by (simp_all add: drop_nonempty_def)

definition
  "takefill_last x n xs = takefill (last (x # xs)) n xs"

lemma takefill_last_simps:
  "takefill_last z (Suc n) (x # xs) = x # takefill_last x n xs"
  "takefill_last z 0 xs = []"
  "takefill_last z n [] = replicate n z"
  apply (simp_all add: takefill_last_def)
  apply (simp_all add: takefill_alt)
  done

lemma rbl_sshiftr:
  "rev (to_bl (w >>> n)) = 
     takefill_last False (size w) 
        (drop_nonempty False n (rev (to_bl w)))"
  apply (cases "n < size w")
   apply (simp add: bl_sshiftr takefill_last_def word_size
                    takefill_alt rev_take last_rev
                    drop_nonempty_def)
  apply (subgoal_tac "(w >>> n) = of_bl (replicate (size w) (msb w))")
   apply (simp add: word_size takefill_last_def takefill_alt
                    last_rev word_msb_alt word_rev_tf
                    drop_nonempty_def take_Cons')
   apply (case_tac "len_of TYPE('a)", simp_all)
  apply (rule word_eqI)
  apply (simp add: nth_sshiftr word_size test_bit_of_bl
                   msb_nth)
  done

lemma nth_word_of_int:
  "(word_of_int x :: ('a :: len0) word) !! n
      = (n < len_of TYPE('a) \<and> bin_nth x n)"
  apply (simp add: test_bit_bl word_size to_bl_of_bin)
  apply (subst conj_cong[OF refl], erule bin_nth_bl)
  apply (auto)
  done

lemma nth_scast:
  "(scast (x :: ('a :: len) word) :: ('b :: len) word) !! n
     = (n < len_of TYPE('b) \<and>
          (if n < len_of TYPE('a) - 1 then x !! n
           else x !! (len_of TYPE('a) - 1)))"
  by (simp add: scast_def nth_word_of_int nth_sint)

lemma rbl_word_scast:
  "rev (to_bl (scast x :: ('a :: len) word))
     = takefill_last False (len_of TYPE('a))
           (rev (to_bl x))"
  apply (rule nth_equalityI)
   apply (simp add: word_size takefill_last_def)
  apply (clarsimp simp: nth_scast takefill_last_def
                        nth_takefill word_size nth_rev to_bl_nth)
  apply (cases "len_of TYPE('b)")
   apply simp
  apply (clarsimp simp: less_Suc_eq_le linorder_not_less
                        last_rev word_msb_alt[symmetric]
                        msb_nth)
  done

definition
  rbl_mul :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
where
 "rbl_mul xs ys = foldr (\<lambda>x sm. rbl_plus False (map (op \<and> x) ys) (False # sm))
    xs []"

lemma rbl_mul_simps:
  "rbl_mul (x # xs) ys
     = rbl_plus False (map (op \<and> x) ys) (False # rbl_mul xs ys)"
  "rbl_mul [] ys = []"
  by (simp_all add: rbl_mul_def)

lemma takefill_le2:
  "length xs \<le> n \<Longrightarrow>
   takefill x m (takefill x n xs)
     = takefill x m xs"
  by (simp add: takefill_alt replicate_add[symmetric])

lemma take_rbl_plus:
  "\<forall>n b. take n (rbl_plus b xs ys)
    = rbl_plus b (take n xs) (take n ys)"
  apply (simp add: rbl_plus_def take_zip[symmetric])
  apply (rule_tac list="zip xs ys" in list.induct)
   apply simp
  apply (clarsimp simp: split_def)
  apply (case_tac n, simp_all)
  done

lemma word_rbl_mul_induct:
  fixes y :: "'a :: len word" shows
  "length xs \<le> size y
   \<Longrightarrow> rbl_mul xs (rev (to_bl y))
     = take (length xs) (rev (to_bl (of_bl (rev xs) * y)))"
proof (induct xs)
  case Nil
  show ?case
    by (simp add: rbl_mul_simps)
next
  case (Cons z zs)

  have rbl_word_plus':
    "\<And>(x :: 'a word) y.
      to_bl (x + y) = rev (rbl_plus False (rev (to_bl x)) (rev (to_bl y)))"
    by (simp add: rbl_word_plus[symmetric])
  
  have mult_bit: "to_bl (of_bl [z] * y) = map (op \<and> z) (to_bl y)"
    apply (cases z)
     apply (simp cong: map_cong)
    apply (simp add: map_replicate_const cong: map_cong)
    done
 
  have shiftl: "\<And>xs. of_bl xs * 2 * y = (of_bl xs * y) << 1"
    by (simp add: shiftl_t2n)

  have zip_take_triv: "\<And>xs ys n. n = length ys
      \<Longrightarrow> zip (take n xs) ys = zip xs ys"
    by (rule nth_equalityI, simp_all)

  show ?case
    using Cons
    apply (simp add: trans [OF of_bl_append add_commute]
                     rbl_mul_simps rbl_word_plus'
                     Cons.hyps distrib_right mult_bit
                     shiftl rbl_shiftl)
    apply (simp add: takefill_alt word_size rev_map take_rbl_plus
                     min_def)
    apply (simp add: rbl_plus_def zip_take_triv)
    done
qed

lemma rbl_word_mul:
  fixes x :: "'a :: len word"
  shows "rev (to_bl (x * y)) = rbl_mul (rev (to_bl x)) (rev (to_bl y))"
  using word_rbl_mul_induct[where xs="rev (to_bl x)" and y=y]
  by (simp add: word_size)

text {* Breaking up inequalities into bitlist properties. *}

definition
  "rev_bl_order F xs ys =
     (length xs = length ys \<and>
       ((xs = ys \<and> F)
          \<or> (\<exists>n < length xs. drop (Suc n) xs = drop (Suc n) ys
                   \<and> \<not> xs ! n \<and> ys ! n)))"

lemma rev_bl_order_simps:
  "rev_bl_order F [] [] = F"
  "rev_bl_order F (x # xs) (y # ys)
     = rev_bl_order ((y \<and> \<not> x) \<or> ((y \<or> \<not> x) \<and> F)) xs ys"
  apply (simp_all add: rev_bl_order_def)
  apply (rule conj_cong[OF refl])
  apply (cases "xs = ys")
   apply (simp add: nth_Cons')
   apply blast
  apply (simp add: nth_Cons')
  apply safe
   apply (rule_tac x="n - 1" in exI)
   apply simp
  apply (rule_tac x="Suc n" in exI)
  apply simp
  done

lemma rev_bl_order_rev_simp:
  "length xs = length ys \<Longrightarrow>
   rev_bl_order F (xs @ [x]) (ys @ [y])
     = ((y \<and> \<not> x) \<or> ((y \<or> \<not> x) \<and> rev_bl_order F xs ys))"
  apply (induct arbitrary: F rule: list_induct2)
   apply (auto simp add: rev_bl_order_simps)
  done

lemma rev_bl_order_bl_to_bin:
  "length xs = length ys
     \<Longrightarrow> rev_bl_order True xs ys
            = (bl_to_bin (rev xs) \<le> bl_to_bin (rev ys))
       \<and> rev_bl_order False xs ys
            = (bl_to_bin (rev xs) < bl_to_bin (rev ys))"
  apply (induct xs ys rule: list_induct2)
   apply (simp_all add: rev_bl_order_simps bl_to_bin_app_cat)
  apply (simp add: bl_to_bin_def Bit_B0 Bit_B1 add1_zle_eq)
  apply arith?
  done

lemma word_le_rbl:
  fixes x :: "('a :: len0) word"
  shows "(x \<le> y) = rev_bl_order True (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: rev_bl_order_bl_to_bin word_le_def)

lemma word_less_rbl:
  fixes x :: "('a :: len0) word"
  shows "(x < y) = rev_bl_order False (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: word_less_alt rev_bl_order_bl_to_bin)

lemma word_sint_msb_eq:
  "sint x = uint x - (if msb x then 2 ^ size x else 0)"
  apply (cases "msb x")
   apply (rule word_sint.Abs_eqD[where 'a='a], simp_all)
    apply (simp add: word_size wi_hom_syms
                     word_of_int_2p_len)
   apply (simp add: sints_num word_size)
   apply (rule conjI)
    apply (simp add: le_diff_eq')
    apply (rule order_trans[where y="2 ^ (len_of TYPE('a) - 1)"])
     apply (simp add: power_Suc[symmetric])
    apply (simp add: linorder_not_less[symmetric] mask_eq_iff[symmetric])
    apply (rule notI, drule word_eqD[where x="size x - 1"])
    apply (simp add: msb_nth word_ops_nth_size word_size)
   apply (simp add: order_less_le_trans[where y=0])
  apply (rule word_uint.Abs_eqD[where 'a='a], simp_all)
  apply (simp add: linorder_not_less uints_num word_msb_sint)
  apply (rule order_less_le_trans[OF sint_lt])
  apply simp
  done

lemma word_sle_msb_le:
  "(x <=s y) = ((msb y --> msb x) \<and> 
                  ((msb x \<and> \<not> msb y) \<or> (x <= y)))"
  apply (simp add: word_sle_def word_sint_msb_eq word_size
                   word_le_def)
  apply safe
   apply (rule order_trans[OF _ uint_ge_0])
   apply (simp add: order_less_imp_le)
  apply (erule notE[OF leD])
  apply (rule order_less_le_trans[OF _ uint_ge_0])
  apply simp
  done

lemma word_sless_msb_less:
  "(x <s y) = ((msb y --> msb x) \<and> 
                  ((msb x \<and> \<not> msb y) \<or> (x < y)))"
  by (auto simp add: word_sless_def word_sle_msb_le)

definition
  "map_last f xs = (if xs = [] then [] else butlast xs @ [f (last xs)])"

lemma map_last_simps:
  "map_last f [] = []"
  "map_last f [x] = [f x]"
  "map_last f (x # y # zs) = x # map_last f (y # zs)"
  by (simp_all add: map_last_def)

lemma word_sle_rbl:
  "(x <=s y) = rev_bl_order True (map_last Not (rev (to_bl x)))
     (map_last Not (rev (to_bl y)))"
  using word_msb_alt[where w=x] word_msb_alt[where w=y]
  apply (simp add: word_sle_msb_le word_le_rbl)
  apply (subgoal_tac "length (to_bl x) = length (to_bl y)")
   apply (cases "to_bl x", simp)
   apply (cases "to_bl y", simp)
   apply (clarsimp simp: map_last_def rev_bl_order_rev_simp)
   apply auto
  done

lemma word_sless_rbl:
  "(x <s y) = rev_bl_order False (map_last Not (rev (to_bl x)))
     (map_last Not (rev (to_bl y)))"
  using word_msb_alt[where w=x] word_msb_alt[where w=y]
  apply (simp add: word_sless_msb_less word_less_rbl)
  apply (subgoal_tac "length (to_bl x) = length (to_bl y)")
   apply (cases "to_bl x", simp)
   apply (cases "to_bl y", simp)
   apply (clarsimp simp: map_last_def rev_bl_order_rev_simp)
   apply auto
  done

text {* Lemmas for unpacking rev (to_bl n) for numerals n and also
for irreducible values and expressions. *}

lemma rev_bin_to_bl_simps:
  "rev (bin_to_bl 0 x) = []"
  "rev (bin_to_bl (Suc n) (numeral (num.Bit0 nm)))
    = False # rev (bin_to_bl n (numeral nm))"
  "rev (bin_to_bl (Suc n) (numeral (num.Bit1 nm)))
    = True # rev (bin_to_bl n (numeral nm))"
  "rev (bin_to_bl (Suc n) (numeral (num.One)))
    = True # replicate n False"
  "rev (bin_to_bl (Suc n) (neg_numeral (num.Bit0 nm)))
    = False # rev (bin_to_bl n (neg_numeral nm))"
  "rev (bin_to_bl (Suc n) (neg_numeral (num.Bit1 nm)))
    = True # rev (bin_to_bl n (neg_numeral (nm + num.One)))"
  "rev (bin_to_bl (Suc n) (neg_numeral (num.One)))
    = True # replicate n True"
  "rev (bin_to_bl (Suc n) (neg_numeral (num.Bit0 nm + num.One)))
    = True # rev (bin_to_bl n (neg_numeral (nm + num.One)))"
  "rev (bin_to_bl (Suc n) (neg_numeral (num.Bit1 nm + num.One)))
    = False # rev (bin_to_bl n (neg_numeral (nm + num.One)))"
  "rev (bin_to_bl (Suc n) (neg_numeral (num.One + num.One)))
    = False # rev (bin_to_bl n (neg_numeral num.One))"
  apply (simp_all add: bin_to_bl_def)
  apply (simp_all only: bin_to_bl_aux_alt)
  apply (simp_all)
  apply (simp_all add: bin_to_bl_zero_aux bin_to_bl_minus1_aux)
  done

lemma to_bl_upt:
  "to_bl x = rev (map (op !! x) [0 ..< size x])"
  apply (rule nth_equalityI)
   apply (simp add: word_size)
  apply (clarsimp simp: to_bl_nth word_size nth_rev)
  done

lemma rev_to_bl_upt:
  "rev (to_bl x) = map (op !! x) [0 ..< size x]"
  by (simp add: to_bl_upt)

lemma upt_eq_list_intros:
  "j <= i \<Longrightarrow> [i ..< j] = []"
  "\<lbrakk> i = x; x < j; [x + 1 ..< j] = xs \<rbrakk> \<Longrightarrow> [i ..< j] = (x # xs)"
  by (simp_all add: upt_eq_Nil_conv upt_eq_Cons_conv)

text {* Tactic definition *}

ML {*

structure Word_Bitwise_Tac = struct

val word_ss = global_simpset_of @{theory Word};

fun mk_nat_clist ns = List.foldr
  (uncurry (Thm.mk_binop @{cterm "Cons :: nat => _"}))
  @{cterm "[] :: nat list"} ns;

fun upt_conv ct = case term_of ct of
  (@{const upt} $ n $ m) => let
    val (i, j) = pairself (snd o HOLogic.dest_number) (n, m);
    val ns = map (Numeral.mk_cnumber @{ctyp nat}) (i upto (j - 1))
      |> mk_nat_clist;
    val prop = Thm.mk_binop @{cterm "op = :: nat list => _"} ct ns
                 |> Thm.apply @{cterm Trueprop};
  in Goal.prove_internal [] prop 
      (K (REPEAT_DETERM (resolve_tac @{thms upt_eq_list_intros} 1
          ORELSE simp_tac word_ss 1))) |> mk_meta_eq |> SOME end
    handle TERM _ => NONE
  | _ => NONE;

val expand_upt_simproc = Simplifier.make_simproc
  {lhss = [@{cpat "upt _ _"}],
   name = "expand_upt", identifier = [],
   proc = K (K upt_conv)};

fun word_len_simproc_fn ct = case term_of ct of
    Const (@{const_name len_of}, _) $ t => (let
        val T = fastype_of t |> dest_Type |> snd |> the_single
        val n = Numeral.mk_cnumber @{ctyp nat} (Word_Lib.dest_binT T);
        val prop = Thm.mk_binop @{cterm "op = :: nat => _"} ct n
                 |> Thm.apply @{cterm Trueprop};
      in Goal.prove_internal [] prop (K (simp_tac word_ss 1))
             |> mk_meta_eq |> SOME end
    handle TERM _ => NONE | TYPE _ => NONE)
  | _ => NONE;

val word_len_simproc = Simplifier.make_simproc
  {lhss = [@{cpat "len_of _"}],
   name = "word_len", identifier = [],
   proc = K (K word_len_simproc_fn)};

(* convert 5 or nat 5 to Suc 4 when n_sucs = 1, Suc (Suc 4) when n_sucs = 2,
   or just 5 (discarding nat) when n_sucs = 0 *)

fun nat_get_Suc_simproc_fn n_sucs thy ct = let
    val (f $ arg) = (term_of ct);
    val n = (case arg of @{term nat} $ n => n | n => n)
      |> HOLogic.dest_number |> snd;
    val (i, j) = if n > n_sucs then (n_sucs, n - n_sucs)
      else (n, 0);
    val arg' = List.foldr (op $) (HOLogic.mk_number @{typ nat} j)
        (replicate i @{term Suc});
    val _ = if arg = arg' then raise TERM ("", []) else ();
    fun propfn g = HOLogic.mk_eq (g arg, g arg')
      |> HOLogic.mk_Trueprop |> cterm_of thy;
    val eq1 = Goal.prove_internal [] (propfn I)
      (K (simp_tac word_ss 1));
  in Goal.prove_internal [] (propfn (curry (op $) f))
      (K (simp_tac (HOL_ss addsimps [eq1]) 1))
       |> mk_meta_eq |> SOME end
    handle TERM _ => NONE;

fun nat_get_Suc_simproc n_sucs thy cts = Simplifier.make_simproc
  {lhss = map (fn t => Thm.apply t @{cpat "?n :: nat"}) cts,
   name = "nat_get_Suc", identifier = [],
   proc = K (K (nat_get_Suc_simproc_fn n_sucs thy))};

val no_split_ss = Splitter.del_split @{thm split_if} HOL_ss;

val expand_word_eq_sss = (HOL_basic_ss addsimps
       @{thms word_eq_rbl_eq word_le_rbl word_less_rbl word_sle_rbl word_sless_rbl},
  [no_split_ss addsimps @{thms rbl_word_plus rbl_word_and rbl_word_or rbl_word_not
                                rbl_word_neg bl_word_sub rbl_word_xor
                                rbl_word_cat rbl_word_slice rbl_word_scast
                                rbl_word_ucast rbl_shiftl rbl_shiftr rbl_sshiftr
                                rbl_word_if},
   no_split_ss addsimps @{thms to_bl_numeral to_bl_neg_numeral
                               to_bl_0 rbl_word_1},
   no_split_ss addsimps @{thms rev_rev_ident
                                rev_replicate rev_map to_bl_upt word_size}
          addsimprocs [word_len_simproc],
   no_split_ss addsimps @{thms list.simps split_conv replicate.simps map.simps
                                zip_Cons_Cons zip_Nil drop_Suc_Cons drop_0 drop_Nil
                                foldr.simps map2_Cons map2_Nil takefill_Suc_Cons
                                takefill_Suc_Nil takefill.Z rbl_succ2_simps
                                rbl_plus_simps rev_bin_to_bl_simps append.simps
                                takefill_last_simps drop_nonempty_simps
                                rev_bl_order_simps}
          addsimprocs [expand_upt_simproc,
                       nat_get_Suc_simproc 4 @{theory}
                         [@{cpat replicate}, @{cpat "takefill ?x"},
                          @{cpat drop}, @{cpat "bin_to_bl"},
                          @{cpat "takefill_last ?x"},
                          @{cpat "drop_nonempty ?x"}]],
    no_split_ss addsimps @{thms xor3_simps carry_simps if_bool_simps}
  ])

val tac = let
    val (ss, sss) = expand_word_eq_sss;
    val st = generic_simp_tac true (true, false, false);
  in foldr1 (op THEN_ALL_NEW) ((CHANGED o st ss) :: map st sss) end;

end

*}

method_setup word_bitwise =
  {* Scan.succeed (K (Method.SIMPLE_METHOD (Word_Bitwise_Tac.tac 1)))  *}
  "decomposer for word equalities and inequalities into bit propositions"

end
