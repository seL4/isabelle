(* 
  ID:      $Id$
  Author:  Jeremy Dawson, NICTA
*) 

header {* Useful Numerical Lemmas *}

theory Num_Lemmas imports Parity begin

(* lemmas funpow_0 = funpow.simps(1) *)
lemmas funpow_Suc = funpow.simps(2)
(* used by BinGeneral.funpow_minus_simp *)

lemma gt_or_eq_0: "0 < y \<or> 0 = (y::nat)" by auto

lemmas xtr1 = xtrans(1)
lemmas xtr2 = xtrans(2)
lemmas xtr3 = xtrans(3)
lemmas xtr4 = xtrans(4)
lemmas xtr5 = xtrans(5)
lemmas xtr6 = xtrans(6)
lemmas xtr7 = xtrans(7)
lemmas xtr8 = xtrans(8)

lemmas PlsMin_defs (*[intro!]*) = 
  Pls_def Min_def Pls_def [symmetric] Min_def [symmetric]

lemmas PlsMin_simps [simp] = PlsMin_defs [THEN Eq_TrueI]

lemma number_of_False_cong: 
  "False ==> number_of x = number_of y" 
  by auto

lemma nobm1:
  "0 < (number_of w :: nat) ==> 
   number_of w - (1 :: nat) = number_of (Numeral.pred w)"
  apply (unfold nat_number_of_def One_nat_def nat_1 [symmetric] pred_def)
  apply (simp add: number_of_eq nat_diff_distrib [symmetric])
  done
(* used in BinGeneral, BinOperations, BinBoolList *)

lemma zless2: "0 < (2 :: int)" 
  by auto

lemmas zless2p [simp] = zless2 [THEN zero_less_power] (* keep *)
lemmas zle2p [simp] = zless2p [THEN order_less_imp_le] (* keep *)

lemma emep1:
  "even n ==> even d ==> 0 <= d ==> (n + 1) mod (d :: int) = (n mod d) + 1"
  apply (simp add: add_commute)
  apply (safe dest!: even_equiv_def [THEN iffD1])
  apply (subst pos_zmod_mult_2)
   apply arith
  apply (simp add: zmod_zmult_zmult1)
 done

lemmas eme1p = emep1 [simplified add_commute]

lemma diff_le_eq': "(a - b \<le> c) = (a \<le> b + (c::int))"
  by (simp add: diff_le_eq add_commute)
(* used by BinGeneral.sb_dec_lem' *)

lemmas m1mod2k = zless2p [THEN zmod_minus1]
(* used in WordArith *)

lemmas p1mod22k' = zless2p [THEN order_less_imp_le, THEN pos_zmod_mult_2]

lemma p1mod22k:
  "(2 * b + 1) mod (2 * 2 ^ n) = 2 * (b mod 2 ^ n) + (1::int)"
  by (simp add: p1mod22k' add_commute)
(* used in BinOperations *)

lemmas zdiv_le_dividend = xtr3 [OF zdiv_1 [symmetric] zdiv_mono2,
  simplified int_one_le_iff_zero_less, simplified, standard]
(* used in WordShift *)

lemma Bit_B0:
  "k BIT bit.B0 = k + k"
   by (unfold Bit_def) simp

lemma Bit_B0_2t: "k BIT bit.B0 = 2 * k"
  by (rule trans, rule Bit_B0) simp
(* used in BinOperations *)

lemmas zadd_diff_inverse = trans [OF diff_add_cancel [symmetric] add_commute,
  standard]
(* used in WordArith *)

lemmas add_diff_cancel2 = add_commute [THEN diff_eq_eq [THEN iffD2], standard]
(* used in WordShift *)

lemma zmod_uminus: "- ((a :: int) mod b) mod b = -a mod b"
  by (simp add : zmod_zminus1_eq_if)
(* used in BinGeneral *)

lemma zmod_zsub_right_eq: "((a::int) - b) mod c = (a - b mod c) mod c"
  apply (unfold diff_int_def)
  apply (rule trans [OF _ zmod_zadd_right_eq [symmetric]])
  apply (simp add : zmod_uminus zmod_zadd_right_eq [symmetric])
  done
(* used in BinGeneral, WordGenLib *)

lemmas zmod_zsub_left_eq = 
  zmod_zadd_left_eq [where b = "- ?b", simplified diff_int_def [symmetric]]
(* used in BinGeneral, WordGenLib *)
  
lemma zmod_zsub_self [simp]: 
  "((b :: int) - a) mod a = b mod a"
  by (simp add: zmod_zsub_right_eq)

lemma zmod_zmult1_eq_rev:
  "b * a mod c = b mod c * a mod (c::int)"
  apply (simp add: mult_commute)
  apply (subst zmod_zmult1_eq)
  apply simp
  done
(* used in BinGeneral *)

lemmas rdmods [symmetric] = zmod_uminus [symmetric]
  zmod_zsub_left_eq zmod_zsub_right_eq zmod_zadd_left_eq
  zmod_zadd_right_eq zmod_zmult1_eq zmod_zmult1_eq_rev
(* used in WordArith, WordShift *)

lemma mod_plus_right:
  "((a + x) mod m = (b + x) mod m) = (a mod m = b mod (m :: nat))"
  apply (induct x)
   apply (simp_all add: mod_Suc)
  apply arith
  done

lemma nat_mod_eq:
  "!!b. b < n ==> a mod n = b mod n ==> a mod n = (b :: nat)" 
  by (induct a) auto

lemmas nat_mod_eq' = refl [THEN [2] nat_mod_eq]
(* used in WordArith, WordGenLib *)

lemma nat_mod_lem: 
  "(0 :: nat) < n ==> b < n = (b mod n = b)"
  apply safe
   apply (erule nat_mod_eq')
  apply (erule subst)
  apply (erule mod_less_divisor)
  done
(* used in WordArith *)

lemma mod_nat_add: 
  "(x :: nat) < z ==> y < z ==> 
   (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  apply (rule nat_mod_eq)
   apply auto
  apply (rule trans)
   apply (rule le_mod_geq)
   apply simp
  apply (rule nat_mod_eq')
  apply arith
  done
(* used in WordArith, WordGenLib *)

lemma int_mod_lem: 
  "(0 :: int) < n ==> (0 <= b & b < n) = (b mod n = b)"
  apply safe
    apply (erule (1) mod_pos_pos_trivial)
   apply (erule_tac [!] subst)
   apply auto
  done
(* used in WordDefinition, WordArith, WordShift *)

lemma int_mod_eq:
  "(0 :: int) <= b ==> b < n ==> a mod n = b mod n ==> a mod n = b"
  by clarsimp (rule mod_pos_pos_trivial)

lemmas int_mod_eq' = refl [THEN [3] int_mod_eq]
(* used in WordDefinition, WordArith, WordShift, WordGenLib *)

lemma int_mod_le: "0 <= a ==> 0 < (n :: int) ==> a mod n <= a"
  apply (cases "a < n")
   apply (auto dest: mod_pos_pos_trivial pos_mod_bound [where a=a])
  done

lemmas int_mod_le' = int_mod_le [where a = "?b - ?n", simplified]

lemma int_mod_ge: "a < n ==> 0 < (n :: int) ==> a <= a mod n"
  apply (cases "0 <= a")
   apply (drule (1) mod_pos_pos_trivial)
   apply simp
  apply (rule order_trans [OF _ pos_mod_sign])
   apply simp
  apply assumption
  done

lemmas int_mod_ge' = int_mod_ge [where a = "?b + ?n", simplified]

lemma mod_add_if_z:
  "(x :: int) < z ==> y < z ==> 0 <= y ==> 0 <= x ==> 0 <= z ==> 
   (x + y) mod z = (if x + y < z then x + y else x + y - z)"
  by (auto intro: int_mod_eq)
(* used in WordArith, WordGenLib *)

lemma mod_sub_if_z:
  "(x :: int) < z ==> y < z ==> 0 <= y ==> 0 <= x ==> 0 <= z ==> 
   (x - y) mod z = (if y <= x then x - y else x - y + z)"
  by (auto intro: int_mod_eq)
(* used in WordArith, WordGenLib *)

lemmas mcl = mult_cancel_left [THEN iffD1, THEN make_pos_rule]

lemma min_pm [simp]: "min a b + (a - b) = (a :: nat)"
  by arith
  
lemmas min_pm1 [simp] = trans [OF add_commute min_pm]

lemma rev_min_pm [simp]: "min b a + (a - b) = (a::nat)"
  by simp

lemmas rev_min_pm1 [simp] = trans [OF add_commute rev_min_pm]

lemma min_minus [simp] : "min m (m - k) = (m - k :: nat)"
  by arith
  
lemmas min_minus' [simp] = trans [OF min_max.inf_commute min_minus]

lemmas dme = box_equals [OF div_mod_equality add_0_right add_0_right]
lemmas dtle = xtr3 [OF dme [symmetric] le_add1]
(* used in WordShift *)
lemmas th2 = order_trans [OF order_refl [THEN [2] mult_le_mono] dtle]

lemma td_gal: 
  "0 < c ==> (a >= b * c) = (a div c >= (b :: nat))"
  apply safe
   apply (erule (1) xtr4 [OF div_le_mono div_mult_self_is_m])
  apply (erule th2)
  done
  
lemmas td_gal_lt = td_gal [simplified le_def, simplified]
(* used in WordShift *)

lemma div_mult_le: "(a :: nat) div b * b <= a"
  apply (cases b)
   prefer 2
   apply (rule order_refl [THEN th2])
  apply auto
  done
(* used in WordArith *)

lemmas sdl = split_div_lemma [THEN iffD1, symmetric]

lemma given_quot: "f > (0 :: nat) ==> (f * l + (f - 1)) div f = l"
  by (rule sdl, assumption) (simp (no_asm))

lemma given_quot_alt: "f > (0 :: nat) ==> (l * f + f - Suc 0) div f = l"
  apply (frule given_quot)
  apply (rule trans)
   prefer 2
   apply (erule asm_rl)
  apply (rule_tac f="%n. n div f" in arg_cong)
  apply (simp add : mult_ac)
  done
(* used in WordShift *)
    
lemma less_le_mult':
  "w * c < b * c ==> 0 \<le> c ==> (w + 1) * c \<le> b * (c::int)"
  apply (rule mult_right_mono)
   apply (rule zless_imp_add1_zle)
   apply (erule (1) mult_right_less_imp_less)
  apply assumption
  done

lemmas less_le_mult = less_le_mult' [simplified left_distrib, simplified]
(* used in WordArith *)

lemma lrlem':
  assumes d: "(i::nat) \<le> j \<or> m < j'"
  assumes R1: "i * k \<le> j * k \<Longrightarrow> R"
  assumes R2: "Suc m * k' \<le> j' * k' \<Longrightarrow> R"
  shows "R" using d
  apply safe
   apply (rule R1, erule mult_le_mono1)
  apply (rule R2, erule Suc_le_eq [THEN iffD2 [THEN mult_le_mono1]])
  done

lemma lrlem: "(0::nat) < sc ==>
    (sc - n + (n + lb * n) <= m * n) = (sc + lb * n <= m * n)"
  apply safe
   apply arith
  apply (case_tac "sc >= n")
   apply arith
  apply (insert linorder_le_less_linear [of m lb])
  apply (erule_tac k=n and k'=n in lrlem')
   apply arith
  apply simp
  done
(* used in BinBoolList *)

lemma gen_minus: "0 < n ==> f n = f (Suc (n - 1))"
  by auto
(* used in BinGeneral *)

lemma mpl_lem: "j <= (i :: nat) ==> k < j ==> i - j + k < i"
  apply (induct i, clarsimp)
  apply (cases j, clarsimp)
  apply arith
  done
(* used in WordShift *)

subsection "if simps"

lemma if_Not_x: "(if p then ~ x else x) = (p = (~ x))"
  by auto

lemma if_x_Not: "(if p then x else ~ x) = (p = x)"
  by auto

lemma if_bool_simps:
  "If p True y = (p | y) & If p False y = (~p & y) & 
    If p y True = (p --> y) & If p y False = (p & y)"
  by auto

lemmas if_simps = if_x_Not if_Not_x if_cancel if_True if_False if_bool_simps
(* used in WordBitwise *)

end
