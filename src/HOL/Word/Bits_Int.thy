(*  Title:      HOL/Word/Bits_Int.thy
    Author:     Jeremy Dawson and Gerwin Klein, NICTA
*)

section \<open>Bitwise Operations on integers\<close>

theory Bits_Int
  imports
    "HOL-Library.Bit_Operations"
    Traditional_Syntax
begin

subsection \<open>Generic auxiliary\<close>

lemma int_mod_ge: "a < n \<Longrightarrow> 0 < n \<Longrightarrow> a \<le> a mod n"
  for a n :: int
  by (metis dual_order.trans le_cases mod_pos_pos_trivial pos_mod_conj)


subsection \<open>Implicit bit representation of \<^typ>\<open>int\<close>\<close>

abbreviation (input) bin_last :: "int \<Rightarrow> bool"
  where "bin_last \<equiv> odd"

lemma bin_last_def:
  "bin_last w \<longleftrightarrow> w mod 2 = 1"
  by (fact odd_iff_mod_2_eq_one)

abbreviation (input) bin_rest :: "int \<Rightarrow> int"
  where "bin_rest w \<equiv> w div 2"

lemma bin_last_numeral_simps [simp]:
  "\<not> bin_last 0"
  "bin_last 1"
  "bin_last (- 1)"
  "bin_last Numeral1"
  "\<not> bin_last (numeral (Num.Bit0 w))"
  "bin_last (numeral (Num.Bit1 w))"
  "\<not> bin_last (- numeral (Num.Bit0 w))"
  "bin_last (- numeral (Num.Bit1 w))"
  by simp_all

lemma bin_rest_numeral_simps [simp]:
  "bin_rest 0 = 0"
  "bin_rest 1 = 0"
  "bin_rest (- 1) = - 1"
  "bin_rest Numeral1 = 0"
  "bin_rest (numeral (Num.Bit0 w)) = numeral w"
  "bin_rest (numeral (Num.Bit1 w)) = numeral w"
  "bin_rest (- numeral (Num.Bit0 w)) = - numeral w"
  "bin_rest (- numeral (Num.Bit1 w)) = - numeral (w + Num.One)"
  by simp_all

lemma bin_rl_eqI: "\<lbrakk>bin_rest x = bin_rest y; bin_last x = bin_last y\<rbrakk> \<Longrightarrow> x = y"
  by (auto elim: oddE)

lemma [simp]: 
  shows bin_rest_lt0: "bin_rest i < 0 \<longleftrightarrow> i < 0"
  and  bin_rest_ge_0: "bin_rest i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by auto

lemma bin_rest_gt_0 [simp]: "bin_rest x > 0 \<longleftrightarrow> x > 1"
  by auto


subsection \<open>Explicit bit representation of \<^typ>\<open>int\<close>\<close>

primrec bl_to_bin_aux :: "bool list \<Rightarrow> int \<Rightarrow> int"
  where
    Nil: "bl_to_bin_aux [] w = w"
  | Cons: "bl_to_bin_aux (b # bs) w = bl_to_bin_aux bs (of_bool b + 2 * w)"

definition bl_to_bin :: "bool list \<Rightarrow> int"
  where "bl_to_bin bs = bl_to_bin_aux bs 0"

primrec bin_to_bl_aux :: "nat \<Rightarrow> int \<Rightarrow> bool list \<Rightarrow> bool list"
  where
    Z: "bin_to_bl_aux 0 w bl = bl"
  | Suc: "bin_to_bl_aux (Suc n) w bl = bin_to_bl_aux n (bin_rest w) ((bin_last w) # bl)"

definition bin_to_bl :: "nat \<Rightarrow> int \<Rightarrow> bool list"
  where "bin_to_bl n w = bin_to_bl_aux n w []"

lemma bin_to_bl_aux_zero_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n 0 bl = bin_to_bl_aux (n - 1) 0 (False # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_minus1_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n (- 1) bl = bin_to_bl_aux (n - 1) (- 1) (True # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_one_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n 1 bl = bin_to_bl_aux (n - 1) 0 (True # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_Bit0_minus_simp [simp]:
  "0 < n \<Longrightarrow>
    bin_to_bl_aux n (numeral (Num.Bit0 w)) bl = bin_to_bl_aux (n - 1) (numeral w) (False # bl)"
  by (cases n) simp_all

lemma bin_to_bl_aux_Bit1_minus_simp [simp]:
  "0 < n \<Longrightarrow>
    bin_to_bl_aux n (numeral (Num.Bit1 w)) bl = bin_to_bl_aux (n - 1) (numeral w) (True # bl)"
  by (cases n) simp_all

lemma bl_to_bin_aux_append: "bl_to_bin_aux (bs @ cs) w = bl_to_bin_aux cs (bl_to_bin_aux bs w)"
  by (induct bs arbitrary: w) auto

lemma bin_to_bl_aux_append: "bin_to_bl_aux n w bs @ cs = bin_to_bl_aux n w (bs @ cs)"
  by (induct n arbitrary: w bs) auto

lemma bl_to_bin_append: "bl_to_bin (bs @ cs) = bl_to_bin_aux cs (bl_to_bin bs)"
  unfolding bl_to_bin_def by (rule bl_to_bin_aux_append)

lemma bin_to_bl_aux_alt: "bin_to_bl_aux n w bs = bin_to_bl n w @ bs"
  by (simp add: bin_to_bl_def bin_to_bl_aux_append)

lemma bin_to_bl_0 [simp]: "bin_to_bl 0 bs = []"
  by (auto simp: bin_to_bl_def)

lemma size_bin_to_bl_aux: "length (bin_to_bl_aux n w bs) = n + length bs"
  by (induct n arbitrary: w bs) auto

lemma size_bin_to_bl [simp]: "length (bin_to_bl n w) = n"
  by (simp add: bin_to_bl_def size_bin_to_bl_aux)

lemma bl_bin_bl': "bin_to_bl (n + length bs) (bl_to_bin_aux bs w) = bin_to_bl_aux n w bs"
  apply (induct bs arbitrary: w n)
   apply auto
    apply (simp_all only: add_Suc [symmetric])
    apply (auto simp add: bin_to_bl_def)
  done

lemma bl_bin_bl [simp]: "bin_to_bl (length bs) (bl_to_bin bs) = bs"
  unfolding bl_to_bin_def
  apply (rule box_equals)
    apply (rule bl_bin_bl')
   prefer 2
   apply (rule bin_to_bl_aux.Z)
  apply simp
  done

lemma bl_to_bin_inj: "bl_to_bin bs = bl_to_bin cs \<Longrightarrow> length bs = length cs \<Longrightarrow> bs = cs"
  apply (rule_tac box_equals)
    defer
    apply (rule bl_bin_bl)
   apply (rule bl_bin_bl)
  apply simp
  done

lemma bl_to_bin_False [simp]: "bl_to_bin (False # bl) = bl_to_bin bl"
  by (auto simp: bl_to_bin_def)

lemma bl_to_bin_Nil [simp]: "bl_to_bin [] = 0"
  by (auto simp: bl_to_bin_def)

lemma bin_to_bl_zero_aux: "bin_to_bl_aux n 0 bl = replicate n False @ bl"
  by (induct n arbitrary: bl) (auto simp: replicate_app_Cons_same)

lemma bin_to_bl_zero: "bin_to_bl n 0 = replicate n False"
  by (simp add: bin_to_bl_def bin_to_bl_zero_aux)

lemma bin_to_bl_minus1_aux: "bin_to_bl_aux n (- 1) bl = replicate n True @ bl"
  by (induct n arbitrary: bl) (auto simp: replicate_app_Cons_same)

lemma bin_to_bl_minus1: "bin_to_bl n (- 1) = replicate n True"
  by (simp add: bin_to_bl_def bin_to_bl_minus1_aux)


subsection \<open>Bit projection\<close>

abbreviation (input) bin_nth :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>bin_nth \<equiv> bit\<close>

lemma bin_nth_eq_iff: "bin_nth x = bin_nth y \<longleftrightarrow> x = y"
  by (simp add: bit_eq_iff fun_eq_iff)

lemma bin_eqI:
  "x = y" if "\<And>n. bin_nth x n \<longleftrightarrow> bin_nth y n"
  using that bin_nth_eq_iff [of x y] by (simp add: fun_eq_iff)

lemma bin_eq_iff: "x = y \<longleftrightarrow> (\<forall>n. bin_nth x n = bin_nth y n)"
  by (fact bit_eq_iff)

lemma bin_nth_zero [simp]: "\<not> bin_nth 0 n"
  by simp

lemma bin_nth_1 [simp]: "bin_nth 1 n \<longleftrightarrow> n = 0"
  by (cases n) (simp_all add: bit_Suc)

lemma bin_nth_minus1 [simp]: "bin_nth (- 1) n"
  by (induction n) (simp_all add: bit_Suc)

lemma bin_nth_numeral: "bin_rest x = y \<Longrightarrow> bin_nth x (numeral n) = bin_nth y (pred_numeral n)"
  by (simp add: numeral_eq_Suc bit_Suc)

lemmas bin_nth_numeral_simps [simp] =
  bin_nth_numeral [OF bin_rest_numeral_simps(2)]
  bin_nth_numeral [OF bin_rest_numeral_simps(5)]
  bin_nth_numeral [OF bin_rest_numeral_simps(6)]
  bin_nth_numeral [OF bin_rest_numeral_simps(7)]
  bin_nth_numeral [OF bin_rest_numeral_simps(8)]

lemmas bin_nth_simps =
  bit_0 bit_Suc bin_nth_zero bin_nth_minus1
  bin_nth_numeral_simps

lemma nth_2p_bin: "bin_nth (2 ^ n) m = (m = n)" \<comment> \<open>for use when simplifying with \<open>bin_nth_Bit\<close>\<close>
  by (auto simp add: bit_exp_iff)
  
lemma nth_rest_power_bin: "bin_nth ((bin_rest ^^ k) w) n = bin_nth w (n + k)"
  apply (induct k arbitrary: n)
   apply clarsimp
  apply clarsimp
  apply (simp only: bit_Suc [symmetric] add_Suc)
  done

lemma bin_nth_numeral_unfold:
  "bin_nth (numeral (num.Bit0 x)) n \<longleftrightarrow> n > 0 \<and> bin_nth (numeral x) (n - 1)"
  "bin_nth (numeral (num.Bit1 x)) n \<longleftrightarrow> (n > 0 \<longrightarrow> bin_nth (numeral x) (n - 1))"
  by (cases n; simp)+


subsection \<open>Truncating\<close>

definition bin_sign :: "int \<Rightarrow> int"
  where "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign 0 = 0"
  "bin_sign 1 = 0"
  "bin_sign (- 1) = - 1"
  "bin_sign (numeral k) = 0"
  "bin_sign (- numeral k) = -1"
  by (simp_all add: bin_sign_def)

lemma bin_sign_rest [simp]: "bin_sign (bin_rest w) = bin_sign w"
  by (simp add: bin_sign_def)

abbreviation (input) bintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bintrunc \<equiv> take_bit\<close>

lemma bintrunc_mod2p: "bintrunc n w = w mod 2 ^ n"
  by (fact take_bit_eq_mod)

abbreviation (input) sbintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>sbintrunc \<equiv> signed_take_bit\<close>

lemma sbintrunc_mod2p: "sbintrunc n w = (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n"
  by (simp add: bintrunc_mod2p signed_take_bit_eq_take_bit_shift)
  
lemma sbintrunc_eq_take_bit:
  \<open>sbintrunc n k = take_bit (Suc n) (k + 2 ^ n) - 2 ^ n\<close>
  by (fact signed_take_bit_eq_take_bit_shift)

lemma sign_bintr: "bin_sign (bintrunc n w) = 0"
  by (simp add: bin_sign_def)

lemma bintrunc_n_0: "bintrunc n 0 = 0"
  by (fact take_bit_of_0)

lemma sbintrunc_n_0: "sbintrunc n 0 = 0"
  by (fact signed_take_bit_of_0)

lemma sbintrunc_n_minus1: "sbintrunc n (- 1) = -1"
  by (fact signed_take_bit_of_minus_1)

lemma bintrunc_Suc_numeral:
  "bintrunc (Suc n) 1 = 1"
  "bintrunc (Suc n) (- 1) = 1 + 2 * bintrunc n (- 1)"
  "bintrunc (Suc n) (numeral (Num.Bit0 w)) = 2 * bintrunc n (numeral w)"
  "bintrunc (Suc n) (numeral (Num.Bit1 w)) = 1 + 2 * bintrunc n (numeral w)"
  "bintrunc (Suc n) (- numeral (Num.Bit0 w)) = 2 * bintrunc n (- numeral w)"
  "bintrunc (Suc n) (- numeral (Num.Bit1 w)) = 1 + 2 * bintrunc n (- numeral (w + Num.One))"
  by (simp_all add: take_bit_Suc)

lemma sbintrunc_0_numeral [simp]:
  "sbintrunc 0 1 = -1"
  "sbintrunc 0 (numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (numeral (Num.Bit1 w)) = -1"
  "sbintrunc 0 (- numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (- numeral (Num.Bit1 w)) = -1"
  by simp_all

lemma sbintrunc_Suc_numeral:
  "sbintrunc (Suc n) 1 = 1"
  "sbintrunc (Suc n) (numeral (Num.Bit0 w)) = 2 * sbintrunc n (numeral w)"
  "sbintrunc (Suc n) (numeral (Num.Bit1 w)) = 1 + 2 * sbintrunc n (numeral w)"
  "sbintrunc (Suc n) (- numeral (Num.Bit0 w)) = 2 * sbintrunc n (- numeral w)"
  "sbintrunc (Suc n) (- numeral (Num.Bit1 w)) = 1 + 2 * sbintrunc n (- numeral (w + Num.One))"
  by (simp_all add: signed_take_bit_Suc)

lemma bin_sign_lem: "(bin_sign (sbintrunc n bin) = -1) = bit bin n"
  by (simp add: bin_sign_def)

lemma nth_bintr: "bin_nth (bintrunc m w) n \<longleftrightarrow> n < m \<and> bin_nth w n"
  by (fact bit_take_bit_iff)

lemma nth_sbintr: "bin_nth (sbintrunc m w) n = (if n < m then bin_nth w n else bin_nth w m)"
  by (simp add: bit_signed_take_bit_iff min_def)

lemma bin_nth_Bit0:
  "bin_nth (numeral (Num.Bit0 w)) n \<longleftrightarrow>
    (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bit_double_iff [of \<open>numeral w :: int\<close> n]
  by (auto intro: exI [of _ \<open>n - 1\<close>])

lemma bin_nth_Bit1:
  "bin_nth (numeral (Num.Bit1 w)) n \<longleftrightarrow>
    n = 0 \<or> (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using even_bit_succ_iff [of \<open>2 * numeral w :: int\<close> n]
    bit_double_iff [of \<open>numeral w :: int\<close> n]
  by auto

lemma bintrunc_bintrunc_l: "n \<le> m \<Longrightarrow> bintrunc m (bintrunc n w) = bintrunc n w"
  by (simp add: min.absorb2)

lemma sbintrunc_sbintrunc_l: "n \<le> m \<Longrightarrow> sbintrunc m (sbintrunc n w) = sbintrunc n w"
  by (simp add: min_def)

lemma bintrunc_bintrunc_ge: "n \<le> m \<Longrightarrow> bintrunc n (bintrunc m w) = bintrunc n w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma bintrunc_bintrunc_min [simp]: "bintrunc m (bintrunc n w) = bintrunc (min m n) w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma sbintrunc_sbintrunc_min [simp]: "sbintrunc m (sbintrunc n w) = sbintrunc (min m n) w"
  by (rule bin_eqI) (auto simp: nth_sbintr min.absorb1 min.absorb2)

lemmas sbintrunc_Suc_Pls =
  signed_take_bit_Suc [where k="0", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Suc_Min =
  signed_take_bit_Suc [where k="-1", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Sucs = sbintrunc_Suc_Pls sbintrunc_Suc_Min
  sbintrunc_Suc_numeral

lemmas sbintrunc_Pls =
  signed_take_bit_0 [where k="0", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Min =
  signed_take_bit_0 [where k="-1", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_0_simps =
  sbintrunc_Pls sbintrunc_Min

lemmas sbintrunc_simps = sbintrunc_0_simps sbintrunc_Sucs

lemma bintrunc_minus: "0 < n \<Longrightarrow> bintrunc (Suc (n - 1)) w = bintrunc n w"
  by auto

lemma sbintrunc_minus: "0 < n \<Longrightarrow> sbintrunc (Suc (n - 1)) w = sbintrunc n w"
  by auto

lemmas sbintrunc_minus_simps =
  sbintrunc_Sucs [THEN [2] sbintrunc_minus [symmetric, THEN trans]]

lemma sbintrunc_BIT_I:
  \<open>0 < n \<Longrightarrow>
  sbintrunc (n - 1) 0 = y \<Longrightarrow>
  sbintrunc n 0 = 2 * y\<close>
  by simp

lemma sbintrunc_Suc_Is:
  \<open>sbintrunc n (- 1) = y \<Longrightarrow>
  sbintrunc (Suc n) (- 1) = 1 + 2 * y\<close>
  by auto

lemma sbintrunc_Suc_lem: "sbintrunc (Suc n) x = y \<Longrightarrow> m = Suc n \<Longrightarrow> sbintrunc m x = y"
  by auto

lemmas sbintrunc_Suc_Ialts =
  sbintrunc_Suc_Is [THEN sbintrunc_Suc_lem]

lemma sbintrunc_bintrunc_lt: "m > n \<Longrightarrow> sbintrunc n (bintrunc m w) = sbintrunc n w"
  by (rule bin_eqI) (auto simp: nth_sbintr nth_bintr)

lemma bintrunc_sbintrunc_le: "m \<le> Suc n \<Longrightarrow> bintrunc m (sbintrunc n w) = bintrunc m w"
  apply (rule bin_eqI)
  using le_Suc_eq less_Suc_eq_le apply (auto simp: nth_sbintr nth_bintr)
  done

lemmas bintrunc_sbintrunc [simp] = order_refl [THEN bintrunc_sbintrunc_le]
lemmas sbintrunc_bintrunc [simp] = lessI [THEN sbintrunc_bintrunc_lt]
lemmas bintrunc_bintrunc [simp] = order_refl [THEN bintrunc_bintrunc_l]
lemmas sbintrunc_sbintrunc [simp] = order_refl [THEN sbintrunc_sbintrunc_l]

lemma bintrunc_sbintrunc' [simp]: "0 < n \<Longrightarrow> bintrunc n (sbintrunc (n - 1) w) = bintrunc n w"
  by (cases n) simp_all

lemma sbintrunc_bintrunc' [simp]: "0 < n \<Longrightarrow> sbintrunc (n - 1) (bintrunc n w) = sbintrunc (n - 1) w"
  by (cases n) simp_all

lemma bin_sbin_eq_iff: "bintrunc (Suc n) x = bintrunc (Suc n) y \<longleftrightarrow> sbintrunc n x = sbintrunc n y"
  apply (rule iffI)
   apply (rule box_equals [OF _ sbintrunc_bintrunc sbintrunc_bintrunc])
   apply simp
  apply (rule box_equals [OF _ bintrunc_sbintrunc bintrunc_sbintrunc])
  apply simp
  done

lemma bin_sbin_eq_iff':
  "0 < n \<Longrightarrow> bintrunc n x = bintrunc n y \<longleftrightarrow> sbintrunc (n - 1) x = sbintrunc (n - 1) y"
  by (cases n) (simp_all add: bin_sbin_eq_iff)

lemmas bintrunc_sbintruncS0 [simp] = bintrunc_sbintrunc' [unfolded One_nat_def]
lemmas sbintrunc_bintruncS0 [simp] = sbintrunc_bintrunc' [unfolded One_nat_def]

lemmas bintrunc_bintrunc_l' = le_add1 [THEN bintrunc_bintrunc_l]
lemmas sbintrunc_sbintrunc_l' = le_add1 [THEN sbintrunc_sbintrunc_l]

(* although bintrunc_minus_simps, if added to default simpset,
  tends to get applied where it's not wanted in developing the theories,
  we get a version for when the word length is given literally *)

lemmas nat_non0_gr =
  trans [OF iszero_def [THEN Not_eq_iff [THEN iffD2]] refl]

lemma bintrunc_numeral:
  "bintrunc (numeral k) x = of_bool (odd x) + 2 * bintrunc (pred_numeral k) (x div 2)"
  by (simp add: numeral_eq_Suc take_bit_Suc mod_2_eq_odd)

lemma sbintrunc_numeral:
  "sbintrunc (numeral k) x = of_bool (odd x) + 2 * sbintrunc (pred_numeral k) (x div 2)"
  by (simp add: numeral_eq_Suc signed_take_bit_Suc mod2_eq_if)

lemma bintrunc_numeral_simps [simp]:
  "bintrunc (numeral k) (numeral (Num.Bit0 w)) =
    2 * bintrunc (pred_numeral k) (numeral w)"
  "bintrunc (numeral k) (numeral (Num.Bit1 w)) =
    1 + 2 * bintrunc (pred_numeral k) (numeral w)"
  "bintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    2 * bintrunc (pred_numeral k) (- numeral w)"
  "bintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    1 + 2 * bintrunc (pred_numeral k) (- numeral (w + Num.One))"
  "bintrunc (numeral k) 1 = 1"
  by (simp_all add: bintrunc_numeral)

lemma sbintrunc_numeral_simps [simp]:
  "sbintrunc (numeral k) (numeral (Num.Bit0 w)) =
    2 * sbintrunc (pred_numeral k) (numeral w)"
  "sbintrunc (numeral k) (numeral (Num.Bit1 w)) =
    1 + 2 * sbintrunc (pred_numeral k) (numeral w)"
  "sbintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    2 * sbintrunc (pred_numeral k) (- numeral w)"
  "sbintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    1 + 2 * sbintrunc (pred_numeral k) (- numeral (w + Num.One))"
  "sbintrunc (numeral k) 1 = 1"
  by (simp_all add: sbintrunc_numeral)

lemma no_bintr_alt1: "bintrunc n = (\<lambda>w. w mod 2 ^ n :: int)"
  by (rule ext) (rule bintrunc_mod2p)

lemma range_bintrunc: "range (bintrunc n) = {i. 0 \<le> i \<and> i < 2 ^ n}"
  by (auto simp add: take_bit_eq_mod image_iff) (metis mod_pos_pos_trivial)

lemma no_sbintr_alt2: "sbintrunc n = (\<lambda>w. (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (rule ext) (simp add : sbintrunc_mod2p)

lemma range_sbintrunc: "range (sbintrunc n) = {i. - (2 ^ n) \<le> i \<and> i < 2 ^ n}"
proof -
  have \<open>surj (\<lambda>k::int. k + 2 ^ n)\<close>
    by (rule surjI [of _ \<open>(\<lambda>k. k - 2 ^ n)\<close>]) simp
  moreover have \<open>sbintrunc n = ((\<lambda>k. k - 2 ^ n) \<circ> take_bit (Suc n) \<circ> (\<lambda>k. k + 2 ^ n))\<close>
    by (simp add: sbintrunc_eq_take_bit fun_eq_iff)
  ultimately show ?thesis
    apply (simp only: fun.set_map range_bintrunc)
    apply (auto simp add: image_iff)
    apply presburger
    done
qed
  
lemma sbintrunc_inc:
  \<open>k + 2 ^ Suc n \<le> sbintrunc n k\<close> if \<open>k < - (2 ^ n)\<close>
  using that by (fact signed_take_bit_greater_eq)
  
lemma sbintrunc_dec:
  \<open>sbintrunc n k \<le> k - 2 ^ (Suc n)\<close> if \<open>k \<ge> 2 ^ n\<close>
  using that by (fact signed_take_bit_less_eq)

lemma bintr_ge0: "0 \<le> bintrunc n w"
  by (simp add: bintrunc_mod2p)

lemma bintr_lt2p: "bintrunc n w < 2 ^ n"
  by (simp add: bintrunc_mod2p)

lemma bintr_Min: "bintrunc n (- 1) = 2 ^ n - 1"
  by (simp add: stable_imp_take_bit_eq)
  
lemma sbintr_ge: "- (2 ^ n) \<le> sbintrunc n w"
  by (simp add: sbintrunc_mod2p)

lemma sbintr_lt: "sbintrunc n w < 2 ^ n"
  by (simp add: sbintrunc_mod2p)

lemma sign_Pls_ge_0: "bin_sign bin = 0 \<longleftrightarrow> bin \<ge> 0"
  for bin :: int
  by (simp add: bin_sign_def)

lemma sign_Min_lt_0: "bin_sign bin = -1 \<longleftrightarrow> bin < 0"
  for bin :: int
  by (simp add: bin_sign_def)

lemma bin_rest_trunc: "bin_rest (bintrunc n bin) = bintrunc (n - 1) (bin_rest bin)"
  by (simp add: take_bit_rec [of n bin])

lemma bin_rest_power_trunc:
  "(bin_rest ^^ k) (bintrunc n bin) = bintrunc (n - k) ((bin_rest ^^ k) bin)"
  by (induct k) (auto simp: bin_rest_trunc)

lemma bin_rest_trunc_i: "bintrunc n (bin_rest bin) = bin_rest (bintrunc (Suc n) bin)"
  by (auto simp add: take_bit_Suc)

lemma bin_rest_strunc: "bin_rest (sbintrunc (Suc n) bin) = sbintrunc n (bin_rest bin)"
  by (simp add: signed_take_bit_Suc)

lemma bintrunc_rest [simp]: "bintrunc n (bin_rest (bintrunc n bin)) = bin_rest (bintrunc n bin)"
  by (induct n arbitrary: bin) (simp_all add: take_bit_Suc)

lemma sbintrunc_rest [simp]: "sbintrunc n (bin_rest (sbintrunc n bin)) = bin_rest (sbintrunc n bin)"
  by (induct n arbitrary: bin) (simp_all add: signed_take_bit_Suc mod2_eq_if)

lemma bintrunc_rest': "bintrunc n \<circ> bin_rest \<circ> bintrunc n = bin_rest \<circ> bintrunc n"
  by (rule ext) auto

lemma sbintrunc_rest': "sbintrunc n \<circ> bin_rest \<circ> sbintrunc n = bin_rest \<circ> sbintrunc n"
  by (rule ext) auto

lemma rco_lem: "f \<circ> g \<circ> f = g \<circ> f \<Longrightarrow> f \<circ> (g \<circ> f) ^^ n = g ^^ n \<circ> f"
  apply (rule ext)
  apply (induct_tac n)
   apply (simp_all (no_asm))
  apply (drule fun_cong)
  apply (unfold o_def)
  apply (erule trans)
  apply simp
  done

lemmas rco_bintr = bintrunc_rest'
  [THEN rco_lem [THEN fun_cong], unfolded o_def]
lemmas rco_sbintr = sbintrunc_rest'
  [THEN rco_lem [THEN fun_cong], unfolded o_def]


subsection \<open>Splitting and concatenation\<close>

definition bin_split :: \<open>nat \<Rightarrow> int \<Rightarrow> int \<times> int\<close>
  where [simp]: \<open>bin_split n k = (drop_bit n k, take_bit n k)\<close>

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (w div 2) in (w1, of_bool (odd w) + 2 * w2))"
  "bin_split 0 w = (w, 0)"
  by (simp_all add: drop_bit_Suc take_bit_Suc mod_2_eq_odd)

abbreviation (input) bin_cat :: \<open>int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bin_cat k n l \<equiv> concat_bit n l k\<close>

lemma bin_cat_eq_push_bit_add_take_bit:
  \<open>bin_cat k n l = push_bit n k + take_bit n l\<close>
  by (simp add: concat_bit_eq)
  
lemma bin_sign_cat: "bin_sign (bin_cat x n y) = bin_sign x"
proof -
  have \<open>0 \<le> x\<close> if \<open>0 \<le> x * 2 ^ n + y mod 2 ^ n\<close>
  proof -
    have \<open>y mod 2 ^ n < 2 ^ n\<close>
      using pos_mod_bound [of \<open>2 ^ n\<close> y] by simp
    then have \<open>\<not> y mod 2 ^ n \<ge> 2 ^ n\<close>
      by (simp add: less_le)
    with that have \<open>x \<noteq> - 1\<close>
      by auto
    have *: \<open>- 1 \<le> (- (y mod 2 ^ n)) div 2 ^ n\<close>
      by (simp add: zdiv_zminus1_eq_if)
    from that have \<open>- (y mod 2 ^ n) \<le> x * 2 ^ n\<close>
      by simp
    then have \<open>(- (y mod 2 ^ n)) div 2 ^ n \<le> (x * 2 ^ n) div 2 ^ n\<close>
      using zdiv_mono1 zero_less_numeral zero_less_power by blast
    with * have \<open>- 1 \<le> x * 2 ^ n div 2 ^ n\<close> by simp
    with \<open>x \<noteq> - 1\<close> show ?thesis
      by simp
  qed
  then show ?thesis
    by (simp add: bin_sign_def not_le not_less bin_cat_eq_push_bit_add_take_bit push_bit_eq_mult take_bit_eq_mod)
qed

lemma bin_cat_assoc: "bin_cat (bin_cat x m y) n z = bin_cat x (m + n) (bin_cat y n z)"
  by (fact concat_bit_assoc)

lemma bin_cat_assoc_sym: "bin_cat x m (bin_cat y n z) = bin_cat (bin_cat x (m - n) y) (min m n) z"
  by (fact concat_bit_assoc_sym)

definition bin_rcat :: "nat \<Rightarrow> int list \<Rightarrow> int"
  where "bin_rcat n = foldl (\<lambda>u v. bin_cat u n v) 0"

fun bin_rsplit_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split n c
      in bin_rsplit_aux n (m - n) a (b # bs))"

definition bin_rsplit :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) []"

fun bin_rsplitl_aux :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list"
  where "bin_rsplitl_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else
      let (a, b) = bin_split (min m n) c
      in bin_rsplitl_aux n (m - n) a (b # bs))"

definition bin_rsplitl :: "nat \<Rightarrow> nat \<times> int \<Rightarrow> int list"
  where "bin_rsplitl n w = bin_rsplitl_aux n (fst w) (snd w) []"

declare bin_rsplit_aux.simps [simp del]
declare bin_rsplitl_aux.simps [simp del]

lemma bin_nth_cat:
  "bin_nth (bin_cat x k y) n =
    (if n < k then bin_nth y n else bin_nth x (n - k))"
  by (simp add: bit_concat_bit_iff)

lemma bin_nth_drop_bit_iff:
  \<open>bin_nth (drop_bit n c) k \<longleftrightarrow> bin_nth c (n + k)\<close>
  by (simp add: bit_drop_bit_eq)

lemma bin_nth_take_bit_iff:
  \<open>bin_nth (take_bit n c) k \<longleftrightarrow> k < n \<and> bin_nth c k\<close>
  by (fact bit_take_bit_iff)

lemma bin_nth_split:
  "bin_split n c = (a, b) \<Longrightarrow>
    (\<forall>k. bin_nth a k = bin_nth c (n + k)) \<and>
    (\<forall>k. bin_nth b k = (k < n \<and> bin_nth c k))"
  by (auto simp add: bin_nth_drop_bit_iff bin_nth_take_bit_iff)

lemma bin_cat_zero [simp]: "bin_cat 0 n w = bintrunc n w"
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma bintr_cat1: "bintrunc (k + n) (bin_cat a n b) = bin_cat (bintrunc k a) n b"
  by (metis bin_cat_assoc bin_cat_zero)

lemma bintr_cat: "bintrunc m (bin_cat a n b) =
    bin_cat (bintrunc (m - n) a) n (bintrunc (min m n) b)"
  
  by (rule bin_eqI) (auto simp: bin_nth_cat nth_bintr)

lemma bintr_cat_same [simp]: "bintrunc n (bin_cat a n b) = bintrunc n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: "bin_cat a n (bintrunc n b) = bin_cat a n b"
  by (simp add: bin_cat_eq_push_bit_add_take_bit)

lemma split_bintrunc: "bin_split n c = (a, b) \<Longrightarrow> b = bintrunc n c"
  by simp

lemma bin_cat_split: "bin_split n w = (u, v) \<Longrightarrow> w = bin_cat u n v"
  by (auto simp add: bin_cat_eq_push_bit_add_take_bit bits_ident)

lemma drop_bit_bin_cat_eq:
  \<open>drop_bit n (bin_cat v n w) = v\<close>
  by (rule bit_eqI) (simp add: bit_drop_bit_eq bit_concat_bit_iff)

lemma take_bit_bin_cat_eq:
  \<open>take_bit n (bin_cat v n w) = take_bit n w\<close>
  by (rule bit_eqI) (simp add: bit_concat_bit_iff)

lemma bin_split_cat: "bin_split n (bin_cat v n w) = (v, bintrunc n w)"
  by (simp add: drop_bit_bin_cat_eq take_bit_bin_cat_eq)

lemma bin_split_zero [simp]: "bin_split n 0 = (0, 0)"
  by simp

lemma bin_split_minus1 [simp]:
  "bin_split n (- 1) = (- 1, bintrunc n (- 1))"
  by simp

lemma bin_split_trunc:
  "bin_split (min m n) c = (a, b) \<Longrightarrow>
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: prod.split_asm)
  apply (case_tac m)
   apply (auto simp: Let_def drop_bit_Suc take_bit_Suc mod_2_eq_odd split: prod.split_asm)
  done

lemma bin_split_trunc1:
  "bin_split n c = (a, b) \<Longrightarrow>
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, bintrunc m b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: prod.split_asm)
  apply (case_tac m)
   apply (auto simp: Let_def drop_bit_Suc take_bit_Suc mod_2_eq_odd split: prod.split_asm)
  done

lemma bin_cat_num: "bin_cat a n b = a * 2 ^ n + bintrunc n b"
  by (simp add: bin_cat_eq_push_bit_add_take_bit push_bit_eq_mult)

lemma bin_split_num: "bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  by (simp add: drop_bit_eq_div take_bit_eq_mod)

lemmas bin_rsplit_aux_simps = bin_rsplit_aux.simps bin_rsplitl_aux.simps
lemmas rsplit_aux_simps = bin_rsplit_aux_simps

lemmas th_if_simp1 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct1, THEN mp] for l
lemmas th_if_simp2 = if_split [where P = "(=) l", THEN iffD1, THEN conjunct2, THEN mp] for l

lemmas rsplit_aux_simp1s = rsplit_aux_simps [THEN th_if_simp1]

lemmas rsplit_aux_simp2ls = rsplit_aux_simps [THEN th_if_simp2]
\<comment> \<open>these safe to \<open>[simp add]\<close> as require calculating \<open>m - n\<close>\<close>
lemmas bin_rsplit_aux_simp2s [simp] = rsplit_aux_simp2ls [unfolded Let_def]
lemmas rbscl = bin_rsplit_aux_simp2s (2)

lemmas rsplit_aux_0_simps [simp] =
  rsplit_aux_simp1s [OF disjI1] rsplit_aux_simp1s [OF disjI2]

lemma bin_rsplit_aux_append: "bin_rsplit_aux n m c (bs @ cs) = bin_rsplit_aux n m c bs @ cs"
  apply (induct n m c bs rule: bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp split: prod.split)
  done

lemma bin_rsplitl_aux_append: "bin_rsplitl_aux n m c (bs @ cs) = bin_rsplitl_aux n m c bs @ cs"
  apply (induct n m c bs rule: bin_rsplitl_aux.induct)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplitl_aux.simps)
  apply (clarsimp split: prod.split)
  done

lemmas rsplit_aux_apps [where bs = "[]"] =
  bin_rsplit_aux_append bin_rsplitl_aux_append

lemmas rsplit_def_auxs = bin_rsplit_def bin_rsplitl_def

lemmas rsplit_aux_alts = rsplit_aux_apps
  [unfolded append_Nil rsplit_def_auxs [symmetric]]

lemma bin_split_minus: "0 < n \<Longrightarrow> bin_split (Suc (n - 1)) w = bin_split n w"
  by auto

lemma bin_split_pred_simp [simp]:
  "(0::nat) < numeral bin \<Longrightarrow>
    bin_split (numeral bin) w =
      (let (w1, w2) = bin_split (numeral bin - 1) (bin_rest w)
       in (w1, of_bool (odd w) + 2 * w2))"
  by (simp add: take_bit_rec drop_bit_rec mod_2_eq_odd)

lemma bin_rsplit_aux_simp_alt:
  "bin_rsplit_aux n m c bs =
    (if m = 0 \<or> n = 0 then bs
     else let (a, b) = bin_split n c in bin_rsplit n (m - n, a) @ b # bs)"
  apply (simp add: bin_rsplit_aux.simps [of n m c bs])
  apply (subst rsplit_aux_alts)
  apply (simp add: bin_rsplit_def)
  done

lemmas bin_rsplit_simp_alt =
  trans [OF bin_rsplit_def bin_rsplit_aux_simp_alt]

lemmas bthrs = bin_rsplit_simp_alt [THEN [2] trans]

lemma bin_rsplit_size_sign' [rule_format]:
  "n > 0 \<Longrightarrow> rev sw = bin_rsplit n (nw, w) \<Longrightarrow> \<forall>v\<in>set sw. bintrunc n v = v"
  apply (induct sw arbitrary: nw w)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: prod.split_asm if_split_asm)
  apply clarify
  apply simp
  done

lemmas bin_rsplit_size_sign = bin_rsplit_size_sign' [OF asm_rl
  rev_rev_ident [THEN trans] set_rev [THEN equalityD2 [THEN subsetD]]]

lemma bin_nth_rsplit [rule_format] :
  "n > 0 \<Longrightarrow> m < n \<Longrightarrow>
    \<forall>w k nw.
      rev sw = bin_rsplit n (nw, w) \<longrightarrow>
      k < size sw \<longrightarrow> bin_nth (sw ! k) m = bin_nth w (k * n + m)"
  apply (induct sw)
   apply clarsimp
  apply clarsimp
  apply (drule bthrs)
  apply (simp (no_asm_use) add: Let_def split: prod.split_asm if_split_asm)
  apply (erule allE, erule impE, erule exI)
  apply (case_tac k)
   apply clarsimp
   prefer 2
   apply clarsimp
   apply (erule allE)
   apply (erule (1) impE)
   apply (simp add: bit_drop_bit_eq ac_simps)
  apply (simp add: bit_take_bit_iff ac_simps)
  done

lemma bin_rsplit_all: "0 < nw \<Longrightarrow> nw \<le> n \<Longrightarrow> bin_rsplit n (nw, w) = [bintrunc n w]"
  by (auto simp: bin_rsplit_def rsplit_aux_simp2ls split: prod.split dest!: split_bintrunc)

lemma bin_rsplit_l [rule_format]:
  "\<forall>bin. bin_rsplitl n (m, bin) = bin_rsplit n (m, bintrunc m bin)"
  apply (rule_tac a = "m" in wf_less_than [THEN wf_induct])
  apply (simp (no_asm) add: bin_rsplitl_def bin_rsplit_def)
  apply (rule allI)
  apply (subst bin_rsplitl_aux.simps)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: prod.split)
  apply (simp add: ac_simps)
  apply (subst rsplit_aux_alts(1))
  apply (subst rsplit_aux_alts(2))
  apply clarsimp
  unfolding bin_rsplit_def bin_rsplitl_def
  apply (simp add: drop_bit_take_bit)
  apply (case_tac \<open>x < n\<close>)
  apply (simp_all add: not_less min_def)
  done

lemma bin_rsplit_rcat [rule_format]:
  "n > 0 \<longrightarrow> bin_rsplit n (n * size ws, bin_rcat n ws) = map (bintrunc n) ws"
  apply (unfold bin_rsplit_def bin_rcat_def)
  apply (rule_tac xs = ws in rev_induct)
   apply clarsimp
  apply clarsimp
  apply (subst rsplit_aux_alts)
  apply (simp add: drop_bit_bin_cat_eq take_bit_bin_cat_eq)
  done

lemma bin_rsplit_aux_len_le [rule_format] :
  "\<forall>ws m. n \<noteq> 0 \<longrightarrow> ws = bin_rsplit_aux n nw w bs \<longrightarrow>
    length ws \<le> m \<longleftrightarrow> nw + length bs * n \<le> m * n"
proof -
  have *: R
    if d: "i \<le> j \<or> m < j'"
    and R1: "i * k \<le> j * k \<Longrightarrow> R"
    and R2: "Suc m * k' \<le> j' * k' \<Longrightarrow> R"
    for i j j' k k' m :: nat and R
    using d
    apply safe
    apply (rule R1, erule mult_le_mono1)
    apply (rule R2, erule Suc_le_eq [THEN iffD2 [THEN mult_le_mono1]])
    done
  have **: "0 < sc \<Longrightarrow> sc - n + (n + lb * n) \<le> m * n \<longleftrightarrow> sc + lb * n \<le> m * n"
    for sc m n lb :: nat
    apply safe
     apply arith
    apply (case_tac "sc \<ge> n")
     apply arith
    apply (insert linorder_le_less_linear [of m lb])
    apply (erule_tac k=n and k'=n in *)
     apply arith
    apply simp
    done
  show ?thesis
    apply (induct n nw w bs rule: bin_rsplit_aux.induct)
    apply (subst bin_rsplit_aux.simps)
    apply (simp add: ** Let_def split: prod.split)
    done
qed

lemma bin_rsplit_len_le: "n \<noteq> 0 \<longrightarrow> ws = bin_rsplit n (nw, w) \<longrightarrow> length ws \<le> m \<longleftrightarrow> nw \<le> m * n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len_le)

lemma bin_rsplit_aux_len:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit_aux n nw w cs) = (nw + n - 1) div n + length cs"
  apply (induct n nw w cs rule: bin_rsplit_aux.induct)
  apply (subst bin_rsplit_aux.simps)
  apply (clarsimp simp: Let_def split: prod.split)
  apply (erule thin_rl)
  apply (case_tac m)
   apply simp
  apply (case_tac "m \<le> n")
   apply (auto simp add: div_add_self2)
  done

lemma bin_rsplit_len: "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, w)) = (nw + n - 1) div n"
  by (auto simp: bin_rsplit_def bin_rsplit_aux_len)

lemma bin_rsplit_aux_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length bs = length cs \<Longrightarrow>
    length (bin_rsplit_aux n nw v bs) =
    length (bin_rsplit_aux n nw w cs)"
proof (induct n nw w cs arbitrary: v bs rule: bin_rsplit_aux.induct)
  case (1 n m w cs v bs)
  show ?case
  proof (cases "m = 0")
    case True
    with \<open>length bs = length cs\<close> show ?thesis by simp
  next
    case False
    from "1.hyps" [of \<open>bin_split n w\<close> \<open>drop_bit n w\<close> \<open>take_bit n w\<close>] \<open>m \<noteq> 0\<close> \<open>n \<noteq> 0\<close>
    have hyp: "\<And>v bs. length bs = Suc (length cs) \<Longrightarrow>
      length (bin_rsplit_aux n (m - n) v bs) =
      length (bin_rsplit_aux n (m - n) (drop_bit n w) (take_bit n w # cs))"
      using bin_rsplit_aux_len by fastforce 
    from \<open>length bs = length cs\<close> \<open>n \<noteq> 0\<close> show ?thesis
      by (auto simp add: bin_rsplit_aux_simp_alt Let_def bin_rsplit_len split: prod.split)
  qed
qed

lemma bin_rsplit_len_indep:
  "n \<noteq> 0 \<Longrightarrow> length (bin_rsplit n (nw, v)) = length (bin_rsplit n (nw, w))"
  apply (unfold bin_rsplit_def)
  apply (simp (no_asm))
  apply (erule bin_rsplit_aux_len_indep)
  apply (rule refl)
  done


subsection \<open>Logical operations\<close>

primrec bin_sc :: "nat \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int"
  where
    Z: "bin_sc 0 b w = of_bool b + 2 * bin_rest w"
  | Suc: "bin_sc (Suc n) b w = of_bool (odd w) + 2 * bin_sc n b (w div 2)"

lemma bin_nth_sc [simp]: "bit (bin_sc n b w) n \<longleftrightarrow> b"
  by (induction n arbitrary: w) (simp_all add: bit_Suc)

lemma bin_sc_sc_same [simp]: "bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induction n arbitrary: w) (simp_all add: bit_Suc)

lemma bin_sc_sc_diff: "m \<noteq> n \<Longrightarrow> bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: "bin_nth (bin_sc n b w) m = (if m = n then b else bin_nth w m)"
  apply (induct n arbitrary: w m)
   apply (case_tac m; simp add: bit_Suc)
  apply (case_tac m; simp add: bit_Suc)
  done

lemma bin_sc_eq:
  \<open>bin_sc n False = unset_bit n\<close>
  \<open>bin_sc n True = Bit_Operations.set_bit n\<close>
  by (simp_all add: fun_eq_iff bit_eq_iff)
    (simp_all add: bin_nth_sc_gen bit_set_bit_iff bit_unset_bit_iff)

lemma bin_sc_nth [simp]: "bin_sc n (bin_nth w n) w = w"
  by (rule bit_eqI) (simp add: bin_nth_sc_gen)

lemma bin_sign_sc [simp]: "bin_sign (bin_sc n b w) = bin_sign w"
proof (induction n arbitrary: w)
  case 0
  then show ?case
    by (auto simp add: bin_sign_def) (use bin_rest_ge_0 in fastforce)
next
  case (Suc n)
  from Suc [of \<open>w div 2\<close>]
  show ?case by (auto simp add: bin_sign_def split: if_splits)
qed

lemma bin_sc_bintr [simp]:
  "bintrunc m (bin_sc n x (bintrunc m w)) = bintrunc m (bin_sc n x w)"
  apply (cases x)
   apply (simp_all add: bin_sc_eq bit_eq_iff)
   apply (auto simp add: bit_take_bit_iff bit_set_bit_iff bit_unset_bit_iff)
  done

lemma bin_clr_le: "bin_sc n False w \<le> w"
  by (simp add: bin_sc_eq unset_bit_less_eq)

lemma bin_set_ge: "bin_sc n True w \<ge> w"
  by (simp add: bin_sc_eq set_bit_greater_eq)

lemma bintr_bin_clr_le: "bintrunc n (bin_sc m False w) \<le> bintrunc n w"
  by (simp add: bin_sc_eq take_bit_unset_bit_eq unset_bit_less_eq)

lemma bintr_bin_set_ge: "bintrunc n (bin_sc m True w) \<ge> bintrunc n w"
  by (simp add: bin_sc_eq take_bit_set_bit_eq set_bit_greater_eq)

lemma bin_sc_FP [simp]: "bin_sc n False 0 = 0"
  by (induct n) auto

lemma bin_sc_TM [simp]: "bin_sc n True (- 1) = - 1"
  by (induct n) auto

lemmas bin_sc_simps = bin_sc.Z bin_sc.Suc bin_sc_TM bin_sc_FP

lemma bin_sc_minus: "0 < n \<Longrightarrow> bin_sc (Suc (n - 1)) b w = bin_sc n b w"
  by auto

lemmas bin_sc_Suc_minus =
  trans [OF bin_sc_minus [symmetric] bin_sc.Suc]

lemma bin_sc_numeral [simp]:
  "bin_sc (numeral k) b w =
    of_bool (odd w) + 2 * bin_sc (pred_numeral k) b (w div 2)"
  by (simp add: numeral_eq_Suc)

instantiation int :: semiring_bit_syntax
begin

definition [iff]: "i !! n \<longleftrightarrow> bin_nth i n"

definition "shiftl x n = x * 2 ^ n" for x :: int

definition "shiftr x n = x div 2 ^ n" for x :: int

instance by standard
  (simp_all add: fun_eq_iff shiftl_int_def shiftr_int_def push_bit_eq_mult drop_bit_eq_div)

end

lemma shiftl_eq_push_bit:
  \<open>k << n = push_bit n k\<close> for k :: int
  by (fact shiftl_eq_push_bit)

lemma shiftr_eq_drop_bit:
  \<open>k >> n = drop_bit n k\<close> for k :: int
  by (fact shiftr_eq_drop_bit)


subsubsection \<open>Basic simplification rules\<close>

lemmas int_not_def = not_int_def

lemma int_not_simps [simp]:
  "NOT (0::int) = -1"
  "NOT (1::int) = -2"
  "NOT (- 1::int) = 0"
  "NOT (numeral w::int) = - numeral (w + Num.One)"
  "NOT (- numeral (Num.Bit0 w)::int) = numeral (Num.BitM w)"
  "NOT (- numeral (Num.Bit1 w)::int) = numeral (Num.Bit0 w)"
  by (simp_all add: not_int_def)

lemma int_not_not: "NOT (NOT x) = x"
  for x :: int
  by (fact bit.double_compl)

lemma int_and_0 [simp]: "0 AND x = 0"
  for x :: int
  by (fact bit.conj_zero_left)

lemma int_and_m1 [simp]: "-1 AND x = x"
  for x :: int
  by (fact bit.conj_one_left)

lemma int_or_zero [simp]: "0 OR x = x"
  for x :: int
  by (fact bit.disj_zero_left)

lemma int_or_minus1 [simp]: "-1 OR x = -1"
  for x :: int
  by (fact bit.disj_one_left)

lemma int_xor_zero [simp]: "0 XOR x = x"
  for x :: int
  by (fact bit.xor_zero_left)


subsubsection \<open>Binary destructors\<close>

lemma bin_rest_NOT [simp]: "bin_rest (NOT x) = NOT (bin_rest x)"
  by (fact not_int_div_2)

lemma bin_last_NOT [simp]: "bin_last (NOT x) \<longleftrightarrow> \<not> bin_last x"
  by simp

lemma bin_rest_AND [simp]: "bin_rest (x AND y) = bin_rest x AND bin_rest y"
  by (subst and_int_rec) auto

lemma bin_last_AND [simp]: "bin_last (x AND y) \<longleftrightarrow> bin_last x \<and> bin_last y"
  by (subst and_int_rec) auto

lemma bin_rest_OR [simp]: "bin_rest (x OR y) = bin_rest x OR bin_rest y"
  by (subst or_int_rec) auto

lemma bin_last_OR [simp]: "bin_last (x OR y) \<longleftrightarrow> bin_last x \<or> bin_last y"
  by (subst or_int_rec) auto

lemma bin_rest_XOR [simp]: "bin_rest (x XOR y) = bin_rest x XOR bin_rest y"
  by (subst xor_int_rec) auto

lemma bin_last_XOR [simp]: "bin_last (x XOR y) \<longleftrightarrow> (bin_last x \<or> bin_last y) \<and> \<not> (bin_last x \<and> bin_last y)"
  by (subst xor_int_rec) auto

lemma bin_nth_ops:
  "\<And>x y. bin_nth (x AND y) n \<longleftrightarrow> bin_nth x n \<and> bin_nth y n"
  "\<And>x y. bin_nth (x OR y) n \<longleftrightarrow> bin_nth x n \<or> bin_nth y n"
  "\<And>x y. bin_nth (x XOR y) n \<longleftrightarrow> bin_nth x n \<noteq> bin_nth y n"
  "\<And>x. bin_nth (NOT x) n \<longleftrightarrow> \<not> bin_nth x n"
  by (simp_all add: bit_and_iff bit_or_iff bit_xor_iff bit_not_iff)


subsubsection \<open>Derived properties\<close>

lemma int_xor_minus1 [simp]: "-1 XOR x = NOT x"
  for x :: int
  by (fact bit.xor_one_left)

lemma int_xor_extra_simps [simp]:
  "w XOR 0 = w"
  "w XOR -1 = NOT w"
  for w :: int
  by simp_all

lemma int_or_extra_simps [simp]:
  "w OR 0 = w"
  "w OR -1 = -1"
  for w :: int
  by simp_all

lemma int_and_extra_simps [simp]:
  "w AND 0 = 0"
  "w AND -1 = w"
  for w :: int
  by simp_all

text \<open>Commutativity of the above.\<close>
lemma bin_ops_comm:
  fixes x y :: int
  shows int_and_comm: "x AND y = y AND x"
    and int_or_comm:  "x OR y = y OR x"
    and int_xor_comm: "x XOR y = y XOR x"
  by (simp_all add: ac_simps)

lemma bin_ops_same [simp]:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: int
  by simp_all

lemmas bin_log_esimps =
  int_and_extra_simps  int_or_extra_simps  int_xor_extra_simps
  int_and_0 int_and_m1 int_or_zero int_or_minus1 int_xor_zero int_xor_minus1


subsubsection \<open>Basic properties of logical (bit-wise) operations\<close>

lemma bbw_ao_absorb: "x AND (y OR x) = x \<and> x OR (y AND x) = x"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_absorbs_other:
  "x AND (x OR y) = x \<and> (y AND x) OR x = x"
  "(y OR x) AND x = x \<and> x OR (x AND y) = x"
  "(x OR y) AND x = x \<and> (x AND y) OR x = x"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_ao_absorbs [simp] = bbw_ao_absorb bbw_ao_absorbs_other

lemma int_xor_not: "(NOT x) XOR y = NOT (x XOR y) \<and> x XOR (NOT y) = NOT (x XOR y)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_assoc: "(x AND y) AND z = x AND (y AND z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_assoc: "(x OR y) OR z = x OR (y OR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_assoc: "(x XOR y) XOR z = x XOR (y XOR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemmas bbw_assocs = int_and_assoc int_or_assoc int_xor_assoc

(* BH: Why are these declared as simp rules??? *)
lemma bbw_lcs [simp]:
  "y AND (x AND z) = x AND (y AND z)"
  "y OR (x OR z) = x OR (y OR z)"
  "y XOR (x XOR z) = x XOR (y XOR z)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_not_dist:
  "NOT (x OR y) = (NOT x) AND (NOT y)"
  "NOT (x AND y) = (NOT x) OR (NOT y)"
  for x y :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_oa_dist: "(x AND y) OR z = (x OR z) AND (y OR z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bbw_ao_dist: "(x OR y) AND z = (x AND z) OR (y AND z)"
  for x y z :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

(*
Why were these declared simp???
declare bin_ops_comm [simp] bbw_assocs [simp]
*)


subsubsection \<open>Simplification with numerals\<close>

text \<open>Cases for \<open>0\<close> and \<open>-1\<close> are already covered by other simp rules.\<close>

lemma bin_rest_neg_numeral_BitM [simp]:
  "bin_rest (- numeral (Num.BitM w)) = - numeral w"
  by simp

lemma bin_last_neg_numeral_BitM [simp]:
  "bin_last (- numeral (Num.BitM w))"
  by simp

(* FIXME: The rule sets below are very large (24 rules for each
  operator). Is there a simpler way to do this? *)

lemma int_and_numerals [simp]:
  "numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND numeral y)"
  "numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (2 :: int) * (numeral x AND numeral y)"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND numeral y)"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x AND numeral y)"
  "numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND - numeral y)"
  "numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (2 :: int) * (numeral x AND - numeral (y + Num.One))"
  "numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (numeral x AND - numeral y)"
  "numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x AND - numeral (y + Num.One))"
  "- numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (2 :: int) * (- numeral x AND numeral y)"
  "- numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (2 :: int) * (- numeral x AND numeral y)"
  "- numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (2 :: int) * (- numeral (x + Num.One) AND numeral y)"
  "- numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) AND numeral y)"
  "- numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (- numeral x AND - numeral y)"
  "- numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (2 :: int) * (- numeral x AND - numeral (y + Num.One))"
  "- numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (2 :: int) * (- numeral (x + Num.One) AND - numeral y)"
  "- numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) AND - numeral (y + Num.One))"
  "(1::int) AND numeral (Num.Bit0 y) = 0"
  "(1::int) AND numeral (Num.Bit1 y) = 1"
  "(1::int) AND - numeral (Num.Bit0 y) = 0"
  "(1::int) AND - numeral (Num.Bit1 y) = 1"
  "numeral (Num.Bit0 x) AND (1::int) = 0"
  "numeral (Num.Bit1 x) AND (1::int) = 1"
  "- numeral (Num.Bit0 x) AND (1::int) = 0"
  "- numeral (Num.Bit1 x) AND (1::int) = 1"
  by (rule bin_rl_eqI; simp)+

lemma int_or_numerals [simp]:
  "numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (2 :: int) * (numeral x OR numeral y)"
  "numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR numeral y)"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x OR numeral y)"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR numeral y)"
  "numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (2 :: int) * (numeral x OR - numeral y)"
  "numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR - numeral (y + Num.One))"
  "numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x OR - numeral y)"
  "numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x OR - numeral (y + Num.One))"
  "- numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (2 :: int) * (- numeral x OR numeral y)"
  "- numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x OR numeral y)"
  "- numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR numeral y)"
  "- numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR numeral y)"
  "- numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (2 :: int) * (- numeral x OR - numeral y)"
  "- numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x OR - numeral (y + Num.One))"
  "- numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR - numeral y)"
  "- numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral (x + Num.One) OR - numeral (y + Num.One))"
  "(1::int) OR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)"
  "(1::int) OR numeral (Num.Bit1 y) = numeral (Num.Bit1 y)"
  "(1::int) OR - numeral (Num.Bit0 y) = - numeral (Num.BitM y)"
  "(1::int) OR - numeral (Num.Bit1 y) = - numeral (Num.Bit1 y)"
  "numeral (Num.Bit0 x) OR (1::int) = numeral (Num.Bit1 x)"
  "numeral (Num.Bit1 x) OR (1::int) = numeral (Num.Bit1 x)"
  "- numeral (Num.Bit0 x) OR (1::int) = - numeral (Num.BitM x)"
  "- numeral (Num.Bit1 x) OR (1::int) = - numeral (Num.Bit1 x)"
  by (rule bin_rl_eqI; simp)+

lemma int_xor_numerals [simp]:
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (2 :: int) * (numeral x XOR numeral y)"
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x XOR numeral y)"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x XOR numeral y)"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (2 :: int) * (numeral x XOR numeral y)"
  "numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (2 :: int) * (numeral x XOR - numeral y)"
  "numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (numeral x XOR - numeral (y + Num.One))"
  "numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (numeral x XOR - numeral y)"
  "numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (2 :: int) * (numeral x XOR - numeral (y + Num.One))"
  "- numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (2 :: int) * (- numeral x XOR numeral y)"
  "- numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x XOR numeral y)"
  "- numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) XOR numeral y)"
  "- numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (2 :: int) * (- numeral (x + Num.One) XOR numeral y)"
  "- numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (2 :: int) * (- numeral x XOR - numeral y)"
  "- numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = 1 + (2 :: int) * (- numeral x XOR - numeral (y + Num.One))"
  "- numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = 1 + (2 :: int) * (- numeral (x + Num.One) XOR - numeral y)"
  "- numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (2 :: int) * (- numeral (x + Num.One) XOR - numeral (y + Num.One))"
  "(1::int) XOR numeral (Num.Bit0 y) = numeral (Num.Bit1 y)"
  "(1::int) XOR numeral (Num.Bit1 y) = numeral (Num.Bit0 y)"
  "(1::int) XOR - numeral (Num.Bit0 y) = - numeral (Num.BitM y)"
  "(1::int) XOR - numeral (Num.Bit1 y) = - numeral (Num.Bit0 (y + Num.One))"
  "numeral (Num.Bit0 x) XOR (1::int) = numeral (Num.Bit1 x)"
  "numeral (Num.Bit1 x) XOR (1::int) = numeral (Num.Bit0 x)"
  "- numeral (Num.Bit0 x) XOR (1::int) = - numeral (Num.BitM x)"
  "- numeral (Num.Bit1 x) XOR (1::int) = - numeral (Num.Bit0 (x + Num.One))"
  by (rule bin_rl_eqI; simp)+


subsubsection \<open>Interactions with arithmetic\<close>

lemma plus_and_or: "(x AND y) + (x OR y) = x + y" for x y :: int
proof (induction x arbitrary: y rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even x)
  from even.IH [of \<open>y div 2\<close>]
  show ?case
    by (auto simp add: and_int_rec [of _ y] or_int_rec [of _ y] elim: oddE)
next
  case (odd x)
  from odd.IH [of \<open>y div 2\<close>]
  show ?case
    by (auto simp add: and_int_rec [of _ y] or_int_rec [of _ y] elim: oddE)
qed

lemma le_int_or: "bin_sign y = 0 \<Longrightarrow> x \<le> x OR y"
  for x y :: int
  by (simp add: bin_sign_def or_greater_eq split: if_splits)

lemmas int_and_le =
  xtrans(3) [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or]

text \<open>Interaction between bit-wise and arithmetic: good example of \<open>bin_induction\<close>.\<close>
lemma bin_add_not: "x + NOT x = (-1::int)"
  by (simp add: not_int_def)

lemma AND_mod: "x AND (2 ^ n - 1) = x mod 2 ^ n"
  for x :: int
  by (simp flip: take_bit_eq_mod add: take_bit_eq_mask mask_eq_exp_minus_1)


subsubsection \<open>Comparison\<close>

lemma AND_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x"
  shows "0 \<le> x AND y"
  using assms by simp

lemma OR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "0 \<le> y"
  shows "0 \<le> x OR y"
  using assms by simp

lemma XOR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "0 \<le> y"
  shows "0 \<le> x XOR y"
  using assms by simp

lemma AND_upper1 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x"
  shows "x AND y \<le> x"
  using assms by (induction x arbitrary: y rule: int_bit_induct)
    (simp_all add: and_int_rec [of \<open>_ * 2\<close>] and_int_rec [of \<open>1 + _ * 2\<close>] add_increasing)

lemmas AND_upper1' [simp] = order_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper1'' [simp] = order_le_less_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma AND_upper2 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> y"
  shows "x AND y \<le> y"
  using assms AND_upper1 [of y x] by (simp add: ac_simps)

lemmas AND_upper2' [simp] = order_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper2'' [simp] = order_le_less_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma OR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x OR y < 2 ^ n"
using assms proof (induction x arbitrary: y n rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even x)
  from even.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] even.prems even.hyps
  show ?case 
    by (cases n) (auto simp add: or_int_rec [of \<open>_ * 2\<close>] elim: oddE)
next
  case (odd x)
  from odd.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] odd.prems odd.hyps
  show ?case
    by (cases n) (auto simp add: or_int_rec [of \<open>1 + _ * 2\<close>], linarith)
qed

lemma XOR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x XOR y < 2 ^ n"
using assms proof (induction x arbitrary: y n rule: int_bit_induct)
  case zero
  then show ?case
    by simp
next
  case minus
  then show ?case
    by simp
next
  case (even x)
  from even.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] even.prems even.hyps
  show ?case 
    by (cases n) (auto simp add: xor_int_rec [of \<open>_ * 2\<close>] elim: oddE)
next
  case (odd x)
  from odd.IH [of \<open>n - 1\<close> \<open>y div 2\<close>] odd.prems odd.hyps
  show ?case
    by (cases n) (auto simp add: xor_int_rec [of \<open>1 + _ * 2\<close>])
qed


subsubsection \<open>Truncating results of bit-wise operations\<close>

lemma bin_trunc_ao:
  "bintrunc n x AND bintrunc n y = bintrunc n (x AND y)"
  "bintrunc n x OR bintrunc n y = bintrunc n (x OR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_xor: "bintrunc n (bintrunc n x XOR bintrunc n y) = bintrunc n (x XOR y)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

lemma bin_trunc_not: "bintrunc n (NOT (bintrunc n x)) = bintrunc n (NOT x)"
  by (auto simp add: bin_eq_iff bin_nth_ops nth_bintr)

text \<open>Want theorems of the form of \<open>bin_trunc_xor\<close>.\<close>
lemma bintr_bintr_i: "x = bintrunc n y \<Longrightarrow> bintrunc n x = bintrunc n y"
  by auto

lemmas bin_trunc_and = bin_trunc_ao(1) [THEN bintr_bintr_i]
lemmas bin_trunc_or = bin_trunc_ao(2) [THEN bintr_bintr_i]


subsubsection \<open>More lemmas\<close>

lemma not_int_cmp_0 [simp]:
  fixes i :: int shows
  "0 < NOT i \<longleftrightarrow> i < -1"
  "0 \<le> NOT i \<longleftrightarrow> i < 0"
  "NOT i < 0 \<longleftrightarrow> i \<ge> 0"
  "NOT i \<le> 0 \<longleftrightarrow> i \<ge> -1"
by(simp_all add: int_not_def) arith+

lemma bbw_ao_dist2: "(x :: int) AND (y OR z) = x AND y OR x AND z"
  by (fact bit.conj_disj_distrib)

lemmas int_and_ac = bbw_lcs(1) int_and_comm int_and_assoc

lemma int_nand_same [simp]: fixes x :: int shows "x AND NOT x = 0"
  by simp

lemma int_nand_same_middle: fixes x :: int shows "x AND y AND NOT x = 0"
  by (simp add: bit_eq_iff bit_and_iff bit_not_iff)

lemma and_xor_dist: fixes x :: int shows
  "x AND (y XOR z) = (x AND y) XOR (x AND z)"
  by (fact bit.conj_xor_distrib)

lemma int_and_lt0 [simp]:
  \<open>x AND y < 0 \<longleftrightarrow> x < 0 \<and> y < 0\<close> for x y :: int
  by (fact and_negative_int_iff)

lemma int_and_ge0 [simp]: 
  \<open>x AND y \<ge> 0 \<longleftrightarrow> x \<ge> 0 \<or> y \<ge> 0\<close> for x y :: int
  by (fact and_nonnegative_int_iff)
  
lemma int_and_1: fixes x :: int shows "x AND 1 = x mod 2"
  by (fact and_one_eq)

lemma int_1_and: fixes x :: int shows "1 AND x = x mod 2"
  by (fact one_and_eq)

lemma int_or_lt0 [simp]: 
  \<open>x OR y < 0 \<longleftrightarrow> x < 0 \<or> y < 0\<close> for x y :: int
  by (fact or_negative_int_iff)

lemma int_or_ge0 [simp]:
  \<open>x OR y \<ge> 0 \<longleftrightarrow> x \<ge> 0 \<and> y \<ge> 0\<close> for x y :: int
  by (fact or_nonnegative_int_iff)
  
lemma int_xor_lt0 [simp]:
  \<open>x XOR y < 0 \<longleftrightarrow> (x < 0) \<noteq> (y < 0)\<close> for x y :: int
  by (fact xor_negative_int_iff)

lemma int_xor_ge0 [simp]:
  \<open>x XOR y \<ge> 0 \<longleftrightarrow> (x \<ge> 0 \<longleftrightarrow> y \<ge> 0)\<close> for x y :: int
  by (fact xor_nonnegative_int_iff)
  
lemma even_conv_AND:
  \<open>even i \<longleftrightarrow> i AND 1 = 0\<close> for i :: int
  by (simp add: and_one_eq mod2_eq_if)

lemma bin_last_conv_AND:
  "bin_last i \<longleftrightarrow> i AND 1 \<noteq> 0"
  by (simp add: and_one_eq mod2_eq_if)

lemma bitval_bin_last:
  "of_bool (bin_last i) = i AND 1"
  by (simp add: and_one_eq mod2_eq_if)

lemma bin_sign_and:
  "bin_sign (i AND j) = - (bin_sign i * bin_sign j)"
by(simp add: bin_sign_def)

lemma int_not_neg_numeral: "NOT (- numeral n) = (Num.sub n num.One :: int)"
by(simp add: int_not_def)

lemma int_neg_numeral_pOne_conv_not: "- numeral (n + num.One) = (NOT (numeral n) :: int)"
by(simp add: int_not_def)


subsection \<open>Setting and clearing bits\<close>

lemma int_shiftl_BIT: fixes x :: int
  shows int_shiftl0 [simp]: "x << 0 = x"
  and int_shiftl_Suc [simp]: "x << Suc n = 2 * (x << n)"
  by (auto simp add: shiftl_int_def)

lemma int_0_shiftl [simp]: "0 << n = (0 :: int)"
by(induct n) simp_all

lemma bin_last_shiftl: "bin_last (x << n) \<longleftrightarrow> n = 0 \<and> bin_last x"
by(cases n)(simp_all)

lemma bin_rest_shiftl: "bin_rest (x << n) = (if n > 0 then x << (n - 1) else bin_rest x)"
by(cases n)(simp_all)

lemma bin_nth_shiftl [simp]: "bin_nth (x << n) m \<longleftrightarrow> n \<le> m \<and> bin_nth x (m - n)"
  by (simp add: bit_push_bit_iff_int shiftl_eq_push_bit)

lemma bin_last_shiftr: "odd (x >> n) \<longleftrightarrow> x !! n" for x :: int
  by (simp add: shiftr_eq_drop_bit bit_iff_odd_drop_bit)

lemma bin_rest_shiftr [simp]: "bin_rest (x >> n) = x >> Suc n"
  by (simp add: bit_eq_iff shiftr_eq_drop_bit drop_bit_Suc bit_drop_bit_eq drop_bit_half)

lemma bin_nth_shiftr [simp]: "bin_nth (x >> n) m = bin_nth x (n + m)"
  by (simp add: shiftr_eq_drop_bit bit_drop_bit_eq)

lemma bin_nth_conv_AND:
  fixes x :: int shows 
  "bin_nth x n \<longleftrightarrow> x AND (1 << n) \<noteq> 0"
  by (simp add: bit_eq_iff)
    (auto simp add: shiftl_eq_push_bit bit_and_iff bit_push_bit_iff bit_exp_iff)

lemma int_shiftl_numeral [simp]: 
  "(numeral w :: int) << numeral w' = numeral (num.Bit0 w) << pred_numeral w'"
  "(- numeral w :: int) << numeral w' = - numeral (num.Bit0 w) << pred_numeral w'"
by(simp_all add: numeral_eq_Suc shiftl_int_def)
  (metis add_One mult_inc semiring_norm(11) semiring_norm(13) semiring_norm(2) semiring_norm(6) semiring_norm(87))+

lemma int_shiftl_One_numeral [simp]:
  "(1 :: int) << numeral w = 2 << pred_numeral w"
  using int_shiftl_numeral [of Num.One w] by simp

lemma shiftl_ge_0 [simp]: fixes i :: int shows "i << n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
by(induct n) simp_all

lemma shiftl_lt_0 [simp]: fixes i :: int shows "i << n < 0 \<longleftrightarrow> i < 0"
by (metis not_le shiftl_ge_0)

lemma int_shiftl_test_bit: "(n << i :: int) !! m \<longleftrightarrow> m \<ge> i \<and> n !! (m - i)"
  by simp

lemma int_0shiftr [simp]: "(0 :: int) >> x = 0"
by(simp add: shiftr_int_def)

lemma int_minus1_shiftr [simp]: "(-1 :: int) >> x = -1"
by(simp add: shiftr_int_def div_eq_minus1)

lemma int_shiftr_ge_0 [simp]: fixes i :: int shows "i >> n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
  by (simp add: shiftr_eq_drop_bit)

lemma int_shiftr_lt_0 [simp]: fixes i :: int shows "i >> n < 0 \<longleftrightarrow> i < 0"
by (metis int_shiftr_ge_0 not_less)

lemma int_shiftr_numeral [simp]:
  "(1 :: int) >> numeral w' = 0"
  "(numeral num.One :: int) >> numeral w' = 0"
  "(numeral (num.Bit0 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(numeral (num.Bit1 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(- numeral (num.Bit0 w) :: int) >> numeral w' = - numeral w >> pred_numeral w'"
  "(- numeral (num.Bit1 w) :: int) >> numeral w' = - numeral (Num.inc w) >> pred_numeral w'"
  by (simp_all add: shiftr_eq_drop_bit numeral_eq_Suc add_One drop_bit_Suc)

lemma int_shiftr_numeral_Suc0 [simp]:
  "(1 :: int) >> Suc 0 = 0"
  "(numeral num.One :: int) >> Suc 0 = 0"
  "(numeral (num.Bit0 w) :: int) >> Suc 0 = numeral w"
  "(numeral (num.Bit1 w) :: int) >> Suc 0 = numeral w"
  "(- numeral (num.Bit0 w) :: int) >> Suc 0 = - numeral w"
  "(- numeral (num.Bit1 w) :: int) >> Suc 0 = - numeral (Num.inc w)"
  by (simp_all add: shiftr_eq_drop_bit drop_bit_Suc add_One)

lemma bin_nth_minus_p2:
  assumes sign: "bin_sign x = 0"
  and y: "y = 1 << n"
  and m: "m < n"
  and x: "x < y"
  shows "bin_nth (x - y) m = bin_nth x m"
proof -
  from sign y x have \<open>x \<ge> 0\<close> and \<open>y = 2 ^ n\<close> and \<open>x < 2 ^ n\<close>
    by (simp_all add: bin_sign_def shiftl_eq_push_bit push_bit_eq_mult split: if_splits)
  from \<open>0 \<le> x\<close> \<open>x < 2 ^ n\<close> \<open>m < n\<close> have \<open>bit x m \<longleftrightarrow> bit (x - 2 ^ n) m\<close>
  proof (induction m arbitrary: x n)
    case 0
    then show ?case
      by simp
  next
    case (Suc m)
    moreover define q where \<open>q = n - 1\<close>
    ultimately have n: \<open>n = Suc q\<close>
      by simp
    have \<open>(x - 2 ^ Suc q) div 2 = x div 2 - 2 ^ q\<close>
      by simp
    moreover from Suc.IH [of \<open>x div 2\<close> q] Suc.prems
    have \<open>bit (x div 2) m \<longleftrightarrow> bit (x div 2 - 2 ^ q) m\<close>
      by (simp add: n)
    ultimately show ?case
      by (simp add: bit_Suc n)
  qed
  with \<open>y = 2 ^ n\<close> show ?thesis
    by simp
qed

lemma bin_clr_conv_NAND:
  "bin_sc n False i = i AND NOT (1 << n)"
  by (induct n arbitrary: i) (rule bin_rl_eqI; simp)+

lemma bin_set_conv_OR:
  "bin_sc n True i = i OR (1 << n)"
  by (induct n arbitrary: i) (rule bin_rl_eqI; simp)+


subsection \<open>Semantic interpretation of \<^typ>\<open>bool list\<close> as \<^typ>\<open>int\<close>\<close>

lemma bin_bl_bin': "bl_to_bin (bin_to_bl_aux n w bs) = bl_to_bin_aux bs (bintrunc n w)"
  by (induct n arbitrary: w bs) (auto simp: bl_to_bin_def take_bit_Suc ac_simps mod_2_eq_odd)

lemma bin_bl_bin [simp]: "bl_to_bin (bin_to_bl n w) = bintrunc n w"
  by (auto simp: bin_to_bl_def bin_bl_bin')

lemma bl_to_bin_rep_F: "bl_to_bin (replicate n False @ bl) = bl_to_bin bl"
  by (simp add: bin_to_bl_zero_aux [symmetric] bin_bl_bin') (simp add: bl_to_bin_def)

lemma bin_to_bl_trunc [simp]: "n \<le> m \<Longrightarrow> bin_to_bl n (bintrunc m w) = bin_to_bl n w"
  by (auto intro: bl_to_bin_inj)

lemma bin_to_bl_aux_bintr:
  "bin_to_bl_aux n (bintrunc m bin) bl =
    replicate (n - m) False @ bin_to_bl_aux (min n m) bin bl"
  apply (induct n arbitrary: m bin bl)
   apply clarsimp
  apply clarsimp
  apply (case_tac "m")
   apply (clarsimp simp: bin_to_bl_zero_aux)
   apply (erule thin_rl)
   apply (induct_tac n)
    apply (auto simp add: take_bit_Suc)
  done

lemma bin_to_bl_bintr:
  "bin_to_bl n (bintrunc m bin) = replicate (n - m) False @ bin_to_bl (min n m) bin"
  unfolding bin_to_bl_def by (rule bin_to_bl_aux_bintr)

lemma bl_to_bin_rep_False: "bl_to_bin (replicate n False) = 0"
  by (induct n) auto

lemma len_bin_to_bl_aux: "length (bin_to_bl_aux n w bs) = n + length bs"
  by (fact size_bin_to_bl_aux)

lemma len_bin_to_bl: "length (bin_to_bl n w) = n"
  by (fact size_bin_to_bl) (* FIXME: duplicate *)

lemma sign_bl_bin': "bin_sign (bl_to_bin_aux bs w) = bin_sign w"
  by (induction bs arbitrary: w) (simp_all add: bin_sign_def)

lemma sign_bl_bin: "bin_sign (bl_to_bin bs) = 0"
  by (simp add: bl_to_bin_def sign_bl_bin')

lemma bl_sbin_sign_aux: "hd (bin_to_bl_aux (Suc n) w bs) = (bin_sign (sbintrunc n w) = -1)"
  by (induction n arbitrary: w bs) (auto simp add: bin_sign_def even_iff_mod_2_eq_zero bit_Suc)

lemma bl_sbin_sign: "hd (bin_to_bl (Suc n) w) = (bin_sign (sbintrunc n w) = -1)"
  unfolding bin_to_bl_def by (rule bl_sbin_sign_aux)

lemma bin_nth_of_bl_aux:
  "bin_nth (bl_to_bin_aux bl w) n =
    (n < size bl \<and> rev bl ! n \<or> n \<ge> length bl \<and> bin_nth w (n - size bl))"
  apply (induction bl arbitrary: w)
   apply simp_all
  apply safe
                      apply (simp_all add: not_le nth_append bit_double_iff even_bit_succ_iff split: if_splits)
  done

lemma bin_nth_of_bl: "bin_nth (bl_to_bin bl) n = (n < length bl \<and> rev bl ! n)"
  by (simp add: bl_to_bin_def bin_nth_of_bl_aux)

lemma bin_nth_bl: "n < m \<Longrightarrow> bin_nth w n = nth (rev (bin_to_bl m w)) n"
  apply (induct n arbitrary: m w)
   apply clarsimp
   apply (case_tac m, clarsimp)
   apply (clarsimp simp: bin_to_bl_def)
   apply (simp add: bin_to_bl_aux_alt)
  apply (case_tac m, clarsimp)
  apply (clarsimp simp: bin_to_bl_def)
  apply (simp add: bin_to_bl_aux_alt bit_Suc)
  done

lemma nth_bin_to_bl_aux:
  "n < m + length bl \<Longrightarrow> (bin_to_bl_aux m w bl) ! n =
    (if n < m then bit w (m - 1 - n) else bl ! (n - m))"
  apply (induction bl arbitrary: w)
   apply simp_all
   apply (simp add: bin_nth_bl [of \<open>m - Suc n\<close> m] rev_nth flip: bin_to_bl_def)
   apply (metis One_nat_def Suc_pred add_diff_cancel_left'
     add_diff_cancel_right' bin_to_bl_aux_alt bin_to_bl_def
     diff_Suc_Suc diff_is_0_eq diff_zero less_Suc_eq_0_disj
     less_antisym less_imp_Suc_add list.size(3) nat_less_le nth_append size_bin_to_bl_aux)
  done

lemma nth_bin_to_bl: "n < m \<Longrightarrow> (bin_to_bl m w) ! n = bin_nth w (m - Suc n)"
  by (simp add: bin_to_bl_def nth_bin_to_bl_aux)

lemma bl_to_bin_lt2p_aux: "bl_to_bin_aux bs w < (w + 1) * (2 ^ length bs)"
proof (induction bs arbitrary: w)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  from Cons.IH [of \<open>1 + 2 * w\<close>] Cons.IH [of \<open>2 * w\<close>]
  show ?case
    apply (auto simp add: algebra_simps)
    apply (subst mult_2 [of \<open>2 ^ length bs\<close>])
    apply (simp only: add.assoc)
    apply (rule pos_add_strict)
     apply simp_all
    done
qed

lemma bl_to_bin_lt2p_drop: "bl_to_bin bs < 2 ^ length (dropWhile Not bs)"
proof (induct bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  with bl_to_bin_lt2p_aux[where w=1] show ?case
    by (simp add: bl_to_bin_def)
qed

lemma bl_to_bin_lt2p: "bl_to_bin bs < 2 ^ length bs"
  by (metis bin_bl_bin bintr_lt2p bl_bin_bl)

lemma bl_to_bin_ge2p_aux: "bl_to_bin_aux bs w \<ge> w * (2 ^ length bs)"
proof (induction bs arbitrary: w)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  from Cons.IH [of \<open>1 + 2 * w\<close>] Cons.IH [of \<open>2 * w\<close>]
  show ?case
    apply (auto simp add: algebra_simps)
    apply (rule add_le_imp_le_left [of \<open>2 ^ length bs\<close>])
    apply (rule add_increasing)
    apply simp_all
    done
qed

lemma bl_to_bin_ge0: "bl_to_bin bs \<ge> 0"
  apply (unfold bl_to_bin_def)
  apply (rule xtrans(4))
   apply (rule bl_to_bin_ge2p_aux)
  apply simp
  done

lemma butlast_rest_bin: "butlast (bin_to_bl n w) = bin_to_bl (n - 1) (bin_rest w)"
  apply (unfold bin_to_bl_def)
  apply (cases n, clarsimp)
  apply clarsimp
  apply (auto simp add: bin_to_bl_aux_alt)
  done

lemma butlast_bin_rest: "butlast bl = bin_to_bl (length bl - Suc 0) (bin_rest (bl_to_bin bl))"
  using butlast_rest_bin [where w="bl_to_bin bl" and n="length bl"] by simp

lemma butlast_rest_bl2bin_aux:
  "bl \<noteq> [] \<Longrightarrow> bl_to_bin_aux (butlast bl) w = bin_rest (bl_to_bin_aux bl w)"
  by (induct bl arbitrary: w) auto

lemma butlast_rest_bl2bin: "bl_to_bin (butlast bl) = bin_rest (bl_to_bin bl)"
  by (cases bl) (auto simp: bl_to_bin_def butlast_rest_bl2bin_aux)

lemma trunc_bl2bin_aux:
  "bintrunc m (bl_to_bin_aux bl w) =
    bl_to_bin_aux (drop (length bl - m) bl) (bintrunc (m - length bl) w)"
proof (induct bl arbitrary: w)
  case Nil
  show ?case by simp
next
  case (Cons b bl)
  show ?case
  proof (cases "m - length bl")
    case 0
    then have "Suc (length bl) - m = Suc (length bl - m)" by simp
    with Cons show ?thesis by simp
  next
    case (Suc n)
    then have "m - Suc (length bl) = n" by simp
    with Cons Suc show ?thesis by (simp add: take_bit_Suc ac_simps)
  qed
qed

lemma trunc_bl2bin: "bintrunc m (bl_to_bin bl) = bl_to_bin (drop (length bl - m) bl)"
  by (simp add: bl_to_bin_def trunc_bl2bin_aux)

lemma trunc_bl2bin_len [simp]: "bintrunc (length bl) (bl_to_bin bl) = bl_to_bin bl"
  by (simp add: trunc_bl2bin)

lemma bl2bin_drop: "bl_to_bin (drop k bl) = bintrunc (length bl - k) (bl_to_bin bl)"
  apply (rule trans)
   prefer 2
   apply (rule trunc_bl2bin [symmetric])
  apply (cases "k \<le> length bl")
   apply auto
  done

lemma take_rest_power_bin: "m \<le> n \<Longrightarrow> take m (bin_to_bl n w) = bin_to_bl m ((bin_rest ^^ (n - m)) w)"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp add: nth_bin_to_bl nth_rest_power_bin)
  done

lemma last_bin_last': "size xs > 0 \<Longrightarrow> last xs \<longleftrightarrow> bin_last (bl_to_bin_aux xs w)"
  by (induct xs arbitrary: w) auto

lemma last_bin_last: "size xs > 0 \<Longrightarrow> last xs \<longleftrightarrow> bin_last (bl_to_bin xs)"
  unfolding bl_to_bin_def by (erule last_bin_last')

lemma bin_last_last: "bin_last w \<longleftrightarrow> last (bin_to_bl (Suc n) w)"
  by (simp add: bin_to_bl_def) (auto simp: bin_to_bl_aux_alt)

lemma drop_bin2bl_aux:
  "drop m (bin_to_bl_aux n bin bs) =
    bin_to_bl_aux (n - m) bin (drop (m - n) bs)"
  apply (induction n arbitrary: m bin bs)
   apply auto
  apply (case_tac "m \<le> n")
   apply (auto simp add: not_le Suc_diff_le)
  apply (case_tac "m - n")
   apply auto
  apply (use Suc_diff_Suc in fastforce)
  done

lemma drop_bin2bl: "drop m (bin_to_bl n bin) = bin_to_bl (n - m) bin"
  by (simp add: bin_to_bl_def drop_bin2bl_aux)

lemma take_bin2bl_lem1: "take m (bin_to_bl_aux m w bs) = bin_to_bl m w"
  apply (induct m arbitrary: w bs)
   apply clarsimp
  apply clarsimp
  apply (simp add: bin_to_bl_aux_alt)
  apply (simp add: bin_to_bl_def)
  apply (simp add: bin_to_bl_aux_alt)
  done

lemma take_bin2bl_lem: "take m (bin_to_bl_aux (m + n) w bs) = take m (bin_to_bl (m + n) w)"
  by (induct n arbitrary: w bs) (simp_all (no_asm) add: bin_to_bl_def take_bin2bl_lem1, simp)

lemma bin_split_take: "bin_split n c = (a, b) \<Longrightarrow> bin_to_bl m a = take m (bin_to_bl (m + n) c)"
  apply (induct n arbitrary: b c)
   apply clarsimp
  apply (clarsimp simp: Let_def split: prod.split_asm)
  apply (simp add: bin_to_bl_def)
  apply (simp add: take_bin2bl_lem drop_bit_Suc)
  done

lemma bin_to_bl_drop_bit:
  "k = m + n \<Longrightarrow> bin_to_bl m (drop_bit n c) = take m (bin_to_bl k c)"
  using bin_split_take by simp

lemma bin_split_take1:
  "k = m + n \<Longrightarrow> bin_split n c = (a, b) \<Longrightarrow> bin_to_bl m a = take m (bin_to_bl k c)"
  using bin_split_take by simp

lemma bl_bin_bl_rep_drop:
  "bin_to_bl n (bl_to_bin bl) =
    replicate (n - length bl) False @ drop (length bl - n) bl"
  by (simp add: bl_to_bin_inj bl_to_bin_rep_F trunc_bl2bin)

lemma bl_to_bin_aux_cat:
  "bl_to_bin_aux bs (bin_cat w nv v) =
    bin_cat w (nv + length bs) (bl_to_bin_aux bs v)"
  by (rule bit_eqI)
    (auto simp add: bin_nth_of_bl_aux bin_nth_cat algebra_simps)

lemma bin_to_bl_aux_cat:
  "bin_to_bl_aux (nv + nw) (bin_cat v nw w) bs =
    bin_to_bl_aux nv v (bin_to_bl_aux nw w bs)"
  by (induction nw arbitrary: w bs) (simp_all add: concat_bit_Suc)

lemma bl_to_bin_aux_alt: "bl_to_bin_aux bs w = bin_cat w (length bs) (bl_to_bin bs)"
  using bl_to_bin_aux_cat [where nv = "0" and v = "0"]
  by (simp add: bl_to_bin_def [symmetric])

lemma bin_to_bl_cat:
  "bin_to_bl (nv + nw) (bin_cat v nw w) =
    bin_to_bl_aux nv v (bin_to_bl nw w)"
  by (simp add: bin_to_bl_def bin_to_bl_aux_cat)

lemmas bl_to_bin_aux_app_cat =
  trans [OF bl_to_bin_aux_append bl_to_bin_aux_alt]

lemmas bin_to_bl_aux_cat_app =
  trans [OF bin_to_bl_aux_cat bin_to_bl_aux_alt]

lemma bl_to_bin_app_cat:
  "bl_to_bin (bsa @ bs) = bin_cat (bl_to_bin bsa) (length bs) (bl_to_bin bs)"
  by (simp only: bl_to_bin_aux_app_cat bl_to_bin_def)

lemma bin_to_bl_cat_app:
  "bin_to_bl (n + nw) (bin_cat w nw wa) = bin_to_bl n w @ bin_to_bl nw wa"
  by (simp only: bin_to_bl_def bin_to_bl_aux_cat_app)

text \<open>\<open>bl_to_bin_app_cat_alt\<close> and \<open>bl_to_bin_app_cat\<close> are easily interderivable.\<close>
lemma bl_to_bin_app_cat_alt: "bin_cat (bl_to_bin cs) n w = bl_to_bin (cs @ bin_to_bl n w)"
  by (simp add: bl_to_bin_app_cat)

lemma mask_lem: "(bl_to_bin (True # replicate n False)) = bl_to_bin (replicate n True) + 1"
  apply (unfold bl_to_bin_def)
  apply (induct n)
   apply simp
  apply (simp only: Suc_eq_plus1 replicate_add append_Cons [symmetric] bl_to_bin_aux_append)
  apply simp
  done

lemma bin_exhaust:
  "(\<And>x b. bin = of_bool b + 2 * x \<Longrightarrow> Q) \<Longrightarrow> Q" for bin :: int
  apply (cases \<open>even bin\<close>)
   apply (auto elim!: evenE oddE)
   apply fastforce
  apply fastforce
  done

primrec rbl_succ :: "bool list \<Rightarrow> bool list"
  where
    Nil: "rbl_succ Nil = Nil"
  | Cons: "rbl_succ (x # xs) = (if x then False # rbl_succ xs else True # xs)"

primrec rbl_pred :: "bool list \<Rightarrow> bool list"
  where
    Nil: "rbl_pred Nil = Nil"
  | Cons: "rbl_pred (x # xs) = (if x then False # xs else True # rbl_pred xs)"

primrec rbl_add :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
  where \<comment> \<open>result is length of first arg, second arg may be longer\<close>
    Nil: "rbl_add Nil x = Nil"
  | Cons: "rbl_add (y # ys) x =
      (let ws = rbl_add ys (tl x)
       in (y \<noteq> hd x) # (if hd x \<and> y then rbl_succ ws else ws))"

primrec rbl_mult :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
  where \<comment> \<open>result is length of first arg, second arg may be longer\<close>
    Nil: "rbl_mult Nil x = Nil"
  | Cons: "rbl_mult (y # ys) x =
      (let ws = False # rbl_mult ys x
       in if y then rbl_add ws x else ws)"

lemma size_rbl_pred: "length (rbl_pred bl) = length bl"
  by (induct bl) auto

lemma size_rbl_succ: "length (rbl_succ bl) = length bl"
  by (induct bl) auto

lemma size_rbl_add: "length (rbl_add bl cl) = length bl"
  by (induct bl arbitrary: cl) (auto simp: Let_def size_rbl_succ)

lemma size_rbl_mult: "length (rbl_mult bl cl) = length bl"
  by (induct bl arbitrary: cl) (auto simp add: Let_def size_rbl_add)

lemmas rbl_sizes [simp] =
  size_rbl_pred size_rbl_succ size_rbl_add size_rbl_mult

lemmas rbl_Nils =
  rbl_pred.Nil rbl_succ.Nil rbl_add.Nil rbl_mult.Nil

lemma rbl_add_app2: "length blb \<ge> length bla \<Longrightarrow> rbl_add bla (blb @ blc) = rbl_add bla blb"
  apply (induct bla arbitrary: blb)
   apply simp
  apply clarsimp
  apply (case_tac blb, clarsimp)
  apply (clarsimp simp: Let_def)
  done

lemma rbl_add_take2:
  "length blb \<ge> length bla \<Longrightarrow> rbl_add bla (take (length bla) blb) = rbl_add bla blb"
  apply (induct bla arbitrary: blb)
   apply simp
  apply clarsimp
  apply (case_tac blb, clarsimp)
  apply (clarsimp simp: Let_def)
  done

lemma rbl_mult_app2: "length blb \<ge> length bla \<Longrightarrow> rbl_mult bla (blb @ blc) = rbl_mult bla blb"
  apply (induct bla arbitrary: blb)
   apply simp
  apply clarsimp
  apply (case_tac blb, clarsimp)
  apply (clarsimp simp: Let_def rbl_add_app2)
  done

lemma rbl_mult_take2:
  "length blb \<ge> length bla \<Longrightarrow> rbl_mult bla (take (length bla) blb) = rbl_mult bla blb"
  apply (rule trans)
   apply (rule rbl_mult_app2 [symmetric])
   apply simp
  apply (rule_tac f = "rbl_mult bla" in arg_cong)
  apply (rule append_take_drop_id)
  done

lemma rbl_add_split:
  "P (rbl_add (y # ys) (x # xs)) =
    (\<forall>ws. length ws = length ys \<longrightarrow> ws = rbl_add ys xs \<longrightarrow>
      (y \<longrightarrow> ((x \<longrightarrow> P (False # rbl_succ ws)) \<and> (\<not> x \<longrightarrow> P (True # ws)))) \<and>
      (\<not> y \<longrightarrow> P (x # ws)))"
  by (cases y) (auto simp: Let_def)

lemma rbl_mult_split:
  "P (rbl_mult (y # ys) xs) =
    (\<forall>ws. length ws = Suc (length ys) \<longrightarrow> ws = False # rbl_mult ys xs \<longrightarrow>
      (y \<longrightarrow> P (rbl_add ws xs)) \<and> (\<not> y \<longrightarrow> P ws))"
  by (auto simp: Let_def)

lemma rbl_pred: "rbl_pred (rev (bin_to_bl n bin)) = rev (bin_to_bl n (bin - 1))"
proof (unfold bin_to_bl_def, induction n arbitrary: bin)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  obtain b k where \<open>bin = of_bool b + 2 * k\<close>
    using bin_exhaust by blast
  moreover have \<open>(2 * k - 1) div 2 = k - 1\<close>
    using even_succ_div_2 [of \<open>2 * (k - 1)\<close>] 
    by simp
  ultimately show ?case
    using Suc [of \<open>bin div 2\<close>]
    by simp (simp add: bin_to_bl_aux_alt)
qed

lemma rbl_succ: "rbl_succ (rev (bin_to_bl n bin)) = rev (bin_to_bl n (bin + 1))"
  apply (unfold bin_to_bl_def)
  apply (induction n arbitrary: bin)
   apply simp_all
  apply (case_tac bin rule: bin_exhaust)
  apply simp
  apply (simp add: bin_to_bl_aux_alt ac_simps)
  done

lemma rbl_add:
  "\<And>bina binb. rbl_add (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) =
    rev (bin_to_bl n (bina + binb))"
  apply (unfold bin_to_bl_def)
  apply (induct n)
   apply simp
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac binb rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] "ba")
     apply (auto simp: rbl_succ bin_to_bl_aux_alt Let_def ac_simps)
  done

lemma rbl_add_long:
  "m \<ge> n \<Longrightarrow> rbl_add (rev (bin_to_bl n bina)) (rev (bin_to_bl m binb)) =
    rev (bin_to_bl n (bina + binb))"
  apply (rule box_equals [OF _ rbl_add_take2 rbl_add])
   apply (rule_tac f = "rbl_add (rev (bin_to_bl n bina))" in arg_cong)
   apply (rule rev_swap [THEN iffD1])
   apply (simp add: rev_take drop_bin2bl)
  apply simp
  done

lemma rbl_mult_gt1:
  "m \<ge> length bl \<Longrightarrow>
    rbl_mult bl (rev (bin_to_bl m binb)) =
    rbl_mult bl (rev (bin_to_bl (length bl) binb))"
  apply (rule trans)
   apply (rule rbl_mult_take2 [symmetric])
   apply simp_all
  apply (rule_tac f = "rbl_mult bl" in arg_cong)
  apply (rule rev_swap [THEN iffD1])
  apply (simp add: rev_take drop_bin2bl)
  done

lemma rbl_mult_gt:
  "m > n \<Longrightarrow>
    rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl m binb)) =
    rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb))"
  by (auto intro: trans [OF rbl_mult_gt1])

lemmas rbl_mult_Suc = lessI [THEN rbl_mult_gt]

lemma rbbl_Cons: "b # rev (bin_to_bl n x) = rev (bin_to_bl (Suc n) (of_bool b + 2 * x))"
  by (simp add: bin_to_bl_def) (simp add: bin_to_bl_aux_alt)

lemma rbl_mult:
  "rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) =
    rev (bin_to_bl n (bina * binb))"
  apply (induct n arbitrary: bina binb)
   apply simp_all
  apply (unfold bin_to_bl_def)
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac binb rule: bin_exhaust)
  apply simp
  apply (simp add: bin_to_bl_aux_alt)
  apply (simp add: rbbl_Cons rbl_mult_Suc rbl_add algebra_simps)
  done

lemma sclem: "size (concat (map (bin_to_bl n) xs)) = length xs * n"
  by (induct xs) auto

lemma bin_cat_foldl_lem:
  "foldl (\<lambda>u. bin_cat u n) x xs =
    bin_cat x (size xs * n) (foldl (\<lambda>u. bin_cat u n) y xs)"
  apply (induct xs arbitrary: x)
   apply simp
  apply (simp (no_asm))
  apply (frule asm_rl)
  apply (drule meta_spec)
  apply (erule trans)
  apply (drule_tac x = "bin_cat y n a" in meta_spec)
  apply (simp add: bin_cat_assoc_sym min.absorb2)
  done

lemma bin_rcat_bl: "bin_rcat n wl = bl_to_bin (concat (map (bin_to_bl n) wl))"
  apply (unfold bin_rcat_def)
  apply (rule sym)
  apply (induct wl)
   apply (auto simp add: bl_to_bin_append)
  apply (simp add: bl_to_bin_aux_alt sclem)
  apply (simp add: bin_cat_foldl_lem [symmetric])
  done

lemma bin_last_bl_to_bin: "bin_last (bl_to_bin bs) \<longleftrightarrow> bs \<noteq> [] \<and> last bs"
by(cases "bs = []")(auto simp add: bl_to_bin_def last_bin_last'[where w=0])

lemma bin_rest_bl_to_bin: "bin_rest (bl_to_bin bs) = bl_to_bin (butlast bs)"
by(cases "bs = []")(simp_all add: bl_to_bin_def butlast_rest_bl2bin_aux)

lemma bl_xor_aux_bin:
  "map2 (\<lambda>x y. x \<noteq> y) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v XOR w) (map2 (\<lambda>x y. x \<noteq> y) bs cs)"
  apply (induction n arbitrary: v w bs cs)
   apply auto
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  done

lemma bl_or_aux_bin:
  "map2 (\<or>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v OR w) (map2 (\<or>) bs cs)"
  by (induct n arbitrary: v w bs cs) simp_all

lemma bl_and_aux_bin:
  "map2 (\<and>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v AND w) (map2 (\<and>) bs cs)"
  by (induction n arbitrary: v w bs cs) simp_all

lemma bl_not_aux_bin: "map Not (bin_to_bl_aux n w cs) = bin_to_bl_aux n (NOT w) (map Not cs)"
  by (induct n arbitrary: w cs) auto

lemma bl_not_bin: "map Not (bin_to_bl n w) = bin_to_bl n (NOT w)"
  by (simp add: bin_to_bl_def bl_not_aux_bin)

lemma bl_and_bin: "map2 (\<and>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v AND w)"
  by (simp add: bin_to_bl_def bl_and_aux_bin)

lemma bl_or_bin: "map2 (\<or>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v OR w)"
  by (simp add: bin_to_bl_def bl_or_aux_bin)

lemma bl_xor_bin: "map2 (\<noteq>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v XOR w)"
  using bl_xor_aux_bin by (simp add: bin_to_bl_def)

end
