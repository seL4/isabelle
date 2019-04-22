(*  Title:      HOL/Word/Bits_Int.thy
    Author:     Jeremy Dawson and Gerwin Klein, NICTA

Definitions and basic theorems for bit-wise logical operations
for integers expressed using Pls, Min, BIT,
and converting them to and from lists of bools.
*)

section \<open>Bitwise Operations on integers\<close>

theory Bits_Int
  imports Bits Misc_Auxiliary
begin

subsection \<open>Implicit bit representation of \<^typ>\<open>int\<close>\<close>

definition Bit :: "int \<Rightarrow> bool \<Rightarrow> int"  (infixl "BIT" 90)
  where "k BIT b = (if b then 1 else 0) + k + k"

lemma Bit_B0: "k BIT False = k + k"
   by (simp add: Bit_def)

lemma Bit_B1: "k BIT True = k + k + 1"
   by (simp add: Bit_def)

lemma Bit_B0_2t: "k BIT False = 2 * k"
  by (rule trans, rule Bit_B0) simp

lemma Bit_B1_2t: "k BIT True = 2 * k + 1"
  by (rule trans, rule Bit_B1) simp

lemma uminus_Bit_eq:
  "- k BIT b = (- k - of_bool b) BIT b"
  by (cases b) (simp_all add: Bit_def)

lemma power_BIT: "2 ^ Suc n - 1 = (2 ^ n - 1) BIT True"
  by (simp add: Bit_B1)

definition bin_last :: "int \<Rightarrow> bool"
  where "bin_last w \<longleftrightarrow> w mod 2 = 1"

lemma bin_last_odd: "bin_last = odd"
  by (rule ext) (simp add: bin_last_def even_iff_mod_2_eq_zero)

definition bin_rest :: "int \<Rightarrow> int"
  where "bin_rest w = w div 2"

lemma bin_rl_simp [simp]: "bin_rest w BIT bin_last w = w"
  unfolding bin_rest_def bin_last_def Bit_def
  by (cases "w mod 2 = 0") (use div_mult_mod_eq [of w 2] in simp_all)

lemma bin_rest_BIT [simp]: "bin_rest (x BIT b) = x"
  unfolding bin_rest_def Bit_def
  by (cases b) simp_all

lemma bin_last_BIT [simp]: "bin_last (x BIT b) = b"
  unfolding bin_last_def Bit_def
  by (cases b) simp_all

lemma BIT_eq_iff [iff]: "u BIT b = v BIT c \<longleftrightarrow> u = v \<and> b = c"
  by (auto simp: Bit_def) arith+

lemma BIT_bin_simps [simp]:
  "numeral k BIT False = numeral (Num.Bit0 k)"
  "numeral k BIT True = numeral (Num.Bit1 k)"
  "(- numeral k) BIT False = - numeral (Num.Bit0 k)"
  "(- numeral k) BIT True = - numeral (Num.BitM k)"
  unfolding numeral.simps numeral_BitM
  by (simp_all add: Bit_def del: arith_simps add_numeral_special diff_numeral_special)

lemma BIT_special_simps [simp]:
  shows "0 BIT False = 0"
    and "0 BIT True = 1"
    and "1 BIT False = 2"
    and "1 BIT True = 3"
    and "(- 1) BIT False = - 2"
    and "(- 1) BIT True = - 1"
  by (simp_all add: Bit_def)

lemma Bit_eq_0_iff: "w BIT b = 0 \<longleftrightarrow> w = 0 \<and> \<not> b"
  by (auto simp: Bit_def) arith

lemma Bit_eq_m1_iff: "w BIT b = -1 \<longleftrightarrow> w = -1 \<and> b"
  by (auto simp: Bit_def) arith

lemma BitM_inc: "Num.BitM (Num.inc w) = Num.Bit1 w"
  by (induct w) simp_all

lemma expand_BIT:
  "numeral (Num.Bit0 w) = numeral w BIT False"
  "numeral (Num.Bit1 w) = numeral w BIT True"
  "- numeral (Num.Bit0 w) = (- numeral w) BIT False"
  "- numeral (Num.Bit1 w) = (- numeral (w + Num.One)) BIT True"
  by (simp_all add: add_One BitM_inc)

lemma bin_last_numeral_simps [simp]:
  "\<not> bin_last 0"
  "bin_last 1"
  "bin_last (- 1)"
  "bin_last Numeral1"
  "\<not> bin_last (numeral (Num.Bit0 w))"
  "bin_last (numeral (Num.Bit1 w))"
  "\<not> bin_last (- numeral (Num.Bit0 w))"
  "bin_last (- numeral (Num.Bit1 w))"
  by (simp_all add: bin_last_def zmod_zminus1_eq_if) (auto simp add: divmod_def)

lemma bin_rest_numeral_simps [simp]:
  "bin_rest 0 = 0"
  "bin_rest 1 = 0"
  "bin_rest (- 1) = - 1"
  "bin_rest Numeral1 = 0"
  "bin_rest (numeral (Num.Bit0 w)) = numeral w"
  "bin_rest (numeral (Num.Bit1 w)) = numeral w"
  "bin_rest (- numeral (Num.Bit0 w)) = - numeral w"
  "bin_rest (- numeral (Num.Bit1 w)) = - numeral (w + Num.One)"
  by (simp_all add: bin_rest_def zdiv_zminus1_eq_if) (auto simp add: divmod_def)

lemma less_Bits: "v BIT b < w BIT c \<longleftrightarrow> v < w \<or> v \<le> w \<and> \<not> b \<and> c"
  by (auto simp: Bit_def)

lemma le_Bits: "v BIT b \<le> w BIT c \<longleftrightarrow> v < w \<or> v \<le> w \<and> (\<not> b \<or> c)"
  by (auto simp: Bit_def)

lemma pred_BIT_simps [simp]:
  "x BIT False - 1 = (x - 1) BIT True"
  "x BIT True - 1 = x BIT False"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

lemma succ_BIT_simps [simp]:
  "x BIT False + 1 = x BIT True"
  "x BIT True + 1 = (x + 1) BIT False"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

lemma add_BIT_simps [simp]:
  "x BIT False + y BIT False = (x + y) BIT False"
  "x BIT False + y BIT True = (x + y) BIT True"
  "x BIT True + y BIT False = (x + y) BIT True"
  "x BIT True + y BIT True = (x + y + 1) BIT False"
  by (simp_all add: Bit_B0_2t Bit_B1_2t)

lemma mult_BIT_simps [simp]:
  "x BIT False * y = (x * y) BIT False"
  "x * y BIT False = (x * y) BIT False"
  "x BIT True * y = (x * y) BIT False + y"
  by (simp_all add: Bit_B0_2t Bit_B1_2t algebra_simps)

lemma B_mod_2': "X = 2 \<Longrightarrow> (w BIT True) mod X = 1 \<and> (w BIT False) mod X = 0"
  by (simp add: Bit_B0 Bit_B1)

lemma bin_ex_rl: "\<exists>w b. w BIT b = bin"
  by (metis bin_rl_simp)

lemma bin_exhaust: "(\<And>x b. bin = x BIT b \<Longrightarrow> Q) \<Longrightarrow> Q"
by (metis bin_ex_rl)

lemma bin_abs_lem: "bin = (w BIT b) \<Longrightarrow> bin \<noteq> -1 \<longrightarrow> bin \<noteq> 0 \<longrightarrow> nat \<bar>w\<bar> < nat \<bar>bin\<bar>"
  apply clarsimp
  apply (unfold Bit_def)
  apply (cases b)
   apply (clarsimp, arith)
  apply (clarsimp, arith)
  done

lemma bin_induct:
  assumes PPls: "P 0"
    and PMin: "P (- 1)"
    and PBit: "\<And>bin bit. P bin \<Longrightarrow> P (bin BIT bit)"
  shows "P bin"
  apply (rule_tac P=P and a=bin and f1="nat \<circ> abs" in wf_measure [THEN wf_induct])
  apply (simp add: measure_def inv_image_def)
  apply (case_tac x rule: bin_exhaust)
  apply (frule bin_abs_lem)
  apply (auto simp add : PPls PMin PBit)
  done

lemma Bit_div2 [simp]: "(w BIT b) div 2 = w"
  unfolding bin_rest_def [symmetric] by (rule bin_rest_BIT)

lemma bin_rl_eqI: "\<lbrakk>bin_rest x = bin_rest y; bin_last x = bin_last y\<rbrakk> \<Longrightarrow> x = y"
  by (metis (mono_tags) BIT_eq_iff bin_ex_rl bin_last_BIT bin_rest_BIT)

lemma twice_conv_BIT: "2 * x = x BIT False"
  by (rule bin_rl_eqI) (simp_all, simp_all add: bin_rest_def bin_last_def)

lemma BIT_lt0 [simp]: "x BIT b < 0 \<longleftrightarrow> x < 0"
by(cases b)(auto simp add: Bit_def)

lemma BIT_ge0 [simp]: "x BIT b \<ge> 0 \<longleftrightarrow> x \<ge> 0"
by(cases b)(auto simp add: Bit_def)

lemma [simp]: 
  shows bin_rest_lt0: "bin_rest i < 0 \<longleftrightarrow> i < 0"
  and  bin_rest_ge_0: "bin_rest i \<ge> 0 \<longleftrightarrow> i \<ge> 0"
by(auto simp add: bin_rest_def)

lemma bin_rest_gt_0 [simp]: "bin_rest x > 0 \<longleftrightarrow> x > 1"
by(simp add: bin_rest_def add1_zle_eq pos_imp_zdiv_pos_iff) (metis add1_zle_eq one_add_one)


subsection \<open>Explicit bit representation of \<^typ>\<open>int\<close>\<close>

primrec bl_to_bin_aux :: "bool list \<Rightarrow> int \<Rightarrow> int"
  where
    Nil: "bl_to_bin_aux [] w = w"
  | Cons: "bl_to_bin_aux (b # bs) w = bl_to_bin_aux bs (w BIT b)"

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

lemma bin_to_bl_aux_Bit_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n (w BIT b) bl = bin_to_bl_aux (n - 1) w (b # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_Bit0_minus_simp [simp]:
  "0 < n \<Longrightarrow>
    bin_to_bl_aux n (numeral (Num.Bit0 w)) bl = bin_to_bl_aux (n - 1) (numeral w) (False # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_Bit1_minus_simp [simp]:
  "0 < n \<Longrightarrow>
    bin_to_bl_aux n (numeral (Num.Bit1 w)) bl = bin_to_bl_aux (n - 1) (numeral w) (True # bl)"
  by (cases n) auto

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

lemma bl_to_bin_BIT:
  "bl_to_bin bs BIT b = bl_to_bin (bs @ [b])"
  by (simp add: bl_to_bin_append)


subsection \<open>Bit projection\<close>

primrec bin_nth :: "int \<Rightarrow> nat \<Rightarrow> bool"
  where
    Z: "bin_nth w 0 \<longleftrightarrow> bin_last w"
  | Suc: "bin_nth w (Suc n) \<longleftrightarrow> bin_nth (bin_rest w) n"

lemma bin_nth_eq_mod:
  "bin_nth w n \<longleftrightarrow> odd (w div 2 ^ n)"
  by (induction n arbitrary: w) (simp_all add: bin_last_def bin_rest_def odd_iff_mod_2_eq_one zdiv_zmult2_eq)

lemma bin_nth_eq_iff: "bin_nth x = bin_nth y \<longleftrightarrow> x = y"
proof -
  have bin_nth_lem [rule_format]: "\<forall>y. bin_nth x = bin_nth y \<longrightarrow> x = y"
    apply (induct x rule: bin_induct)
      apply safe
      apply (erule rev_mp)
      apply (induct_tac y rule: bin_induct)
        apply safe
        apply (drule_tac x=0 in fun_cong, force)
       apply (erule notE, rule ext, drule_tac x="Suc x" in fun_cong, force)
      apply (drule_tac x=0 in fun_cong, force)
     apply (erule rev_mp)
     apply (induct_tac y rule: bin_induct)
       apply safe
       apply (drule_tac x=0 in fun_cong, force)
      apply (erule notE, rule ext, drule_tac x="Suc x" in fun_cong, force)
     apply (metis Bit_eq_m1_iff Z bin_last_BIT)
    apply (case_tac y rule: bin_exhaust)
    apply clarify
    apply (erule allE)
    apply (erule impE)
     prefer 2
     apply (erule conjI)
     apply (drule_tac x=0 in fun_cong, force)
    apply (rule ext)
    apply (drule_tac x="Suc x" for x in fun_cong, force)
    done
  show ?thesis
    by (auto elim: bin_nth_lem)
qed

lemma bin_eqI:
  "x = y" if "\<And>n. bin_nth x n \<longleftrightarrow> bin_nth y n"
  using that bin_nth_eq_iff [of x y] by (simp add: fun_eq_iff)

lemma bin_eq_iff: "x = y \<longleftrightarrow> (\<forall>n. bin_nth x n = bin_nth y n)"
  using bin_nth_eq_iff by auto

lemma bin_nth_zero [simp]: "\<not> bin_nth 0 n"
  by (induct n) auto

lemma bin_nth_1 [simp]: "bin_nth 1 n \<longleftrightarrow> n = 0"
  by (cases n) simp_all

lemma bin_nth_minus1 [simp]: "bin_nth (- 1) n"
  by (induct n) auto

lemma bin_nth_0_BIT: "bin_nth (w BIT b) 0 \<longleftrightarrow> b"
  by auto

lemma bin_nth_Suc_BIT: "bin_nth (w BIT b) (Suc n) = bin_nth w n"
  by auto

lemma bin_nth_minus [simp]: "0 < n \<Longrightarrow> bin_nth (w BIT b) n = bin_nth w (n - 1)"
  by (cases n) auto

lemma bin_nth_numeral: "bin_rest x = y \<Longrightarrow> bin_nth x (numeral n) = bin_nth y (pred_numeral n)"
  by (simp add: numeral_eq_Suc)

lemmas bin_nth_numeral_simps [simp] =
  bin_nth_numeral [OF bin_rest_numeral_simps(2)]
  bin_nth_numeral [OF bin_rest_numeral_simps(5)]
  bin_nth_numeral [OF bin_rest_numeral_simps(6)]
  bin_nth_numeral [OF bin_rest_numeral_simps(7)]
  bin_nth_numeral [OF bin_rest_numeral_simps(8)]

lemmas bin_nth_simps =
  bin_nth.Z bin_nth.Suc bin_nth_zero bin_nth_minus1
  bin_nth_numeral_simps

lemma nth_2p_bin: "bin_nth (2 ^ n) m = (m = n)" \<comment> \<open>for use when simplifying with \<open>bin_nth_Bit\<close>\<close>
  apply (induct n arbitrary: m)
   apply clarsimp
   apply safe
   apply (case_tac m)
    apply (auto simp: Bit_B0_2t [symmetric])
  done 

lemma nth_rest_power_bin: "bin_nth ((bin_rest ^^ k) w) n = bin_nth w (n + k)"
  apply (induct k arbitrary: n)
   apply clarsimp
  apply clarsimp
  apply (simp only: bin_nth.Suc [symmetric] add_Suc)
  done

lemma bin_nth_numeral_unfold:
  "bin_nth (numeral (num.Bit0 x)) n \<longleftrightarrow> n > 0 \<and> bin_nth (numeral x) (n - 1)"
  "bin_nth (numeral (num.Bit1 x)) n \<longleftrightarrow> (n > 0 \<longrightarrow> bin_nth (numeral x) (n - 1))"
by(case_tac [!] n) simp_all


subsection \<open>Truncating\<close>

definition bin_sign :: "int \<Rightarrow> int"
  where "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign 0 = 0"
  "bin_sign 1 = 0"
  "bin_sign (- 1) = - 1"
  "bin_sign (numeral k) = 0"
  "bin_sign (- numeral k) = -1"
  "bin_sign (w BIT b) = bin_sign w"
  by (simp_all add: bin_sign_def Bit_def)

lemma bin_sign_rest [simp]: "bin_sign (bin_rest w) = bin_sign w"
  by (cases w rule: bin_exhaust) auto

primrec bintrunc :: "nat \<Rightarrow> int \<Rightarrow> int"
  where
    Z : "bintrunc 0 bin = 0"
  | Suc : "bintrunc (Suc n) bin = bintrunc n (bin_rest bin) BIT (bin_last bin)"

primrec sbintrunc :: "nat \<Rightarrow> int \<Rightarrow> int"
  where
    Z : "sbintrunc 0 bin = (if bin_last bin then -1 else 0)"
  | Suc : "sbintrunc (Suc n) bin = sbintrunc n (bin_rest bin) BIT (bin_last bin)"

lemma bintrunc_mod2p: "bintrunc n w = w mod 2 ^ n"
  by (induct n arbitrary: w) (auto simp add: bin_last_def bin_rest_def Bit_def zmod_zmult2_eq)

lemma sbintrunc_mod2p: "sbintrunc n w = (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n"
proof (induction n arbitrary: w)
  case 0
  then show ?case
    by (auto simp add: bin_last_odd odd_iff_mod_2_eq_one)
next
  case (Suc n)
  moreover have "((bin_rest w + 2 ^ n) mod (2 * 2 ^ n) - 2 ^ n) BIT bin_last w =
    (w + 2 * 2 ^ n) mod (4 * 2 ^ n) - 2 * 2 ^ n"
  proof (cases w rule: parity_cases)
    case even
    then show ?thesis
      by (simp add: bin_last_odd bin_rest_def Bit_B0_2t mult_mod_right)
  next
    case odd
    then have "2 * (w div 2) = w - 1"
      using minus_mod_eq_mult_div [of w 2] by simp
    moreover have "(2 * 2 ^ n + w - 1) mod (2 * 2 * 2 ^ n) + 1 = (2 * 2 ^ n + w) mod (2 * 2 * 2 ^ n)"
      using odd emep1 [of "2 * 2 ^ n + w - 1" "2 * 2 * 2 ^ n"] by simp
    ultimately show ?thesis 
      using odd by (simp add: bin_last_odd bin_rest_def Bit_B1_2t mult_mod_right) (simp add: algebra_simps)
  qed
  ultimately show ?case
    by simp
qed

lemma sign_bintr: "bin_sign (bintrunc n w) = 0"
  by (simp add: bintrunc_mod2p bin_sign_def)

lemma bintrunc_n_0 [simp]: "bintrunc n 0 = 0"
  by (simp add: bintrunc_mod2p)

lemma sbintrunc_n_0 [simp]: "sbintrunc n 0 = 0"
  by (simp add: sbintrunc_mod2p)

lemma sbintrunc_n_minus1 [simp]: "sbintrunc n (- 1) = -1"
  by (induct n) auto

lemma bintrunc_Suc_numeral:
  "bintrunc (Suc n) 1 = 1"
  "bintrunc (Suc n) (- 1) = bintrunc n (- 1) BIT True"
  "bintrunc (Suc n) (numeral (Num.Bit0 w)) = bintrunc n (numeral w) BIT False"
  "bintrunc (Suc n) (numeral (Num.Bit1 w)) = bintrunc n (numeral w) BIT True"
  "bintrunc (Suc n) (- numeral (Num.Bit0 w)) = bintrunc n (- numeral w) BIT False"
  "bintrunc (Suc n) (- numeral (Num.Bit1 w)) = bintrunc n (- numeral (w + Num.One)) BIT True"
  by simp_all

lemma sbintrunc_0_numeral [simp]:
  "sbintrunc 0 1 = -1"
  "sbintrunc 0 (numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (numeral (Num.Bit1 w)) = -1"
  "sbintrunc 0 (- numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (- numeral (Num.Bit1 w)) = -1"
  by simp_all

lemma sbintrunc_Suc_numeral:
  "sbintrunc (Suc n) 1 = 1"
  "sbintrunc (Suc n) (numeral (Num.Bit0 w)) = sbintrunc n (numeral w) BIT False"
  "sbintrunc (Suc n) (numeral (Num.Bit1 w)) = sbintrunc n (numeral w) BIT True"
  "sbintrunc (Suc n) (- numeral (Num.Bit0 w)) = sbintrunc n (- numeral w) BIT False"
  "sbintrunc (Suc n) (- numeral (Num.Bit1 w)) = sbintrunc n (- numeral (w + Num.One)) BIT True"
  by simp_all

lemma bin_sign_lem: "(bin_sign (sbintrunc n bin) = -1) = bin_nth bin n"
  apply (induct n arbitrary: bin)
  apply (case_tac bin rule: bin_exhaust, case_tac b, auto)
  done

lemma nth_bintr: "bin_nth (bintrunc m w) n \<longleftrightarrow> n < m \<and> bin_nth w n"
  apply (induct n arbitrary: w m)
   apply (case_tac m, auto)[1]
  apply (case_tac m, auto)[1]
  done

lemma nth_sbintr: "bin_nth (sbintrunc m w) n = (if n < m then bin_nth w n else bin_nth w m)"
  apply (induct n arbitrary: w m)
   apply (case_tac m)
    apply simp_all
  apply (case_tac m)
   apply simp_all
  done

lemma bin_nth_Bit: "bin_nth (w BIT b) n \<longleftrightarrow> n = 0 \<and> b \<or> (\<exists>m. n = Suc m \<and> bin_nth w m)"
  by (cases n) auto

lemma bin_nth_Bit0:
  "bin_nth (numeral (Num.Bit0 w)) n \<longleftrightarrow>
    (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bin_nth_Bit [where w="numeral w" and b="False"] by simp

lemma bin_nth_Bit1:
  "bin_nth (numeral (Num.Bit1 w)) n \<longleftrightarrow>
    n = 0 \<or> (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bin_nth_Bit [where w="numeral w" and b="True"] by simp

lemma bintrunc_bintrunc_l: "n \<le> m \<Longrightarrow> bintrunc m (bintrunc n w) = bintrunc n w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma sbintrunc_sbintrunc_l: "n \<le> m \<Longrightarrow> sbintrunc m (sbintrunc n w) = sbintrunc n w"
  by (rule bin_eqI) (auto simp: nth_sbintr)

lemma bintrunc_bintrunc_ge: "n \<le> m \<Longrightarrow> bintrunc n (bintrunc m w) = bintrunc n w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma bintrunc_bintrunc_min [simp]: "bintrunc m (bintrunc n w) = bintrunc (min m n) w"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma sbintrunc_sbintrunc_min [simp]: "sbintrunc m (sbintrunc n w) = sbintrunc (min m n) w"
  by (rule bin_eqI) (auto simp: nth_sbintr min.absorb1 min.absorb2)

lemmas bintrunc_Pls =
  bintrunc.Suc [where bin="0", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas bintrunc_Min [simp] =
  bintrunc.Suc [where bin="-1", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas bintrunc_BIT  [simp] =
  bintrunc.Suc [where bin="w BIT b", simplified bin_last_BIT bin_rest_BIT] for w b

lemmas bintrunc_Sucs = bintrunc_Pls bintrunc_Min bintrunc_BIT
  bintrunc_Suc_numeral

lemmas sbintrunc_Suc_Pls =
  sbintrunc.Suc [where bin="0", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Suc_Min =
  sbintrunc.Suc [where bin="-1", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Suc_BIT [simp] =
  sbintrunc.Suc [where bin="w BIT b", simplified bin_last_BIT bin_rest_BIT] for w b

lemmas sbintrunc_Sucs = sbintrunc_Suc_Pls sbintrunc_Suc_Min sbintrunc_Suc_BIT
  sbintrunc_Suc_numeral

lemmas sbintrunc_Pls =
  sbintrunc.Z [where bin="0", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Min =
  sbintrunc.Z [where bin="-1", simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_0_BIT_B0 [simp] =
  sbintrunc.Z [where bin="w BIT False", simplified bin_last_numeral_simps bin_rest_numeral_simps]
  for w

lemmas sbintrunc_0_BIT_B1 [simp] =
  sbintrunc.Z [where bin="w BIT True", simplified bin_last_BIT bin_rest_numeral_simps]
  for w

lemmas sbintrunc_0_simps =
  sbintrunc_Pls sbintrunc_Min sbintrunc_0_BIT_B0 sbintrunc_0_BIT_B1

lemmas bintrunc_simps = bintrunc.Z bintrunc_Sucs
lemmas sbintrunc_simps = sbintrunc_0_simps sbintrunc_Sucs

lemma bintrunc_minus: "0 < n \<Longrightarrow> bintrunc (Suc (n - 1)) w = bintrunc n w"
  by auto

lemma sbintrunc_minus: "0 < n \<Longrightarrow> sbintrunc (Suc (n - 1)) w = sbintrunc n w"
  by auto

lemmas bintrunc_minus_simps =
  bintrunc_Sucs [THEN [2] bintrunc_minus [symmetric, THEN trans]]
lemmas sbintrunc_minus_simps =
  sbintrunc_Sucs [THEN [2] sbintrunc_minus [symmetric, THEN trans]]

lemmas thobini1 = arg_cong [where f = "\<lambda>w. w BIT b"] for b

lemmas bintrunc_BIT_I = trans [OF bintrunc_BIT thobini1]
lemmas bintrunc_Min_I = trans [OF bintrunc_Min thobini1]

lemmas bmsts = bintrunc_minus_simps(1-3) [THEN thobini1 [THEN [2] trans]]
lemmas bintrunc_Pls_minus_I = bmsts(1)
lemmas bintrunc_Min_minus_I = bmsts(2)
lemmas bintrunc_BIT_minus_I = bmsts(3)

lemma bintrunc_Suc_lem: "bintrunc (Suc n) x = y \<Longrightarrow> m = Suc n \<Longrightarrow> bintrunc m x = y"
  by auto

lemmas bintrunc_Suc_Ialts =
  bintrunc_Min_I [THEN bintrunc_Suc_lem]
  bintrunc_BIT_I [THEN bintrunc_Suc_lem]

lemmas sbintrunc_BIT_I = trans [OF sbintrunc_Suc_BIT thobini1]

lemmas sbintrunc_Suc_Is =
  sbintrunc_Sucs(1-3) [THEN thobini1 [THEN [2] trans]]

lemmas sbintrunc_Suc_minus_Is =
  sbintrunc_minus_simps(1-3) [THEN thobini1 [THEN [2] trans]]

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
  by (cases n) (auto simp del: bintrunc.Suc)

lemma sbintrunc_bintrunc' [simp]: "0 < n \<Longrightarrow> sbintrunc (n - 1) (bintrunc n w) = sbintrunc (n - 1) w"
  by (cases n) (auto simp del: bintrunc.Suc)

lemma bin_sbin_eq_iff: "bintrunc (Suc n) x = bintrunc (Suc n) y \<longleftrightarrow> sbintrunc n x = sbintrunc n y"
  apply (rule iffI)
   apply (rule box_equals [OF _ sbintrunc_bintrunc sbintrunc_bintrunc])
   apply simp
  apply (rule box_equals [OF _ bintrunc_sbintrunc bintrunc_sbintrunc])
  apply simp
  done

lemma bin_sbin_eq_iff':
  "0 < n \<Longrightarrow> bintrunc n x = bintrunc n y \<longleftrightarrow> sbintrunc (n - 1) x = sbintrunc (n - 1) y"
  by (cases n) (simp_all add: bin_sbin_eq_iff del: bintrunc.Suc)

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
  "bintrunc (numeral k) x = bintrunc (pred_numeral k) (bin_rest x) BIT bin_last x"
  by (simp add: numeral_eq_Suc)

lemma sbintrunc_numeral:
  "sbintrunc (numeral k) x = sbintrunc (pred_numeral k) (bin_rest x) BIT bin_last x"
  by (simp add: numeral_eq_Suc)

lemma bintrunc_numeral_simps [simp]:
  "bintrunc (numeral k) (numeral (Num.Bit0 w)) = bintrunc (pred_numeral k) (numeral w) BIT False"
  "bintrunc (numeral k) (numeral (Num.Bit1 w)) = bintrunc (pred_numeral k) (numeral w) BIT True"
  "bintrunc (numeral k) (- numeral (Num.Bit0 w)) = bintrunc (pred_numeral k) (- numeral w) BIT False"
  "bintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    bintrunc (pred_numeral k) (- numeral (w + Num.One)) BIT True"
  "bintrunc (numeral k) 1 = 1"
  by (simp_all add: bintrunc_numeral)

lemma sbintrunc_numeral_simps [simp]:
  "sbintrunc (numeral k) (numeral (Num.Bit0 w)) = sbintrunc (pred_numeral k) (numeral w) BIT False"
  "sbintrunc (numeral k) (numeral (Num.Bit1 w)) = sbintrunc (pred_numeral k) (numeral w) BIT True"
  "sbintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    sbintrunc (pred_numeral k) (- numeral w) BIT False"
  "sbintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    sbintrunc (pred_numeral k) (- numeral (w + Num.One)) BIT True"
  "sbintrunc (numeral k) 1 = 1"
  by (simp_all add: sbintrunc_numeral)

lemma no_bintr_alt1: "bintrunc n = (\<lambda>w. w mod 2 ^ n :: int)"
  by (rule ext) (rule bintrunc_mod2p)

lemma range_bintrunc: "range (bintrunc n) = {i. 0 \<le> i \<and> i < 2 ^ n}"
  apply (unfold no_bintr_alt1)
  apply (auto simp add: image_iff)
  apply (rule exI)
  apply (rule sym)
  using int_mod_lem [symmetric, of "2 ^ n"]
  apply auto
  done

lemma no_sbintr_alt2: "sbintrunc n = (\<lambda>w. (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (rule ext) (simp add : sbintrunc_mod2p)

lemma range_sbintrunc: "range (sbintrunc n) = {i. - (2 ^ n) \<le> i \<and> i < 2 ^ n}"
  apply (unfold no_sbintr_alt2)
  apply (auto simp add: image_iff eq_diff_eq)

  apply (rule exI)
  apply (auto intro: int_mod_lem [THEN iffD1, symmetric])
  done

lemma sb_inc_lem: "a + 2^k < 0 \<Longrightarrow> a + 2^k + 2^(Suc k) \<le> (a + 2^k) mod 2^(Suc k)"
  for a :: int
  using int_mod_ge' [where n = "2 ^ (Suc k)" and b = "a + 2 ^ k"]
  by simp

lemma sb_inc_lem': "a < - (2^k) \<Longrightarrow> a + 2^k + 2^(Suc k) \<le> (a + 2^k) mod 2^(Suc k)"
  for a :: int
  by (rule sb_inc_lem) simp

lemma sbintrunc_inc: "x < - (2^n) \<Longrightarrow> x + 2^(Suc n) \<le> sbintrunc n x"
  unfolding no_sbintr_alt2 by (drule sb_inc_lem') simp

lemma sb_dec_lem: "0 \<le> - (2 ^ k) + a \<Longrightarrow> (a + 2 ^ k) mod (2 * 2 ^ k) \<le> - (2 ^ k) + a"
  for a :: int
  using int_mod_le'[where n = "2 ^ (Suc k)" and b = "a + 2 ^ k"] by simp

lemma sb_dec_lem': "2 ^ k \<le> a \<Longrightarrow> (a + 2 ^ k) mod (2 * 2 ^ k) \<le> - (2 ^ k) + a"
  for a :: int
  by (rule sb_dec_lem) simp

lemma sbintrunc_dec: "x \<ge> (2 ^ n) \<Longrightarrow> x - 2 ^ (Suc n) >= sbintrunc n x"
  unfolding no_sbintr_alt2 by (drule sb_dec_lem') simp

lemma bintr_ge0: "0 \<le> bintrunc n w"
  by (simp add: bintrunc_mod2p)

lemma bintr_lt2p: "bintrunc n w < 2 ^ n"
  by (simp add: bintrunc_mod2p)

lemma bintr_Min: "bintrunc n (- 1) = 2 ^ n - 1"
  by (simp add: bintrunc_mod2p m1mod2k)

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
  by (induct n arbitrary: bin) auto

lemma bin_rest_power_trunc:
  "(bin_rest ^^ k) (bintrunc n bin) = bintrunc (n - k) ((bin_rest ^^ k) bin)"
  by (induct k) (auto simp: bin_rest_trunc)

lemma bin_rest_trunc_i: "bintrunc n (bin_rest bin) = bin_rest (bintrunc (Suc n) bin)"
  by auto

lemma bin_rest_strunc: "bin_rest (sbintrunc (Suc n) bin) = sbintrunc n (bin_rest bin)"
  by (induct n arbitrary: bin) auto

lemma bintrunc_rest [simp]: "bintrunc n (bin_rest (bintrunc n bin)) = bin_rest (bintrunc n bin)"
  apply (induct n arbitrary: bin)
   apply simp
  apply (case_tac bin rule: bin_exhaust)
  apply (auto simp: bintrunc_bintrunc_l)
  done

lemma sbintrunc_rest [simp]: "sbintrunc n (bin_rest (sbintrunc n bin)) = bin_rest (sbintrunc n bin)"
  apply (induct n arbitrary: bin)
   apply simp
  apply (case_tac bin rule: bin_exhaust)
  apply (auto simp: bintrunc_bintrunc_l split: bool.splits)
  done

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

primrec bin_split :: "nat \<Rightarrow> int \<Rightarrow> int \<times> int"
  where
    Z: "bin_split 0 w = (w, 0)"
  | Suc: "bin_split (Suc n) w =
      (let (w1, w2) = bin_split n (bin_rest w)
       in (w1, w2 BIT bin_last w))"

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w) in (w1, w2 BIT bin_last w))"
  "bin_split 0 w = (w, 0)"
  by simp_all

primrec bin_cat :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int"
  where
    Z: "bin_cat w 0 v = w"
  | Suc: "bin_cat w (Suc n) v = bin_cat w n (bin_rest v) BIT bin_last v"

lemma bin_sign_cat: "bin_sign (bin_cat x n y) = bin_sign x"
  by (induct n arbitrary: y) auto

lemma bin_cat_Suc_Bit: "bin_cat w (Suc n) (v BIT b) = bin_cat w n v BIT b"
  by auto

lemma bin_cat_assoc: "bin_cat (bin_cat x m y) n z = bin_cat x (m + n) (bin_cat y n z)"
  by (induct n arbitrary: z) auto

lemma bin_cat_assoc_sym: "bin_cat x m (bin_cat y n z) = bin_cat (bin_cat x (m - n) y) (min m n) z"
  apply (induct n arbitrary: z m)
   apply clarsimp
  apply (case_tac m, auto)
  done

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
  apply (induct k arbitrary: n y)
   apply clarsimp
  apply (case_tac n, auto)
  done

lemma bin_nth_split:
  "bin_split n c = (a, b) \<Longrightarrow>
    (\<forall>k. bin_nth a k = bin_nth c (n + k)) \<and>
    (\<forall>k. bin_nth b k = (k < n \<and> bin_nth c k))"
  apply (induct n arbitrary: b c)
   apply clarsimp
  apply (clarsimp simp: Let_def split: prod.split_asm)
  apply (case_tac k)
  apply auto
  done

lemma bin_cat_zero [simp]: "bin_cat 0 n w = bintrunc n w"
  by (induct n arbitrary: w) auto

lemma bintr_cat1: "bintrunc (k + n) (bin_cat a n b) = bin_cat (bintrunc k a) n b"
  by (induct n arbitrary: b) auto

lemma bintr_cat: "bintrunc m (bin_cat a n b) =
    bin_cat (bintrunc (m - n) a) n (bintrunc (min m n) b)"
  by (rule bin_eqI) (auto simp: bin_nth_cat nth_bintr)

lemma bintr_cat_same [simp]: "bintrunc n (bin_cat a n b) = bintrunc n b"
  by (auto simp add : bintr_cat)

lemma cat_bintr [simp]: "bin_cat a n (bintrunc n b) = bin_cat a n b"
  by (induct n arbitrary: b) auto

lemma split_bintrunc: "bin_split n c = (a, b) \<Longrightarrow> b = bintrunc n c"
  by (induct n arbitrary: b c) (auto simp: Let_def split: prod.split_asm)

lemma bin_cat_split: "bin_split n w = (u, v) \<Longrightarrow> w = bin_cat u n v"
  by (induct n arbitrary: v w) (auto simp: Let_def split: prod.split_asm)

lemma bin_split_cat: "bin_split n (bin_cat v n w) = (v, bintrunc n w)"
  by (induct n arbitrary: w) auto

lemma bin_split_zero [simp]: "bin_split n 0 = (0, 0)"
  by (induct n) auto

lemma bin_split_minus1 [simp]:
  "bin_split n (- 1) = (- 1, bintrunc n (- 1))"
  by (induct n) auto

lemma bin_split_trunc:
  "bin_split (min m n) c = (a, b) \<Longrightarrow>
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: prod.split_asm)
  apply (case_tac m)
   apply (auto simp: Let_def split: prod.split_asm)
  done

lemma bin_split_trunc1:
  "bin_split n c = (a, b) \<Longrightarrow>
    bin_split n (bintrunc m c) = (bintrunc (m - n) a, bintrunc m b)"
  apply (induct n arbitrary: m b c, clarsimp)
  apply (simp add: bin_rest_trunc Let_def split: prod.split_asm)
  apply (case_tac m)
   apply (auto simp: Let_def split: prod.split_asm)
  done

lemma bin_cat_num: "bin_cat a n b = a * 2 ^ n + bintrunc n b"
  apply (induct n arbitrary: b)
   apply clarsimp
  apply (simp add: Bit_def)
  done

lemma bin_split_num: "bin_split n b = (b div 2 ^ n, b mod 2 ^ n)"
  apply (induct n arbitrary: b)
   apply simp
  apply (simp add: bin_rest_def zdiv_zmult2_eq)
  apply (case_tac b rule: bin_exhaust)
  apply simp
  apply (simp add: Bit_def mod_mult_mult1 pos_zmod_mult_2 add.commute)
  done

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

lemmas bin_split_minus_simp =
  bin_split.Suc [THEN [2] bin_split_minus [symmetric, THEN trans]]

lemma bin_split_pred_simp [simp]:
  "(0::nat) < numeral bin \<Longrightarrow>
    bin_split (numeral bin) w =
      (let (w1, w2) = bin_split (numeral bin - 1) (bin_rest w)
       in (w1, w2 BIT bin_last w))"
  by (simp only: bin_split_minus_simp)

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
  apply (drule split_bintrunc)
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
  apply clarify
  apply (erule allE, erule impE, erule exI)
  apply (case_tac k)
   apply clarsimp
   prefer 2
   apply clarsimp
   apply (erule allE)
   apply (erule (1) impE)
   apply (drule bin_nth_split, erule conjE, erule allE, erule trans, simp add: ac_simps)+
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
  apply (drule bin_split_trunc)
  apply (drule sym [THEN trans], assumption)
  apply (subst rsplit_aux_alts(1))
  apply (subst rsplit_aux_alts(2))
  apply clarsimp
  unfolding bin_rsplit_def bin_rsplitl_def
  apply simp
  done

lemma bin_rsplit_rcat [rule_format]:
  "n > 0 \<longrightarrow> bin_rsplit n (n * size ws, bin_rcat n ws) = map (bintrunc n) ws"
  apply (unfold bin_rsplit_def bin_rcat_def)
  apply (rule_tac xs = ws in rev_induct)
   apply clarsimp
  apply clarsimp
  apply (subst rsplit_aux_alts)
  unfolding bin_split_cat
  apply simp
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
    from "1.hyps" \<open>m \<noteq> 0\<close> \<open>n \<noteq> 0\<close>
    have hyp: "\<And>v bs. length bs = Suc (length cs) \<Longrightarrow>
      length (bin_rsplit_aux n (m - n) v bs) =
      length (bin_rsplit_aux n (m - n) (fst (bin_split n w)) (snd (bin_split n w) # cs))"
      by auto
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
    Z: "bin_sc 0 b w = bin_rest w BIT b"
  | Suc: "bin_sc (Suc n) b w = bin_sc n b (bin_rest w) BIT bin_last w"

lemma bin_nth_sc [simp]: "bin_nth (bin_sc n b w) n \<longleftrightarrow> b"
  by (induct n arbitrary: w) auto

lemma bin_sc_sc_same [simp]: "bin_sc n c (bin_sc n b w) = bin_sc n c w"
  by (induct n arbitrary: w) auto

lemma bin_sc_sc_diff: "m \<noteq> n \<Longrightarrow> bin_sc m c (bin_sc n b w) = bin_sc n b (bin_sc m c w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] m)
     apply auto
  done

lemma bin_nth_sc_gen: "bin_nth (bin_sc n b w) m = (if m = n then b else bin_nth w m)"
  by (induct n arbitrary: w m) (case_tac [!] m, auto)

lemma bin_sc_nth [simp]: "bin_sc n (bin_nth w n) w = w"
  by (induct n arbitrary: w) auto

lemma bin_sign_sc [simp]: "bin_sign (bin_sc n b w) = bin_sign w"
  by (induct n arbitrary: w) auto

lemma bin_sc_bintr [simp]: "bintrunc m (bin_sc n x (bintrunc m (w))) = bintrunc m (bin_sc n x w)"
  apply (induct n arbitrary: w m)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (case_tac [!] m, auto)
  done

lemma bin_clr_le: "bin_sc n False w \<le> w"
  apply (induct n arbitrary: w)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp: le_Bits)
  done

lemma bin_set_ge: "bin_sc n True w \<ge> w"
  apply (induct n arbitrary: w)
   apply (case_tac [!] w rule: bin_exhaust)
   apply (auto simp: le_Bits)
  done

lemma bintr_bin_clr_le: "bintrunc n (bin_sc m False w) \<le> bintrunc n w"
  apply (induct n arbitrary: w m)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp: le_Bits)
  done

lemma bintr_bin_set_ge: "bintrunc n (bin_sc m True w) \<ge> bintrunc n w"
  apply (induct n arbitrary: w m)
   apply simp
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac m)
   apply (auto simp: le_Bits)
  done

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
    bin_sc (pred_numeral k) b (bin_rest w) BIT bin_last w"
  by (simp add: numeral_eq_Suc)

instantiation int :: bit_operations
begin

definition int_not_def: "bitNOT = (\<lambda>x::int. - x - 1)"

function bitAND_int
  where "bitAND_int x y =
    (if x = 0 then 0 else if x = -1 then y
     else (bin_rest x AND bin_rest y) BIT (bin_last x \<and> bin_last y))"
  by pat_completeness simp

termination
  by (relation "measure (nat \<circ> abs \<circ> fst)", simp_all add: bin_rest_def)

declare bitAND_int.simps [simp del]

definition int_or_def: "bitOR = (\<lambda>x y::int. NOT (NOT x AND NOT y))"

definition int_xor_def: "bitXOR = (\<lambda>x y::int. (x AND NOT y) OR (NOT x AND y))"

definition [iff]: "i !! n \<longleftrightarrow> bin_nth i n"

definition "lsb i = i !! 0" for i :: int

definition "set_bit i n b = bin_sc n b i"

definition "shiftl x n = x * 2 ^ n" for x :: int

definition "shiftr x n = x div 2 ^ n" for x :: int

definition "msb x \<longleftrightarrow> x < 0" for x :: int

instance ..

end


subsubsection \<open>Basic simplification rules\<close>

lemma int_not_BIT [simp]: "NOT (w BIT b) = (NOT w) BIT (\<not> b)"
  by (cases b) (simp_all add: int_not_def Bit_def)

lemma int_not_simps [simp]:
  "NOT (0::int) = -1"
  "NOT (1::int) = -2"
  "NOT (- 1::int) = 0"
  "NOT (numeral w::int) = - numeral (w + Num.One)"
  "NOT (- numeral (Num.Bit0 w)::int) = numeral (Num.BitM w)"
  "NOT (- numeral (Num.Bit1 w)::int) = numeral (Num.Bit0 w)"
  unfolding int_not_def by simp_all

lemma int_not_not [simp]: "NOT (NOT x) = x"
  for x :: int
  unfolding int_not_def by simp

lemma int_and_0 [simp]: "0 AND x = 0"
  for x :: int
  by (simp add: bitAND_int.simps)

lemma int_and_m1 [simp]: "-1 AND x = x"
  for x :: int
  by (simp add: bitAND_int.simps)

lemma int_and_Bits [simp]: "(x BIT b) AND (y BIT c) = (x AND y) BIT (b \<and> c)"
  by (subst bitAND_int.simps) (simp add: Bit_eq_0_iff Bit_eq_m1_iff)

lemma int_or_zero [simp]: "0 OR x = x"
  for x :: int
  by (simp add: int_or_def)

lemma int_or_minus1 [simp]: "-1 OR x = -1"
  for x :: int
  by (simp add: int_or_def)

lemma int_or_Bits [simp]: "(x BIT b) OR (y BIT c) = (x OR y) BIT (b \<or> c)"
  by (simp add: int_or_def)

lemma int_xor_zero [simp]: "0 XOR x = x"
  for x :: int
  by (simp add: int_xor_def)

lemma int_xor_Bits [simp]: "(x BIT b) XOR (y BIT c) = (x XOR y) BIT ((b \<or> c) \<and> \<not> (b \<and> c))"
  unfolding int_xor_def by auto


subsubsection \<open>Binary destructors\<close>

lemma bin_rest_NOT [simp]: "bin_rest (NOT x) = NOT (bin_rest x)"
  by (cases x rule: bin_exhaust) simp

lemma bin_last_NOT [simp]: "bin_last (NOT x) \<longleftrightarrow> \<not> bin_last x"
  by (cases x rule: bin_exhaust) simp

lemma bin_rest_AND [simp]: "bin_rest (x AND y) = bin_rest x AND bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_last_AND [simp]: "bin_last (x AND y) \<longleftrightarrow> bin_last x \<and> bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_rest_OR [simp]: "bin_rest (x OR y) = bin_rest x OR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_last_OR [simp]: "bin_last (x OR y) \<longleftrightarrow> bin_last x \<or> bin_last y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_rest_XOR [simp]: "bin_rest (x XOR y) = bin_rest x XOR bin_rest y"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_last_XOR [simp]:
  "bin_last (x XOR y) \<longleftrightarrow> (bin_last x \<or> bin_last y) \<and> \<not> (bin_last x \<and> bin_last y)"
  by (cases x rule: bin_exhaust, cases y rule: bin_exhaust) simp

lemma bin_nth_ops:
  "\<And>x y. bin_nth (x AND y) n \<longleftrightarrow> bin_nth x n \<and> bin_nth y n"
  "\<And>x y. bin_nth (x OR y) n \<longleftrightarrow> bin_nth x n \<or> bin_nth y n"
  "\<And>x y. bin_nth (x XOR y) n \<longleftrightarrow> bin_nth x n \<noteq> bin_nth y n"
  "\<And>x. bin_nth (NOT x) n \<longleftrightarrow> \<not> bin_nth x n"
  by (induct n) auto


subsubsection \<open>Derived properties\<close>

lemma int_xor_minus1 [simp]: "-1 XOR x = NOT x"
  for x :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_xor_extra_simps [simp]:
  "w XOR 0 = w"
  "w XOR -1 = NOT w"
  for w :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_or_extra_simps [simp]:
  "w OR 0 = w"
  "w OR -1 = -1"
  for w :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma int_and_extra_simps [simp]:
  "w AND 0 = 0"
  "w AND -1 = w"
  for w :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

text \<open>Commutativity of the above.\<close>
lemma bin_ops_comm:
  fixes x y :: int
  shows int_and_comm: "x AND y = y AND x"
    and int_or_comm:  "x OR y = y OR x"
    and int_xor_comm: "x XOR y = y XOR x"
  by (auto simp add: bin_eq_iff bin_nth_ops)

lemma bin_ops_same [simp]:
  "x AND x = x"
  "x OR x = x"
  "x XOR x = 0"
  for x :: int
  by (auto simp add: bin_eq_iff bin_nth_ops)

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
  by (simp only: BIT_bin_simps [symmetric] bin_rest_BIT)

lemma bin_last_neg_numeral_BitM [simp]:
  "bin_last (- numeral (Num.BitM w))"
  by (simp only: BIT_bin_simps [symmetric] bin_last_BIT)

(* FIXME: The rule sets below are very large (24 rules for each
  operator). Is there a simpler way to do this? *)

lemma int_and_numerals [simp]:
  "numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (numeral x AND numeral y) BIT False"
  "numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (numeral x AND numeral y) BIT False"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (numeral x AND numeral y) BIT False"
  "numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (numeral x AND numeral y) BIT True"
  "numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (numeral x AND - numeral y) BIT False"
  "numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (numeral x AND - numeral (y + Num.One)) BIT False"
  "numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (numeral x AND - numeral y) BIT False"
  "numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = (numeral x AND - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit0 x) AND numeral (Num.Bit0 y) = (- numeral x AND numeral y) BIT False"
  "- numeral (Num.Bit0 x) AND numeral (Num.Bit1 y) = (- numeral x AND numeral y) BIT False"
  "- numeral (Num.Bit1 x) AND numeral (Num.Bit0 y) = (- numeral (x + Num.One) AND numeral y) BIT False"
  "- numeral (Num.Bit1 x) AND numeral (Num.Bit1 y) = (- numeral (x + Num.One) AND numeral y) BIT True"
  "- numeral (Num.Bit0 x) AND - numeral (Num.Bit0 y) = (- numeral x AND - numeral y) BIT False"
  "- numeral (Num.Bit0 x) AND - numeral (Num.Bit1 y) = (- numeral x AND - numeral (y + Num.One)) BIT False"
  "- numeral (Num.Bit1 x) AND - numeral (Num.Bit0 y) = (- numeral (x + Num.One) AND - numeral y) BIT False"
  "- numeral (Num.Bit1 x) AND - numeral (Num.Bit1 y) = (- numeral (x + Num.One) AND - numeral (y + Num.One)) BIT True"
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
  "numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (numeral x OR numeral y) BIT False"
  "numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = (numeral x OR numeral y) BIT True"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = (numeral x OR numeral y) BIT True"
  "numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = (numeral x OR numeral y) BIT True"
  "numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (numeral x OR - numeral y) BIT False"
  "numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = (numeral x OR - numeral (y + Num.One)) BIT True"
  "numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = (numeral x OR - numeral y) BIT True"
  "numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = (numeral x OR - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit0 x) OR numeral (Num.Bit0 y) = (- numeral x OR numeral y) BIT False"
  "- numeral (Num.Bit0 x) OR numeral (Num.Bit1 y) = (- numeral x OR numeral y) BIT True"
  "- numeral (Num.Bit1 x) OR numeral (Num.Bit0 y) = (- numeral (x + Num.One) OR numeral y) BIT True"
  "- numeral (Num.Bit1 x) OR numeral (Num.Bit1 y) = (- numeral (x + Num.One) OR numeral y) BIT True"
  "- numeral (Num.Bit0 x) OR - numeral (Num.Bit0 y) = (- numeral x OR - numeral y) BIT False"
  "- numeral (Num.Bit0 x) OR - numeral (Num.Bit1 y) = (- numeral x OR - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit1 x) OR - numeral (Num.Bit0 y) = (- numeral (x + Num.One) OR - numeral y) BIT True"
  "- numeral (Num.Bit1 x) OR - numeral (Num.Bit1 y) = (- numeral (x + Num.One) OR - numeral (y + Num.One)) BIT True"
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
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (numeral x XOR numeral y) BIT False"
  "numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = (numeral x XOR numeral y) BIT True"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = (numeral x XOR numeral y) BIT True"
  "numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (numeral x XOR numeral y) BIT False"
  "numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (numeral x XOR - numeral y) BIT False"
  "numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = (numeral x XOR - numeral (y + Num.One)) BIT True"
  "numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = (numeral x XOR - numeral y) BIT True"
  "numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (numeral x XOR - numeral (y + Num.One)) BIT False"
  "- numeral (Num.Bit0 x) XOR numeral (Num.Bit0 y) = (- numeral x XOR numeral y) BIT False"
  "- numeral (Num.Bit0 x) XOR numeral (Num.Bit1 y) = (- numeral x XOR numeral y) BIT True"
  "- numeral (Num.Bit1 x) XOR numeral (Num.Bit0 y) = (- numeral (x + Num.One) XOR numeral y) BIT True"
  "- numeral (Num.Bit1 x) XOR numeral (Num.Bit1 y) = (- numeral (x + Num.One) XOR numeral y) BIT False"
  "- numeral (Num.Bit0 x) XOR - numeral (Num.Bit0 y) = (- numeral x XOR - numeral y) BIT False"
  "- numeral (Num.Bit0 x) XOR - numeral (Num.Bit1 y) = (- numeral x XOR - numeral (y + Num.One)) BIT True"
  "- numeral (Num.Bit1 x) XOR - numeral (Num.Bit0 y) = (- numeral (x + Num.One) XOR - numeral y) BIT True"
  "- numeral (Num.Bit1 x) XOR - numeral (Num.Bit1 y) = (- numeral (x + Num.One) XOR - numeral (y + Num.One)) BIT False"
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

lemma plus_and_or [rule_format]: "\<forall>y::int. (x AND y) + (x OR y) = x + y"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac y rule: bin_exhaust)
  apply clarsimp
  apply (unfold Bit_def)
  apply clarsimp
  apply (erule_tac x = "x" in allE)
  apply simp
  done

lemma le_int_or: "bin_sign y = 0 \<Longrightarrow> x \<le> x OR y"
  for x y :: int
  apply (induct y arbitrary: x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac x rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] bit)
     apply (auto simp: le_Bits)
  done

lemmas int_and_le =
  xtrans(3) [OF bbw_ao_absorbs (2) [THEN conjunct2, symmetric] le_int_or]

text \<open>Interaction between bit-wise and arithmetic: good example of \<open>bin_induction\<close>.\<close>
lemma bin_add_not: "x + NOT x = (-1::int)"
  apply (induct x rule: bin_induct)
    apply clarsimp
   apply clarsimp
  apply (case_tac bit, auto)
  done

lemma mod_BIT: "bin BIT bit mod 2 ^ Suc n = (bin mod 2 ^ n) BIT bit"
proof -
  have "2 * (bin mod 2 ^ n) + 1 = (2 * bin mod 2 ^ Suc n) + 1"
    by (simp add: mod_mult_mult1)
  also have "\<dots> = ((2 * bin mod 2 ^ Suc n) + 1) mod 2 ^ Suc n"
    by (simp add: ac_simps pos_zmod_mult_2)
  also have "\<dots> = (2 * bin + 1) mod 2 ^ Suc n"
    by (simp only: mod_simps)
  finally show ?thesis
    by (auto simp add: Bit_def)
qed

lemma AND_mod: "x AND 2 ^ n - 1 = x mod 2 ^ n"
  for x :: int
proof (induct x arbitrary: n rule: bin_induct)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    by (simp, simp add: m1mod2k)
next
  case (3 bin bit)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    with 3 show ?thesis
      by (simp only: power_BIT mod_BIT int_and_Bits) simp
  qed
qed


subsubsection \<open>Comparison\<close>

lemma AND_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x"
  shows "0 \<le> x AND y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp only: Min_def)
next
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (cases bit) (simp_all add: Bit_def)
    then have "0 \<le> bin AND bin'" by (rule 3)
    with 1 show ?thesis
      by simp
  qed
qed

lemma OR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "0 \<le> y"
  shows "0 \<le> x OR y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (cases bit) (simp_all add: Bit_def)
    moreover from 1 3 have "0 \<le> bin'"
      by (cases bit') (simp_all add: Bit_def)
    ultimately have "0 \<le> bin OR bin'" by (rule 3)
    with 1 show ?thesis
      by simp
  qed
qed simp_all

lemma XOR_lower [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "0 \<le> y"
  shows "0 \<le> x XOR y"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (cases bit) (simp_all add: Bit_def)
    moreover from 1 3 have "0 \<le> bin'"
      by (cases bit') (simp_all add: Bit_def)
    ultimately have "0 \<le> bin XOR bin'" by (rule 3)
    with 1 show ?thesis
      by simp
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemma AND_upper1 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x"
  shows "x AND y \<le> x"
  using assms
proof (induct x arbitrary: y rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (cases bit) (simp_all add: Bit_def)
    then have "bin AND bin' \<le> bin" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
  qed
next
  case 2
  then show ?case by (simp only: Min_def)
qed simp

lemmas AND_upper1' [simp] = order_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper1'' [simp] = order_le_less_trans [OF AND_upper1] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma AND_upper2 [simp]: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> y"
  shows "x AND y \<le> y"
  using assms
proof (induct y arbitrary: x rule: bin_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp only: Min_def)
next
  case (3 bin bit)
  show ?case
  proof (cases x rule: bin_exhaust)
    case (1 bin' bit')
    from 3 have "0 \<le> bin"
      by (cases bit) (simp_all add: Bit_def)
    then have "bin' AND bin \<le> bin" by (rule 3)
    with 1 show ?thesis
      by simp (simp add: Bit_def)
  qed
qed

lemmas AND_upper2' [simp] = order_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
lemmas AND_upper2'' [simp] = order_le_less_trans [OF AND_upper2] \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>

lemma OR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x OR y < 2 ^ n"
  using assms
proof (induct x arbitrary: y n rule: bin_induct)
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    show ?thesis
    proof (cases n)
      case 0
      with 3 have "bin BIT bit = 0"
        by (simp add: Bit_def)
      then have "bin = 0" and "\<not> bit"
        by (auto simp add: Bit_def split: if_splits) arith
      then show ?thesis using 0 1 \<open>y < 2 ^ n\<close>
        by simp
    next
      case (Suc m)
      from 3 have "0 \<le> bin"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 3 Suc have "bin < 2 ^ m"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 1 3 Suc have "bin' < 2 ^ m"
        by (cases bit') (simp_all add: Bit_def)
      ultimately have "bin OR bin' < 2 ^ m" by (rule 3)
      with 1 Suc show ?thesis
        by simp (simp add: Bit_def)
    qed
  qed
qed simp_all

lemma XOR_upper: \<^marker>\<open>contributor \<open>Stefan Berghofer\<close>\<close>
  fixes x y :: int
  assumes "0 \<le> x" "x < 2 ^ n" "y < 2 ^ n"
  shows "x XOR y < 2 ^ n"
  using assms
proof (induct x arbitrary: y n rule: bin_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by (simp only: Min_def)
next
  case (3 bin bit)
  show ?case
  proof (cases y rule: bin_exhaust)
    case (1 bin' bit')
    show ?thesis
    proof (cases n)
      case 0
      with 3 have "bin BIT bit = 0"
        by (simp add: Bit_def)
      then have "bin = 0" and "\<not> bit"
        by (auto simp add: Bit_def split: if_splits) arith
      then show ?thesis using 0 1 \<open>y < 2 ^ n\<close>
        by simp
    next
      case (Suc m)
      from 3 have "0 \<le> bin"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 3 Suc have "bin < 2 ^ m"
        by (cases bit) (simp_all add: Bit_def)
      moreover from 1 3 Suc have "bin' < 2 ^ m"
        by (cases bit') (simp_all add: Bit_def)
      ultimately have "bin XOR bin' < 2 ^ m" by (rule 3)
      with 1 Suc show ?thesis
        by simp (simp add: Bit_def)
    qed
  qed
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
by(metis int_and_comm bbw_ao_dist)

lemmas int_and_ac = bbw_lcs(1) int_and_comm int_and_assoc

lemma int_nand_same [simp]: fixes x :: int shows "x AND NOT x = 0"
by(induct x y\<equiv>"NOT x" rule: bitAND_int.induct)(subst bitAND_int.simps, clarsimp)

lemma int_nand_same_middle: fixes x :: int shows "x AND y AND NOT x = 0"
by (metis bbw_lcs(1) int_and_0 int_nand_same)

lemma and_xor_dist: fixes x :: int shows
  "x AND (y XOR z) = (x AND y) XOR (x AND z)"
by(simp add: int_xor_def bbw_ao_dist2 bbw_not_dist int_and_ac int_nand_same_middle)

lemma int_and_lt0 [simp]: fixes x y :: int shows
  "x AND y < 0 \<longleftrightarrow> x < 0 \<and> y < 0"
by(induct x y rule: bitAND_int.induct)(subst bitAND_int.simps, simp)

lemma int_and_ge0 [simp]: fixes x y :: int shows 
  "x AND y \<ge> 0 \<longleftrightarrow> x \<ge> 0 \<or> y \<ge> 0"
by (metis int_and_lt0 linorder_not_less)

lemma int_and_1: fixes x :: int shows "x AND 1 = x mod 2"
by(subst bitAND_int.simps)(simp add: Bit_def bin_last_def zmod_minus1)

lemma int_1_and: fixes x :: int shows "1 AND x = x mod 2"
by(subst int_and_comm)(simp add: int_and_1)

lemma int_or_lt0 [simp]: fixes x y :: int shows 
  "x OR y < 0 \<longleftrightarrow> x < 0 \<or> y < 0"
by(simp add: int_or_def)

lemma int_xor_lt0 [simp]: fixes x y :: int shows
  "x XOR y < 0 \<longleftrightarrow> ((x < 0) \<noteq> (y < 0))"
by(auto simp add: int_xor_def)

lemma int_xor_ge0 [simp]: fixes x y :: int shows
  "x XOR y \<ge> 0 \<longleftrightarrow> ((x \<ge> 0) \<longleftrightarrow> (y \<ge> 0))"
by (metis int_xor_lt0 linorder_not_le)

lemma bin_last_conv_AND:
  "bin_last i \<longleftrightarrow> i AND 1 \<noteq> 0"
proof -
  obtain x b where "i = x BIT b" by(cases i rule: bin_exhaust)
  hence "i AND 1 = 0 BIT b"
    by(simp add: BIT_special_simps(2)[symmetric] del: BIT_special_simps(2))
  thus ?thesis using \<open>i = x BIT b\<close> by(cases b) simp_all
qed

lemma bitval_bin_last:
  "of_bool (bin_last i) = i AND 1"
proof -
  obtain x b where "i = x BIT b" by(cases i rule: bin_exhaust)
  hence "i AND 1 = 0 BIT b"
    by(simp add: BIT_special_simps(2)[symmetric] del: BIT_special_simps(2))
  thus ?thesis by(cases b)(simp_all add: bin_last_conv_AND)
qed

lemma bin_sign_and:
  "bin_sign (i AND j) = - (bin_sign i * bin_sign j)"
by(simp add: bin_sign_def)

lemma minus_BIT_0: fixes x y :: int shows "x BIT b - y BIT False = (x - y) BIT b"
by(simp add: Bit_def)

lemma int_not_neg_numeral: "NOT (- numeral n) = (Num.sub n num.One :: int)"
by(simp add: int_not_def)

lemma int_neg_numeral_pOne_conv_not: "- numeral (n + num.One) = (NOT (numeral n) :: int)"
by(simp add: int_not_def)


subsection \<open>Setting and clearing bits\<close>



lemma int_lsb_BIT [simp]: fixes x :: int shows
  "lsb (x BIT b) \<longleftrightarrow> b"
by(simp add: lsb_int_def)

lemma bin_last_conv_lsb: "bin_last = lsb"
by(clarsimp simp add: lsb_int_def fun_eq_iff)

lemma int_lsb_numeral [simp]:
  "lsb (0 :: int) = False"
  "lsb (1 :: int) = True"
  "lsb (Numeral1 :: int) = True"
  "lsb (- 1 :: int) = True"
  "lsb (- Numeral1 :: int) = True"
  "lsb (numeral (num.Bit0 w) :: int) = False"
  "lsb (numeral (num.Bit1 w) :: int) = True"
  "lsb (- numeral (num.Bit0 w) :: int) = False"
  "lsb (- numeral (num.Bit1 w) :: int) = True"
by(simp_all add: lsb_int_def)

lemma int_set_bit_0 [simp]: fixes x :: int shows
  "set_bit x 0 b = bin_rest x BIT b"
by(auto simp add: set_bit_int_def intro: bin_rl_eqI)

lemma int_set_bit_Suc: fixes x :: int shows
  "set_bit x (Suc n) b = set_bit (bin_rest x) n b BIT bin_last x"
by(auto simp add: set_bit_int_def twice_conv_BIT intro: bin_rl_eqI)

lemma bin_last_set_bit:
  "bin_last (set_bit x n b) = (if n > 0 then bin_last x else b)"
by(cases n)(simp_all add: int_set_bit_Suc)

lemma bin_rest_set_bit: 
  "bin_rest (set_bit x n b) = (if n > 0 then set_bit (bin_rest x) (n - 1) b else bin_rest x)"
by(cases n)(simp_all add: int_set_bit_Suc)

lemma int_set_bit_numeral: fixes x :: int shows
  "set_bit x (numeral w) b = set_bit (bin_rest x) (pred_numeral w) b BIT bin_last x"
by(simp add: set_bit_int_def)

lemmas int_set_bit_numerals [simp] =
  int_set_bit_numeral[where x="numeral w'"] 
  int_set_bit_numeral[where x="- numeral w'"]
  int_set_bit_numeral[where x="Numeral1"]
  int_set_bit_numeral[where x="1"]
  int_set_bit_numeral[where x="0"]
  int_set_bit_Suc[where x="numeral w'"]
  int_set_bit_Suc[where x="- numeral w'"]
  int_set_bit_Suc[where x="Numeral1"]
  int_set_bit_Suc[where x="1"]
  int_set_bit_Suc[where x="0"]
  for w'

lemma int_shiftl_BIT: fixes x :: int
  shows int_shiftl0 [simp]: "x << 0 = x"
  and int_shiftl_Suc [simp]: "x << Suc n = (x << n) BIT False"
by(auto simp add: shiftl_int_def Bit_def)

lemma int_0_shiftl [simp]: "0 << n = (0 :: int)"
by(induct n) simp_all

lemma bin_last_shiftl: "bin_last (x << n) \<longleftrightarrow> n = 0 \<and> bin_last x"
by(cases n)(simp_all)

lemma bin_rest_shiftl: "bin_rest (x << n) = (if n > 0 then x << (n - 1) else bin_rest x)"
by(cases n)(simp_all)

lemma bin_nth_shiftl [simp]: "bin_nth (x << n) m \<longleftrightarrow> n \<le> m \<and> bin_nth x (m - n)"
proof(induct n arbitrary: x m)
  case (Suc n)
  thus ?case by(cases m) simp_all
qed simp

lemma int_shiftr_BIT [simp]: fixes x :: int
  shows int_shiftr0: "x >> 0 = x"
  and int_shiftr_Suc: "x BIT b >> Suc n = x >> n"
proof -
  show "x >> 0 = x" by (simp add: shiftr_int_def)
  show "x BIT b >> Suc n = x >> n" by (cases b)
   (simp_all add: shiftr_int_def Bit_def add.commute pos_zdiv_mult_2)
qed

lemma bin_last_shiftr: "bin_last (x >> n) \<longleftrightarrow> x !! n"
proof(induct n arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust) simp
qed

lemma bin_rest_shiftr [simp]: "bin_rest (x >> n) = x >> Suc n"
proof(induct n arbitrary: x)
  case 0
  thus ?case by(cases x rule: bin_exhaust) auto
next
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust) auto
qed

lemma bin_nth_shiftr [simp]: "bin_nth (x >> n) m = bin_nth x (n + m)"
proof(induct n arbitrary: x m)
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust) simp_all
qed simp

lemma bin_nth_conv_AND:
  fixes x :: int shows 
  "bin_nth x n \<longleftrightarrow> x AND (1 << n) \<noteq> 0"
proof(induct n arbitrary: x)
  case 0 
  thus ?case by(simp add: int_and_1 bin_last_def)
next
  case (Suc n)
  thus ?case by(cases x rule: bin_exhaust)(simp_all add: bin_nth_ops Bit_eq_0_iff)
qed

lemma int_shiftl_numeral [simp]: 
  "(numeral w :: int) << numeral w' = numeral (num.Bit0 w) << pred_numeral w'"
  "(- numeral w :: int) << numeral w' = - numeral (num.Bit0 w) << pred_numeral w'"
by(simp_all add: numeral_eq_Suc Bit_def shiftl_int_def)
  (metis add_One mult_inc semiring_norm(11) semiring_norm(13) semiring_norm(2) semiring_norm(6) semiring_norm(87))+

lemma int_shiftl_One_numeral [simp]: "(1 :: int) << numeral w = 2 << pred_numeral w"
by(metis int_shiftl_numeral numeral_One)

lemma shiftl_ge_0 [simp]: fixes i :: int shows "i << n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
by(induct n) simp_all

lemma shiftl_lt_0 [simp]: fixes i :: int shows "i << n < 0 \<longleftrightarrow> i < 0"
by (metis not_le shiftl_ge_0)

lemma int_shiftl_test_bit: "(n << i :: int) !! m \<longleftrightarrow> m \<ge> i \<and> n !! (m - i)"
proof(induction i)
  case (Suc n)
  thus ?case by(cases m) simp_all
qed simp

lemma int_0shiftr [simp]: "(0 :: int) >> x = 0"
by(simp add: shiftr_int_def)

lemma int_minus1_shiftr [simp]: "(-1 :: int) >> x = -1"
by(simp add: shiftr_int_def div_eq_minus1)

lemma int_shiftr_ge_0 [simp]: fixes i :: int shows "i >> n \<ge> 0 \<longleftrightarrow> i \<ge> 0"
proof(induct n arbitrary: i)
  case (Suc n)
  thus ?case by(cases i rule: bin_exhaust) simp_all
qed simp

lemma int_shiftr_lt_0 [simp]: fixes i :: int shows "i >> n < 0 \<longleftrightarrow> i < 0"
by (metis int_shiftr_ge_0 not_less)

lemma int_shiftr_numeral [simp]:
  "(1 :: int) >> numeral w' = 0"
  "(numeral num.One :: int) >> numeral w' = 0"
  "(numeral (num.Bit0 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(numeral (num.Bit1 w) :: int) >> numeral w' = numeral w >> pred_numeral w'"
  "(- numeral (num.Bit0 w) :: int) >> numeral w' = - numeral w >> pred_numeral w'"
  "(- numeral (num.Bit1 w) :: int) >> numeral w' = - numeral (Num.inc w) >> pred_numeral w'"
  by (simp_all only: numeral_One expand_BIT numeral_eq_Suc int_shiftr_Suc BIT_special_simps(2)[symmetric] int_0shiftr add_One uminus_Bit_eq)
    (simp_all add: add_One)

lemma int_shiftr_numeral_Suc0 [simp]:
  "(1 :: int) >> Suc 0 = 0"
  "(numeral num.One :: int) >> Suc 0 = 0"
  "(numeral (num.Bit0 w) :: int) >> Suc 0 = numeral w"
  "(numeral (num.Bit1 w) :: int) >> Suc 0 = numeral w"
  "(- numeral (num.Bit0 w) :: int) >> Suc 0 = - numeral w"
  "(- numeral (num.Bit1 w) :: int) >> Suc 0 = - numeral (Num.inc w)"
by(simp_all only: One_nat_def[symmetric] numeral_One[symmetric] int_shiftr_numeral pred_numeral_simps int_shiftr0)

lemma bin_nth_minus_p2:
  assumes sign: "bin_sign x = 0"
  and y: "y = 1 << n"
  and m: "m < n"
  and x: "x < y"
  shows "bin_nth (x - y) m = bin_nth x m"
using sign m x unfolding y
proof(induction m arbitrary: x y n)
  case 0
  thus ?case
    by(simp add: bin_last_def shiftl_int_def) (metis (hide_lams, no_types) mod_diff_right_eq mod_self neq0_conv numeral_One power_eq_0_iff power_mod diff_zero zero_neq_numeral)
next
  case (Suc m)
  from \<open>Suc m < n\<close> obtain n' where [simp]: "n = Suc n'" by(cases n) auto
  obtain x' b where [simp]: "x = x' BIT b" by(cases x rule: bin_exhaust)
  from \<open>bin_sign x = 0\<close> have "bin_sign x' = 0" by simp
  moreover from \<open>x < 1 << n\<close> have "x' < 1 << n'"
    by(cases b)(simp_all add: Bit_def shiftl_int_def)
  moreover have "(2 * x' + of_bool b - 2 * 2 ^ n') div 2 = x' + (- (2 ^ n') + of_bool b div 2)"
    by(simp only: add_diff_eq[symmetric] add.commute div_mult_self2[OF zero_neq_numeral[symmetric]])
  ultimately show ?case using Suc.IH[of x' n'] Suc.prems
    by(cases b)(simp_all add: Bit_def bin_rest_def shiftl_int_def)
qed

lemma bin_clr_conv_NAND:
  "bin_sc n False i = i AND NOT (1 << n)"
by(induct n arbitrary: i)(auto intro: bin_rl_eqI)

lemma bin_set_conv_OR:
  "bin_sc n True i = i OR (1 << n)"
by(induct n arbitrary: i)(auto intro: bin_rl_eqI)

lemma msb_conv_bin_sign: "msb x \<longleftrightarrow> bin_sign x = -1"
by(simp add: bin_sign_def not_le msb_int_def)

lemma msb_BIT [simp]: "msb (x BIT b) = msb x"
by(simp add: msb_int_def)

lemma msb_bin_rest [simp]: "msb (bin_rest x) = msb x"
by(simp add: msb_int_def)

lemma int_msb_and [simp]: "msb ((x :: int) AND y) \<longleftrightarrow> msb x \<and> msb y"
by(simp add: msb_int_def)

lemma int_msb_or [simp]: "msb ((x :: int) OR y) \<longleftrightarrow> msb x \<or> msb y"
by(simp add: msb_int_def)

lemma int_msb_xor [simp]: "msb ((x :: int) XOR y) \<longleftrightarrow> msb x \<noteq> msb y"
by(simp add: msb_int_def)

lemma int_msb_not [simp]: "msb (NOT (x :: int)) \<longleftrightarrow> \<not> msb x"
by(simp add: msb_int_def not_less)

lemma msb_shiftl [simp]: "msb ((x :: int) << n) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_shiftr [simp]: "msb ((x :: int) >> r) \<longleftrightarrow> msb x"
by(simp add: msb_int_def)

lemma msb_bin_sc [simp]: "msb (bin_sc n b x) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign)

lemma msb_set_bit [simp]: "msb (set_bit (x :: int) n b) \<longleftrightarrow> msb x"
by(simp add: msb_conv_bin_sign set_bit_int_def)

lemma msb_0 [simp]: "msb (0 :: int) = False"
by(simp add: msb_int_def)

lemma msb_1 [simp]: "msb (1 :: int) = False"
by(simp add: msb_int_def)

lemma msb_numeral [simp]:
  "msb (numeral n :: int) = False"
  "msb (- numeral n :: int) = True"
by(simp_all add: msb_int_def)


subsection \<open>Semantic interpretation of \<^typ>\<open>bool list\<close> as \<^typ>\<open>int\<close>\<close>

lemma bin_bl_bin': "bl_to_bin (bin_to_bl_aux n w bs) = bl_to_bin_aux bs (bintrunc n w)"
  by (induct n arbitrary: w bs) (auto simp: bl_to_bin_def)

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
    apply auto
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
  by (induct bs arbitrary: w) auto

lemma sign_bl_bin: "bin_sign (bl_to_bin bs) = 0"
  by (simp add: bl_to_bin_def sign_bl_bin')

lemma bl_sbin_sign_aux: "hd (bin_to_bl_aux (Suc n) w bs) = (bin_sign (sbintrunc n w) = -1)"
  apply (induct n arbitrary: w bs)
   apply clarsimp
   apply (cases w rule: bin_exhaust)
   apply simp
  done

lemma bl_sbin_sign: "hd (bin_to_bl (Suc n) w) = (bin_sign (sbintrunc n w) = -1)"
  unfolding bin_to_bl_def by (rule bl_sbin_sign_aux)

lemma bin_nth_of_bl_aux:
  "bin_nth (bl_to_bin_aux bl w) n =
    (n < size bl \<and> rev bl ! n \<or> n \<ge> length bl \<and> bin_nth w (n - size bl))"
  apply (induct bl arbitrary: w)
   apply clarsimp
  apply clarsimp
  apply (cut_tac x=n and y="size bl" in linorder_less_linear)
  apply (erule disjE, simp add: nth_append)+
  apply auto
  done

lemma bin_nth_of_bl: "bin_nth (bl_to_bin bl) n = (n < length bl \<and> rev bl ! n)"
  by (simp add: bl_to_bin_def bin_nth_of_bl_aux)

lemma bin_nth_bl: "n < m \<Longrightarrow> bin_nth w n = nth (rev (bin_to_bl m w)) n"
  apply (induct n arbitrary: m w)
   apply clarsimp
   apply (case_tac m, clarsimp)
   apply (clarsimp simp: bin_to_bl_def)
   apply (simp add: bin_to_bl_aux_alt)
  apply clarsimp
  apply (case_tac m, clarsimp)
  apply (clarsimp simp: bin_to_bl_def)
  apply (simp add: bin_to_bl_aux_alt)
  done

lemma nth_bin_to_bl_aux:
  "n < m + length bl \<Longrightarrow> (bin_to_bl_aux m w bl) ! n =
    (if n < m then bin_nth w (m - 1 - n) else bl ! (n - m))"
  apply (induct m arbitrary: w n bl)
   apply clarsimp
  apply clarsimp
  apply (case_tac w rule: bin_exhaust)
  apply simp
  done

lemma nth_bin_to_bl: "n < m \<Longrightarrow> (bin_to_bl m w) ! n = bin_nth w (m - Suc n)"
  by (simp add: bin_to_bl_def nth_bin_to_bl_aux)

lemma bl_to_bin_lt2p_aux: "bl_to_bin_aux bs w < (w + 1) * (2 ^ length bs)"
  apply (induct bs arbitrary: w)
   apply clarsimp
  apply clarsimp
  apply (drule meta_spec, erule xtrans(8) [rotated], simp add: Bit_def)+
  done

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
  apply (induct bs arbitrary: w)
   apply clarsimp
  apply clarsimp
   apply (drule meta_spec, erule order_trans [rotated],
          simp add: Bit_B0_2t Bit_B1_2t algebra_simps)+
   apply (simp add: Bit_def)
  done

lemma bl_to_bin_ge0: "bl_to_bin bs \<ge> 0"
  apply (unfold bl_to_bin_def)
  apply (rule xtrans(4))
   apply (rule bl_to_bin_ge2p_aux)
  apply simp
  done

lemma butlast_rest_bin: "butlast (bin_to_bl n w) = bin_to_bl (n - 1) (bin_rest w)"
  apply (unfold bin_to_bl_def)
  apply (cases w rule: bin_exhaust)
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
    with Cons Suc show ?thesis by simp
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
  apply (induct n arbitrary: m bin bs, clarsimp)
  apply clarsimp
  apply (case_tac bin rule: bin_exhaust)
  apply (case_tac "m \<le> n", simp)
  apply (case_tac "m - n", simp)
  apply simp
  apply (rule_tac f = "\<lambda>nat. drop nat bs" in arg_cong)
  apply simp
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
  apply (simp add: take_bin2bl_lem)
  done

lemma bin_split_take1:
  "k = m + n \<Longrightarrow> bin_split n c = (a, b) \<Longrightarrow> bin_to_bl m a = take m (bin_to_bl k c)"
  by (auto elim: bin_split_take)

lemma takefill_bintrunc: "takefill False n bl = rev (bin_to_bl n (bl_to_bin (rev bl)))"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp: nth_takefill nth_rev nth_bin_to_bl bin_nth_of_bl)
  done

lemma bl_bin_bl_rtf: "bin_to_bl n (bl_to_bin bl) = rev (takefill False n (rev bl))"
  by (simp add: takefill_bintrunc)

lemma bl_bin_bl_rep_drop:
  "bin_to_bl n (bl_to_bin bl) =
    replicate (n - length bl) False @ drop (length bl - n) bl"
  by (simp add: bl_bin_bl_rtf takefill_alt rev_take)

lemma bl_to_bin_aux_cat:
  "\<And>nv v. bl_to_bin_aux bs (bin_cat w nv v) =
    bin_cat w (nv + length bs) (bl_to_bin_aux bs v)"
  by (induct bs) (simp, simp add: bin_cat_Suc_Bit [symmetric] del: bin_cat.simps)

lemma bin_to_bl_aux_cat:
  "\<And>w bs. bin_to_bl_aux (nv + nw) (bin_cat v nw w) bs =
    bin_to_bl_aux nv v (bin_to_bl_aux nw w bs)"
  by (induct nw) auto

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
  apply (simp add: Bit_B0_2t Bit_B1_2t)
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
  apply (unfold bin_to_bl_def)
  apply (induct n arbitrary: bin)
   apply simp
  apply clarsimp
  apply (case_tac bin rule: bin_exhaust)
  apply (case_tac b)
   apply (clarsimp simp: bin_to_bl_aux_alt)+
  done

lemma rbl_succ: "rbl_succ (rev (bin_to_bl n bin)) = rev (bin_to_bl n (bin + 1))"
  apply (unfold bin_to_bl_def)
  apply (induct n arbitrary: bin)
   apply simp
  apply clarsimp
  apply (case_tac bin rule: bin_exhaust)
  apply (case_tac b)
   apply (clarsimp simp: bin_to_bl_aux_alt)+
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

lemma rbbl_Cons: "b # rev (bin_to_bl n x) = rev (bin_to_bl (Suc n) (x BIT b))"
  by (simp add: bin_to_bl_def) (simp add: bin_to_bl_aux_alt)

lemma rbl_mult:
  "rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) =
    rev (bin_to_bl n (bina * binb))"
  apply (induct n arbitrary: bina binb)
   apply simp
  apply (unfold bin_to_bl_def)
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac binb rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] "ba")
     apply (auto simp: bin_to_bl_aux_alt Let_def)
     apply (auto simp: rbbl_Cons rbl_mult_Suc rbl_add)
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
  apply (induct n arbitrary: v w bs cs)
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  apply (case_tac b)
   apply auto
  done

lemma bl_or_aux_bin:
  "map2 (\<or>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v OR w) (map2 (\<or>) bs cs)"
  apply (induct n arbitrary: v w bs cs)
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  done

lemma bl_and_aux_bin:
  "map2 (\<and>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v AND w) (map2 (\<and>) bs cs)"
  apply (induct n arbitrary: v w bs cs)
   apply simp
  apply (case_tac v rule: bin_exhaust)
  apply (case_tac w rule: bin_exhaust)
  apply clarsimp
  done

lemma bl_not_aux_bin: "map Not (bin_to_bl_aux n w cs) = bin_to_bl_aux n (NOT w) (map Not cs)"
  by (induct n arbitrary: w cs) auto

lemma bl_not_bin: "map Not (bin_to_bl n w) = bin_to_bl n (NOT w)"
  by (simp add: bin_to_bl_def bl_not_aux_bin)

lemma bl_and_bin: "map2 (\<and>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v AND w)"
  by (simp add: bin_to_bl_def bl_and_aux_bin)

lemma bl_or_bin: "map2 (\<or>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v OR w)"
  by (simp add: bin_to_bl_def bl_or_aux_bin)

lemma bl_xor_bin: "map2 (\<lambda>x y. x \<noteq> y) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v XOR w)"
  by (simp only: bin_to_bl_def bl_xor_aux_bin map2_Nil)

end
