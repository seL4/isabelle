(* 
  Author: Jeremy Dawson, NICTA
*) 

section {* Integers as implict bit strings *}

theory Bit_Representation
imports Misc_Numeric
begin

subsection {* Constructors and destructors for binary integers *}

definition Bit :: "int \<Rightarrow> bool \<Rightarrow> int" (infixl "BIT" 90)
where
  "k BIT b = (if b then 1 else 0) + k + k"

lemma Bit_B0:
  "k BIT False = k + k"
   by (unfold Bit_def) simp

lemma Bit_B1:
  "k BIT True = k + k + 1"
   by (unfold Bit_def) simp
  
lemma Bit_B0_2t: "k BIT False = 2 * k"
  by (rule trans, rule Bit_B0) simp

lemma Bit_B1_2t: "k BIT True = 2 * k + 1"
  by (rule trans, rule Bit_B1) simp

definition bin_last :: "int \<Rightarrow> bool"
where
  "bin_last w \<longleftrightarrow> w mod 2 = 1"

lemma bin_last_odd:
  "bin_last = odd"
  by (rule ext) (simp add: bin_last_def even_iff_mod_2_eq_zero)

definition bin_rest :: "int \<Rightarrow> int"
where
  "bin_rest w = w div 2"

lemma bin_rl_simp [simp]:
  "bin_rest w BIT bin_last w = w"
  unfolding bin_rest_def bin_last_def Bit_def
  using mod_div_equality [of w 2]
  by (cases "w mod 2 = 0", simp_all)

lemma bin_rest_BIT [simp]: "bin_rest (x BIT b) = x"
  unfolding bin_rest_def Bit_def
  by (cases b, simp_all)

lemma bin_last_BIT [simp]: "bin_last (x BIT b) = b"
  unfolding bin_last_def Bit_def
  by (cases b) simp_all

lemma BIT_eq_iff [iff]: "u BIT b = v BIT c \<longleftrightarrow> u = v \<and> b = c"
  apply (auto simp add: Bit_def)
  apply arith
  apply arith
  done

lemma BIT_bin_simps [simp]:
  "numeral k BIT False = numeral (Num.Bit0 k)"
  "numeral k BIT True = numeral (Num.Bit1 k)"
  "(- numeral k) BIT False = - numeral (Num.Bit0 k)"
  "(- numeral k) BIT True = - numeral (Num.BitM k)"
  unfolding numeral.simps numeral_BitM
  unfolding Bit_def
  by (simp_all del: arith_simps add_numeral_special diff_numeral_special)

lemma BIT_special_simps [simp]:
  shows "0 BIT False = 0" and "0 BIT True = 1"
  and "1 BIT False = 2" and "1 BIT True = 3"
  and "(- 1) BIT False = - 2" and "(- 1) BIT True = - 1"
  unfolding Bit_def by simp_all

lemma Bit_eq_0_iff: "w BIT b = 0 \<longleftrightarrow> w = 0 \<and> \<not> b"
  apply (auto simp add: Bit_def)
  apply arith
  done

lemma Bit_eq_m1_iff: "w BIT b = -1 \<longleftrightarrow> w = -1 \<and> b"
  apply (auto simp add: Bit_def)
  apply arith
  done

lemma BitM_inc: "Num.BitM (Num.inc w) = Num.Bit1 w"
  by (induct w, simp_all)

lemma expand_BIT:
  "numeral (Num.Bit0 w) = numeral w BIT False"
  "numeral (Num.Bit1 w) = numeral w BIT True"
  "- numeral (Num.Bit0 w) = (- numeral w) BIT False"
  "- numeral (Num.Bit1 w) = (- numeral (w + Num.One)) BIT True"
  unfolding add_One by (simp_all add: BitM_inc)

lemma bin_last_numeral_simps [simp]:
  "\<not> bin_last 0"
  "bin_last 1"
  "bin_last (- 1)"
  "bin_last Numeral1"
  "\<not> bin_last (numeral (Num.Bit0 w))"
  "bin_last (numeral (Num.Bit1 w))"
  "\<not> bin_last (- numeral (Num.Bit0 w))"
  "bin_last (- numeral (Num.Bit1 w))"
  unfolding expand_BIT bin_last_BIT by (simp_all add: bin_last_def zmod_zminus1_eq_if)

lemma bin_rest_numeral_simps [simp]:
  "bin_rest 0 = 0"
  "bin_rest 1 = 0"
  "bin_rest (- 1) = - 1"
  "bin_rest Numeral1 = 0"
  "bin_rest (numeral (Num.Bit0 w)) = numeral w"
  "bin_rest (numeral (Num.Bit1 w)) = numeral w"
  "bin_rest (- numeral (Num.Bit0 w)) = - numeral w"
  "bin_rest (- numeral (Num.Bit1 w)) = - numeral (w + Num.One)"
  unfolding expand_BIT bin_rest_BIT by (simp_all add: bin_rest_def zdiv_zminus1_eq_if)

lemma less_Bits: 
  "v BIT b < w BIT c \<longleftrightarrow> v < w \<or> v \<le> w \<and> \<not> b \<and> c"
  unfolding Bit_def by auto

lemma le_Bits: 
  "v BIT b \<le> w BIT c \<longleftrightarrow> v < w \<or> v \<le> w \<and> (\<not> b \<or> c)" 
  unfolding Bit_def by auto

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

lemma B_mod_2': 
  "X = 2 ==> (w BIT True) mod X = 1 & (w BIT False) mod X = 0"
  apply (simp (no_asm) only: Bit_B0 Bit_B1)
  apply simp
  done

lemma bin_ex_rl: "EX w b. w BIT b = bin"
  by (metis bin_rl_simp)

lemma bin_exhaust:
  assumes Q: "\<And>x b. bin = x BIT b \<Longrightarrow> Q"
  shows "Q"
  apply (insert bin_ex_rl [of bin])  
  apply (erule exE)+
  apply (rule Q)
  apply force
  done

primrec bin_nth where
  Z: "bin_nth w 0 \<longleftrightarrow> bin_last w"
  | Suc: "bin_nth w (Suc n) \<longleftrightarrow> bin_nth (bin_rest w) n"

lemma bin_abs_lem:
  "bin = (w BIT b) ==> bin ~= -1 --> bin ~= 0 -->
    nat (abs w) < nat (abs bin)"
  apply clarsimp
  apply (unfold Bit_def)
  apply (cases b)
   apply (clarsimp, arith)
  apply (clarsimp, arith)
  done

lemma bin_induct:
  assumes PPls: "P 0"
    and PMin: "P (- 1)"
    and PBit: "!!bin bit. P bin ==> P (bin BIT bit)"
  shows "P bin"
  apply (rule_tac P=P and a=bin and f1="nat o abs" 
                  in wf_measure [THEN wf_induct])
  apply (simp add: measure_def inv_image_def)
  apply (case_tac x rule: bin_exhaust)
  apply (frule bin_abs_lem)
  apply (auto simp add : PPls PMin PBit)
  done

lemma Bit_div2 [simp]: "(w BIT b) div 2 = w"
  unfolding bin_rest_def [symmetric] by (rule bin_rest_BIT)

lemma bin_nth_eq_iff:
  "bin_nth x = bin_nth y \<longleftrightarrow> x = y"
proof -
  have bin_nth_lem [rule_format]: "ALL y. bin_nth x = bin_nth y --> x = y"
    apply (induct x rule: bin_induct)
      apply safe
      apply (erule rev_mp)
      apply (induct_tac y rule: bin_induct)
        apply safe
        apply (drule_tac x=0 in fun_cong, force)
       apply (erule notE, rule ext, 
            drule_tac x="Suc x" in fun_cong, force)
      apply (drule_tac x=0 in fun_cong, force)
     apply (erule rev_mp)
     apply (induct_tac y rule: bin_induct)
       apply safe
       apply (drule_tac x=0 in fun_cong, force)
      apply (erule notE, rule ext, 
           drule_tac x="Suc x" in fun_cong, force)
      apply (metis Bit_eq_m1_iff Z bin_last_BIT)
    apply (case_tac y rule: bin_exhaust)
    apply clarify
    apply (erule allE)
    apply (erule impE)
     prefer 2
     apply (erule conjI)
     apply (drule_tac x=0 in fun_cong, force)
    apply (rule ext)
    apply (drule_tac x="Suc ?x" in fun_cong, force)
    done
  show ?thesis
  by (auto elim: bin_nth_lem)
qed

lemmas bin_eqI = ext [THEN bin_nth_eq_iff [THEN iffD1]]

lemma bin_eq_iff:
  "x = y \<longleftrightarrow> (\<forall>n. bin_nth x n = bin_nth y n)"
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

lemma bin_nth_minus [simp]: "0 < n ==> bin_nth (w BIT b) n = bin_nth w (n - 1)"
  by (cases n) auto

lemma bin_nth_numeral:
  "bin_rest x = y \<Longrightarrow> bin_nth x (numeral n) = bin_nth y (pred_numeral n)"
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


subsection {* Truncating binary integers *}

definition bin_sign :: "int \<Rightarrow> int"
where
  bin_sign_def: "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign 0 = 0"
  "bin_sign 1 = 0"
  "bin_sign (- 1) = - 1"
  "bin_sign (numeral k) = 0"
  "bin_sign (- numeral k) = -1"
  "bin_sign (w BIT b) = bin_sign w"
  unfolding bin_sign_def Bit_def
  by simp_all

lemma bin_sign_rest [simp]: 
  "bin_sign (bin_rest w) = bin_sign w"
  by (cases w rule: bin_exhaust) auto

primrec bintrunc :: "nat \<Rightarrow> int \<Rightarrow> int" where
  Z : "bintrunc 0 bin = 0"
| Suc : "bintrunc (Suc n) bin = bintrunc n (bin_rest bin) BIT (bin_last bin)"

primrec sbintrunc :: "nat => int => int" where
  Z : "sbintrunc 0 bin = (if bin_last bin then -1 else 0)"
| Suc : "sbintrunc (Suc n) bin = sbintrunc n (bin_rest bin) BIT (bin_last bin)"

lemma sign_bintr: "bin_sign (bintrunc n w) = 0"
  by (induct n arbitrary: w) auto

lemma bintrunc_mod2p: "bintrunc n w = (w mod 2 ^ n)"
  apply (induct n arbitrary: w, clarsimp)
  apply (simp add: bin_last_def bin_rest_def Bit_def zmod_zmult2_eq)
  done

lemma sbintrunc_mod2p: "sbintrunc n w = (w + 2 ^ n) mod 2 ^ (Suc n) - 2 ^ n"
  apply (induct n arbitrary: w)
   apply simp
   apply (subst mod_add_left_eq)
   apply (simp add: bin_last_def)
   apply arith
  apply (simp add: bin_last_def bin_rest_def Bit_def)
  apply (clarsimp simp: mod_mult_mult1 [symmetric] 
         zmod_zdiv_equality [THEN diff_eq_eq [THEN iffD2 [THEN sym]]])
  apply (rule trans [symmetric, OF _ emep1])
  apply auto
  done

subsection "Simplifications for (s)bintrunc"

lemma bintrunc_n_0 [simp]: "bintrunc n 0 = 0"
  by (induct n) auto

lemma sbintrunc_n_0 [simp]: "sbintrunc n 0 = 0"
  by (induct n) auto

lemma sbintrunc_n_minus1 [simp]: "sbintrunc n (- 1) = -1"
  by (induct n) auto

lemma bintrunc_Suc_numeral:
  "bintrunc (Suc n) 1 = 1"
  "bintrunc (Suc n) (- 1) = bintrunc n (- 1) BIT True"
  "bintrunc (Suc n) (numeral (Num.Bit0 w)) = bintrunc n (numeral w) BIT False"
  "bintrunc (Suc n) (numeral (Num.Bit1 w)) = bintrunc n (numeral w) BIT True"
  "bintrunc (Suc n) (- numeral (Num.Bit0 w)) =
    bintrunc n (- numeral w) BIT False"
  "bintrunc (Suc n) (- numeral (Num.Bit1 w)) =
    bintrunc n (- numeral (w + Num.One)) BIT True"
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
  "sbintrunc (Suc n) (numeral (Num.Bit0 w)) =
    sbintrunc n (numeral w) BIT False"
  "sbintrunc (Suc n) (numeral (Num.Bit1 w)) =
    sbintrunc n (numeral w) BIT True"
  "sbintrunc (Suc n) (- numeral (Num.Bit0 w)) =
    sbintrunc n (- numeral w) BIT False"
  "sbintrunc (Suc n) (- numeral (Num.Bit1 w)) =
    sbintrunc n (- numeral (w + Num.One)) BIT True"
  by simp_all

lemma bin_sign_lem: "(bin_sign (sbintrunc n bin) = -1) = bin_nth bin n"
  apply (induct n arbitrary: bin)
  apply (case_tac bin rule: bin_exhaust, case_tac b, auto)
  done

lemma nth_bintr: "bin_nth (bintrunc m w) n = (n < m & bin_nth w n)"
  apply (induct n arbitrary: w m)
   apply (case_tac m, auto)[1]
  apply (case_tac m, auto)[1]
  done

lemma nth_sbintr:
  "bin_nth (sbintrunc m w) n = 
          (if n < m then bin_nth w n else bin_nth w m)"
  apply (induct n arbitrary: w m)
  apply (case_tac m)
  apply simp_all
  apply (case_tac m)
  apply simp_all
  done

lemma bin_nth_Bit:
  "bin_nth (w BIT b) n = (n = 0 & b | (EX m. n = Suc m & bin_nth w m))"
  by (cases n) auto

lemma bin_nth_Bit0:
  "bin_nth (numeral (Num.Bit0 w)) n \<longleftrightarrow>
    (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bin_nth_Bit [where w="numeral w" and b="False"] by simp

lemma bin_nth_Bit1:
  "bin_nth (numeral (Num.Bit1 w)) n \<longleftrightarrow>
    n = 0 \<or> (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bin_nth_Bit [where w="numeral w" and b="True"] by simp

lemma bintrunc_bintrunc_l:
  "n <= m ==> (bintrunc m (bintrunc n w) = bintrunc n w)"
  by (rule bin_eqI) (auto simp add : nth_bintr)

lemma sbintrunc_sbintrunc_l:
  "n <= m ==> (sbintrunc m (sbintrunc n w) = sbintrunc n w)"
  by (rule bin_eqI) (auto simp: nth_sbintr)

lemma bintrunc_bintrunc_ge:
  "n <= m ==> (bintrunc n (bintrunc m w) = bintrunc n w)"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma bintrunc_bintrunc_min [simp]:
  "bintrunc m (bintrunc n w) = bintrunc (min m n) w"
  apply (rule bin_eqI)
  apply (auto simp: nth_bintr)
  done

lemma sbintrunc_sbintrunc_min [simp]:
  "sbintrunc m (sbintrunc n w) = sbintrunc (min m n) w"
  apply (rule bin_eqI)
  apply (auto simp: nth_sbintr min.absorb1 min.absorb2)
  done

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
  sbintrunc.Z [where bin="0", 
               simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_Min = 
  sbintrunc.Z [where bin="-1",
               simplified bin_last_numeral_simps bin_rest_numeral_simps]

lemmas sbintrunc_0_BIT_B0 [simp] = 
  sbintrunc.Z [where bin="w BIT False", 
               simplified bin_last_numeral_simps bin_rest_numeral_simps] for w

lemmas sbintrunc_0_BIT_B1 [simp] = 
  sbintrunc.Z [where bin="w BIT True", 
               simplified bin_last_BIT bin_rest_numeral_simps] for w

lemmas sbintrunc_0_simps =
  sbintrunc_Pls sbintrunc_Min sbintrunc_0_BIT_B0 sbintrunc_0_BIT_B1

lemmas bintrunc_simps = bintrunc.Z bintrunc_Sucs
lemmas sbintrunc_simps = sbintrunc_0_simps sbintrunc_Sucs

lemma bintrunc_minus:
  "0 < n ==> bintrunc (Suc (n - 1)) w = bintrunc n w"
  by auto

lemma sbintrunc_minus:
  "0 < n ==> sbintrunc (Suc (n - 1)) w = sbintrunc n w"
  by auto

lemmas bintrunc_minus_simps = 
  bintrunc_Sucs [THEN [2] bintrunc_minus [symmetric, THEN trans]]
lemmas sbintrunc_minus_simps = 
  sbintrunc_Sucs [THEN [2] sbintrunc_minus [symmetric, THEN trans]]

lemmas thobini1 = arg_cong [where f = "%w. w BIT b"] for b

lemmas bintrunc_BIT_I = trans [OF bintrunc_BIT thobini1]
lemmas bintrunc_Min_I = trans [OF bintrunc_Min thobini1]

lemmas bmsts = bintrunc_minus_simps(1-3) [THEN thobini1 [THEN [2] trans]]
lemmas bintrunc_Pls_minus_I = bmsts(1)
lemmas bintrunc_Min_minus_I = bmsts(2)
lemmas bintrunc_BIT_minus_I = bmsts(3)

lemma bintrunc_Suc_lem:
  "bintrunc (Suc n) x = y ==> m = Suc n ==> bintrunc m x = y"
  by auto

lemmas bintrunc_Suc_Ialts = 
  bintrunc_Min_I [THEN bintrunc_Suc_lem]
  bintrunc_BIT_I [THEN bintrunc_Suc_lem]

lemmas sbintrunc_BIT_I = trans [OF sbintrunc_Suc_BIT thobini1]

lemmas sbintrunc_Suc_Is = 
  sbintrunc_Sucs(1-3) [THEN thobini1 [THEN [2] trans]]

lemmas sbintrunc_Suc_minus_Is = 
  sbintrunc_minus_simps(1-3) [THEN thobini1 [THEN [2] trans]]

lemma sbintrunc_Suc_lem:
  "sbintrunc (Suc n) x = y ==> m = Suc n ==> sbintrunc m x = y"
  by auto

lemmas sbintrunc_Suc_Ialts = 
  sbintrunc_Suc_Is [THEN sbintrunc_Suc_lem]

lemma sbintrunc_bintrunc_lt:
  "m > n ==> sbintrunc n (bintrunc m w) = sbintrunc n w"
  by (rule bin_eqI) (auto simp: nth_sbintr nth_bintr)

lemma bintrunc_sbintrunc_le:
  "m <= Suc n ==> bintrunc m (sbintrunc n w) = bintrunc m w"
  apply (rule bin_eqI)
  apply (auto simp: nth_sbintr nth_bintr)
   apply (subgoal_tac "x=n", safe, arith+)[1]
  apply (subgoal_tac "x=n", safe, arith+)[1]
  done

lemmas bintrunc_sbintrunc [simp] = order_refl [THEN bintrunc_sbintrunc_le]
lemmas sbintrunc_bintrunc [simp] = lessI [THEN sbintrunc_bintrunc_lt]
lemmas bintrunc_bintrunc [simp] = order_refl [THEN bintrunc_bintrunc_l]
lemmas sbintrunc_sbintrunc [simp] = order_refl [THEN sbintrunc_sbintrunc_l] 

lemma bintrunc_sbintrunc' [simp]:
  "0 < n \<Longrightarrow> bintrunc n (sbintrunc (n - 1) w) = bintrunc n w"
  by (cases n) (auto simp del: bintrunc.Suc)

lemma sbintrunc_bintrunc' [simp]:
  "0 < n \<Longrightarrow> sbintrunc (n - 1) (bintrunc n w) = sbintrunc (n - 1) w"
  by (cases n) (auto simp del: bintrunc.Suc)

lemma bin_sbin_eq_iff: 
  "bintrunc (Suc n) x = bintrunc (Suc n) y <-> 
   sbintrunc n x = sbintrunc n y"
  apply (rule iffI)
   apply (rule box_equals [OF _ sbintrunc_bintrunc sbintrunc_bintrunc])
   apply simp
  apply (rule box_equals [OF _ bintrunc_sbintrunc bintrunc_sbintrunc])
  apply simp
  done

lemma bin_sbin_eq_iff':
  "0 < n \<Longrightarrow> bintrunc n x = bintrunc n y <-> 
            sbintrunc (n - 1) x = sbintrunc (n - 1) y"
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
  "bintrunc (numeral k) x =
    bintrunc (pred_numeral k) (bin_rest x) BIT bin_last x"
  by (simp add: numeral_eq_Suc)

lemma sbintrunc_numeral:
  "sbintrunc (numeral k) x =
    sbintrunc (pred_numeral k) (bin_rest x) BIT bin_last x"
  by (simp add: numeral_eq_Suc)

lemma bintrunc_numeral_simps [simp]:
  "bintrunc (numeral k) (numeral (Num.Bit0 w)) =
    bintrunc (pred_numeral k) (numeral w) BIT False"
  "bintrunc (numeral k) (numeral (Num.Bit1 w)) =
    bintrunc (pred_numeral k) (numeral w) BIT True"
  "bintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    bintrunc (pred_numeral k) (- numeral w) BIT False"
  "bintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    bintrunc (pred_numeral k) (- numeral (w + Num.One)) BIT True"
  "bintrunc (numeral k) 1 = 1"
  by (simp_all add: bintrunc_numeral)

lemma sbintrunc_numeral_simps [simp]:
  "sbintrunc (numeral k) (numeral (Num.Bit0 w)) =
    sbintrunc (pred_numeral k) (numeral w) BIT False"
  "sbintrunc (numeral k) (numeral (Num.Bit1 w)) =
    sbintrunc (pred_numeral k) (numeral w) BIT True"
  "sbintrunc (numeral k) (- numeral (Num.Bit0 w)) =
    sbintrunc (pred_numeral k) (- numeral w) BIT False"
  "sbintrunc (numeral k) (- numeral (Num.Bit1 w)) =
    sbintrunc (pred_numeral k) (- numeral (w + Num.One)) BIT True"
  "sbintrunc (numeral k) 1 = 1"
  by (simp_all add: sbintrunc_numeral)

lemma no_bintr_alt1: "bintrunc n = (\<lambda>w. w mod 2 ^ n :: int)"
  by (rule ext) (rule bintrunc_mod2p)

lemma range_bintrunc: "range (bintrunc n) = {i. 0 <= i & i < 2 ^ n}"
  apply (unfold no_bintr_alt1)
  apply (auto simp add: image_iff)
  apply (rule exI)
  apply (auto intro: int_mod_lem [THEN iffD1, symmetric])
  done

lemma no_sbintr_alt2: 
  "sbintrunc n = (%w. (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (rule ext) (simp add : sbintrunc_mod2p)

lemma range_sbintrunc: 
  "range (sbintrunc n) = {i. - (2 ^ n) <= i & i < 2 ^ n}"
  apply (unfold no_sbintr_alt2)
  apply (auto simp add: image_iff eq_diff_eq)
  apply (rule exI)
  apply (auto intro: int_mod_lem [THEN iffD1, symmetric])
  done

lemma sb_inc_lem:
  "(a::int) + 2^k < 0 \<Longrightarrow> a + 2^k + 2^(Suc k) <= (a + 2^k) mod 2^(Suc k)"
  apply (erule int_mod_ge' [where n = "2 ^ (Suc k)" and b = "a + 2 ^ k", simplified zless2p])
  apply (rule TrueI)
  done

lemma sb_inc_lem':
  "(a::int) < - (2^k) \<Longrightarrow> a + 2^k + 2^(Suc k) <= (a + 2^k) mod 2^(Suc k)"
  by (rule sb_inc_lem) simp

lemma sbintrunc_inc:
  "x < - (2^n) ==> x + 2^(Suc n) <= sbintrunc n x"
  unfolding no_sbintr_alt2 by (drule sb_inc_lem') simp

lemma sb_dec_lem:
  "(0::int) \<le> - (2 ^ k) + a \<Longrightarrow> (a + 2 ^ k) mod (2 * 2 ^ k) \<le> - (2 ^ k) + a"
  using int_mod_le'[where n = "2 ^ (Suc k)" and b = "a + 2 ^ k"] by simp

lemma sb_dec_lem':
  "(2::int) ^ k \<le> a \<Longrightarrow> (a + 2 ^ k) mod (2 * 2 ^ k) \<le> - (2 ^ k) + a"
  by (rule sb_dec_lem) simp

lemma sbintrunc_dec:
  "x >= (2 ^ n) ==> x - 2 ^ (Suc n) >= sbintrunc n x"
  unfolding no_sbintr_alt2 by (drule sb_dec_lem') simp

lemmas zmod_uminus' = zminus_zmod [where m=c] for c
lemmas zpower_zmod' = power_mod [where b=c and n=k] for c k

lemmas brdmod1s' [symmetric] =
  mod_add_left_eq mod_add_right_eq
  mod_diff_left_eq mod_diff_right_eq
  mod_mult_left_eq mod_mult_right_eq

lemmas brdmods' [symmetric] = 
  zpower_zmod' [symmetric]
  trans [OF mod_add_left_eq mod_add_right_eq] 
  trans [OF mod_diff_left_eq mod_diff_right_eq] 
  trans [OF mod_mult_right_eq mod_mult_left_eq] 
  zmod_uminus' [symmetric]
  mod_add_left_eq [where b = "1::int"]
  mod_diff_left_eq [where b = "1::int"]

lemmas bintr_arith1s =
  brdmod1s' [where c="2^n::int", folded bintrunc_mod2p] for n
lemmas bintr_ariths =
  brdmods' [where c="2^n::int", folded bintrunc_mod2p] for n

lemmas m2pths = pos_mod_sign pos_mod_bound [OF zless2p]

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

lemma sign_Pls_ge_0: 
  "(bin_sign bin = 0) = (bin >= (0 :: int))"
  unfolding bin_sign_def by simp

lemma sign_Min_lt_0: 
  "(bin_sign bin = -1) = (bin < (0 :: int))"
  unfolding bin_sign_def by simp

lemma bin_rest_trunc:
  "(bin_rest (bintrunc n bin)) = bintrunc (n - 1) (bin_rest bin)"
  by (induct n arbitrary: bin) auto

lemma bin_rest_power_trunc:
  "(bin_rest ^^ k) (bintrunc n bin) = 
    bintrunc (n - k) ((bin_rest ^^ k) bin)"
  by (induct k) (auto simp: bin_rest_trunc)

lemma bin_rest_trunc_i:
  "bintrunc n (bin_rest bin) = bin_rest (bintrunc (Suc n) bin)"
  by auto

lemma bin_rest_strunc:
  "bin_rest (sbintrunc (Suc n) bin) = sbintrunc n (bin_rest bin)"
  by (induct n arbitrary: bin) auto

lemma bintrunc_rest [simp]: 
  "bintrunc n (bin_rest (bintrunc n bin)) = bin_rest (bintrunc n bin)"
  apply (induct n arbitrary: bin, simp)
  apply (case_tac bin rule: bin_exhaust)
  apply (auto simp: bintrunc_bintrunc_l)
  done

lemma sbintrunc_rest [simp]:
  "sbintrunc n (bin_rest (sbintrunc n bin)) = bin_rest (sbintrunc n bin)"
  apply (induct n arbitrary: bin, simp)
  apply (case_tac bin rule: bin_exhaust)
  apply (auto simp: bintrunc_bintrunc_l split: bool.splits)
  done

lemma bintrunc_rest':
  "bintrunc n o bin_rest o bintrunc n = bin_rest o bintrunc n"
  by (rule ext) auto

lemma sbintrunc_rest' :
  "sbintrunc n o bin_rest o sbintrunc n = bin_rest o sbintrunc n"
  by (rule ext) auto

lemma rco_lem:
  "f o g o f = g o f ==> f o (g o f) ^^ n = g ^^ n o f"
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

  
subsection {* Splitting and concatenation *}

primrec bin_split :: "nat \<Rightarrow> int \<Rightarrow> int \<times> int" where
  Z: "bin_split 0 w = (w, 0)"
  | Suc: "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w)
        in (w1, w2 BIT bin_last w))"

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w) in (w1, w2 BIT bin_last w))"
  "bin_split 0 w = (w, 0)"
  by simp_all

primrec bin_cat :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  Z: "bin_cat w 0 v = w"
  | Suc: "bin_cat w (Suc n) v = bin_cat w n (bin_rest v) BIT bin_last v"

end

