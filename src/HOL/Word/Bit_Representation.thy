(* 
  Author: Jeremy Dawson, NICTA

  Basic definitions to do with integers, expressed using Pls, Min, BIT.
*) 

header {* Basic Definitions for Binary Integers *}

theory Bit_Representation
imports Misc_Numeric "~~/src/HOL/Library/Bit"
begin

subsection {* Further properties of numerals *}

definition bitval :: "bit \<Rightarrow> 'a\<Colon>zero_neq_one" where
  "bitval = bit_case 0 1"

lemma bitval_simps [simp]:
  "bitval 0 = 0"
  "bitval 1 = 1"
  by (simp_all add: bitval_def)

definition Bit :: "int \<Rightarrow> bit \<Rightarrow> int" (infixl "BIT" 90) where
  "k BIT b = bitval b + k + k"

definition bin_last :: "int \<Rightarrow> bit" where
  "bin_last w = (if w mod 2 = 0 then (0::bit) else (1::bit))"

definition bin_rest :: "int \<Rightarrow> int" where
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
  by (cases b, simp_all add: z1pmod2)

lemma BIT_eq_iff [iff]: "u BIT b = v BIT c \<longleftrightarrow> u = v \<and> b = c"
  by (metis bin_rest_BIT bin_last_BIT)

lemma BIT_bin_simps [simp]:
  "numeral k BIT 0 = numeral (Num.Bit0 k)"
  "numeral k BIT 1 = numeral (Num.Bit1 k)"
  "neg_numeral k BIT 0 = neg_numeral (Num.Bit0 k)"
  "neg_numeral k BIT 1 = neg_numeral (Num.BitM k)"
  unfolding neg_numeral_def numeral.simps numeral_BitM
  unfolding Bit_def bitval_simps
  by (simp_all del: arith_simps add_numeral_special diff_numeral_special)

lemma BIT_special_simps [simp]:
  shows "0 BIT 0 = 0" and "0 BIT 1 = 1" and "1 BIT 0 = 2" and "1 BIT 1 = 3"
  unfolding Bit_def by simp_all

lemma BitM_inc: "Num.BitM (Num.inc w) = Num.Bit1 w"
  by (induct w, simp_all)

lemma expand_BIT:
  "numeral (Num.Bit0 w) = numeral w BIT 0"
  "numeral (Num.Bit1 w) = numeral w BIT 1"
  "neg_numeral (Num.Bit0 w) = neg_numeral w BIT 0"
  "neg_numeral (Num.Bit1 w) = neg_numeral (w + Num.One) BIT 1"
  unfolding add_One by (simp_all add: BitM_inc)

lemma bin_last_numeral_simps [simp]:
  "bin_last 0 = 0"
  "bin_last 1 = 1"
  "bin_last -1 = 1"
  "bin_last Numeral1 = 1"
  "bin_last (numeral (Num.Bit0 w)) = 0"
  "bin_last (numeral (Num.Bit1 w)) = 1"
  "bin_last (neg_numeral (Num.Bit0 w)) = 0"
  "bin_last (neg_numeral (Num.Bit1 w)) = 1"
  unfolding expand_BIT bin_last_BIT by (simp_all add: bin_last_def)

lemma bin_rest_numeral_simps [simp]:
  "bin_rest 0 = 0"
  "bin_rest 1 = 0"
  "bin_rest -1 = -1"
  "bin_rest Numeral1 = 0"
  "bin_rest (numeral (Num.Bit0 w)) = numeral w"
  "bin_rest (numeral (Num.Bit1 w)) = numeral w"
  "bin_rest (neg_numeral (Num.Bit0 w)) = neg_numeral w"
  "bin_rest (neg_numeral (Num.Bit1 w)) = neg_numeral (w + Num.One)"
  unfolding expand_BIT bin_rest_BIT by (simp_all add: bin_rest_def)

lemma less_Bits: 
  "(v BIT b < w BIT c) = (v < w | v <= w & b = (0::bit) & c = (1::bit))"
  unfolding Bit_def by (auto simp add: bitval_def split: bit.split)

lemma le_Bits: 
  "(v BIT b <= w BIT c) = (v < w | v <= w & (b ~= (1::bit) | c ~= (0::bit)))" 
  unfolding Bit_def by (auto simp add: bitval_def split: bit.split)

lemma Bit_B0:
  "k BIT (0::bit) = k + k"
   by (unfold Bit_def) simp

lemma Bit_B1:
  "k BIT (1::bit) = k + k + 1"
   by (unfold Bit_def) simp
  
lemma Bit_B0_2t: "k BIT (0::bit) = 2 * k"
  by (rule trans, rule Bit_B0) simp

lemma Bit_B1_2t: "k BIT (1::bit) = 2 * k + 1"
  by (rule trans, rule Bit_B1) simp

lemma B_mod_2': 
  "X = 2 ==> (w BIT (1::bit)) mod X = 1 & (w BIT (0::bit)) mod X = 0"
  apply (simp (no_asm) only: Bit_B0 Bit_B1)
  apply (simp add: z1pmod2)
  done

lemma neB1E [elim!]:
  assumes ne: "y \<noteq> (1::bit)"
  assumes y: "y = (0::bit) \<Longrightarrow> P"
  shows "P"
  apply (rule y)
  apply (cases y rule: bit.exhaust, simp)
  apply (simp add: ne)
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


subsection {* Destructors for binary integers *}

primrec bin_nth where
  Z: "bin_nth w 0 = (bin_last w = (1::bit))"
  | Suc: "bin_nth w (Suc n) = bin_nth (bin_rest w) n"

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
    and PMin: "P -1"
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

lemma bin_nth_lem [rule_format]:
  "ALL y. bin_nth x = bin_nth y --> x = y"
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
   apply (drule_tac x=0 in fun_cong, force)
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

lemma bin_nth_eq_iff: "(bin_nth x = bin_nth y) = (x = y)"
  by (auto elim: bin_nth_lem)

lemmas bin_eqI = ext [THEN bin_nth_eq_iff [THEN iffD1]]

lemma bin_eq_iff: "x = y \<longleftrightarrow> (\<forall>n. bin_nth x n = bin_nth y n)"
  by (auto intro!: bin_nth_lem del: equalityI)

lemma bin_nth_zero [simp]: "\<not> bin_nth 0 n"
  by (induct n) auto

lemma bin_nth_1 [simp]: "bin_nth 1 n \<longleftrightarrow> n = 0"
  by (cases n) simp_all

lemma bin_nth_minus1 [simp]: "bin_nth -1 n"
  by (induct n) auto

lemma bin_nth_0_BIT: "bin_nth (w BIT b) 0 = (b = (1::bit))"
  by auto

lemma bin_nth_Suc_BIT: "bin_nth (w BIT b) (Suc n) = bin_nth w n"
  by auto

lemma bin_nth_minus [simp]: "0 < n ==> bin_nth (w BIT b) n = bin_nth w (n - 1)"
  by (cases n) auto

lemma bin_nth_numeral:
  "bin_rest x = y \<Longrightarrow> bin_nth x (numeral n) = bin_nth y (numeral n - 1)"
  by (subst expand_Suc, simp only: bin_nth.simps)

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

definition bin_sign :: "int \<Rightarrow> int" where
  bin_sign_def: "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign 0 = 0"
  "bin_sign 1 = 0"
  "bin_sign (numeral k) = 0"
  "bin_sign (neg_numeral k) = -1"
  "bin_sign (w BIT b) = bin_sign w"
  unfolding bin_sign_def Bit_def bitval_def
  by (simp_all split: bit.split)

lemma bin_sign_rest [simp]: 
  "bin_sign (bin_rest w) = bin_sign w"
  by (cases w rule: bin_exhaust) auto

primrec bintrunc :: "nat \<Rightarrow> int \<Rightarrow> int" where
  Z : "bintrunc 0 bin = 0"
| Suc : "bintrunc (Suc n) bin = bintrunc n (bin_rest bin) BIT (bin_last bin)"

primrec sbintrunc :: "nat => int => int" where
  Z : "sbintrunc 0 bin = (case bin_last bin of (1::bit) \<Rightarrow> -1 | (0::bit) \<Rightarrow> 0)"
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
  apply (simp add: bin_last_def bin_rest_def Bit_def)
  apply (clarsimp simp: mod_mult_mult1 [symmetric] 
         zmod_zdiv_equality [THEN diff_eq_eq [THEN iffD2 [THEN sym]]])
  apply (rule trans [symmetric, OF _ emep1])
     apply auto
  apply (auto simp: even_def)
  done

subsection "Simplifications for (s)bintrunc"

lemma bintrunc_n_0 [simp]: "bintrunc n 0 = 0"
  by (induct n) auto

lemma sbintrunc_n_0 [simp]: "sbintrunc n 0 = 0"
  by (induct n) auto

lemma sbintrunc_n_minus1 [simp]: "sbintrunc n -1 = -1"
  by (induct n) auto

lemma bintrunc_Suc_numeral:
  "bintrunc (Suc n) 1 = 1"
  "bintrunc (Suc n) -1 = bintrunc n -1 BIT 1"
  "bintrunc (Suc n) (numeral (Num.Bit0 w)) = bintrunc n (numeral w) BIT 0"
  "bintrunc (Suc n) (numeral (Num.Bit1 w)) = bintrunc n (numeral w) BIT 1"
  "bintrunc (Suc n) (neg_numeral (Num.Bit0 w)) =
    bintrunc n (neg_numeral w) BIT 0"
  "bintrunc (Suc n) (neg_numeral (Num.Bit1 w)) =
    bintrunc n (neg_numeral (w + Num.One)) BIT 1"
  by simp_all

lemma sbintrunc_0_numeral [simp]:
  "sbintrunc 0 1 = -1"
  "sbintrunc 0 (numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (numeral (Num.Bit1 w)) = -1"
  "sbintrunc 0 (neg_numeral (Num.Bit0 w)) = 0"
  "sbintrunc 0 (neg_numeral (Num.Bit1 w)) = -1"
  by simp_all

lemma sbintrunc_Suc_numeral:
  "sbintrunc (Suc n) 1 = 1"
  "sbintrunc (Suc n) (numeral (Num.Bit0 w)) =
    sbintrunc n (numeral w) BIT 0"
  "sbintrunc (Suc n) (numeral (Num.Bit1 w)) =
    sbintrunc n (numeral w) BIT 1"
  "sbintrunc (Suc n) (neg_numeral (Num.Bit0 w)) =
    sbintrunc n (neg_numeral w) BIT 0"
  "sbintrunc (Suc n) (neg_numeral (Num.Bit1 w)) =
    sbintrunc n (neg_numeral (w + Num.One)) BIT 1"
  by simp_all

lemma bit_bool:
  "(b = (b' = (1::bit))) = (b' = (if b then (1::bit) else (0::bit)))"
  by (cases b') auto

lemmas bit_bool1 [simp] = refl [THEN bit_bool [THEN iffD1], symmetric]

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
   apply (case_tac m, simp_all split: bit.splits)[1]
  apply (case_tac m, simp_all split: bit.splits)[1]
  done

lemma bin_nth_Bit:
  "bin_nth (w BIT b) n = (n = 0 & b = (1::bit) | (EX m. n = Suc m & bin_nth w m))"
  by (cases n) auto

lemma bin_nth_Bit0:
  "bin_nth (numeral (Num.Bit0 w)) n \<longleftrightarrow>
    (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bin_nth_Bit [where w="numeral w" and b="(0::bit)"] by simp

lemma bin_nth_Bit1:
  "bin_nth (numeral (Num.Bit1 w)) n \<longleftrightarrow>
    n = 0 \<or> (\<exists>m. n = Suc m \<and> bin_nth (numeral w) m)"
  using bin_nth_Bit [where w="numeral w" and b="(1::bit)"] by simp

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
  apply (auto simp: nth_sbintr min_max.inf_absorb1 min_max.inf_absorb2)
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
               simplified bin_last_numeral_simps bin_rest_numeral_simps bit.simps]

lemmas sbintrunc_Min = 
  sbintrunc.Z [where bin="-1",
               simplified bin_last_numeral_simps bin_rest_numeral_simps bit.simps]

lemmas sbintrunc_0_BIT_B0 [simp] = 
  sbintrunc.Z [where bin="w BIT (0::bit)", 
               simplified bin_last_numeral_simps bin_rest_numeral_simps bit.simps] for w

lemmas sbintrunc_0_BIT_B1 [simp] = 
  sbintrunc.Z [where bin="w BIT (1::bit)", 
               simplified bin_last_BIT bin_rest_numeral_simps bit.simps] for w

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
    bintrunc (numeral k - 1) (bin_rest x) BIT bin_last x"
  by (subst expand_Suc, rule bintrunc.simps)

lemma sbintrunc_numeral:
  "sbintrunc (numeral k) x =
    sbintrunc (numeral k - 1) (bin_rest x) BIT bin_last x"
  by (subst expand_Suc, rule sbintrunc.simps)

lemma bintrunc_numeral_simps [simp]:
  "bintrunc (numeral k) (numeral (Num.Bit0 w)) =
    bintrunc (numeral k - 1) (numeral w) BIT 0"
  "bintrunc (numeral k) (numeral (Num.Bit1 w)) =
    bintrunc (numeral k - 1) (numeral w) BIT 1"
  "bintrunc (numeral k) (neg_numeral (Num.Bit0 w)) =
    bintrunc (numeral k - 1) (neg_numeral w) BIT 0"
  "bintrunc (numeral k) (neg_numeral (Num.Bit1 w)) =
    bintrunc (numeral k - 1) (neg_numeral (w + Num.One)) BIT 1"
  "bintrunc (numeral k) 1 = 1"
  by (simp_all add: bintrunc_numeral)

lemma sbintrunc_numeral_simps [simp]:
  "sbintrunc (numeral k) (numeral (Num.Bit0 w)) =
    sbintrunc (numeral k - 1) (numeral w) BIT 0"
  "sbintrunc (numeral k) (numeral (Num.Bit1 w)) =
    sbintrunc (numeral k - 1) (numeral w) BIT 1"
  "sbintrunc (numeral k) (neg_numeral (Num.Bit0 w)) =
    sbintrunc (numeral k - 1) (neg_numeral w) BIT 0"
  "sbintrunc (numeral k) (neg_numeral (Num.Bit1 w)) =
    sbintrunc (numeral k - 1) (neg_numeral (w + Num.One)) BIT 1"
  "sbintrunc (numeral k) 1 = 1"
  by (simp_all add: sbintrunc_numeral)

lemma no_bintr_alt1: "bintrunc n = (%w. w mod 2 ^ n :: int)"
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
  "(0::int) <= - (2^k) + a ==> (a + 2^k) mod (2 * 2 ^ k) <= - (2 ^ k) + a"
  by (rule int_mod_le' [where n = "2 ^ (Suc k)" and b = "a + 2 ^ k",
    simplified zless2p, OF _ TrueI, simplified])

lemma sb_dec_lem':
  "(2::int) ^ k <= a ==> (a + 2 ^ k) mod (2 * 2 ^ k) <= - (2 ^ k) + a"
  by (rule iffD1 [OF diff_le_eq', THEN sb_dec_lem, simplified])

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

lemma bintr_Min: "bintrunc n -1 = 2 ^ n - 1"
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

lemma bin_rest_power_trunc [rule_format] :
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
  apply (auto simp: bintrunc_bintrunc_l split: bit.splits)
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

lemma rco_alt: "(f o g) ^^ n o f = f o (g o f) ^^ n"
  apply (rule ext)
  apply (induct n)
   apply (simp_all add: o_def)
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

subsection {* Miscellaneous lemmas *}

lemma funpow_minus_simp:
  "0 < n \<Longrightarrow> f ^^ n = f \<circ> f ^^ (n - 1)"
  by (cases n) simp_all

lemma funpow_numeral [simp]:
  "f ^^ numeral k = f \<circ> f ^^ (numeral k - 1)"
  by (subst expand_Suc, rule funpow.simps)

lemma replicate_numeral [simp]: (* TODO: move to List.thy *)
  "replicate (numeral k) x = x # replicate (numeral k - 1) x"
  by (subst expand_Suc, rule replicate_Suc)

lemmas power_minus_simp = 
  trans [OF gen_minus [where f = "power f"] power_Suc] for f

lemma list_exhaust_size_gt0:
  assumes y: "\<And>a list. y = a # list \<Longrightarrow> P"
  shows "0 < length y \<Longrightarrow> P"
  apply (cases y, simp)
  apply (rule y)
  apply fastforce
  done

lemma list_exhaust_size_eq0:
  assumes y: "y = [] \<Longrightarrow> P"
  shows "length y = 0 \<Longrightarrow> P"
  apply (cases y)
   apply (rule y, simp)
  apply simp
  done

lemma size_Cons_lem_eq:
  "y = xa # list ==> size y = Suc k ==> size list = k"
  by auto

lemmas ls_splits = prod.split prod.split_asm split_if_asm

lemma not_B1_is_B0: "y \<noteq> (1::bit) \<Longrightarrow> y = (0::bit)"
  by (cases y) auto

lemma B1_ass_B0: 
  assumes y: "y = (0::bit) \<Longrightarrow> y = (1::bit)"
  shows "y = (1::bit)"
  apply (rule classical)
  apply (drule not_B1_is_B0)
  apply (erule y)
  done

-- "simplifications for specific word lengths"
lemmas n2s_ths [THEN eq_reflection] = add_2_eq_Suc add_2_eq_Suc'

lemmas s2n_ths = n2s_ths [symmetric]

end
