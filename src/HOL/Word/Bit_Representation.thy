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

lemma bin_rest_BIT: "bin_rest (x BIT b) = x"
  unfolding bin_rest_def Bit_def
  by (cases b, simp_all)

lemma bin_last_BIT: "bin_last (x BIT b) = b"
  unfolding bin_last_def Bit_def
  by (cases b, simp_all add: z1pmod2)

lemma BIT_eq: "u BIT b = v BIT c ==> u = v & b = c"
  by (metis bin_rest_BIT bin_last_BIT)

lemma BIT_B0_eq_Bit0 [simp]: "w BIT 0 = Int.Bit0 w"
  unfolding Bit_def Bit0_def by simp

lemma BIT_B1_eq_Bit1 [simp]: "w BIT 1 = Int.Bit1 w"
  unfolding Bit_def Bit1_def by simp

lemmas BIT_simps = BIT_B0_eq_Bit0 BIT_B1_eq_Bit1

lemma number_of_False_cong: 
  "False \<Longrightarrow> number_of x = number_of y"
  by (rule FalseE)

lemmas BIT_eqE [elim!] = BIT_eq [THEN conjE]

lemma BIT_eq_iff [simp]: 
  "(u BIT b = v BIT c) = (u = v \<and> b = c)"
  by (rule iffI) auto

lemmas BIT_eqI [intro!] = conjI [THEN BIT_eq_iff [THEN iffD2]]

lemma less_Bits: 
  "(v BIT b < w BIT c) = (v < w | v <= w & b = (0::bit) & c = (1::bit))"
  unfolding Bit_def by (auto simp add: bitval_def split: bit.split)

lemma le_Bits: 
  "(v BIT b <= w BIT c) = (v < w | v <= w & (b ~= (1::bit) | c ~= (0::bit)))" 
  unfolding Bit_def by (auto simp add: bitval_def split: bit.split)

lemma no_no [simp]: "number_of (number_of i) = i"
  unfolding number_of_eq by simp

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

lemma B1_mod_2 [simp]: "(Int.Bit1 w) mod 2 = 1"
  unfolding numeral_simps number_of_is_id by (simp add: z1pmod2)

lemma B0_mod_2 [simp]: "(Int.Bit0 w) mod 2 = 0"
  unfolding numeral_simps number_of_is_id by simp

lemma neB1E [elim!]:
  assumes ne: "y \<noteq> (1::bit)"
  assumes y: "y = (0::bit) \<Longrightarrow> P"
  shows "P"
  apply (rule y)
  apply (cases y rule: bit.exhaust, simp)
  apply (simp add: ne)
  done

lemma bin_ex_rl: "EX w b. w BIT b = bin"
  apply (unfold Bit_def)
  apply (cases "even bin")
   apply (clarsimp simp: even_equiv_def)
   apply (auto simp: odd_equiv_def bitval_def split: bit.split)
  done

lemma bin_exhaust:
  assumes Q: "\<And>x b. bin = x BIT b \<Longrightarrow> Q"
  shows "Q"
  apply (insert bin_ex_rl [of bin])  
  apply (erule exE)+
  apply (rule Q)
  apply force
  done


subsection {* Destructors for binary integers *}

definition bin_rl :: "int \<Rightarrow> int \<times> bit" where 
  "bin_rl w = (bin_rest w, bin_last w)"

lemma bin_rl_char: "bin_rl w = (r, l) \<longleftrightarrow> r BIT l = w"
  unfolding bin_rl_def by (auto simp: bin_rest_BIT bin_last_BIT)

primrec bin_nth where
  Z: "bin_nth w 0 = (bin_last w = (1::bit))"
  | Suc: "bin_nth w (Suc n) = bin_nth (bin_rest w) n"

lemma bin_rl_simps [simp]:
  "bin_rl Int.Pls = (Int.Pls, (0::bit))"
  "bin_rl Int.Min = (Int.Min, (1::bit))"
  "bin_rl (Int.Bit0 r) = (r, (0::bit))"
  "bin_rl (Int.Bit1 r) = (r, (1::bit))"
  "bin_rl (r BIT b) = (r, b)"
  unfolding bin_rl_char by simp_all

lemma bin_abs_lem:
  "bin = (w BIT b) ==> ~ bin = Int.Min --> ~ bin = Int.Pls -->
    nat (abs w) < nat (abs bin)"
  apply (clarsimp simp add: bin_rl_char)
  apply (unfold Pls_def Min_def Bit_def)
  apply (cases b)
   apply (clarsimp, arith)
  apply (clarsimp, arith)
  done

lemma bin_induct:
  assumes PPls: "P Int.Pls"
    and PMin: "P Int.Min"
    and PBit: "!!bin bit. P bin ==> P (bin BIT bit)"
  shows "P bin"
  apply (rule_tac P=P and a=bin and f1="nat o abs" 
                  in wf_measure [THEN wf_induct])
  apply (simp add: measure_def inv_image_def)
  apply (case_tac x rule: bin_exhaust)
  apply (frule bin_abs_lem)
  apply (auto simp add : PPls PMin PBit)
  done

lemma numeral_induct:
  assumes Pls: "P Int.Pls"
  assumes Min: "P Int.Min"
  assumes Bit0: "\<And>w. \<lbrakk>P w; w \<noteq> Int.Pls\<rbrakk> \<Longrightarrow> P (Int.Bit0 w)"
  assumes Bit1: "\<And>w. \<lbrakk>P w; w \<noteq> Int.Min\<rbrakk> \<Longrightarrow> P (Int.Bit1 w)"
  shows "P x"
  apply (induct x rule: bin_induct)
    apply (rule Pls)
   apply (rule Min)
  apply (case_tac bit)
   apply (case_tac "bin = Int.Pls")
    apply simp
   apply (simp add: Bit0)
  apply (case_tac "bin = Int.Min")
   apply simp
  apply (simp add: Bit1)
  done

lemma bin_rest_simps [simp]: 
  "bin_rest Int.Pls = Int.Pls"
  "bin_rest Int.Min = Int.Min"
  "bin_rest (Int.Bit0 w) = w"
  "bin_rest (Int.Bit1 w) = w"
  "bin_rest (w BIT b) = w"
  using bin_rl_simps bin_rl_def by auto

lemma bin_last_simps [simp]: 
  "bin_last Int.Pls = (0::bit)"
  "bin_last Int.Min = (1::bit)"
  "bin_last (Int.Bit0 w) = (0::bit)"
  "bin_last (Int.Bit1 w) = (1::bit)"
  "bin_last (w BIT b) = b"
  using bin_rl_simps bin_rl_def by auto

lemma bin_r_l_extras [simp]:
  "bin_last 0 = (0::bit)"
  "bin_last (- 1) = (1::bit)"
  "bin_last -1 = (1::bit)"
  "bin_last 1 = (1::bit)"
  "bin_rest 1 = 0"
  "bin_rest 0 = 0"
  "bin_rest (- 1) = - 1"
  "bin_rest -1 = -1"
  by (simp_all add: bin_last_def bin_rest_def)

lemma Bit_div2 [simp]: "(w BIT b) div 2 = w"
  unfolding bin_rest_def [symmetric] by auto

lemma Bit0_div2 [simp]: "(Int.Bit0 w) div 2 = w"
  using Bit_div2 [where b="(0::bit)"] by simp

lemma Bit1_div2 [simp]: "(Int.Bit1 w) div 2 = w"
  using Bit_div2 [where b="(1::bit)"] by simp

lemma bin_nth_lem [rule_format]:
  "ALL y. bin_nth x = bin_nth y --> x = y"
  apply (induct x rule: bin_induct)
    apply safe
    apply (erule rev_mp)
    apply (induct_tac y rule: bin_induct)
      apply (safe del: subset_antisym)
      apply (drule_tac x=0 in fun_cong, force)
     apply (erule notE, rule ext, 
            drule_tac x="Suc x" in fun_cong, force)
    apply (drule_tac x=0 in fun_cong, force)
   apply (erule rev_mp)
   apply (induct_tac y rule: bin_induct)
     apply (safe del: subset_antisym)
     apply (drule_tac x=0 in fun_cong, force)
    apply (erule notE, rule ext, 
           drule_tac x="Suc x" in fun_cong, force)
   apply (drule_tac x=0 in fun_cong, force)
  apply (case_tac y rule: bin_exhaust)
  apply clarify
  apply (erule allE)
  apply (erule impE)
   prefer 2
   apply (erule BIT_eqI)
   apply (drule_tac x=0 in fun_cong, force)
  apply (rule ext)
  apply (drule_tac x="Suc ?x" in fun_cong, force)
  done

lemma bin_nth_eq_iff: "(bin_nth x = bin_nth y) = (x = y)"
  by (auto elim: bin_nth_lem)

lemmas bin_eqI = ext [THEN bin_nth_eq_iff [THEN iffD1]]

lemma bin_eq_iff: "x = y \<longleftrightarrow> (\<forall>n. bin_nth x n = bin_nth y n)"
  by (auto intro!: bin_nth_lem del: equalityI)

lemma bin_nth_Pls [simp]: "~ bin_nth Int.Pls n"
  by (induct n) auto

lemma bin_nth_Min [simp]: "bin_nth Int.Min n"
  by (induct n) auto

lemma bin_nth_0_BIT: "bin_nth (w BIT b) 0 = (b = (1::bit))"
  by auto

lemma bin_nth_Suc_BIT: "bin_nth (w BIT b) (Suc n) = bin_nth w n"
  by auto

lemma bin_nth_minus [simp]: "0 < n ==> bin_nth (w BIT b) n = bin_nth w (n - 1)"
  by (cases n) auto

lemma bin_nth_minus_Bit0 [simp]:
  "0 < n ==> bin_nth (Int.Bit0 w) n = bin_nth w (n - 1)"
  using bin_nth_minus [where b="(0::bit)"] by simp

lemma bin_nth_minus_Bit1 [simp]:
  "0 < n ==> bin_nth (Int.Bit1 w) n = bin_nth w (n - 1)"
  using bin_nth_minus [where b="(1::bit)"] by simp

lemmas bin_nth_0 = bin_nth.simps(1)
lemmas bin_nth_Suc = bin_nth.simps(2)

lemmas bin_nth_simps = 
  bin_nth_0 bin_nth_Suc bin_nth_Pls bin_nth_Min bin_nth_minus
  bin_nth_minus_Bit0 bin_nth_minus_Bit1


subsection {* Truncating binary integers *}

definition bin_sign :: "int \<Rightarrow> int" where
  bin_sign_def: "bin_sign k = (if k \<ge> 0 then 0 else - 1)"

lemma bin_sign_simps [simp]:
  "bin_sign Int.Pls = Int.Pls"
  "bin_sign Int.Min = Int.Min"
  "bin_sign (Int.Bit0 w) = bin_sign w"
  "bin_sign (Int.Bit1 w) = bin_sign w"
  "bin_sign (w BIT b) = bin_sign w"
  by (unfold bin_sign_def numeral_simps Bit_def bitval_def) (simp_all split: bit.split)

lemma bin_sign_rest [simp]: 
  "bin_sign (bin_rest w) = bin_sign w"
  by (cases w rule: bin_exhaust) auto

primrec bintrunc :: "nat \<Rightarrow> int \<Rightarrow> int" where
  Z : "bintrunc 0 bin = Int.Pls"
| Suc : "bintrunc (Suc n) bin = bintrunc n (bin_rest bin) BIT (bin_last bin)"

primrec sbintrunc :: "nat => int => int" where
  Z : "sbintrunc 0 bin = 
    (case bin_last bin of (1::bit) => Int.Min | (0::bit) => Int.Pls)"
| Suc : "sbintrunc (Suc n) bin = sbintrunc n (bin_rest bin) BIT (bin_last bin)"

lemma [code]:
  "sbintrunc 0 bin = 
    (case bin_last bin of (1::bit) => - 1 | (0::bit) => 0)"
  "sbintrunc (Suc n) bin = sbintrunc n (bin_rest bin) BIT (bin_last bin)"
  apply simp_all
  apply (simp only: Pls_def Min_def)
  done

lemma sign_bintr:
  "!!w. bin_sign (bintrunc n w) = Int.Pls"
  by (induct n) auto

lemma bintrunc_mod2p:
  "!!w. bintrunc n w = (w mod 2 ^ n :: int)"
  apply (induct n)
  apply (simp add: Pls_def)
  apply (simp add: bin_last_def bin_rest_def Bit_def zmod_zmult2_eq
              cong: number_of_False_cong)
  done

lemma sbintrunc_mod2p:
  "!!w. sbintrunc n w = ((w + 2 ^ n) mod 2 ^ (Suc n) - 2 ^ n :: int)"
  apply (induct n)
   apply clarsimp
   apply (subst mod_add_left_eq)
   apply (simp add: bin_last_def)
   apply (simp add: number_of_eq)
  apply (simp add: Pls_def)
  apply (simp add: bin_last_def bin_rest_def Bit_def 
              cong: number_of_False_cong)
  apply (clarsimp simp: mod_mult_mult1 [symmetric] 
         zmod_zdiv_equality [THEN diff_eq_eq [THEN iffD2 [THEN sym]]])
  apply (rule trans [symmetric, OF _ emep1])
     apply auto
  apply (auto simp: even_def)
  done

subsection "Simplifications for (s)bintrunc"

lemma bit_bool:
  "(b = (b' = (1::bit))) = (b' = (if b then (1::bit) else (0::bit)))"
  by (cases b') auto

lemmas bit_bool1 [simp] = refl [THEN bit_bool [THEN iffD1], symmetric]

lemma bin_sign_lem:
  "!!bin. (bin_sign (sbintrunc n bin) = Int.Min) = bin_nth bin n"
  apply (induct n)
   apply (case_tac bin rule: bin_exhaust, case_tac b, auto)+
  done

lemma nth_bintr:
  "!!w m. bin_nth (bintrunc m w) n = (n < m & bin_nth w n)"
  apply (induct n)
   apply (case_tac m, auto)[1]
  apply (case_tac m, auto)[1]
  done

lemma nth_sbintr:
  "!!w m. bin_nth (sbintrunc m w) n = 
          (if n < m then bin_nth w n else bin_nth w m)"
  apply (induct n)
   apply (case_tac m, simp_all split: bit.splits)[1]
  apply (case_tac m, simp_all split: bit.splits)[1]
  done

lemma bin_nth_Bit:
  "bin_nth (w BIT b) n = (n = 0 & b = (1::bit) | (EX m. n = Suc m & bin_nth w m))"
  by (cases n) auto

lemma bin_nth_Bit0:
  "bin_nth (Int.Bit0 w) n = (EX m. n = Suc m & bin_nth w m)"
  using bin_nth_Bit [where b="(0::bit)"] by simp

lemma bin_nth_Bit1:
  "bin_nth (Int.Bit1 w) n = (n = 0 | (EX m. n = Suc m & bin_nth w m))"
  using bin_nth_Bit [where b="(1::bit)"] by simp

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
  bintrunc.Suc [where bin="Int.Pls", simplified bin_last_simps bin_rest_simps]

lemmas bintrunc_Min [simp] = 
  bintrunc.Suc [where bin="Int.Min", simplified bin_last_simps bin_rest_simps]

lemmas bintrunc_BIT  [simp] = 
  bintrunc.Suc [where bin="w BIT b", simplified bin_last_simps bin_rest_simps] for w b

lemma bintrunc_Bit0 [simp]:
  "bintrunc (Suc n) (Int.Bit0 w) = Int.Bit0 (bintrunc n w)"
  using bintrunc_BIT [where b="(0::bit)"] by simp

lemma bintrunc_Bit1 [simp]:
  "bintrunc (Suc n) (Int.Bit1 w) = Int.Bit1 (bintrunc n w)"
  using bintrunc_BIT [where b="(1::bit)"] by simp

lemmas bintrunc_Sucs = bintrunc_Pls bintrunc_Min bintrunc_BIT
  bintrunc_Bit0 bintrunc_Bit1

lemmas sbintrunc_Suc_Pls = 
  sbintrunc.Suc [where bin="Int.Pls", simplified bin_last_simps bin_rest_simps]

lemmas sbintrunc_Suc_Min = 
  sbintrunc.Suc [where bin="Int.Min", simplified bin_last_simps bin_rest_simps]

lemmas sbintrunc_Suc_BIT [simp] = 
  sbintrunc.Suc [where bin="w BIT b", simplified bin_last_simps bin_rest_simps] for w b

lemma sbintrunc_Suc_Bit0 [simp]:
  "sbintrunc (Suc n) (Int.Bit0 w) = Int.Bit0 (sbintrunc n w)"
  using sbintrunc_Suc_BIT [where b="(0::bit)"] by simp

lemma sbintrunc_Suc_Bit1 [simp]:
  "sbintrunc (Suc n) (Int.Bit1 w) = Int.Bit1 (sbintrunc n w)"
  using sbintrunc_Suc_BIT [where b="(1::bit)"] by simp

lemmas sbintrunc_Sucs = sbintrunc_Suc_Pls sbintrunc_Suc_Min sbintrunc_Suc_BIT
  sbintrunc_Suc_Bit0 sbintrunc_Suc_Bit1

lemmas sbintrunc_Pls = 
  sbintrunc.Z [where bin="Int.Pls", 
               simplified bin_last_simps bin_rest_simps bit.simps]

lemmas sbintrunc_Min = 
  sbintrunc.Z [where bin="Int.Min", 
               simplified bin_last_simps bin_rest_simps bit.simps]

lemmas sbintrunc_0_BIT_B0 [simp] = 
  sbintrunc.Z [where bin="w BIT (0::bit)", 
               simplified bin_last_simps bin_rest_simps bit.simps] for w

lemmas sbintrunc_0_BIT_B1 [simp] = 
  sbintrunc.Z [where bin="w BIT (1::bit)", 
               simplified bin_last_simps bin_rest_simps bit.simps] for w

lemma sbintrunc_0_Bit0 [simp]: "sbintrunc 0 (Int.Bit0 w) = Int.Pls"
  using sbintrunc_0_BIT_B0 by simp

lemma sbintrunc_0_Bit1 [simp]: "sbintrunc 0 (Int.Bit1 w) = Int.Min"
  using sbintrunc_0_BIT_B1 by simp

lemmas sbintrunc_0_simps =
  sbintrunc_Pls sbintrunc_Min sbintrunc_0_BIT_B0 sbintrunc_0_BIT_B1
  sbintrunc_0_Bit0 sbintrunc_0_Bit1

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

lemma bintrunc_n_Pls [simp]:
  "bintrunc n Int.Pls = Int.Pls"
  by (induct n) auto

lemma sbintrunc_n_PM [simp]:
  "sbintrunc n Int.Pls = Int.Pls"
  "sbintrunc n Int.Min = Int.Min"
  by (induct n) auto

lemmas thobini1 = arg_cong [where f = "%w. w BIT b"] for b

lemmas bintrunc_BIT_I = trans [OF bintrunc_BIT thobini1]
lemmas bintrunc_Min_I = trans [OF bintrunc_Min thobini1]

lemmas bmsts = bintrunc_minus_simps(1-3) [THEN thobini1 [THEN [2] trans]]
lemmas bintrunc_Pls_minus_I = bmsts(1)
lemmas bintrunc_Min_minus_I = bmsts(2)
lemmas bintrunc_BIT_minus_I = bmsts(3)

lemma bintrunc_0_Min: "bintrunc 0 Int.Min = Int.Pls"
  by auto
lemma bintrunc_0_BIT: "bintrunc 0 (w BIT b) = Int.Pls"
  by auto

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

lemmas bintrunc_pred_simps [simp] = 
  bintrunc_minus_simps [of "number_of bin", simplified nobm1] for bin

lemmas sbintrunc_pred_simps [simp] = 
  sbintrunc_minus_simps [of "number_of bin", simplified nobm1] for bin

lemma no_bintr_alt:
  "number_of (bintrunc n w) = w mod 2 ^ n"
  by (simp add: number_of_eq bintrunc_mod2p)

lemma no_bintr_alt1: "bintrunc n = (%w. w mod 2 ^ n :: int)"
  by (rule ext) (rule bintrunc_mod2p)

lemma range_bintrunc: "range (bintrunc n) = {i. 0 <= i & i < 2 ^ n}"
  apply (unfold no_bintr_alt1)
  apply (auto simp add: image_iff)
  apply (rule exI)
  apply (auto intro: int_mod_lem [THEN iffD1, symmetric])
  done

lemma no_bintr: 
  "number_of (bintrunc n w) = (number_of w mod 2 ^ n :: int)"
  by (simp add : bintrunc_mod2p number_of_eq)

lemma no_sbintr_alt2: 
  "sbintrunc n = (%w. (w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (rule ext) (simp add : sbintrunc_mod2p)

lemma no_sbintr: 
  "number_of (sbintrunc n w) = 
   ((number_of w + 2 ^ n) mod 2 ^ Suc n - 2 ^ n :: int)"
  by (simp add : no_sbintr_alt2 number_of_eq)

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

lemmas zmod_uminus' = zmod_uminus [where b=c] for c
lemmas zpower_zmod' = zpower_zmod [where m=c and y=k] for c k

lemmas brdmod1s' [symmetric] = 
  mod_add_left_eq mod_add_right_eq 
  zmod_zsub_left_eq zmod_zsub_right_eq 
  zmod_zmult1_eq zmod_zmult1_eq_rev 

lemmas brdmods' [symmetric] = 
  zpower_zmod' [symmetric]
  trans [OF mod_add_left_eq mod_add_right_eq] 
  trans [OF zmod_zsub_left_eq zmod_zsub_right_eq] 
  trans [OF zmod_zmult1_eq zmod_zmult1_eq_rev] 
  zmod_uminus' [symmetric]
  mod_add_left_eq [where b = "1::int"]
  zmod_zsub_left_eq [where b = "1"]

lemmas bintr_arith1s =
  brdmod1s' [where c="2^n::int", folded pred_def succ_def bintrunc_mod2p] for n
lemmas bintr_ariths =
  brdmods' [where c="2^n::int", folded pred_def succ_def bintrunc_mod2p] for n

lemmas m2pths = pos_mod_sign pos_mod_bound [OF zless2p]

lemma bintr_ge0: "(0 :: int) <= number_of (bintrunc n w)"
  by (simp add : no_bintr m2pths)

lemma bintr_lt2p: "number_of (bintrunc n w) < (2 ^ n :: int)"
  by (simp add : no_bintr m2pths)

lemma bintr_Min: 
  "number_of (bintrunc n Int.Min) = (2 ^ n :: int) - 1"
  by (simp add : no_bintr m1mod2k)

lemma sbintr_ge: "(- (2 ^ n) :: int) <= number_of (sbintrunc n w)"
  by (simp add : no_sbintr m2pths)

lemma sbintr_lt: "number_of (sbintrunc n w) < (2 ^ n :: int)"
  by (simp add : no_sbintr m2pths)

lemma bintrunc_Suc:
  "bintrunc (Suc n) bin = bintrunc n (bin_rest bin) BIT bin_last bin"
  by (case_tac bin rule: bin_exhaust) auto

lemma sign_Pls_ge_0: 
  "(bin_sign bin = Int.Pls) = (number_of bin >= (0 :: int))"
  by (induct bin rule: numeral_induct) auto

lemma sign_Min_lt_0: 
  "(bin_sign bin = Int.Min) = (number_of bin < (0 :: int))"
  by (induct bin rule: numeral_induct) auto

lemmas sign_Min_neg = trans [OF sign_Min_lt_0 neg_def [symmetric]] 

lemma bin_rest_trunc:
  "!!bin. (bin_rest (bintrunc n bin)) = bintrunc (n - 1) (bin_rest bin)"
  by (induct n) auto

lemma bin_rest_power_trunc [rule_format] :
  "(bin_rest ^^ k) (bintrunc n bin) = 
    bintrunc (n - k) ((bin_rest ^^ k) bin)"
  by (induct k) (auto simp: bin_rest_trunc)

lemma bin_rest_trunc_i:
  "bintrunc n (bin_rest bin) = bin_rest (bintrunc (Suc n) bin)"
  by auto

lemma bin_rest_strunc:
  "!!bin. bin_rest (sbintrunc (Suc n) bin) = sbintrunc n (bin_rest bin)"
  by (induct n) auto

lemma bintrunc_rest [simp]: 
  "!!bin. bintrunc n (bin_rest (bintrunc n bin)) = bin_rest (bintrunc n bin)"
  apply (induct n, simp)
  apply (case_tac bin rule: bin_exhaust)
  apply (auto simp: bintrunc_bintrunc_l)
  done

lemma sbintrunc_rest [simp]:
  "!!bin. sbintrunc n (bin_rest (sbintrunc n bin)) = bin_rest (sbintrunc n bin)"
  apply (induct n, simp)
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
  Z: "bin_split 0 w = (w, Int.Pls)"
  | Suc: "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w)
        in (w1, w2 BIT bin_last w))"

lemma [code]:
  "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w) in (w1, w2 BIT bin_last w))"
  "bin_split 0 w = (w, 0)"
  by (simp_all add: Pls_def)

primrec bin_cat :: "int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  Z: "bin_cat w 0 v = w"
  | Suc: "bin_cat w (Suc n) v = bin_cat w n (bin_rest v) BIT bin_last v"

subsection {* Miscellaneous lemmas *}

lemma funpow_minus_simp:
  "0 < n \<Longrightarrow> f ^^ n = f \<circ> f ^^ (n - 1)"
  by (cases n) simp_all

lemmas funpow_pred_simp [simp] =
  funpow_minus_simp [of "number_of bin", simplified nobm1] for bin

lemmas replicate_minus_simp = 
  trans [OF gen_minus [where f = "%n. replicate n x"] replicate.replicate_Suc] for x

lemmas replicate_pred_simp [simp] =
  replicate_minus_simp [of "number_of bin", simplified nobm1] for bin

lemmas power_Suc_no [simp] = power_Suc [of "number_of a"] for a

lemmas power_minus_simp = 
  trans [OF gen_minus [where f = "power f"] power_Suc] for f

lemmas power_pred_simp = 
  power_minus_simp [of "number_of bin", simplified nobm1] for bin
lemmas power_pred_simp_no [simp] = power_pred_simp [where f= "number_of f"] for f

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

lemma size_Cons_lem_eq_bin:
  "y = xa # list ==> size y = number_of (Int.succ k) ==> 
    size list = number_of k"
  by (auto simp: pred_def succ_def split add : split_if_asm)

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
