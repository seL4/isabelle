(* 
  ID:     $Id$
  Author: Jeremy Dawson, NICTA

  contains basic definition to do with integers
  expressed using Pls, Min, BIT and important resulting theorems, 
  in particular, bin_rec and related work
*) 

header {* Basic Definitions for Binary Integers *}

theory BinGeneral imports Num_Lemmas

begin

subsection {* Recursion combinator for binary integers *}

lemma brlem: "(bin = Int.Min) = (- bin + Int.pred 0 = 0)"
  unfolding Min_def pred_def by arith

function
  bin_rec' :: "int * 'a * 'a * (int => bit => 'a => 'a) => 'a"  
  where 
  "bin_rec' (bin, f1, f2, f3) = (if bin = Int.Pls then f1 
    else if bin = Int.Min then f2
    else case bin_rl bin of (w, b) => f3 w b (bin_rec' (w, f1, f2, f3)))"
  by pat_completeness auto

termination 
  apply (relation "measure (nat o abs o fst)")
   apply simp
  apply (simp add: Pls_def brlem)
  apply (clarsimp simp: bin_rl_char pred_def)
  apply (frule thin_rl [THEN refl [THEN bin_abs_lem [rule_format]]]) 
    apply (unfold Pls_def Min_def number_of_eq)
    prefer 2
    apply (erule asm_rl)
   apply auto
  done

constdefs
  bin_rec :: "'a => 'a => (int => bit => 'a => 'a) => int => 'a"
  "bin_rec f1 f2 f3 bin == bin_rec' (bin, f1, f2, f3)"

lemma bin_rec_PM:
  "f = bin_rec f1 f2 f3 ==> f Int.Pls = f1 & f Int.Min = f2"
  apply safe
   apply (unfold bin_rec_def)
   apply (auto intro: bin_rec'.simps [THEN trans])
  done

lemmas bin_rec_Pls = refl [THEN bin_rec_PM, THEN conjunct1, standard]
lemmas bin_rec_Min = refl [THEN bin_rec_PM, THEN conjunct2, standard]

lemma bin_rec_Bit:
  "f = bin_rec f1 f2 f3  ==> f3 Int.Pls bit.B0 f1 = f1 ==> 
    f3 Int.Min bit.B1 f2 = f2 ==> f (w BIT b) = f3 w b (f w)"
  apply clarify
  apply (unfold bin_rec_def)
  apply (rule bin_rec'.simps [THEN trans])
  apply auto
       apply (unfold Pls_def Min_def Bit_def)
       apply (cases b, auto)+
  done

lemmas bin_rec_simps = refl [THEN bin_rec_Bit] bin_rec_Pls bin_rec_Min

subsection {* Destructors for binary integers *}

consts
  -- "corresponding operations analysing bins"
  bin_last :: "int => bit"
  bin_rest :: "int => int"
  bin_sign :: "int => int"
  bin_nth :: "int => nat => bool"

primrec
  Z : "bin_nth w 0 = (bin_last w = bit.B1)"
  Suc : "bin_nth w (Suc n) = bin_nth (bin_rest w) n"

defs  
  bin_rest_def : "bin_rest w == fst (bin_rl w)"
  bin_last_def : "bin_last w == snd (bin_rl w)"
  bin_sign_def : "bin_sign == bin_rec Int.Pls Int.Min (%w b s. s)"

lemma bin_rl: "bin_rl w = (bin_rest w, bin_last w)"
  unfolding bin_rest_def bin_last_def by auto

lemmas bin_rl_simp [simp] = iffD1 [OF bin_rl_char bin_rl]

lemma bin_rest_simps [simp]: 
  "bin_rest Int.Pls = Int.Pls"
  "bin_rest Int.Min = Int.Min"
  "bin_rest (w BIT b) = w"
  unfolding bin_rest_def by auto

lemma bin_last_simps [simp]: 
  "bin_last Int.Pls = bit.B0"
  "bin_last Int.Min = bit.B1"
  "bin_last (w BIT b) = b"
  unfolding bin_last_def by auto
    
lemma bin_sign_simps [simp]:
  "bin_sign Int.Pls = Int.Pls"
  "bin_sign Int.Min = Int.Min"
  "bin_sign (w BIT b) = bin_sign w"
  unfolding bin_sign_def by (auto simp: bin_rec_simps)

lemma bin_r_l_extras [simp]:
  "bin_last 0 = bit.B0"
  "bin_last (- 1) = bit.B1"
  "bin_last -1 = bit.B1"
  "bin_last 1 = bit.B1"
  "bin_rest 1 = 0"
  "bin_rest 0 = 0"
  "bin_rest (- 1) = - 1"
  "bin_rest -1 = -1"
  apply (unfold number_of_Min)
  apply (unfold Pls_def [symmetric] Min_def [symmetric])
  apply (unfold numeral_1_eq_1 [symmetric])
  apply (auto simp: number_of_eq) 
  done

lemma bin_last_mod: 
  "bin_last w = (if w mod 2 = 0 then bit.B0 else bit.B1)"
  apply (case_tac w rule: bin_exhaust)
  apply (case_tac b)
   apply auto
  done

lemma bin_rest_div: 
  "bin_rest w = w div 2"
  apply (case_tac w rule: bin_exhaust)
  apply (rule trans)
   apply clarsimp
   apply (rule refl)
  apply (drule trans)
   apply (rule Bit_def)
  apply (simp add: z1pdiv2 split: bit.split)
  done

lemma Bit_div2 [simp]: "(w BIT b) div 2 = w"
  unfolding bin_rest_div [symmetric] by auto

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
   apply (erule BIT_eqI)
   apply (drule_tac x=0 in fun_cong, force)
  apply (rule ext)
  apply (drule_tac x="Suc ?x" in fun_cong, force)
  done

lemma bin_nth_eq_iff: "(bin_nth x = bin_nth y) = (x = y)"
  by (auto elim: bin_nth_lem)

lemmas bin_eqI = ext [THEN bin_nth_eq_iff [THEN iffD1], standard]

lemma bin_nth_Pls [simp]: "~ bin_nth Int.Pls n"
  by (induct n) auto

lemma bin_nth_Min [simp]: "bin_nth Int.Min n"
  by (induct n) auto

lemma bin_nth_0_BIT: "bin_nth (w BIT b) 0 = (b = bit.B1)"
  by auto

lemma bin_nth_Suc_BIT: "bin_nth (w BIT b) (Suc n) = bin_nth w n"
  by auto

lemma bin_nth_minus [simp]: "0 < n ==> bin_nth (w BIT b) n = bin_nth w (n - 1)"
  by (cases n) auto

lemmas bin_nth_0 = bin_nth.simps(1)
lemmas bin_nth_Suc = bin_nth.simps(2)

lemmas bin_nth_simps = 
  bin_nth_0 bin_nth_Suc bin_nth_Pls bin_nth_Min bin_nth_minus

lemma bin_sign_rest [simp]: 
  "bin_sign (bin_rest w) = (bin_sign w)"
  by (case_tac w rule: bin_exhaust) auto

subsection {* Truncating binary integers *}

consts
  bintrunc :: "nat => int => int"
primrec 
  Z : "bintrunc 0 bin = Int.Pls"
  Suc : "bintrunc (Suc n) bin = bintrunc n (bin_rest bin) BIT (bin_last bin)"

consts
  sbintrunc :: "nat => int => int" 
primrec 
  Z : "sbintrunc 0 bin = 
    (case bin_last bin of bit.B1 => Int.Min | bit.B0 => Int.Pls)"
  Suc : "sbintrunc (Suc n) bin = sbintrunc n (bin_rest bin) BIT (bin_last bin)"

lemma sign_bintr:
  "!!w. bin_sign (bintrunc n w) = Int.Pls"
  by (induct n) auto

lemma bintrunc_mod2p:
  "!!w. bintrunc n w = (w mod 2 ^ n :: int)"
  apply (induct n, clarsimp)
  apply (simp add: bin_last_mod bin_rest_div Bit_def zmod_zmult2_eq
              cong: number_of_False_cong)
  done

lemma sbintrunc_mod2p:
  "!!w. sbintrunc n w = ((w + 2 ^ n) mod 2 ^ (Suc n) - 2 ^ n :: int)"
  apply (induct n)
   apply clarsimp
   apply (subst zmod_zadd_left_eq)
   apply (simp add: bin_last_mod)
   apply (simp add: number_of_eq)
  apply clarsimp
  apply (simp add: bin_last_mod bin_rest_div Bit_def 
              cong: number_of_False_cong)
  apply (clarsimp simp: zmod_zmult_zmult1 [symmetric] 
         zmod_zdiv_equality [THEN diff_eq_eq [THEN iffD2 [THEN sym]]])
  apply (rule trans [symmetric, OF _ emep1])
     apply auto
  apply (auto simp: even_def)
  done

subsection "Simplifications for (s)bintrunc"

lemma bit_bool:
  "(b = (b' = bit.B1)) = (b' = (if b then bit.B1 else bit.B0))"
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
  "bin_nth (w BIT b) n = (n = 0 & b = bit.B1 | (EX m. n = Suc m & bin_nth w m))"
  by (cases n) auto

lemma bintrunc_bintrunc_l:
  "n <= m ==> (bintrunc m (bintrunc n w) = bintrunc n w)"
  by (rule bin_eqI) (auto simp add : nth_bintr)

lemma sbintrunc_sbintrunc_l:
  "n <= m ==> (sbintrunc m (sbintrunc n w) = sbintrunc n w)"
  by (rule bin_eqI) (auto simp: nth_sbintr min_def)

lemma bintrunc_bintrunc_ge:
  "n <= m ==> (bintrunc n (bintrunc m w) = bintrunc n w)"
  by (rule bin_eqI) (auto simp: nth_bintr)

lemma bintrunc_bintrunc_min [simp]:
  "bintrunc m (bintrunc n w) = bintrunc (min m n) w"
  apply (unfold min_def)
  apply (rule bin_eqI)
  apply (auto simp: nth_bintr)
  done

lemma sbintrunc_sbintrunc_min [simp]:
  "sbintrunc m (sbintrunc n w) = sbintrunc (min m n) w"
  apply (unfold min_def)
  apply (rule bin_eqI)
  apply (auto simp: nth_sbintr)
  done

lemmas bintrunc_Pls = 
  bintrunc.Suc [where bin="Int.Pls", simplified bin_last_simps bin_rest_simps, standard]

lemmas bintrunc_Min [simp] = 
  bintrunc.Suc [where bin="Int.Min", simplified bin_last_simps bin_rest_simps, standard]

lemmas bintrunc_BIT  [simp] = 
  bintrunc.Suc [where bin="w BIT b", simplified bin_last_simps bin_rest_simps, standard]

lemmas bintrunc_Sucs = bintrunc_Pls bintrunc_Min bintrunc_BIT

lemmas sbintrunc_Suc_Pls = 
  sbintrunc.Suc [where bin="Int.Pls", simplified bin_last_simps bin_rest_simps, standard]

lemmas sbintrunc_Suc_Min = 
  sbintrunc.Suc [where bin="Int.Min", simplified bin_last_simps bin_rest_simps, standard]

lemmas sbintrunc_Suc_BIT [simp] = 
  sbintrunc.Suc [where bin="w BIT b", simplified bin_last_simps bin_rest_simps, standard]

lemmas sbintrunc_Sucs = sbintrunc_Suc_Pls sbintrunc_Suc_Min sbintrunc_Suc_BIT

lemmas sbintrunc_Pls = 
  sbintrunc.Z [where bin="Int.Pls", 
               simplified bin_last_simps bin_rest_simps bit.simps, standard]

lemmas sbintrunc_Min = 
  sbintrunc.Z [where bin="Int.Min", 
               simplified bin_last_simps bin_rest_simps bit.simps, standard]

lemmas sbintrunc_0_BIT_B0 [simp] = 
  sbintrunc.Z [where bin="w BIT bit.B0", 
               simplified bin_last_simps bin_rest_simps bit.simps, standard]

lemmas sbintrunc_0_BIT_B1 [simp] = 
  sbintrunc.Z [where bin="w BIT bit.B1", 
               simplified bin_last_simps bin_rest_simps bit.simps, standard]

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
  bintrunc_Sucs [THEN [2] bintrunc_minus [symmetric, THEN trans], standard]
lemmas sbintrunc_minus_simps = 
  sbintrunc_Sucs [THEN [2] sbintrunc_minus [symmetric, THEN trans], standard]

lemma bintrunc_n_Pls [simp]:
  "bintrunc n Int.Pls = Int.Pls"
  by (induct n) auto

lemma sbintrunc_n_PM [simp]:
  "sbintrunc n Int.Pls = Int.Pls"
  "sbintrunc n Int.Min = Int.Min"
  by (induct n) auto

lemmas thobini1 = arg_cong [where f = "%w. w BIT b", standard]

lemmas bintrunc_BIT_I = trans [OF bintrunc_BIT thobini1]
lemmas bintrunc_Min_I = trans [OF bintrunc_Min thobini1]

lemmas bmsts = bintrunc_minus_simps [THEN thobini1 [THEN [2] trans], standard]
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
  bintrunc_Min_I bintrunc_BIT_I [THEN bintrunc_Suc_lem, standard]

lemmas sbintrunc_BIT_I = trans [OF sbintrunc_Suc_BIT thobini1]

lemmas sbintrunc_Suc_Is = 
  sbintrunc_Sucs [THEN thobini1 [THEN [2] trans], standard]

lemmas sbintrunc_Suc_minus_Is = 
  sbintrunc_minus_simps [THEN thobini1 [THEN [2] trans], standard]

lemma sbintrunc_Suc_lem:
  "sbintrunc (Suc n) x = y ==> m = Suc n ==> sbintrunc m x = y"
  by auto

lemmas sbintrunc_Suc_Ialts = 
  sbintrunc_Suc_Is [THEN sbintrunc_Suc_lem, standard]

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
  trans [OF iszero_def [THEN Not_eq_iff [THEN iffD2]] refl, standard]

lemmas bintrunc_pred_simps [simp] = 
  bintrunc_minus_simps [of "number_of bin", simplified nobm1, standard]

lemmas sbintrunc_pred_simps [simp] = 
  sbintrunc_minus_simps [of "number_of bin", simplified nobm1, standard]

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
  by (rule iffD1 [OF less_diff_eq, THEN sb_inc_lem, simplified OrderedGroup.diff_0])

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

lemmas zmod_uminus' = zmod_uminus [where b="c", standard]
lemmas zpower_zmod' = zpower_zmod [where m="c" and y="k", standard]

lemmas brdmod1s' [symmetric] = 
  zmod_zadd_left_eq zmod_zadd_right_eq 
  zmod_zsub_left_eq zmod_zsub_right_eq 
  zmod_zmult1_eq zmod_zmult1_eq_rev 

lemmas brdmods' [symmetric] = 
  zpower_zmod' [symmetric]
  trans [OF zmod_zadd_left_eq zmod_zadd_right_eq] 
  trans [OF zmod_zsub_left_eq zmod_zsub_right_eq] 
  trans [OF zmod_zmult1_eq zmod_zmult1_eq_rev] 
  zmod_uminus' [symmetric]
  zmod_zadd_left_eq [where b = "1"]
  zmod_zsub_left_eq [where b = "1"]

lemmas bintr_arith1s =
  brdmod1s' [where c="2^n", folded pred_def succ_def bintrunc_mod2p, standard]
lemmas bintr_ariths =
  brdmods' [where c="2^n", folded pred_def succ_def bintrunc_mod2p, standard]

lemmas m2pths = pos_mod_sign pos_mod_bound [OF zless2p, standard] 

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
  by (induct bin rule: bin_induct) auto

lemma sign_Min_lt_0: 
  "(bin_sign bin = Int.Min) = (number_of bin < (0 :: int))"
  by (induct bin rule: bin_induct) auto

lemmas sign_Min_neg = trans [OF sign_Min_lt_0 neg_def [symmetric]] 

lemma bin_rest_trunc:
  "!!bin. (bin_rest (bintrunc n bin)) = bintrunc (n - 1) (bin_rest bin)"
  by (induct n) auto

lemma bin_rest_power_trunc [rule_format] :
  "(bin_rest ^ k) (bintrunc n bin) = 
    bintrunc (n - k) ((bin_rest ^ k) bin)"
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
  "f o g o f = g o f ==> f o (g o f) ^ n = g ^ n o f"
  apply (rule ext)
  apply (induct_tac n)
   apply (simp_all (no_asm))
  apply (drule fun_cong)
  apply (unfold o_def)
  apply (erule trans)
  apply simp
  done

lemma rco_alt: "(f o g) ^ n o f = f o (g o f) ^ n"
  apply (rule ext)
  apply (induct n)
   apply (simp_all add: o_def)
  done

lemmas rco_bintr = bintrunc_rest' 
  [THEN rco_lem [THEN fun_cong], unfolded o_def]
lemmas rco_sbintr = sbintrunc_rest' 
  [THEN rco_lem [THEN fun_cong], unfolded o_def]

subsection {* Splitting and concatenation *}

consts
  bin_split :: "nat => int => int * int"
primrec
  Z : "bin_split 0 w = (w, Int.Pls)"
  Suc : "bin_split (Suc n) w = (let (w1, w2) = bin_split n (bin_rest w)
    in (w1, w2 BIT bin_last w))"

consts
  bin_cat :: "int => nat => int => int"
primrec
  Z : "bin_cat w 0 v = w"
  Suc : "bin_cat w (Suc n) v = bin_cat w n (bin_rest v) BIT bin_last v"

subsection {* Miscellaneous lemmas *}

lemmas funpow_minus_simp = 
  trans [OF gen_minus [where f = "power f"] funpow_Suc, standard]

lemmas funpow_pred_simp [simp] =
  funpow_minus_simp [of "number_of bin", simplified nobm1, standard]

lemmas replicate_minus_simp = 
  trans [OF gen_minus [where f = "%n. replicate n x"] replicate.replicate_Suc,
         standard]

lemmas replicate_pred_simp [simp] =
  replicate_minus_simp [of "number_of bin", simplified nobm1, standard]

lemmas power_Suc_no [simp] = power_Suc [of "number_of a", standard]

lemmas power_minus_simp = 
  trans [OF gen_minus [where f = "power f"] power_Suc, standard]

lemmas power_pred_simp = 
  power_minus_simp [of "number_of bin", simplified nobm1, standard]
lemmas power_pred_simp_no [simp] = power_pred_simp [where f= "number_of f", standard]

lemma list_exhaust_size_gt0:
  assumes y: "\<And>a list. y = a # list \<Longrightarrow> P"
  shows "0 < length y \<Longrightarrow> P"
  apply (cases y, simp)
  apply (rule y)
  apply fastsimp
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

lemmas ls_splits = 
  prod.split split_split prod.split_asm split_split_asm split_if_asm

lemma not_B1_is_B0: "y \<noteq> bit.B1 \<Longrightarrow> y = bit.B0"
  by (cases y) auto

lemma B1_ass_B0: 
  assumes y: "y = bit.B0 \<Longrightarrow> y = bit.B1"
  shows "y = bit.B1"
  apply (rule classical)
  apply (drule not_B1_is_B0)
  apply (erule y)
  done

-- "simplifications for specific word lengths"
lemmas n2s_ths [THEN eq_reflection] = add_2_eq_Suc add_2_eq_Suc'

lemmas s2n_ths = n2s_ths [symmetric]


end
