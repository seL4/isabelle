(*  Title:      HOL/Import/HOLLightCompat.thy
    Author:     Steven Obua and Sebastian Skalberg, TU Muenchen
    Author:     Cezary Kaliszyk
*)

theory HOLLightCompat
imports Main Fact Parity "~~/src/HOL/Library/Infinite_Set"
  HOLLightList HOLLightReal HOLLightInt HOL4Setup
begin

(* list *)
lemmas [hol4rew] = list_el_def member_def list_mem_def
(* int *)
lemmas [hol4rew] = int_coprime.simps int_gcd.simps hl_mod_def hl_div_def int_mod_def eqeq_def
(* real *)
lemma [hol4rew]:
  "real (0::nat) = 0" "real (1::nat) = 1" "real (2::nat) = 2"
  by simp_all

lemma one:
  "\<forall>v. v = ()"
  by simp

lemma num_Axiom:
  "\<forall>e f. \<exists>!fn. fn 0 = e \<and> (\<forall>n. fn (Suc n) = f (fn n) n)"
  apply (intro allI)
  apply (rule_tac a="nat_rec e (%n e. f e n)" in ex1I)
  apply auto
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa)
  apply simp_all
  done

lemma SUC_INJ:
  "\<forall>m n. Suc m = Suc n \<longleftrightarrow> m = n"
  by auto

lemma PAIR:
  "(fst x, snd x) = x"
  by simp

lemma EXISTS_UNIQUE_THM:
  "(Ex1 P) = (Ex P & (\<forall>x y. P x & P y --> (x = y)))"
  by auto

lemma DEF__star_:
  "op * = (SOME mult. (\<forall>n. mult 0 n = 0) \<and> (\<forall>m n. mult (Suc m) n = mult m n + n))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)+
  apply (induct_tac x)
  apply auto
  done

lemma DEF__slash__backslash_:
  "(t1 \<and> t2) = ((\<lambda>f. f t1 t2 :: bool) = (\<lambda>f. f True True))"
  unfolding fun_eq_iff
  by (intro iffI, simp_all) (erule allE[of _ "(%a b. a \<and> b)"], simp)

lemma DEF__lessthan__equal_:
  "op \<le> = (SOME u. (\<forall>m. u m 0 = (m = 0)) \<and> (\<forall>m n. u m (Suc n) = (m = Suc n \<or> u m n)))"
  apply (rule some_equality[symmetric])
  apply auto[1]
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa)
  apply auto
  done

lemma DEF__lessthan_:
  "op < = (SOME u. (\<forall>m. u m 0 = False) \<and> (\<forall>m n. u m (Suc n) = (m = n \<or> u m n)))"
  apply (rule some_equality[symmetric])
  apply auto[1]
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  apply (induct_tac xa)
  apply auto
  done

lemma DEF__greaterthan__equal_:
  "(op \<ge>) = (%u ua. ua \<le> u)"
  by (simp)

lemma DEF__greaterthan_:
  "(op >) = (%u ua. ua < u)"
  by (simp)

lemma DEF__equal__equal__greaterthan_:
  "(t1 \<longrightarrow> t2) = ((t1 \<and> t2) = t1)"
  by auto

lemma DEF_WF:
  "wfP = (\<lambda>u. \<forall>P. (\<exists>x. P x) \<longrightarrow> (\<exists>x. P x \<and> (\<forall>y. u y x \<longrightarrow> \<not> P y)))"
  unfolding fun_eq_iff
  apply (intro allI, rule, intro allI impI, elim exE)
  apply (drule_tac wfE_min[to_pred, unfolded mem_def])
  apply assumption
  prefer 2
  apply assumption
  apply auto[1]
  apply (intro wfI_min[to_pred, unfolded mem_def])
  apply (drule_tac x="Q" in spec)
  apply auto
  apply (rule_tac x="xb" in bexI)
  apply (auto simp add: mem_def)
  done

lemma DEF_UNIV: "UNIV = (%x. True)"
  by (auto simp add: mem_def)

lemma DEF_UNIONS:
  "Sup = (\<lambda>u. {ua. \<exists>x. (\<exists>ua. ua \<in> u \<and> x \<in> ua) \<and> ua = x})"
  by (simp add: fun_eq_iff Collect_def)
     (metis UnionE complete_lattice_class.Sup_upper mem_def predicate1D)

lemma DEF_UNION:
  "op \<union> = (\<lambda>u ua. {ub. \<exists>x. (x \<in> u \<or> x \<in> ua) \<and> ub = x})"
  by (auto simp add: mem_def fun_eq_iff Collect_def)

lemma DEF_SUBSET: "op \<subseteq> = (\<lambda>u ua. \<forall>x. x \<in> u \<longrightarrow> x \<in> ua)"
  by (metis set_rev_mp subsetI)

lemma DEF_SND:
  "snd = (\<lambda>p. SOME x. EX y. p = (y, x))"
  unfolding fun_eq_iff
  by (rule someI2) (auto intro: snd_conv[symmetric] someI2)

definition [simp, hol4rew]: "SETSPEC x P y \<longleftrightarrow> P & x = y"

lemma DEF_PSUBSET: "op \<subset> = (\<lambda>u ua. u \<subseteq> ua & u \<noteq> ua)"
  by (auto simp add: mem_def fun_eq_iff)

definition [hol4rew]: "Pred n = n - (Suc 0)"

lemma DEF_PRE: "Pred = (SOME PRE. PRE 0 = 0 & (\<forall>n. PRE (Suc n) = n))"
  apply (rule some_equality[symmetric])
  apply (simp add: Pred_def)
  apply (rule ext)
  apply (induct_tac x)
  apply (auto simp add: Pred_def)
  done

lemma DEF_ONE_ONE:
  "inj = (\<lambda>u. \<forall>x1 x2. u x1 = u x2 \<longrightarrow> x1 = x2)"
  by (simp add: inj_on_def)

definition ODD'[hol4rew]: "(ODD :: nat \<Rightarrow> bool) = odd"

lemma DEF_ODD:
  "odd = (SOME ODD. ODD 0 = False \<and> (\<forall>n. ODD (Suc n) = (\<not> ODD n)))"
  apply (rule some_equality[symmetric])
  apply simp
  unfolding fun_eq_iff
  apply (intro allI)
  apply (induct_tac x)
  apply simp_all
  done

definition [hol4rew, simp]: "NUMERAL (x :: nat) = x"

lemma DEF_MOD:
  "op mod = (SOME r. \<forall>m n. if n = (0 :: nat) then m div n = 0 \<and>
     r m n = m else m = m div n * n + r m n \<and> r m n < n)"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
  apply (case_tac "xa = 0")
  apply auto
  apply (drule_tac x="x" in spec)
  apply (drule_tac x="xa" in spec)
  apply auto
  by (metis mod_less mod_mult_self2 nat_add_commute nat_mult_commute)

definition "MEASURE = (%u x y. (u x :: nat) < u y)"

lemma [hol4rew]:
  "MEASURE u = (%a b. measure u (a, b))"
  unfolding MEASURE_def measure_def fun_eq_iff inv_image_def Collect_def
  by simp

definition
  "LET f s = f s"

lemma [hol4rew]:
  "LET f s = Let s f"
  by (simp add: LET_def Let_def)

lemma DEF_INTERS:
  "Inter = (\<lambda>u. {ua. \<exists>x. (\<forall>ua. ua \<in> u \<longrightarrow> x \<in> ua) \<and> ua = x})"
  by (auto simp add: fun_eq_iff mem_def Collect_def)
     (metis InterD InterI mem_def)+

lemma DEF_INTER:
  "op \<inter> = (\<lambda>u ua. {ub. \<exists>x. (x \<in> u \<and> x \<in> ua) \<and> ub = x})"
  by (auto simp add: mem_def fun_eq_iff Collect_def)

lemma DEF_INSERT:
  "insert = (%u ua y. y \<in> ua | y = u)"
  unfolding mem_def fun_eq_iff insert_code by blast

lemma DEF_IMAGE:
  "op ` = (\<lambda>u ua. {ub. \<exists>y. (\<exists>x. x \<in> ua \<and> y = u x) \<and> ub = y})"
  by (simp add: fun_eq_iff image_def Bex_def)

lemma DEF_GSPEC:
  "Collect = (\<lambda>u. u)"
  by (simp add: Collect_def ext)

lemma DEF_GEQ:
  "(op =) = (op =)"
  by simp

lemma DEF_GABS:
  "Eps = Eps"
  by simp

lemma DEF_FST:
  "fst = (%p. SOME x. EX y. p = (x, y))"
  unfolding fun_eq_iff
  by (rule someI2) (auto intro: fst_conv[symmetric] someI2)

lemma DEF_FINITE:
  "finite = (\<lambda>a. \<forall>FP. (\<forall>a. a = {} \<or> (\<exists>x s. a = insert x s \<and> FP s) \<longrightarrow> FP a) \<longrightarrow> FP a)"
  unfolding fun_eq_iff
  apply (intro allI iffI impI)
  apply (erule finite_induct)
  apply auto[2]
  apply (drule_tac x="finite" in spec)
  apply auto
  apply (metis Collect_def Collect_empty_eq finite.emptyI)
  by (metis (no_types) finite.insertI predicate1I sup.commute sup_absorb1)

lemma DEF_FACT:
  "fact = (SOME FACT. FACT 0 = 1 & (\<forall>n. FACT (Suc n) = Suc n * FACT n))"
  apply (rule some_equality[symmetric])
  apply (simp_all)
  unfolding fun_eq_iff
  apply (intro allI)
  apply (induct_tac x)
  apply simp_all
  done

lemma DEF_EXP:
  "power = (SOME EXP. (\<forall>m. EXP m 0 = 1) \<and> (\<forall>m n. EXP m (Suc n) = m * EXP m n))"
  apply (rule some_equality[symmetric])
  apply (simp_all)
  unfolding fun_eq_iff
  apply (intro allI)
  apply (induct_tac xa)
  apply simp_all
  done

lemma DEF_EVEN:
  "even = (SOME EVEN. EVEN 0 = True \<and> (\<forall>n. EVEN (Suc n) = (\<not> EVEN n)))"
  apply (rule some_equality[symmetric])
  apply simp
  unfolding fun_eq_iff
  apply (intro allI)
  apply (induct_tac x)
  apply simp_all
  done

lemma DEF_EMPTY: "{} = (%x. False)"
  unfolding fun_eq_iff empty_def
  by auto

lemma DEF_DIV:
  "op div = (SOME q. \<exists>r. \<forall>m n. if n = (0 :: nat) then q m n = 0 \<and> r m n = m
     else m = q m n * n + r m n \<and> r m n < n)"
  apply (rule some_equality[symmetric])
  apply (rule_tac x="op mod" in exI)
  apply (auto simp add: fun_eq_iff)
  apply (case_tac "xa = 0")
  apply auto
  apply (drule_tac x="x" in spec)
  apply (drule_tac x="xa" in spec)
  apply auto
  by (metis div_mult_self2 gr_implies_not0 mod_div_trivial mod_less
      nat_add_commute nat_mult_commute plus_nat.add_0)

definition [hol4rew]: "DISJOINT a b \<longleftrightarrow> a \<inter> b = {}"

lemma DEF_DISJOINT:
  "DISJOINT = (%u ua. u \<inter> ua = {})"
  by (auto simp add: DISJOINT_def_raw)

lemma DEF_DIFF:
  "op - = (\<lambda>u ua. {ub. \<exists>x. (x \<in> u \<and> x \<notin> ua) \<and> ub = x})"
  by (simp add: fun_eq_iff Collect_def)
     (metis DiffE DiffI mem_def)

definition [hol4rew]: "DELETE s e = s - {e}"

lemma DEF_DELETE:
  "DELETE = (\<lambda>u ua. {ub. \<exists>y. (y \<in> u \<and> y \<noteq> ua) \<and> ub = y})"
  by (auto simp add: DELETE_def_raw)

lemma COND_DEF:
  "(if b then t else f) = (SOME x. (b = True \<longrightarrow> x = t) \<and> (b = False \<longrightarrow> x = f))"
  by auto

definition [simp]: "NUMERAL_BIT1 n = n + (n + Suc 0)"

lemma BIT1_DEF:
  "NUMERAL_BIT1 = (%u. Suc (2 * u))"
  by (auto)

definition [simp]: "NUMERAL_BIT0 (n :: nat) = n + n"

lemma BIT0_DEF:
  "NUMERAL_BIT0 = (SOME BIT0. BIT0 0 = 0 \<and> (\<forall>n. BIT0 (Suc n) = Suc (Suc (BIT0 n))))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)
  apply (induct_tac x)
  apply auto
  done

lemma [hol4rew]:
  "NUMERAL_BIT0 n = 2 * n"
  "NUMERAL_BIT1 n = 2 * n + 1"
  "2 * 0 = (0 :: nat)"
  "2 * 1 = (2 :: nat)"
  "0 + 1 = (1 :: nat)"
  by simp_all

lemma DEF_MINUS: "op - = (SOME sub. (\<forall>m. sub m 0 = m) & (\<forall>m n. sub m (Suc n) = sub m n - Suc 0))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)+
  apply (induct_tac xa)
  apply auto
  done

lemma DEF_PLUS: "op + = (SOME add. (\<forall>n. add 0 n = n) & (\<forall>m n. add (Suc m) n = Suc (add m n)))"
  apply (rule some_equality[symmetric])
  apply auto
  apply (rule ext)+
  apply (induct_tac x)
  apply auto
  done

lemmas [hol4rew] = id_apply

lemma DEF_CHOICE: "Eps = (%u. SOME x. x \<in> u)"
  by (simp add: mem_def)

definition dotdot :: "nat => nat => nat => bool"
  where "dotdot == %(u::nat) ua::nat. {ub::nat. EX x::nat. (u <= x & x <= ua) & ub = x}"

lemma DEF__dot__dot_: "dotdot = (%u ua. {ub. EX x. (u <= x & x <= ua) & ub = x})"
  by (simp add: dotdot_def)

lemma [hol4rew]: "dotdot a b = {a..b}"
  unfolding fun_eq_iff atLeastAtMost_def atLeast_def atMost_def dotdot_def
  by (simp add: Collect_conj_eq)

definition [hol4rew,simp]: "INFINITE S \<longleftrightarrow> \<not> finite S"

lemma DEF_INFINITE: "INFINITE = (\<lambda>u. \<not>finite u)"
  by (simp add: INFINITE_def_raw)

end
