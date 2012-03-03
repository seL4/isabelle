(*  Title:      HOL/Import/HOL_Light/Compatibility.thy
    Author:     Steven Obua and Sebastian Skalberg, TU Muenchen
    Author:     Cezary Kaliszyk
*)

theory Compatibility
imports Main Fact Parity "~~/src/HOL/Library/Infinite_Set"
  HOLLightList HOLLightReal HOLLightInt "~~/src/HOL/Import/HOL4Setup"
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
  "\<exists>!fn. fn 0 = e \<and> (\<forall>n. fn (Suc n) = f (fn n) n)"
  apply (rule ex1I[of _ "nat_rec e (%n e. f e n)"])
  apply (auto simp add: fun_eq_iff)
  apply (induct_tac x)
  apply simp_all
  done

lemma SUC_INJ:
  "\<forall>m n. Suc m = Suc n \<longleftrightarrow> m = n"
  by simp

lemma PAIR:
  "(fst x, snd x) = x"
  by simp

lemma EXISTS_UNIQUE_THM:
  "(Ex1 P) = (Ex P & (\<forall>x y. P x & P y --> (x = y)))"
  by auto

lemma DEF__star_:
  "op * = (SOME mult. (\<forall>n. mult 0 n = 0) \<and> (\<forall>m n. mult (Suc m) n = mult m n + n))"
  apply (rule some_equality[symmetric])
  apply (auto simp add: fun_eq_iff)
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
proof (intro allI iffI impI wfI_min[to_pred], elim exE wfE_min[to_pred])
  fix P :: "'a \<Rightarrow> bool" and xa :: "'a"
  assume "P xa"
  then show "xa \<in> Collect P" by simp
next
  fix x P xa z
  assume "P xa" "z \<in> {a. P a}" "\<And>y. x y z \<Longrightarrow> y \<notin> {a. P a}"
  then show "\<exists>xa. P xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> P y)" by auto
next
  fix x :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and xa :: "'a" and Q
  assume a: "xa \<in> Q"
  assume b: "\<forall>P. Ex P \<longrightarrow> (\<exists>xa. P xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> P y))"
  then have "Ex (\<lambda>x. x \<in> Q) \<longrightarrow> (\<exists>xa. (\<lambda>x. x \<in> Q) xa \<and> (\<forall>y. x y xa \<longrightarrow> \<not> (\<lambda>x. x \<in> Q) y))" by auto
  then show "\<exists>z\<in>Q. \<forall>y. x y z \<longrightarrow> y \<notin> Q" using a by auto
qed

lemma DEF_UNIV: "top = (%x. True)"
  by (rule ext) (simp add: top1I)

lemma DEF_UNIONS:
  "Sup = (\<lambda>u. {ua. \<exists>x. (\<exists>ua. ua \<in> u \<and> x \<in> ua) \<and> ua = x})"
  by (auto simp add: Union_eq)

lemma DEF_UNION:
  "op \<union> = (\<lambda>u ua. {ub. \<exists>x. (x \<in> u \<or> x \<in> ua) \<and> ub = x})"
  by auto

lemma DEF_SUBSET: "op \<subseteq> = (\<lambda>u ua. \<forall>x. x \<in> u \<longrightarrow> x \<in> ua)"
  by (metis set_rev_mp subsetI)

lemma DEF_SND:
  "snd = (\<lambda>p. SOME x. EX y. p = (y, x))"
  unfolding fun_eq_iff
  by (rule someI2) (auto intro: snd_conv[symmetric] someI2)

definition [simp, hol4rew]: "SETSPEC x P y \<longleftrightarrow> P & x = y"

lemma DEF_PSUBSET: "op \<subset> = (\<lambda>u ua. u \<subseteq> ua & u \<noteq> ua)"
  by (metis psubset_eq)

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
  "MEASURE u = (%a b. (a, b) \<in> measure u)"
  unfolding MEASURE_def measure_def
  by simp

definition
  "LET f s = f s"

lemma [hol4rew]:
  "LET f s = Let s f"
  by (simp add: LET_def Let_def)

lemma DEF_INTERS:
  "Inter = (\<lambda>u. {ua. \<exists>x. (\<forall>ua. ua \<in> u \<longrightarrow> x \<in> ua) \<and> ua = x})"
  by auto

lemma DEF_INTER:
  "op \<inter> = (\<lambda>u ua. {ub. \<exists>x. (x \<in> u \<and> x \<in> ua) \<and> ub = x})"
  by auto

lemma DEF_INSERT:
  "insert = (\<lambda>u ua. {y. y \<in> ua | y = u})"
  by auto

lemma DEF_IMAGE:
  "op ` = (\<lambda>u ua. {ub. \<exists>y. (\<exists>x. x \<in> ua \<and> y = u x) \<and> ub = y})"
  by (simp add: fun_eq_iff image_def Bex_def)

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
  by (metis finite_insert infinite_imp_nonempty infinite_super predicate1I)

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

lemma DEF_EMPTY: "bot = (%x. False)"
  by (rule ext) auto
  
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
  by (metis set_diff_eq)

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

lemma DEF_CHOICE: "Eps = (%u. SOME x. u x)"
  by simp

definition dotdot :: "nat => nat => nat set"
  where "dotdot u ua = {ub. EX x. (u <= x & x <= ua) & ub = x}"

lemma [hol4rew]: "dotdot a b = {a..b}"
  unfolding fun_eq_iff atLeastAtMost_def atLeast_def atMost_def dotdot_def
  by (simp add: Collect_conj_eq)

definition [hol4rew,simp]: "INFINITE S \<longleftrightarrow> \<not> finite S"

lemma DEF_INFINITE: "INFINITE = (\<lambda>u. \<not>finite u)"
  by (simp add: INFINITE_def_raw)

end

