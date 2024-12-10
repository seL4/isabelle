(*  Title:      HOL/HOLCF/Fixrec.thy
    Author:     Franz Regensburger
    Author:     Amber Telfer and Brian Huffman
*)

theory Fixrec
imports Cprod Sprod Ssum Up One Tr Cfun
keywords "fixrec" :: thy_defn
begin

section \<open>Fixed point operator and admissibility\<close>

default_sort pcpo


subsection \<open>Iteration\<close>

primrec iterate :: "nat \<Rightarrow> ('a::cpo \<rightarrow> 'a) \<rightarrow> ('a \<rightarrow> 'a)"
  where
    "iterate 0 = (\<Lambda> F x. x)"
  | "iterate (Suc n) = (\<Lambda> F x. F\<cdot>(iterate n\<cdot>F\<cdot>x))"

text \<open>Derive inductive properties of iterate from primitive recursion\<close>

lemma iterate_0 [simp]: "iterate 0\<cdot>F\<cdot>x = x"
  by simp

lemma iterate_Suc [simp]: "iterate (Suc n)\<cdot>F\<cdot>x = F\<cdot>(iterate n\<cdot>F\<cdot>x)"
  by simp

declare iterate.simps [simp del]

lemma iterate_Suc2: "iterate (Suc n)\<cdot>F\<cdot>x = iterate n\<cdot>F\<cdot>(F\<cdot>x)"
  by (induct n) simp_all

lemma iterate_iterate: "iterate m\<cdot>F\<cdot>(iterate n\<cdot>F\<cdot>x) = iterate (m + n)\<cdot>F\<cdot>x"
  by (induct m) simp_all

text \<open>The sequence of function iterations is a chain.\<close>

lemma chain_iterate [simp]: "chain (\<lambda>i. iterate i\<cdot>F\<cdot>\<bottom>)"
  by (rule chainI, unfold iterate_Suc2, rule monofun_cfun_arg, rule minimal)


subsection \<open>Least fixed point operator\<close>

definition "fix" :: "('a \<rightarrow> 'a) \<rightarrow> 'a"
  where "fix = (\<Lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>)"

text \<open>Binder syntax for \<^term>\<open>fix\<close>\<close>

abbreviation fix_syn :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"  (binder \<open>\<mu> \<close> 10)
  where "fix_syn (\<lambda>x. f x) \<equiv> fix\<cdot>(\<Lambda> x. f x)"

notation (ASCII)
  fix_syn  (binder \<open>FIX \<close> 10)

text \<open>Properties of \<^term>\<open>fix\<close>\<close>

text \<open>direct connection between \<^term>\<open>fix\<close> and iteration\<close>

lemma fix_def2: "fix\<cdot>F = (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>)"
  by (simp add: fix_def)

lemma iterate_below_fix: "iterate n\<cdot>f\<cdot>\<bottom> \<sqsubseteq> fix\<cdot>f"
  unfolding fix_def2
  using chain_iterate by (rule is_ub_thelub)

text \<open>
  Kleene's fixed point theorems for continuous functions in pointed
  omega cpo's
\<close>

lemma fix_eq: "fix\<cdot>F = F\<cdot>(fix\<cdot>F)"
  apply (simp add: fix_def2)
  apply (subst lub_range_shift [of _ 1, symmetric])
   apply (rule chain_iterate)
  apply (subst contlub_cfun_arg)
   apply (rule chain_iterate)
  apply simp
  done

lemma fix_least_below: "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
  apply (simp add: fix_def2)
  apply (rule lub_below)
   apply (rule chain_iterate)
  apply (induct_tac i)
   apply simp
  apply simp
  apply (erule rev_below_trans)
  apply (erule monofun_cfun_arg)
  done

lemma fix_least: "F\<cdot>x = x \<Longrightarrow> fix\<cdot>F \<sqsubseteq> x"
  by (rule fix_least_below) simp

lemma fix_eqI:
  assumes fixed: "F\<cdot>x = x"
    and least: "\<And>z. F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
  shows "fix\<cdot>F = x"
  apply (rule below_antisym)
   apply (rule fix_least [OF fixed])
  apply (rule least [OF fix_eq [symmetric]])
  done

lemma fix_eq2: "f \<equiv> fix\<cdot>F \<Longrightarrow> f = F\<cdot>f"
  by (simp add: fix_eq [symmetric])

lemma fix_eq3: "f \<equiv> fix\<cdot>F \<Longrightarrow> f\<cdot>x = F\<cdot>f\<cdot>x"
  by (erule fix_eq2 [THEN cfun_fun_cong])

lemma fix_eq4: "f = fix\<cdot>F \<Longrightarrow> f = F\<cdot>f"
  by (erule ssubst) (rule fix_eq)

lemma fix_eq5: "f = fix\<cdot>F \<Longrightarrow> f\<cdot>x = F\<cdot>f\<cdot>x"
  by (erule fix_eq4 [THEN cfun_fun_cong])

text \<open>strictness of \<^term>\<open>fix\<close>\<close>

lemma fix_bottom_iff: "fix\<cdot>F = \<bottom> \<longleftrightarrow> F\<cdot>\<bottom> = \<bottom>"
  apply (rule iffI)
   apply (erule subst)
   apply (rule fix_eq [symmetric])
  apply (erule fix_least [THEN bottomI])
  done

lemma fix_strict: "F\<cdot>\<bottom> = \<bottom> \<Longrightarrow> fix\<cdot>F = \<bottom>"
  by (simp add: fix_bottom_iff)

lemma fix_defined: "F\<cdot>\<bottom> \<noteq> \<bottom> \<Longrightarrow> fix\<cdot>F \<noteq> \<bottom>"
  by (simp add: fix_bottom_iff)

text \<open>\<^term>\<open>fix\<close> applied to identity and constant functions\<close>

lemma fix_id: "(\<mu> x. x) = \<bottom>"
  by (simp add: fix_strict)

lemma fix_const: "(\<mu> x. c) = c"
  by (subst fix_eq) simp


subsection \<open>Fixed point induction\<close>

lemma fix_ind: "adm P \<Longrightarrow> P \<bottom> \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P (F\<cdot>x)) \<Longrightarrow> P (fix\<cdot>F)"
  unfolding fix_def2
  apply (erule admD)
   apply (rule chain_iterate)
  apply (rule nat_induct, simp_all)
  done

lemma cont_fix_ind: "cont F \<Longrightarrow> adm P \<Longrightarrow> P \<bottom> \<Longrightarrow> (\<And>x. P x \<Longrightarrow> P (F x)) \<Longrightarrow> P (fix\<cdot>(Abs_cfun F))"
  by (simp add: fix_ind)

lemma def_fix_ind: "\<lbrakk>f \<equiv> fix\<cdot>F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P f"
  by (simp add: fix_ind)

lemma fix_ind2:
  assumes adm: "adm P"
  assumes 0: "P \<bottom>" and 1: "P (F\<cdot>\<bottom>)"
  assumes step: "\<And>x. \<lbrakk>P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
  shows "P (fix\<cdot>F)"
  unfolding fix_def2
  apply (rule admD [OF adm chain_iterate])
  apply (rule nat_less_induct)
  apply (case_tac n)
   apply (simp add: 0)
  apply (case_tac nat)
   apply (simp add: 1)
  apply (frule_tac x=nat in spec)
  apply (simp add: step)
  done

lemma parallel_fix_ind:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes base: "P \<bottom> \<bottom>"
  assumes step: "\<And>x y. P x y \<Longrightarrow> P (F\<cdot>x) (G\<cdot>y)"
  shows "P (fix\<cdot>F) (fix\<cdot>G)"
proof -
  from adm have adm': "adm (case_prod P)"
    unfolding split_def .
  have "P (iterate i\<cdot>F\<cdot>\<bottom>) (iterate i\<cdot>G\<cdot>\<bottom>)" for i
    by (induct i) (simp add: base, simp add: step)
  then have "\<And>i. case_prod P (iterate i\<cdot>F\<cdot>\<bottom>, iterate i\<cdot>G\<cdot>\<bottom>)"
    by simp
  then have "case_prod P (\<Squnion>i. (iterate i\<cdot>F\<cdot>\<bottom>, iterate i\<cdot>G\<cdot>\<bottom>))"
    by - (rule admD [OF adm'], simp, assumption)
  then have "case_prod P (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>, \<Squnion>i. iterate i\<cdot>G\<cdot>\<bottom>)"
    by (simp add: lub_Pair)
  then have "P (\<Squnion>i. iterate i\<cdot>F\<cdot>\<bottom>) (\<Squnion>i. iterate i\<cdot>G\<cdot>\<bottom>)"
    by simp
  then show "P (fix\<cdot>F) (fix\<cdot>G)"
    by (simp add: fix_def2)
qed

lemma cont_parallel_fix_ind:
  assumes "cont F" and "cont G"
  assumes "adm (\<lambda>x. P (fst x) (snd x))"
  assumes "P \<bottom> \<bottom>"
  assumes "\<And>x y. P x y \<Longrightarrow> P (F x) (G y)"
  shows "P (fix\<cdot>(Abs_cfun F)) (fix\<cdot>(Abs_cfun G))"
  by (rule parallel_fix_ind) (simp_all add: assms)


subsection \<open>Fixed-points on product types\<close>

text \<open>
  Bekic's Theorem: Simultaneous fixed points over pairs
  can be written in terms of separate fixed points.
\<close>

lemma fix_cprod:
  "fix\<cdot>(F::'a \<times> 'b \<rightarrow> 'a \<times> 'b) =
   (\<mu> x. fst (F\<cdot>(x, \<mu> y. snd (F\<cdot>(x, y)))),
    \<mu> y. snd (F\<cdot>(\<mu> x. fst (F\<cdot>(x, \<mu> y. snd (F\<cdot>(x, y)))), y)))"
  (is "fix\<cdot>F = (?x, ?y)")
proof (rule fix_eqI)
  have *: "fst (F\<cdot>(?x, ?y)) = ?x"
    by (rule trans [symmetric, OF fix_eq], simp)
  have "snd (F\<cdot>(?x, ?y)) = ?y"
    by (rule trans [symmetric, OF fix_eq], simp)
  with * show "F\<cdot>(?x, ?y) = (?x, ?y)"
    by (simp add: prod_eq_iff)
next
  fix z
  assume F_z: "F\<cdot>z = z"
  obtain x y where z: "z = (x, y)" by (rule prod.exhaust)
  from F_z z have F_x: "fst (F\<cdot>(x, y)) = x" by simp
  from F_z z have F_y: "snd (F\<cdot>(x, y)) = y" by simp
  let ?y1 = "\<mu> y. snd (F\<cdot>(x, y))"
  have "?y1 \<sqsubseteq> y"
    by (rule fix_least) (simp add: F_y)
  then have "fst (F\<cdot>(x, ?y1)) \<sqsubseteq> fst (F\<cdot>(x, y))"
    by (simp add: fst_monofun monofun_cfun)
  with F_x have "fst (F\<cdot>(x, ?y1)) \<sqsubseteq> x"
    by simp
  then have *: "?x \<sqsubseteq> x"
    by (simp add: fix_least_below)
  then have "snd (F\<cdot>(?x, y)) \<sqsubseteq> snd (F\<cdot>(x, y))"
    by (simp add: snd_monofun monofun_cfun)
  with F_y have "snd (F\<cdot>(?x, y)) \<sqsubseteq> y"
    by simp
  then have "?y \<sqsubseteq> y"
    by (simp add: fix_least_below)
  with z * show "(?x, ?y) \<sqsubseteq> z"
    by simp
qed


section "Package for defining recursive functions in HOLCF"

subsection \<open>Pattern-match monad\<close>

default_sort cpo

pcpodef 'a match = "UNIV::(one ++ 'a u) set"
by simp_all

definition
  fail :: "'a match" where
  "fail = Abs_match (sinl\<cdot>ONE)"

definition
  succeed :: "'a \<rightarrow> 'a match" where
  "succeed = (\<Lambda> x. Abs_match (sinr\<cdot>(up\<cdot>x)))"

lemma matchE [case_names bottom fail succeed, cases type: match]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = fail \<Longrightarrow> Q; \<And>x. p = succeed\<cdot>x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding fail_def succeed_def
apply (cases p, rename_tac r)
apply (rule_tac p=r in ssumE, simp add: Abs_match_strict)
apply (rule_tac p=x in oneE, simp, simp)
apply (rule_tac p=y in upE, simp, simp add: cont_Abs_match)
done

lemma succeed_defined [simp]: "succeed\<cdot>x \<noteq> \<bottom>"
by (simp add: succeed_def cont_Abs_match Abs_match_bottom_iff)

lemma fail_defined [simp]: "fail \<noteq> \<bottom>"
by (simp add: fail_def Abs_match_bottom_iff)

lemma succeed_eq [simp]: "(succeed\<cdot>x = succeed\<cdot>y) = (x = y)"
by (simp add: succeed_def cont_Abs_match Abs_match_inject)

lemma succeed_neq_fail [simp]:
  "succeed\<cdot>x \<noteq> fail" "fail \<noteq> succeed\<cdot>x"
by (simp_all add: succeed_def fail_def cont_Abs_match Abs_match_inject)

subsubsection \<open>Run operator\<close>

definition
  run :: "'a match \<rightarrow> 'a::pcpo" where
  "run = (\<Lambda> m. sscase\<cdot>\<bottom>\<cdot>(fup\<cdot>ID)\<cdot>(Rep_match m))"

text \<open>rewrite rules for run\<close>

lemma run_strict [simp]: "run\<cdot>\<bottom> = \<bottom>"
unfolding run_def
by (simp add: cont_Rep_match Rep_match_strict)

lemma run_fail [simp]: "run\<cdot>fail = \<bottom>"
unfolding run_def fail_def
by (simp add: cont_Rep_match Abs_match_inverse)

lemma run_succeed [simp]: "run\<cdot>(succeed\<cdot>x) = x"
unfolding run_def succeed_def
by (simp add: cont_Rep_match cont_Abs_match Abs_match_inverse)

subsubsection \<open>Monad plus operator\<close>

definition
  mplus :: "'a match \<rightarrow> 'a match \<rightarrow> 'a match" where
  "mplus = (\<Lambda> m1 m2. sscase\<cdot>(\<Lambda> _. m2)\<cdot>(\<Lambda> _. m1)\<cdot>(Rep_match m1))"

abbreviation
  mplus_syn :: "['a match, 'a match] \<Rightarrow> 'a match"  (infixr \<open>+++\<close> 65)  where
  "m1 +++ m2 == mplus\<cdot>m1\<cdot>m2"

text \<open>rewrite rules for mplus\<close>

lemma mplus_strict [simp]: "\<bottom> +++ m = \<bottom>"
unfolding mplus_def
by (simp add: cont_Rep_match Rep_match_strict)

lemma mplus_fail [simp]: "fail +++ m = m"
unfolding mplus_def fail_def
by (simp add: cont_Rep_match Abs_match_inverse)

lemma mplus_succeed [simp]: "succeed\<cdot>x +++ m = succeed\<cdot>x"
unfolding mplus_def succeed_def
by (simp add: cont_Rep_match cont_Abs_match Abs_match_inverse)

lemma mplus_fail2 [simp]: "m +++ fail = m"
by (cases m, simp_all)

lemma mplus_assoc: "(x +++ y) +++ z = x +++ (y +++ z)"
by (cases x, simp_all)

subsection \<open>Match functions for built-in types\<close>

default_sort pcpo

definition
  match_bottom :: "'a \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_bottom = (\<Lambda> x k. seq\<cdot>x\<cdot>fail)"

definition
  match_Pair :: "'a::cpo \<times> 'b::cpo \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_Pair = (\<Lambda> x k. csplit\<cdot>k\<cdot>x)"

definition
  match_spair :: "'a \<otimes> 'b \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_spair = (\<Lambda> x k. ssplit\<cdot>k\<cdot>x)"

definition
  match_sinl :: "'a \<oplus> 'b \<rightarrow> ('a \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_sinl = (\<Lambda> x k. sscase\<cdot>k\<cdot>(\<Lambda> b. fail)\<cdot>x)"

definition
  match_sinr :: "'a \<oplus> 'b \<rightarrow> ('b \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_sinr = (\<Lambda> x k. sscase\<cdot>(\<Lambda> a. fail)\<cdot>k\<cdot>x)"

definition
  match_up :: "'a::cpo u \<rightarrow> ('a \<rightarrow> 'c match) \<rightarrow> 'c match"
where
  "match_up = (\<Lambda> x k. fup\<cdot>k\<cdot>x)"

definition
  match_ONE :: "one \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_ONE = (\<Lambda> ONE k. k)"

definition
  match_TT :: "tr \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_TT = (\<Lambda> x k. If x then k else fail)"

definition
  match_FF :: "tr \<rightarrow> 'c match \<rightarrow> 'c match"
where
  "match_FF = (\<Lambda> x k. If x then fail else k)"

lemma match_bottom_simps [simp]:
  "match_bottom\<cdot>x\<cdot>k = (if x = \<bottom> then \<bottom> else fail)"
by (simp add: match_bottom_def)

lemma match_Pair_simps [simp]:
  "match_Pair\<cdot>(x, y)\<cdot>k = k\<cdot>x\<cdot>y"
by (simp_all add: match_Pair_def)

lemma match_spair_simps [simp]:
  "\<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> match_spair\<cdot>(:x, y:)\<cdot>k = k\<cdot>x\<cdot>y"
  "match_spair\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_spair_def)

lemma match_sinl_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinl\<cdot>x)\<cdot>k = k\<cdot>x"
  "y \<noteq> \<bottom> \<Longrightarrow> match_sinl\<cdot>(sinr\<cdot>y)\<cdot>k = fail"
  "match_sinl\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_sinl_def)

lemma match_sinr_simps [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinl\<cdot>x)\<cdot>k = fail"
  "y \<noteq> \<bottom> \<Longrightarrow> match_sinr\<cdot>(sinr\<cdot>y)\<cdot>k = k\<cdot>y"
  "match_sinr\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_sinr_def)

lemma match_up_simps [simp]:
  "match_up\<cdot>(up\<cdot>x)\<cdot>k = k\<cdot>x"
  "match_up\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_up_def)

lemma match_ONE_simps [simp]:
  "match_ONE\<cdot>ONE\<cdot>k = k"
  "match_ONE\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_ONE_def)

lemma match_TT_simps [simp]:
  "match_TT\<cdot>TT\<cdot>k = k"
  "match_TT\<cdot>FF\<cdot>k = fail"
  "match_TT\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_TT_def)

lemma match_FF_simps [simp]:
  "match_FF\<cdot>FF\<cdot>k = k"
  "match_FF\<cdot>TT\<cdot>k = fail"
  "match_FF\<cdot>\<bottom>\<cdot>k = \<bottom>"
by (simp_all add: match_FF_def)

subsection \<open>Mutual recursion\<close>

text \<open>
  The following rules are used to prove unfolding theorems from
  fixed-point definitions of mutually recursive functions.
\<close>

lemma Pair_equalI: "\<lbrakk>x \<equiv> fst p; y \<equiv> snd p\<rbrakk> \<Longrightarrow> (x, y) \<equiv> p"
by simp

lemma Pair_eqD1: "(x, y) = (x', y') \<Longrightarrow> x = x'"
by simp

lemma Pair_eqD2: "(x, y) = (x', y') \<Longrightarrow> y = y'"
by simp

lemma def_cont_fix_eq:
  "\<lbrakk>f \<equiv> fix\<cdot>(Abs_cfun F); cont F\<rbrakk> \<Longrightarrow> f = F f"
by (simp, subst fix_eq, simp)

lemma def_cont_fix_ind:
  "\<lbrakk>f \<equiv> fix\<cdot>(Abs_cfun F); cont F; adm P; P \<bottom>; \<And>x. P x \<Longrightarrow> P (F x)\<rbrakk> \<Longrightarrow> P f"
by (simp add: fix_ind)

text \<open>lemma for proving rewrite rules\<close>

lemma ssubst_lhs: "\<lbrakk>t = s; P s = Q\<rbrakk> \<Longrightarrow> P t = Q"
by simp


subsection \<open>Initializing the fixrec package\<close>

ML_file \<open>Tools/holcf_library.ML\<close>
ML_file \<open>Tools/fixrec.ML\<close>

method_setup fixrec_simp = \<open>
  Scan.succeed (SIMPLE_METHOD' o Fixrec.fixrec_simp_tac)
\<close> "pattern prover for fixrec constants"

setup \<open>
  Fixrec.add_matchers
    [ (\<^const_name>\<open>up\<close>, \<^const_name>\<open>match_up\<close>),
      (\<^const_name>\<open>sinl\<close>, \<^const_name>\<open>match_sinl\<close>),
      (\<^const_name>\<open>sinr\<close>, \<^const_name>\<open>match_sinr\<close>),
      (\<^const_name>\<open>spair\<close>, \<^const_name>\<open>match_spair\<close>),
      (\<^const_name>\<open>Pair\<close>, \<^const_name>\<open>match_Pair\<close>),
      (\<^const_name>\<open>ONE\<close>, \<^const_name>\<open>match_ONE\<close>),
      (\<^const_name>\<open>TT\<close>, \<^const_name>\<open>match_TT\<close>),
      (\<^const_name>\<open>FF\<close>, \<^const_name>\<open>match_FF\<close>),
      (\<^const_name>\<open>bottom\<close>, \<^const_name>\<open>match_bottom\<close>) ]
\<close>

hide_const (open) succeed fail run

end
