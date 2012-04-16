(*  Title:      HOL/Nominal/Examples/Standardization.thy
    Author:     Stefan Berghofer and Tobias Nipkow
    Copyright   2005, 2008 TU Muenchen
*)

header {* Standardization *}

theory Standardization
imports "../Nominal"
begin

text {*
The proof of the standardization theorem, as well as most of the theorems about
lambda calculus in the following sections, are taken from @{text "HOL/Lambda"}.
*}

subsection {* Lambda terms *}

atom_decl name

nominal_datatype lam =
  Var "name"
| App "lam" "lam" (infixl "\<degree>" 200)
| Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [0, 10] 10)

instantiation lam :: size
begin

nominal_primrec size_lam
where
  "size (Var n) = 0"
| "size (t \<degree> u) = size t + size u + 1"
| "size (Lam [x].t) = size t + 1"
  apply finite_guess+
  apply (rule TrueI)+
  apply (simp add: fresh_nat)
  apply fresh_guess+
  done

instance ..

end

nominal_primrec
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [300, 0, 0] 300)
where
  subst_Var: "(Var x)[y::=s] = (if x=y then s else (Var x))"
| subst_App: "(t\<^isub>1 \<degree> t\<^isub>2)[y::=s] = t\<^isub>1[y::=s] \<degree> t\<^isub>2[y::=s]"
| subst_Lam: "x \<sharp> (y, s) \<Longrightarrow> (Lam [x].t)[y::=s] = (Lam [x].(t[y::=s]))"
  apply(finite_guess)+
  apply(rule TrueI)+
  apply(simp add: abs_fresh)
  apply(fresh_guess)+
  done

lemma subst_eqvt [eqvt]:
  "(pi::name prm) \<bullet> (t[x::=u]) = (pi \<bullet> t)[(pi \<bullet> x)::=(pi \<bullet> u)]"
  by (nominal_induct t avoiding: x u rule: lam.strong_induct)
    (perm_simp add: fresh_bij)+

lemma subst_rename:
  "y \<sharp> t \<Longrightarrow> ([(y, x)] \<bullet> t)[y::=u] = t[x::=u]"
  by (nominal_induct t avoiding: x y u rule: lam.strong_induct)
    (simp_all add: fresh_atm calc_atm abs_fresh)

lemma fresh_subst: 
  "(x::name) \<sharp> t \<Longrightarrow> x \<sharp> u \<Longrightarrow> x \<sharp> t[y::=u]"
  by (nominal_induct t avoiding: x y u rule: lam.strong_induct)
    (auto simp add: abs_fresh fresh_atm)

lemma fresh_subst': 
  "(x::name) \<sharp> u \<Longrightarrow> x \<sharp> t[x::=u]"
  by (nominal_induct t avoiding: x u rule: lam.strong_induct)
    (auto simp add: abs_fresh fresh_atm)

lemma subst_forget: "(x::name) \<sharp> t \<Longrightarrow> t[x::=u] = t"
  by (nominal_induct t avoiding: x u rule: lam.strong_induct)
    (auto simp add: abs_fresh fresh_atm)

lemma subst_subst:
  "x \<noteq> y \<Longrightarrow> x \<sharp> v \<Longrightarrow> t[y::=v][x::=u[y::=v]] = t[x::=u][y::=v]"
  by (nominal_induct t avoiding: x y u v rule: lam.strong_induct)
    (auto simp add: fresh_subst subst_forget)

declare subst_Var [simp del]

lemma subst_eq [simp]: "(Var x)[x::=u] = u"
  by (simp add: subst_Var)

lemma subst_neq [simp]: "x \<noteq> y \<Longrightarrow> (Var x)[y::=u] = Var x"
  by (simp add: subst_Var)

inductive beta :: "lam \<Rightarrow> lam \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta: "x \<sharp> t \<Longrightarrow> (Lam [x].s) \<degree> t \<rightarrow>\<^sub>\<beta> s[x::=t]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> (Lam [x].s) \<rightarrow>\<^sub>\<beta> (Lam [x].t)"

equivariance beta
nominal_inductive beta
  by (simp_all add: abs_fresh fresh_subst')

lemma better_beta [simp, intro!]: "(Lam [x].s) \<degree> t \<rightarrow>\<^sub>\<beta> s[x::=t]"
proof -
  obtain y::name where y: "y \<sharp> (x, s, t)"
    by (rule exists_fresh) (rule fin_supp)
  then have "y \<sharp> t" by simp
  then have "(Lam [y]. [(y, x)] \<bullet> s) \<degree> t \<rightarrow>\<^sub>\<beta> ([(y, x)] \<bullet> s)[y::=t]"
    by (rule beta)
  moreover from y have "(Lam [x].s) = (Lam [y]. [(y, x)] \<bullet> s)"
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  ultimately show ?thesis using y by (simp add: subst_rename)
qed

abbreviation
  beta_reds :: "lam \<Rightarrow> lam \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<equiv> beta\<^sup>*\<^sup>* s t"


subsection {* Application of a term to a list of terms *}

abbreviation
  list_application :: "lam \<Rightarrow> lam list \<Rightarrow> lam"  (infixl "\<degree>\<degree>" 150) where
  "t \<degree>\<degree> ts \<equiv> foldl (op \<degree>) t ts"

lemma apps_eq_tail_conv [iff]: "(r \<degree>\<degree> ts = s \<degree>\<degree> ts) = (r = s)"
  by (induct ts rule: rev_induct) (auto simp add: lam.inject)

lemma Var_eq_apps_conv [iff]: "(Var m = s \<degree>\<degree> ss) = (Var m = s \<and> ss = [])"
  by (induct ss arbitrary: s) auto

lemma Var_apps_eq_Var_apps_conv [iff]:
    "(Var m \<degree>\<degree> rs = Var n \<degree>\<degree> ss) = (m = n \<and> rs = ss)"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply (simp add: lam.inject)
   apply blast
  apply (induct_tac ss rule: rev_induct)
   apply (auto simp add: lam.inject)
  done

lemma App_eq_foldl_conv:
  "(r \<degree> s = t \<degree>\<degree> ts) =
    (if ts = [] then r \<degree> s = t
    else (\<exists>ss. ts = ss @ [s] \<and> r = t \<degree>\<degree> ss))"
  apply (rule_tac xs = ts in rev_exhaust)
   apply (auto simp add: lam.inject)
  done

lemma Abs_eq_apps_conv [iff]:
    "((Lam [x].r) = s \<degree>\<degree> ss) = ((Lam [x].r) = s \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma apps_eq_Abs_conv [iff]: "(s \<degree>\<degree> ss = (Lam [x].r)) = (s = (Lam [x].r) \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma Abs_App_neq_Var_apps [iff]:
    "(Lam [x].s) \<degree> t \<noteq> Var n \<degree>\<degree> ss"
  by (induct ss arbitrary: s t rule: rev_induct) (auto simp add: lam.inject)

lemma Var_apps_neq_Abs_apps [iff]:
    "Var n \<degree>\<degree> ts \<noteq> (Lam [x].r) \<degree>\<degree> ss"
  apply (induct ss arbitrary: ts rule: rev_induct)
   apply simp
  apply (induct_tac ts rule: rev_induct)
   apply (auto simp add: lam.inject)
  done

lemma ex_head_tail:
  "\<exists>ts h. t = h \<degree>\<degree> ts \<and> ((\<exists>n. h = Var n) \<or> (\<exists>x u. h = (Lam [x].u)))"
  apply (induct t rule: lam.induct)
    apply (metis foldl_Nil)
   apply (metis foldl_Cons foldl_Nil foldl_append)
  apply (metis foldl_Nil)
  done

lemma size_apps [simp]:
  "size (r \<degree>\<degree> rs) = size r + foldl (op +) 0 (map size rs) + length rs"
  by (induct rs rule: rev_induct) auto

lemma lem0: "(0::nat) < k \<Longrightarrow> m \<le> n \<Longrightarrow> m < n + k"
  by simp

lemma subst_map [simp]:
    "(t \<degree>\<degree> ts)[x::=u] = t[x::=u] \<degree>\<degree> map (\<lambda>t. t[x::=u]) ts"
  by (induct ts arbitrary: t) simp_all

lemma app_last: "(t \<degree>\<degree> ts) \<degree> u = t \<degree>\<degree> (ts @ [u])"
  by simp

lemma perm_apps [eqvt]:
  "(pi::name prm) \<bullet> (t \<degree>\<degree> ts) = ((pi \<bullet> t) \<degree>\<degree> (pi \<bullet> ts))"
  by (induct ts rule: rev_induct) (auto simp add: append_eqvt)

lemma fresh_apps [simp]: "(x::name) \<sharp> (t \<degree>\<degree> ts) = (x \<sharp> t \<and> x \<sharp> ts)"
  by (induct ts rule: rev_induct)
    (auto simp add: fresh_list_append fresh_list_nil fresh_list_cons)

text {* A customized induction schema for @{text "\<degree>\<degree>"}. *}

lemma lem:
  assumes "\<And>n ts (z::'a::fs_name). (\<And>z. \<forall>t \<in> set ts. P z t) \<Longrightarrow> P z (Var n \<degree>\<degree> ts)"
    and "\<And>x u ts z. x \<sharp> z \<Longrightarrow> (\<And>z. P z u) \<Longrightarrow> (\<And>z. \<forall>t \<in> set ts. P z t) \<Longrightarrow> P z ((Lam [x].u) \<degree>\<degree> ts)"
  shows "size t = n \<Longrightarrow> P z t"
  apply (induct n arbitrary: t z rule: nat_less_induct)
  apply (cut_tac t = t in ex_head_tail)
  apply clarify
  apply (erule disjE)
   apply clarify
   apply (rule assms)
   apply clarify
   apply (erule allE, erule impE)
    prefer 2
    apply (erule allE, erule impE, rule refl, erule spec)
    apply simp
    apply (simp only: foldl_conv_fold add_commute fold_plus_listsum_rev)
    apply (fastforce simp add: listsum_map_remove1)
  apply clarify
  apply (subgoal_tac "\<exists>y::name. y \<sharp> (x, u, z)")
   prefer 2
   apply (blast intro: exists_fresh' fin_supp) 
  apply (erule exE)
  apply (subgoal_tac "(Lam [x].u) = (Lam [y].([(y, x)] \<bullet> u))")
  prefer 2
  apply (auto simp add: lam.inject alpha' fresh_prod fresh_atm)[]
  apply (simp (no_asm_simp))
  apply (rule assms)
  apply (simp add: fresh_prod)
   apply (erule allE, erule impE)
    prefer 2
    apply (erule allE, erule impE, rule refl, erule spec)
   apply simp
  apply clarify
  apply (erule allE, erule impE)
   prefer 2
   apply blast
  apply simp
  apply (simp only: foldl_conv_fold add_commute fold_plus_listsum_rev)
  apply (fastforce simp add: listsum_map_remove1)
  done

theorem Apps_lam_induct:
  assumes "\<And>n ts (z::'a::fs_name). (\<And>z. \<forall>t \<in> set ts. P z t) \<Longrightarrow> P z (Var n \<degree>\<degree> ts)"
    and "\<And>x u ts z. x \<sharp> z \<Longrightarrow> (\<And>z. P z u) \<Longrightarrow> (\<And>z. \<forall>t \<in> set ts. P z t) \<Longrightarrow> P z ((Lam [x].u) \<degree>\<degree> ts)"
  shows "P z t"
  apply (rule_tac t = t and z = z in lem)
    prefer 3
    apply (rule refl)
    using assms apply blast+
  done


subsection {* Congruence rules *}

lemma apps_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta> s \<degree>\<degree> ss"
  by (induct ss rule: rev_induct) auto

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> (Lam [x].s) \<rightarrow>\<^sub>\<beta>\<^sup>* (Lam [x].s')"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s \<degree> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)


subsection {* Lifting an order to lists of elements *}

definition
  step1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "step1 r =
    (\<lambda>ys xs. \<exists>us z z' vs. xs = us @ z # vs \<and> r z' z \<and> ys =
      us @ z' # vs)"

lemma not_Nil_step1 [iff]: "\<not> step1 r [] xs"
  apply (unfold step1_def)
  apply blast
  done

lemma not_step1_Nil [iff]: "\<not> step1 r xs []"
  apply (unfold step1_def)
  apply blast
  done

lemma Cons_step1_Cons [iff]:
    "(step1 r (y # ys) (x # xs)) =
      (r y x \<and> xs = ys \<or> x = y \<and> step1 r ys xs)"
  apply (unfold step1_def)
  apply (rule iffI)
   apply (erule exE)
   apply (rename_tac ts)
   apply (case_tac ts)
    apply fastforce
   apply force
  apply (erule disjE)
   apply blast
  apply (blast intro: Cons_eq_appendI)
  done

lemma append_step1I:
  "step1 r ys xs \<and> vs = us \<or> ys = xs \<and> step1 r vs us
    \<Longrightarrow> step1 r (ys @ vs) (xs @ us)"
  apply (unfold step1_def)
  apply auto
   apply blast
  apply (blast intro: append_eq_appendI)
  done

lemma Cons_step1E [elim!]:
  assumes "step1 r ys (x # xs)"
    and "\<And>y. ys = y # xs \<Longrightarrow> r y x \<Longrightarrow> R"
    and "\<And>zs. ys = x # zs \<Longrightarrow> step1 r zs xs \<Longrightarrow> R"
  shows R
  using assms
  apply (cases ys)
   apply (simp add: step1_def)
  apply blast
  done

lemma Snoc_step1_SnocD:
  "step1 r (ys @ [y]) (xs @ [x])
    \<Longrightarrow> (step1 r ys xs \<and> y = x \<or> ys = xs \<and> r y x)"
  apply (unfold step1_def)
  apply (clarify del: disjCI)
  apply (rename_tac vs)
  apply (rule_tac xs = vs in rev_exhaust)
   apply force
  apply simp
  apply blast
  done


subsection {* Lifting beta-reduction to lists *}

abbreviation
  list_beta :: "lam list \<Rightarrow> lam list \<Rightarrow> bool"  (infixl "[\<rightarrow>\<^sub>\<beta>]\<^sub>1" 50) where
  "rs [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ss \<equiv> step1 beta rs ss"

lemma head_Var_reduction:
  "Var n \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> v \<Longrightarrow> \<exists>ss. rs [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ss \<and> v = Var n \<degree>\<degree> ss"
  apply (induct u \<equiv> "Var n \<degree>\<degree> rs" v arbitrary: rs set: beta)
     apply simp
    apply (rule_tac xs = rs in rev_exhaust)
     apply simp
    apply (atomize, force intro: append_step1I iff: lam.inject)
   apply (rule_tac xs = rs in rev_exhaust)
    apply simp
    apply (auto 0 3 intro: disjI2 [THEN append_step1I] simp add: lam.inject)
  done

lemma apps_betasE [case_names appL appR beta, consumes 1]:
  assumes major: "r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> s"
    and cases: "\<And>r'. r \<rightarrow>\<^sub>\<beta> r' \<Longrightarrow> s = r' \<degree>\<degree> rs \<Longrightarrow> R"
      "\<And>rs'. rs [\<rightarrow>\<^sub>\<beta>]\<^sub>1 rs' \<Longrightarrow> s = r \<degree>\<degree> rs' \<Longrightarrow> R"
      "\<And>t u us. (x \<sharp> r \<Longrightarrow> r = (Lam [x].t) \<and> rs = u # us \<and> s = t[x::=u] \<degree>\<degree> us) \<Longrightarrow> R"
  shows R
proof -
  from major have
   "(\<exists>r'. r \<rightarrow>\<^sub>\<beta> r' \<and> s = r' \<degree>\<degree> rs) \<or>
    (\<exists>rs'. rs [\<rightarrow>\<^sub>\<beta>]\<^sub>1 rs' \<and> s = r \<degree>\<degree> rs') \<or>
    (\<exists>t u us. x \<sharp> r \<longrightarrow> r = (Lam [x].t) \<and> rs = u # us \<and> s = t[x::=u] \<degree>\<degree> us)"
    apply (nominal_induct u \<equiv> "r \<degree>\<degree> rs" s avoiding: x r rs rule: beta.strong_induct)
    apply (simp add: App_eq_foldl_conv)
    apply (split split_if_asm)
    apply simp
    apply blast
    apply simp
    apply (rule impI)+
    apply (rule disjI2)
    apply (rule disjI2)
    apply (subgoal_tac "r = [(xa, x)] \<bullet> (Lam [x].s)")
    prefer 2
    apply (simp add: perm_fresh_fresh)
    apply (drule conjunct1)
    apply (subgoal_tac "r = (Lam [xa]. [(xa, x)] \<bullet> s)")
    prefer 2
    apply (simp add: calc_atm)
    apply (thin_tac "r = ?t")
    apply simp
    apply (rule exI)
    apply (rule conjI)
    apply (rule refl)
    apply (simp add: abs_fresh fresh_atm fresh_left calc_atm subst_rename)
      apply (drule App_eq_foldl_conv [THEN iffD1])
      apply (split split_if_asm)
       apply simp
       apply blast
      apply (force intro!: disjI1 [THEN append_step1I] simp add: fresh_list_append)
     apply (drule App_eq_foldl_conv [THEN iffD1])
     apply (split split_if_asm)
      apply simp
      apply blast
     apply (clarify, auto 0 3 intro!: exI intro: append_step1I)
    done
  with cases show ?thesis by blast
qed

lemma apps_preserves_betas [simp]:
    "rs [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ss \<Longrightarrow> r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> r \<degree>\<degree> ss"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
  apply simp
  apply (rule_tac xs = ss in rev_exhaust)
   apply simp
  apply simp
  apply (drule Snoc_step1_SnocD)
  apply blast
  done


subsection {* Standard reduction relation *}

text {*
Based on lecture notes by Ralph Matthes,
original proof idea due to Ralph Loader.
*}

declare listrel_mono [mono_set]

lemma listrelp_eqvt [eqvt]:
  fixes f :: "'a::pt_name \<Rightarrow> 'b::pt_name \<Rightarrow> bool"
  assumes xy: "listrelp f (x::'a::pt_name list) y"
  shows "listrelp ((pi::name prm) \<bullet> f) (pi \<bullet> x) (pi \<bullet> y)" using xy
  by induct (simp_all add: listrelp.intros perm_app [symmetric])

inductive
  sred :: "lam \<Rightarrow> lam \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>s" 50)
  and sredlist :: "lam list \<Rightarrow> lam list \<Rightarrow> bool"  (infixl "[\<rightarrow>\<^sub>s]" 50)
where
  "s [\<rightarrow>\<^sub>s] t \<equiv> listrelp op \<rightarrow>\<^sub>s s t"
| Var: "rs [\<rightarrow>\<^sub>s] rs' \<Longrightarrow> Var x \<degree>\<degree> rs \<rightarrow>\<^sub>s Var x \<degree>\<degree> rs'"
| Abs: "x \<sharp> (ss, ss') \<Longrightarrow> r \<rightarrow>\<^sub>s r' \<Longrightarrow> ss [\<rightarrow>\<^sub>s] ss' \<Longrightarrow> (Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s (Lam [x].r') \<degree>\<degree> ss'"
| Beta: "x \<sharp> (s, ss, t) \<Longrightarrow> r[x::=s] \<degree>\<degree> ss \<rightarrow>\<^sub>s t \<Longrightarrow> (Lam [x].r) \<degree> s \<degree>\<degree> ss \<rightarrow>\<^sub>s t"

equivariance sred
nominal_inductive sred
  by (simp add: abs_fresh)+

lemma better_sred_Abs:
  assumes H1: "r \<rightarrow>\<^sub>s r'"
  and H2: "ss [\<rightarrow>\<^sub>s] ss'"
  shows "(Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s (Lam [x].r') \<degree>\<degree> ss'"
proof -
  obtain y::name where y: "y \<sharp> (x, r, r', ss, ss')"
    by (rule exists_fresh) (rule fin_supp)
  then have "y \<sharp> (ss, ss')" by simp
  moreover from H1 have "[(y, x)] \<bullet> (r \<rightarrow>\<^sub>s r')" by (rule perm_boolI)
  then have "([(y, x)] \<bullet> r) \<rightarrow>\<^sub>s ([(y, x)] \<bullet> r')" by (simp add: eqvts)
  ultimately have "(Lam [y]. [(y, x)] \<bullet> r) \<degree>\<degree> ss \<rightarrow>\<^sub>s (Lam [y]. [(y, x)] \<bullet> r') \<degree>\<degree> ss'" using H2
    by (rule sred.Abs)
  moreover from y have "(Lam [x].r) = (Lam [y]. [(y, x)] \<bullet> r)"
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  moreover from y have "(Lam [x].r') = (Lam [y]. [(y, x)] \<bullet> r')"
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  ultimately show ?thesis by simp
qed

lemma better_sred_Beta:
  assumes H: "r[x::=s] \<degree>\<degree> ss \<rightarrow>\<^sub>s t"
  shows "(Lam [x].r) \<degree> s \<degree>\<degree> ss \<rightarrow>\<^sub>s t"
proof -
  obtain y::name where y: "y \<sharp> (x, r, s, ss, t)"
    by (rule exists_fresh) (rule fin_supp)
  then have "y \<sharp> (s, ss, t)" by simp
  moreover from y H have "([(y, x)] \<bullet> r)[y::=s] \<degree>\<degree> ss \<rightarrow>\<^sub>s t"
    by (simp add: subst_rename)
  ultimately have "(Lam [y].[(y, x)] \<bullet> r) \<degree> s \<degree>\<degree> ss \<rightarrow>\<^sub>s t"
    by (rule sred.Beta)
  moreover from y have "(Lam [x].r) = (Lam [y]. [(y, x)] \<bullet> r)"
    by (auto simp add: lam.inject alpha' fresh_prod fresh_atm)
  ultimately show ?thesis by simp
qed

lemmas better_sred_intros = sred.Var better_sred_Abs better_sred_Beta

lemma refl_listrelp: "\<forall>x\<in>set xs. R x x \<Longrightarrow> listrelp R xs xs"
  by (induct xs) (auto intro: listrelp.intros)

lemma refl_sred: "t \<rightarrow>\<^sub>s t"
  by (nominal_induct t rule: Apps_lam_induct) (auto intro: refl_listrelp better_sred_intros)

lemma listrelp_conj1: "listrelp (\<lambda>x y. R x y \<and> S x y) x y \<Longrightarrow> listrelp R x y"
  by (erule listrelp.induct) (auto intro: listrelp.intros)

lemma listrelp_conj2: "listrelp (\<lambda>x y. R x y \<and> S x y) x y \<Longrightarrow> listrelp S x y"
  by (erule listrelp.induct) (auto intro: listrelp.intros)

lemma listrelp_app:
  assumes xsys: "listrelp R xs ys"
  shows "listrelp R xs' ys' \<Longrightarrow> listrelp R (xs @ xs') (ys @ ys')" using xsys
  by (induct arbitrary: xs' ys') (auto intro: listrelp.intros)

lemma lemma1:
  assumes r: "r \<rightarrow>\<^sub>s r'" and s: "s \<rightarrow>\<^sub>s s'"
  shows "r \<degree> s \<rightarrow>\<^sub>s r' \<degree> s'" using r
proof induct
  case (Var rs rs' x)
  then have "rs [\<rightarrow>\<^sub>s] rs'" by (rule listrelp_conj1)
  moreover have "[s] [\<rightarrow>\<^sub>s] [s']" by (iprover intro: s listrelp.intros)
  ultimately have "rs @ [s] [\<rightarrow>\<^sub>s] rs' @ [s']" by (rule listrelp_app)
  hence "Var x \<degree>\<degree> (rs @ [s]) \<rightarrow>\<^sub>s Var x \<degree>\<degree> (rs' @ [s'])" by (rule sred.Var)
  thus ?case by (simp only: app_last)
next
  case (Abs x ss ss' r r')
  from Abs(4) have "ss [\<rightarrow>\<^sub>s] ss'" by (rule listrelp_conj1)
  moreover have "[s] [\<rightarrow>\<^sub>s] [s']" by (iprover intro: s listrelp.intros)
  ultimately have "ss @ [s] [\<rightarrow>\<^sub>s] ss' @ [s']" by (rule listrelp_app)
  with `r \<rightarrow>\<^sub>s r'` have "(Lam [x].r) \<degree>\<degree> (ss @ [s]) \<rightarrow>\<^sub>s (Lam [x].r') \<degree>\<degree> (ss' @ [s'])"
    by (rule better_sred_Abs)
  thus ?case by (simp only: app_last)
next
  case (Beta x u ss t r)
  hence "r[x::=u] \<degree>\<degree> (ss @ [s]) \<rightarrow>\<^sub>s t \<degree> s'" by (simp only: app_last)
  hence "(Lam [x].r) \<degree> u \<degree>\<degree> (ss @ [s]) \<rightarrow>\<^sub>s t \<degree> s'" by (rule better_sred_Beta)
  thus ?case by (simp only: app_last)
qed

lemma lemma1':
  assumes ts: "ts [\<rightarrow>\<^sub>s] ts'"
  shows "r \<rightarrow>\<^sub>s r' \<Longrightarrow> r \<degree>\<degree> ts \<rightarrow>\<^sub>s r' \<degree>\<degree> ts'" using ts
  by (induct arbitrary: r r') (auto intro: lemma1)

lemma listrelp_betas:
  assumes ts: "listrelp op \<rightarrow>\<^sub>\<beta>\<^sup>* ts ts'"
  shows "\<And>t t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> t \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<degree>\<degree> ts'" using ts
  by induct auto

lemma lemma2:
  assumes t: "t \<rightarrow>\<^sub>s u"
  shows "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" using t
  by induct (auto dest: listrelp_conj2
    intro: listrelp_betas apps_preserves_beta converse_rtranclp_into_rtranclp)

lemma lemma3:
  assumes r: "r \<rightarrow>\<^sub>s r'"
  shows "s \<rightarrow>\<^sub>s s' \<Longrightarrow> r[x::=s] \<rightarrow>\<^sub>s r'[x::=s']" using r
proof (nominal_induct avoiding: x s s' rule: sred.strong_induct)
  case (Var rs rs' y)
  hence "map (\<lambda>t. t[x::=s]) rs [\<rightarrow>\<^sub>s] map (\<lambda>t. t[x::=s']) rs'"
    by induct (auto intro: listrelp.intros Var)
  moreover have "Var y[x::=s] \<rightarrow>\<^sub>s Var y[x::=s']"
    by (cases "y = x") (auto simp add: Var intro: refl_sred)
  ultimately show ?case by simp (rule lemma1')
next
  case (Abs y ss ss' r r')
  then have "r[x::=s] \<rightarrow>\<^sub>s r'[x::=s']" by fast
  moreover from Abs(8) `s \<rightarrow>\<^sub>s s'` have "map (\<lambda>t. t[x::=s]) ss [\<rightarrow>\<^sub>s] map (\<lambda>t. t[x::=s']) ss'"
    by induct (auto intro: listrelp.intros Abs)
  ultimately show ?case using Abs(6) `y \<sharp> x` `y \<sharp> s` `y \<sharp> s'`
    by simp (rule better_sred_Abs)
next
  case (Beta y u ss t r)
  thus ?case by (auto simp add: subst_subst fresh_atm intro: better_sred_Beta)
qed

lemma lemma4_aux:
  assumes rs: "listrelp (\<lambda>t u. t \<rightarrow>\<^sub>s u \<and> (\<forall>r. u \<rightarrow>\<^sub>\<beta> r \<longrightarrow> t \<rightarrow>\<^sub>s r)) rs rs'"
  shows "rs' [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ss \<Longrightarrow> rs [\<rightarrow>\<^sub>s] ss" using rs
proof (induct arbitrary: ss)
  case Nil
  thus ?case by cases (auto intro: listrelp.Nil)
next
  case (Cons x y xs ys)
  note Cons' = Cons
  show ?case
  proof (cases ss)
    case Nil with Cons show ?thesis by simp
  next
    case (Cons y' ys')
    hence ss: "ss = y' # ys'" by simp
    from Cons Cons' have "y \<rightarrow>\<^sub>\<beta> y' \<and> ys' = ys \<or> y' = y \<and> ys [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ys'" by simp
    hence "x # xs [\<rightarrow>\<^sub>s] y' # ys'"
    proof
      assume H: "y \<rightarrow>\<^sub>\<beta> y' \<and> ys' = ys"
      with Cons' have "x \<rightarrow>\<^sub>s y'" by blast
      moreover from Cons' have "xs [\<rightarrow>\<^sub>s] ys" by (iprover dest: listrelp_conj1)
      ultimately have "x # xs [\<rightarrow>\<^sub>s] y' # ys" by (rule listrelp.Cons)
      with H show ?thesis by simp
    next
      assume H: "y' = y \<and> ys [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ys'"
      with Cons' have "x \<rightarrow>\<^sub>s y'" by blast
      moreover from H have "xs [\<rightarrow>\<^sub>s] ys'" by (blast intro: Cons')
      ultimately show ?thesis by (rule listrelp.Cons)
    qed
    with ss show ?thesis by simp
  qed
qed

lemma lemma4:
  assumes r: "r \<rightarrow>\<^sub>s r'"
  shows "r' \<rightarrow>\<^sub>\<beta> r'' \<Longrightarrow> r \<rightarrow>\<^sub>s r''" using r
proof (nominal_induct avoiding: r'' rule: sred.strong_induct)
  case (Var rs rs' x)
  then obtain ss where rs: "rs' [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ss" and r'': "r'' = Var x \<degree>\<degree> ss"
    by (blast dest: head_Var_reduction)
  from Var(1) [simplified] rs have "rs [\<rightarrow>\<^sub>s] ss" by (rule lemma4_aux)
  hence "Var x \<degree>\<degree> rs \<rightarrow>\<^sub>s Var x \<degree>\<degree> ss" by (rule sred.Var)
  with r'' show ?case by simp
next
  case (Abs x ss ss' r r')
  from `(Lam [x].r') \<degree>\<degree> ss' \<rightarrow>\<^sub>\<beta> r''` show ?case
  proof (cases rule: apps_betasE [where x=x])
    case (appL s)
    then obtain r''' where s: "s = (Lam [x].r''')" and r''': "r' \<rightarrow>\<^sub>\<beta> r'''" using `x \<sharp> r''`
      by (cases rule: beta.strong_cases) (auto simp add: abs_fresh lam.inject alpha)
    from r''' have "r \<rightarrow>\<^sub>s r'''" by (blast intro: Abs)
    moreover from Abs have "ss [\<rightarrow>\<^sub>s] ss'" by (iprover dest: listrelp_conj1)
    ultimately have "(Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s (Lam [x].r''') \<degree>\<degree> ss'" by (rule better_sred_Abs)
    with appL s show "(Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s r''" by simp
  next
    case (appR rs')
    from Abs(6) [simplified] `ss' [\<rightarrow>\<^sub>\<beta>]\<^sub>1 rs'`
    have "ss [\<rightarrow>\<^sub>s] rs'" by (rule lemma4_aux)
    with `r \<rightarrow>\<^sub>s r'` have "(Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s (Lam [x].r') \<degree>\<degree> rs'" by (rule better_sred_Abs)
    with appR show "(Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s r''" by simp
  next
    case (beta t u' us')
    then have Lam_eq: "(Lam [x].r') = (Lam [x].t)" and ss': "ss' = u' # us'"
      and r'': "r'' = t[x::=u'] \<degree>\<degree> us'"
      by (simp_all add: abs_fresh)
    from Abs(6) ss' obtain u us where
      ss: "ss = u # us" and u: "u \<rightarrow>\<^sub>s u'" and us: "us [\<rightarrow>\<^sub>s] us'"
      by cases (auto dest!: listrelp_conj1)
    have "r[x::=u] \<rightarrow>\<^sub>s r'[x::=u']" using `r \<rightarrow>\<^sub>s r'` and u by (rule lemma3)
    with us have "r[x::=u] \<degree>\<degree> us \<rightarrow>\<^sub>s r'[x::=u'] \<degree>\<degree> us'" by (rule lemma1')
    hence "(Lam [x].r) \<degree> u \<degree>\<degree> us \<rightarrow>\<^sub>s r'[x::=u'] \<degree>\<degree> us'" by (rule better_sred_Beta)
    with ss r'' Lam_eq show "(Lam [x].r) \<degree>\<degree> ss \<rightarrow>\<^sub>s r''" by (simp add: lam.inject alpha)
  qed
next
  case (Beta x s ss t r)
  show ?case
    by (rule better_sred_Beta) (rule Beta)+
qed

lemma rtrancl_beta_sred:
  assumes r: "r \<rightarrow>\<^sub>\<beta>\<^sup>* r'"
  shows "r \<rightarrow>\<^sub>s r'" using r
  by induct (iprover intro: refl_sred lemma4)+


subsection {* Terms in normal form *}

lemma listsp_eqvt [eqvt]:
  assumes xs: "listsp p (xs::'a::pt_name list)"
  shows "listsp ((pi::name prm) \<bullet> p) (pi \<bullet> xs)" using xs
  apply induct
  apply simp
  apply simp
  apply (rule listsp.intros)
  apply (drule_tac pi=pi in perm_boolI)
  apply perm_simp
  apply assumption
  done

inductive NF :: "lam \<Rightarrow> bool"
where
  App: "listsp NF ts \<Longrightarrow> NF (Var x \<degree>\<degree> ts)"
| Abs: "NF t \<Longrightarrow> NF (Lam [x].t)"

equivariance NF
nominal_inductive NF
  by (simp add: abs_fresh)

lemma Abs_NF:
  assumes NF: "NF ((Lam [x].t) \<degree>\<degree> ts)"
  shows "ts = []" using NF
proof cases
  case (App us i)
  thus ?thesis by (simp add: Var_apps_neq_Abs_apps [THEN not_sym])
next
  case (Abs u)
  thus ?thesis by simp
qed

text {*
@{term NF} characterizes exactly the terms that are in normal form.
*}
  
lemma NF_eq: "NF t = (\<forall>t'. \<not> t \<rightarrow>\<^sub>\<beta> t')"
proof
  assume H: "NF t"
  show "\<forall>t'. \<not> t \<rightarrow>\<^sub>\<beta> t'"
  proof
    fix t'
    from H show "\<not> t \<rightarrow>\<^sub>\<beta> t'"
    proof (nominal_induct avoiding: t' rule: NF.strong_induct)
      case (App ts t)
      show ?case
      proof
        assume "Var t \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> t'"
        then obtain rs where "ts [\<rightarrow>\<^sub>\<beta>]\<^sub>1 rs"
          by (iprover dest: head_Var_reduction)
        with App show False
          by (induct rs arbitrary: ts) (auto del: in_listspD)
      qed
    next
      case (Abs t x)
      show ?case
      proof
        assume "(Lam [x].t) \<rightarrow>\<^sub>\<beta> t'"
        then show False using Abs
          by (cases rule: beta.strong_cases) (auto simp add: abs_fresh lam.inject alpha)
      qed
    qed
  qed
next
  assume H: "\<forall>t'. \<not> t \<rightarrow>\<^sub>\<beta> t'"
  then show "NF t"
  proof (nominal_induct t rule: Apps_lam_induct)
    case (1 n ts)
    then have "\<forall>ts'. \<not> ts [\<rightarrow>\<^sub>\<beta>]\<^sub>1 ts'"
      by (iprover intro: apps_preserves_betas)
    with 1(1) have "listsp NF ts"
      by (induct ts) (auto simp add: in_listsp_conv_set)
    then show ?case by (rule NF.App)
  next
    case (2 x u ts)
    show ?case
    proof (cases ts)
      case Nil thus ?thesis by (metis 2 NF.Abs abs foldl_Nil)
    next
      case (Cons r rs)
      have "(Lam [x].u) \<degree> r \<rightarrow>\<^sub>\<beta> u[x::=r]" ..
      then have "(Lam [x].u) \<degree> r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> u[x::=r] \<degree>\<degree> rs"
        by (rule apps_preserves_beta)
      with Cons have "(Lam [x].u) \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> u[x::=r] \<degree>\<degree> rs"
        by simp
      with 2 show ?thesis by iprover
    qed
  qed
qed


subsection {* Leftmost reduction and weakly normalizing terms *}

inductive
  lred :: "lam \<Rightarrow> lam \<Rightarrow> bool"  (infixl "\<rightarrow>\<^sub>l" 50)
  and lredlist :: "lam list \<Rightarrow> lam list \<Rightarrow> bool"  (infixl "[\<rightarrow>\<^sub>l]" 50)
where
  "s [\<rightarrow>\<^sub>l] t \<equiv> listrelp op \<rightarrow>\<^sub>l s t"
| Var: "rs [\<rightarrow>\<^sub>l] rs' \<Longrightarrow> Var x \<degree>\<degree> rs \<rightarrow>\<^sub>l Var x \<degree>\<degree> rs'"
| Abs: "r \<rightarrow>\<^sub>l r' \<Longrightarrow> (Lam [x].r) \<rightarrow>\<^sub>l (Lam [x].r')"
| Beta: "r[x::=s] \<degree>\<degree> ss \<rightarrow>\<^sub>l t \<Longrightarrow> (Lam [x].r) \<degree> s \<degree>\<degree> ss \<rightarrow>\<^sub>l t"

lemma lred_imp_sred:
  assumes lred: "s \<rightarrow>\<^sub>l t"
  shows "s \<rightarrow>\<^sub>s t" using lred
proof induct
  case (Var rs rs' x)
  then have "rs [\<rightarrow>\<^sub>s] rs'"
    by induct (iprover intro: listrelp.intros)+
  then show ?case by (rule sred.Var)
next
  case (Abs r r' x)
  from `r \<rightarrow>\<^sub>s r'`
  have "(Lam [x].r) \<degree>\<degree> [] \<rightarrow>\<^sub>s (Lam [x].r') \<degree>\<degree> []" using listrelp.Nil
    by (rule better_sred_Abs)
  then show ?case by simp
next
  case (Beta r x s ss t)
  from `r[x::=s] \<degree>\<degree> ss \<rightarrow>\<^sub>s t`
  show ?case by (rule better_sred_Beta)
qed

inductive WN :: "lam \<Rightarrow> bool"
  where
    Var: "listsp WN rs \<Longrightarrow> WN (Var n \<degree>\<degree> rs)"
  | Lambda: "WN r \<Longrightarrow> WN (Lam [x].r)"
  | Beta: "WN ((r[x::=s]) \<degree>\<degree> ss) \<Longrightarrow> WN (((Lam [x].r) \<degree> s) \<degree>\<degree> ss)"

lemma listrelp_imp_listsp1:
  assumes H: "listrelp (\<lambda>x y. P x) xs ys"
  shows "listsp P xs" using H
  by induct auto

lemma listrelp_imp_listsp2:
  assumes H: "listrelp (\<lambda>x y. P y) xs ys"
  shows "listsp P ys" using H
  by induct auto

lemma lemma5:
  assumes lred: "r \<rightarrow>\<^sub>l r'"
  shows "WN r" and "NF r'" using lred
  by induct
    (iprover dest: listrelp_conj1 listrelp_conj2
     listrelp_imp_listsp1 listrelp_imp_listsp2 intro: WN.intros
     NF.intros)+

lemma lemma6:
  assumes wn: "WN r"
  shows "\<exists>r'. r \<rightarrow>\<^sub>l r'" using wn
proof induct
  case (Var rs n)
  then have "\<exists>rs'. rs [\<rightarrow>\<^sub>l] rs'"
    by induct (iprover intro: listrelp.intros)+
  then show ?case by (iprover intro: lred.Var)
qed (iprover intro: lred.intros)+

lemma lemma7:
  assumes r: "r \<rightarrow>\<^sub>s r'"
  shows "NF r' \<Longrightarrow> r \<rightarrow>\<^sub>l r'" using r
proof induct
  case (Var rs rs' x)
  from `NF (Var x \<degree>\<degree> rs')` have "listsp NF rs'"
    by cases simp_all
  with Var(1) have "rs [\<rightarrow>\<^sub>l] rs'"
  proof induct
    case Nil
    show ?case by (rule listrelp.Nil)
  next
    case (Cons x y xs ys) 
    hence "x \<rightarrow>\<^sub>l y" and "xs [\<rightarrow>\<^sub>l] ys" by (auto del: in_listspD)
    thus ?case by (rule listrelp.Cons)
  qed
  thus ?case by (rule lred.Var)
next
  case (Abs x ss ss' r r')
  from `NF ((Lam [x].r') \<degree>\<degree> ss')`
  have ss': "ss' = []" by (rule Abs_NF)
  from Abs(4) have ss: "ss = []" using ss'
    by cases simp_all
  from ss' Abs have "NF (Lam [x].r')" by simp
  hence "NF r'" by (cases rule: NF.strong_cases) (auto simp add: abs_fresh lam.inject alpha)
  with Abs have "r \<rightarrow>\<^sub>l r'" by simp
  hence "(Lam [x].r) \<rightarrow>\<^sub>l (Lam [x].r')" by (rule lred.Abs)
  with ss ss' show ?case by simp
next
  case (Beta x s ss t r)
  hence "r[x::=s] \<degree>\<degree> ss \<rightarrow>\<^sub>l t" by simp
  thus ?case by (rule lred.Beta)
qed

lemma WN_eq: "WN t = (\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t')"
proof
  assume "WN t"
  then have "\<exists>t'. t \<rightarrow>\<^sub>l t'" by (rule lemma6)
  then obtain t' where t': "t \<rightarrow>\<^sub>l t'" ..
  then have NF: "NF t'" by (rule lemma5)
  from t' have "t \<rightarrow>\<^sub>s t'" by (rule lred_imp_sred)
  then have "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by (rule lemma2)
  with NF show "\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'" by iprover
next
  assume "\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'"
  then obtain t' where t': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and NF: "NF t'"
    by iprover
  from t' have "t \<rightarrow>\<^sub>s t'" by (rule rtrancl_beta_sred)
  then have "t \<rightarrow>\<^sub>l t'" using NF by (rule lemma7)
  then show "WN t" by (rule lemma5)
qed

end

