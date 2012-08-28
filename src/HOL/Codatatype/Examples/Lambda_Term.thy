(*  Title:      Codatatype_Examples/Lambda_Term.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Lambda-terms.
*)

header {* Lambda-Terms *}

theory Lambda_Term
imports "../Codatatype"
begin


section {* Datatype definition *}

bnf_data trm: 'trm = "'a + 'trm \<times> 'trm + 'a \<times> 'trm + ('a \<times> 'trm) fset \<times> 'trm"


section {* Customization of terms *}

subsection{* Set and map *}

lemma trmBNF_set2_Lt: "trmBNF_set2 (Inr (Inr (Inr (xts, t)))) = snd ` (fset xts) \<union> {t}"
unfolding trmBNF_set2_def sum_set_defs prod_set_defs collect_def[abs_def]
by auto

lemma trmBNF_set2_Var: "\<And>x. trmBNF_set2 (Inl x) = {}"
and trmBNF_set2_App:
"\<And>t1 t2. trmBNF_set2 (Inr (Inl t1t2)) = {fst t1t2, snd t1t2}"
and trmBNF_set2_Lam:
"\<And>x t. trmBNF_set2 (Inr (Inr (Inl (x, t)))) = {t}"
unfolding trmBNF_set2_def sum_set_defs prod_set_defs collect_def[abs_def]
by auto

lemma trmBNF_map:
"\<And> a1. trmBNF_map f1 f2 (Inl a1) = Inl (f1 a1)"
"\<And> a2 b2. trmBNF_map f1 f2 (Inr (Inl (a2,b2))) = Inr (Inl (f2 a2, f2 b2))"
"\<And> a1 a2. trmBNF_map f1 f2 (Inr (Inr (Inl (a1,a2)))) = Inr (Inr (Inl (f1 a1, f2 a2)))"
"\<And> a1a2s a2.
   trmBNF_map f1 f2 (Inr (Inr (Inr (a1a2s, a2)))) =
   Inr (Inr (Inr (map_fset (\<lambda> (a1', a2'). (f1 a1', f2 a2')) a1a2s, f2 a2)))"
unfolding trmBNF_map_def collect_def[abs_def] map_pair_def by auto


subsection{* Constructors *}

definition "Var x \<equiv> trm_fld (Inl x)"
definition "App t1 t2 \<equiv> trm_fld (Inr (Inl (t1,t2)))"
definition "Lam x t \<equiv> trm_fld (Inr (Inr (Inl (x,t))))"
definition "Lt xts t \<equiv> trm_fld (Inr (Inr (Inr (xts,t))))"

lemmas ctor_defs = Var_def App_def Lam_def Lt_def

theorem trm_simps[simp]:
"\<And>x y. Var x = Var y \<longleftrightarrow> x = y"
"\<And>t1 t2 t1' t2'. App t1 t2 = App t1' t2' \<longleftrightarrow> t1 = t1' \<and> t2 = t2'"
"\<And>x x' t t'. Lam x t = Lam x' t' \<longleftrightarrow> x = x' \<and> t = t'"
"\<And> xts xts' t t'. Lt xts t = Lt xts' t' \<longleftrightarrow> xts = xts' \<and> t = t'"
(*  *)
"\<And> x t1 t2. Var x \<noteq> App t1 t2"  "\<And>x y t. Var x \<noteq> Lam y t"  "\<And> x xts t. Var x \<noteq> Lt xts t"
"\<And> t1 t2 x t. App t1 t2 \<noteq> Lam x t"  "\<And> t1 t2 xts t. App t1 t2 \<noteq> Lt xts t"
"\<And>x t xts t1. Lam x t \<noteq> Lt xts t1"
unfolding ctor_defs trm.fld_inject by auto

theorem trm_cases[elim, case_names Var App Lam Lt]:
assumes Var: "\<And> x. t = Var x \<Longrightarrow> phi"
and App: "\<And> t1 t2. t = App t1 t2 \<Longrightarrow> phi"
and Lam: "\<And> x t1. t = Lam x t1 \<Longrightarrow> phi"
and Lt: "\<And> xts t1. t = Lt xts t1 \<Longrightarrow> phi"
shows phi
proof(cases rule: trm.fld_exhaust[of t])
  fix x assume "t = trm_fld x"
  thus ?thesis
  apply(cases x) using Var unfolding ctor_defs apply blast
  apply(case_tac b) using App unfolding ctor_defs apply(case_tac a, blast)
  apply(case_tac ba) using Lam unfolding ctor_defs apply(case_tac a, blast)
  apply(case_tac bb) using Lt unfolding ctor_defs by blast
qed

lemma trm_induct[case_names Var App Lam Lt, induct type: trm]:
assumes Var: "\<And> (x::'a). phi (Var x)"
and App: "\<And> t1 t2. \<lbrakk>phi t1; phi t2\<rbrakk> \<Longrightarrow> phi (App t1 t2)"
and Lam: "\<And> x t. phi t \<Longrightarrow> phi (Lam x t)"
and Lt: "\<And> xts t. \<lbrakk>\<And> x1 t1. (x1,t1) |\<in>| xts \<Longrightarrow> phi t1; phi t\<rbrakk> \<Longrightarrow> phi (Lt xts t)"
shows "phi t"
proof(induct rule: trm.fld_induct)
  fix u :: "'a + 'a trm \<times> 'a trm + 'a \<times> 'a trm + ('a \<times> 'a trm) fset \<times> 'a trm"
  assume IH: "\<And>t. t \<in> trmBNF_set2 u \<Longrightarrow> phi t"
  show "phi (trm_fld u)"
  proof(cases u)
    case (Inl x)
    show ?thesis using Var unfolding Var_def Inl .
  next
    case (Inr uu) note Inr1 = Inr
    show ?thesis
    proof(cases uu)
      case (Inl t1t2)
      obtain t1 t2 where t1t2: "t1t2 = (t1,t2)" by (cases t1t2, blast)
      show ?thesis unfolding Inr1 Inl t1t2 App_def[symmetric] apply(rule App)
      using IH unfolding Inr1 Inl trmBNF_set2_App t1t2 fst_conv snd_conv by blast+
    next
      case (Inr uuu) note Inr2 = Inr
      show ?thesis
      proof(cases uuu)
        case (Inl xt)
        obtain x t where xt: "xt = (x,t)" by (cases xt, blast)
        show ?thesis unfolding Inr1 Inr2 Inl xt Lam_def[symmetric] apply(rule Lam)
        using IH unfolding Inr1 Inr2 Inl trmBNF_set2_Lam xt by blast
      next
        case (Inr xts_t)
        obtain xts t where xts_t: "xts_t = (xts,t)" by (cases xts_t, blast)
        show ?thesis unfolding Inr1 Inr2 Inr xts_t Lt_def[symmetric] apply(rule Lt) using IH
        unfolding Inr1 Inr2 Inr trmBNF_set2_Lt xts_t fset_fset_member image_def by auto
      qed
    qed
  qed
qed


subsection{* Recursion and iteration *}

definition
"sumJoin4 f1 f2 f3 f4 \<equiv>
\<lambda> k. (case k of
 Inl x1 \<Rightarrow> f1 x1
|Inr k1 \<Rightarrow> (case k1 of
 Inl ((s2,a2),(t2,b2)) \<Rightarrow> f2 s2 a2 t2 b2
|Inr k2 \<Rightarrow> (case k2 of Inl (x3,(t3,b3)) \<Rightarrow> f3 x3 t3 b3
|Inr (xts,(t4,b4)) \<Rightarrow> f4 xts t4 b4)))"

lemma sumJoin4_simps[simp]:
"\<And>x. sumJoin4 var app lam lt (Inl x) = var x"
"\<And> t1 a1 t2 a2. sumJoin4 var app lam lt (Inr (Inl ((t1,a1),(t2,a2)))) = app t1 a1 t2 a2"
"\<And> x t a. sumJoin4 var app lam lt (Inr (Inr (Inl (x,(t,a))))) = lam x t a"
"\<And> xtas t a. sumJoin4 var app lam lt (Inr (Inr (Inr (xtas,(t,a))))) = lt xtas t a"
unfolding sumJoin4_def by auto

definition "trmrec var app lam lt \<equiv> trm_rec (sumJoin4 var app lam lt)"

lemma trmrec_Var[simp]:
"trmrec var app lam lt (Var x) = var x"
unfolding trmrec_def Var_def trm.rec trmBNF_map(1) by simp

lemma trmrec_App[simp]:
"trmrec var app lam lt (App t1 t2) =
 app t1 (trmrec var app lam lt t1) t2 (trmrec var app lam lt t2)"
unfolding trmrec_def App_def trm.rec trmBNF_map(2) convol_def by simp

lemma trmrec_Lam[simp]:
"trmrec var app lam lt (Lam x t) = lam x t (trmrec var app lam lt t)"
unfolding trmrec_def Lam_def trm.rec trmBNF_map(3) convol_def by simp

lemma trmrec_Lt[simp]:
"trmrec var app lam lt (Lt xts t) =
 lt (map_fset (\<lambda> (x,t). (x,t,trmrec var app lam lt t)) xts) t (trmrec var app lam lt t)"
unfolding trmrec_def Lt_def trm.rec trmBNF_map(4) convol_def by simp

definition
"sumJoinI4 f1 f2 f3 f4 \<equiv>
\<lambda> k. (case k of
 Inl x1 \<Rightarrow> f1 x1
|Inr k1 \<Rightarrow> (case k1 of
 Inl (a2,b2) \<Rightarrow> f2 a2 b2
|Inr k2 \<Rightarrow> (case k2 of Inl (x3,b3) \<Rightarrow> f3 x3 b3
|Inr (xts,b4) \<Rightarrow> f4 xts b4)))"

lemma sumJoinI4_simps[simp]:
"\<And>x. sumJoinI4 var app lam lt (Inl x) = var x"
"\<And> a1 a2. sumJoinI4 var app lam lt (Inr (Inl (a1,a2))) = app a1 a2"
"\<And> x a. sumJoinI4 var app lam lt (Inr (Inr (Inl (x,a)))) = lam x a"
"\<And> xtas a. sumJoinI4 var app lam lt (Inr (Inr (Inr (xtas,a)))) = lt xtas a"
unfolding sumJoinI4_def by auto

(* The iterator has a simpler, hence more manageable type. *)
definition "trmiter var app lam lt \<equiv> trm_iter (sumJoinI4 var app lam lt)"

lemma trmiter_Var[simp]:
"trmiter var app lam lt (Var x) = var x"
unfolding trmiter_def Var_def trm.iter trmBNF_map(1) by simp

lemma trmiter_App[simp]:
"trmiter var app lam lt (App t1 t2) =
 app (trmiter var app lam lt t1) (trmiter var app lam lt t2)"
unfolding trmiter_def App_def trm.iter trmBNF_map(2) by simp

lemma trmiter_Lam[simp]:
"trmiter var app lam lt (Lam x t) = lam x (trmiter var app lam lt t)"
unfolding trmiter_def Lam_def trm.iter trmBNF_map(3) by simp

lemma trmiter_Lt[simp]:
"trmiter var app lam lt (Lt xts t) =
 lt (map_fset (\<lambda> (x,t). (x,trmiter var app lam lt t)) xts) (trmiter var app lam lt t)"
unfolding trmiter_def Lt_def trm.iter trmBNF_map(4) by simp


subsection{* Example: The set of all variables varsOf and free variables fvarsOf of a term: *}

definition "varsOf = trmiter
(\<lambda> x. {x})
(\<lambda> X1 X2. X1 \<union> X2)
(\<lambda> x X. X \<union> {x})
(\<lambda> xXs Y. Y \<union> (\<Union> { {x} \<union> X | x X. (x,X) |\<in>| xXs}))"

lemma varsOf_simps[simp]:
"varsOf (Var x) = {x}"
"varsOf (App t1 t2) = varsOf t1 \<union> varsOf t2"
"varsOf (Lam x t) = varsOf t \<union> {x}"
"varsOf (Lt xts t) =
 varsOf t \<union> (\<Union> { {x} \<union> X | x X. (x,X) |\<in>| map_fset (\<lambda> (x,t1). (x,varsOf t1)) xts})"
unfolding varsOf_def by simp_all

definition "fvarsOf = trmiter
(\<lambda> x. {x})
(\<lambda> X1 X2. X1 \<union> X2)
(\<lambda> x X. X - {x})
(\<lambda> xtXs Y. Y - {x | x X. (x,X) |\<in>| xtXs} \<union> (\<Union> {X | x X. (x,X) |\<in>| xtXs}))"

lemma fvarsOf_simps[simp]:
"fvarsOf (Var x) = {x}"
"fvarsOf (App t1 t2) = fvarsOf t1 \<union> fvarsOf t2"
"fvarsOf (Lam x t) = fvarsOf t - {x}"
"fvarsOf (Lt xts t) =
 fvarsOf t
 - {x | x X. (x,X) |\<in>| map_fset (\<lambda> (x,t1). (x,fvarsOf t1)) xts}
 \<union> (\<Union> {X | x X. (x,X) |\<in>| map_fset (\<lambda> (x,t1). (x,fvarsOf t1)) xts})"
unfolding fvarsOf_def by simp_all

lemma diff_Un_incl_triv: "\<lbrakk>A \<subseteq> D; C \<subseteq> E\<rbrakk> \<Longrightarrow> A - B \<union> C \<subseteq> D \<union> E" by blast

lemma in_map_fset_iff:
"(x, X) |\<in>| map_fset (\<lambda>(x, t1). (x, f t1)) xts \<longleftrightarrow>
 (\<exists> t1. (x,t1) |\<in>| xts \<and> X = f t1)"
unfolding map_fset_def2_raw in_fset fset_afset unfolding fset_def2_raw by auto

lemma fvarsOf_varsOf: "fvarsOf t \<subseteq> varsOf t"
proof induct
  case (Lt xts t)
  thus ?case unfolding fvarsOf_simps varsOf_simps
  proof (elim diff_Un_incl_triv)
    show
    "\<Union>{X | x X. (x, X) |\<in>| map_fset (\<lambda>(x, t1). (x, fvarsOf t1)) xts}
     \<subseteq> \<Union>{{x} \<union> X |x X. (x, X) |\<in>| map_fset (\<lambda>(x, t1). (x, varsOf t1)) xts}"
     (is "_ \<subseteq> \<Union> ?L")
    proof(rule Sup_mono, safe)
      fix a x X
      assume "(x, X) |\<in>| map_fset (\<lambda>(x, t1). (x, fvarsOf t1)) xts"
      then obtain t1 where x_t1: "(x,t1) |\<in>| xts" and X: "X = fvarsOf t1"
      unfolding in_map_fset_iff by auto
      let ?Y = "varsOf t1"
      have x_Y: "(x,?Y) |\<in>| map_fset (\<lambda>(x, t1). (x, varsOf t1)) xts"
      using x_t1 unfolding in_map_fset_iff by auto
      show "\<exists> Y \<in> ?L. X \<subseteq> Y" unfolding X using Lt(1) x_Y x_t1 by auto
    qed
  qed
qed auto

end
