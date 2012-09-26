(*  Title:      HOL/BNF/Examples/Lambda_Term.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Lambda-terms.
*)

header {* Lambda-Terms *}

theory Lambda_Term
imports "../BNF"
begin


section {* Datatype definition *}

data 'a trm =
  Var 'a |
  App "'a trm" "'a trm" |
  Lam 'a "'a trm" |
  Lt "('a \<times> 'a trm) fset" "'a trm"


section {* Customi induction rule *}

lemma trm_induct[case_names Var App Lam Lt, induct type: trm]:
assumes Var: "\<And> x. phi (Var x)"
and App: "\<And> t1 t2. \<lbrakk>phi t1; phi t2\<rbrakk> \<Longrightarrow> phi (App t1 t2)"
and Lam: "\<And> x t. phi t \<Longrightarrow> phi (Lam x t)"
and Lt: "\<And> xts t. \<lbrakk>\<And> x1 t1. (x1,t1) |\<in>| xts \<Longrightarrow> phi t1; phi t\<rbrakk> \<Longrightarrow> phi (Lt xts t)"
shows "phi t"
apply induct
apply (rule Var)
apply (erule App, assumption)
apply (erule Lam)
using Lt unfolding fset_fset_member mem_Collect_eq
apply (rule meta_mp)
defer
apply assumption
apply (erule thin_rl)
apply assumption
apply (drule meta_spec)
apply (drule meta_spec)
apply (drule meta_mp)
apply assumption
apply (auto simp: snds_def)
done


subsection{* Example: The set of all variables varsOf and free variables fvarsOf of a term: *}

definition "varsOf = trm_fold
(\<lambda> x. {x})
(\<lambda> X1 X2. X1 \<union> X2)
(\<lambda> x X. X \<union> {x})
(\<lambda> xXs Y. Y \<union> (\<Union> { {x} \<union> X | x X. (x,X) |\<in>| xXs}))"

thm trm.fold
lemma varsOf_simps[simp]:
"varsOf (Var x) = {x}"
"varsOf (App t1 t2) = varsOf t1 \<union> varsOf t2"
"varsOf (Lam x t) = varsOf t \<union> {x}"
"varsOf (Lt xts t) =
 varsOf t \<union> (\<Union> { {x} \<union> X | x X. (x,X) |\<in>| map_fset (\<lambda> (x,t1). (x,varsOf t1)) xts})"
unfolding varsOf_def by (simp add: map_pair_def)+

definition "fvarsOf = trm_fold
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
unfolding fvarsOf_def by (simp add: map_pair_def)+

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
