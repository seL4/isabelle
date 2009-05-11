(*  Title:      HOLCF/Algebraic.thy
    Author:     Brian Huffman
*)

header {* Algebraic deflations *}

theory Algebraic
imports Completion Fix Eventual
begin

subsection {* Constructing finite deflations by iteration *}

lemma finite_deflation_imp_deflation:
  "finite_deflation d \<Longrightarrow> deflation d"
unfolding finite_deflation_def by simp

lemma le_Suc_induct:
  assumes le: "i \<le> j"
  assumes step: "\<And>i. P i (Suc i)"
  assumes refl: "\<And>i. P i i"
  assumes trans: "\<And>i j k. \<lbrakk>P i j; P j k\<rbrakk> \<Longrightarrow> P i k"
  shows "P i j"
proof (cases "i = j")
  assume "i = j"
  thus "P i j" by (simp add: refl)
next
  assume "i \<noteq> j"
  with le have "i < j" by simp
  thus "P i j" using step trans by (rule less_Suc_induct)
qed

text {* A pre-deflation is like a deflation, but not idempotent. *}

locale pre_deflation =
  fixes f :: "'a \<rightarrow> 'a::cpo"
  assumes below: "\<And>x. f\<cdot>x \<sqsubseteq> x"
  assumes finite_range: "finite (range (\<lambda>x. f\<cdot>x))"
begin

lemma iterate_below: "iterate i\<cdot>f\<cdot>x \<sqsubseteq> x"
by (induct i, simp_all add: below_trans [OF below])

lemma iterate_fixed: "f\<cdot>x = x \<Longrightarrow> iterate i\<cdot>f\<cdot>x = x"
by (induct i, simp_all)

lemma antichain_iterate_app: "i \<le> j \<Longrightarrow> iterate j\<cdot>f\<cdot>x \<sqsubseteq> iterate i\<cdot>f\<cdot>x"
apply (erule le_Suc_induct)
apply (simp add: below)
apply (rule below_refl)
apply (erule (1) below_trans)
done

lemma finite_range_iterate_app: "finite (range (\<lambda>i. iterate i\<cdot>f\<cdot>x))"
proof (rule finite_subset)
  show "range (\<lambda>i. iterate i\<cdot>f\<cdot>x) \<subseteq> insert x (range (\<lambda>x. f\<cdot>x))"
    by (clarify, case_tac i, simp_all)
  show "finite (insert x (range (\<lambda>x. f\<cdot>x)))"
    by (simp add: finite_range)
qed

lemma eventually_constant_iterate_app:
  "eventually_constant (\<lambda>i. iterate i\<cdot>f\<cdot>x)"
unfolding eventually_constant_def MOST_nat_le
proof -
  let ?Y = "\<lambda>i. iterate i\<cdot>f\<cdot>x"
  have "\<exists>j. \<forall>k. ?Y j \<sqsubseteq> ?Y k"
    apply (rule finite_range_has_max)
    apply (erule antichain_iterate_app)
    apply (rule finite_range_iterate_app)
    done
  then obtain j where j: "\<And>k. ?Y j \<sqsubseteq> ?Y k" by fast
  show "\<exists>z m. \<forall>n\<ge>m. ?Y n = z"
  proof (intro exI allI impI)
    fix k
    assume "j \<le> k"
    hence "?Y k \<sqsubseteq> ?Y j" by (rule antichain_iterate_app)
    also have "?Y j \<sqsubseteq> ?Y k" by (rule j)
    finally show "?Y k = ?Y j" .
  qed
qed

lemma eventually_constant_iterate:
  "eventually_constant (\<lambda>n. iterate n\<cdot>f)"
proof -
  have "\<forall>y\<in>range (\<lambda>x. f\<cdot>x). eventually_constant (\<lambda>i. iterate i\<cdot>f\<cdot>y)"
    by (simp add: eventually_constant_iterate_app)
  hence "\<forall>y\<in>range (\<lambda>x. f\<cdot>x). MOST i. MOST j. iterate j\<cdot>f\<cdot>y = iterate i\<cdot>f\<cdot>y"
    unfolding eventually_constant_MOST_MOST .
  hence "MOST i. MOST j. \<forall>y\<in>range (\<lambda>x. f\<cdot>x). iterate j\<cdot>f\<cdot>y = iterate i\<cdot>f\<cdot>y"
    by (simp only: MOST_finite_Ball_distrib [OF finite_range])
  hence "MOST i. MOST j. \<forall>x. iterate j\<cdot>f\<cdot>(f\<cdot>x) = iterate i\<cdot>f\<cdot>(f\<cdot>x)"
    by simp
  hence "MOST i. MOST j. \<forall>x. iterate (Suc j)\<cdot>f\<cdot>x = iterate (Suc i)\<cdot>f\<cdot>x"
    by (simp only: iterate_Suc2)
  hence "MOST i. MOST j. iterate (Suc j)\<cdot>f = iterate (Suc i)\<cdot>f"
    by (simp only: expand_cfun_eq)
  hence "eventually_constant (\<lambda>i. iterate (Suc i)\<cdot>f)"
    unfolding eventually_constant_MOST_MOST .
  thus "eventually_constant (\<lambda>i. iterate i\<cdot>f)"
    by (rule eventually_constant_SucD)
qed

abbreviation
  d :: "'a \<rightarrow> 'a"
where
  "d \<equiv> eventual (\<lambda>n. iterate n\<cdot>f)"

lemma MOST_d: "MOST n. P (iterate n\<cdot>f) \<Longrightarrow> P d"
using eventually_constant_iterate by (rule MOST_eventual)

lemma f_d: "f\<cdot>(d\<cdot>x) = d\<cdot>x"
apply (rule MOST_d)
apply (subst iterate_Suc [symmetric])
apply (rule eventually_constant_MOST_Suc_eq)
apply (rule eventually_constant_iterate_app)
done

lemma d_fixed_iff: "d\<cdot>x = x \<longleftrightarrow> f\<cdot>x = x"
proof
  assume "d\<cdot>x = x"
  with f_d [where x=x]
  show "f\<cdot>x = x" by simp
next
  assume f: "f\<cdot>x = x"
  have "\<forall>n. iterate n\<cdot>f\<cdot>x = x"
    by (rule allI, rule nat.induct, simp, simp add: f)
  hence "MOST n. iterate n\<cdot>f\<cdot>x = x"
    by (rule ALL_MOST)
  thus "d\<cdot>x = x"
    by (rule MOST_d)
qed

lemma finite_deflation_d: "finite_deflation d"
proof
  fix x :: 'a
  have "d \<in> range (\<lambda>n. iterate n\<cdot>f)"
    using eventually_constant_iterate
    by (rule eventual_mem_range)
  then obtain n where n: "d = iterate n\<cdot>f" ..
  have "iterate n\<cdot>f\<cdot>(d\<cdot>x) = d\<cdot>x"
    using f_d by (rule iterate_fixed)
  thus "d\<cdot>(d\<cdot>x) = d\<cdot>x"
    by (simp add: n)
next
  fix x :: 'a
  show "d\<cdot>x \<sqsubseteq> x"
    by (rule MOST_d, simp add: iterate_below)
next
  from finite_range
  have "finite {x. f\<cdot>x = x}"
    by (rule finite_range_imp_finite_fixes)
  thus "finite {x. d\<cdot>x = x}"
    by (simp add: d_fixed_iff)
qed

end

lemma pre_deflation_d_f:
  assumes "finite_deflation d"
  assumes f: "\<And>x. f\<cdot>x \<sqsubseteq> x"
  shows "pre_deflation (d oo f)"
proof
  interpret d: finite_deflation d by fact
  fix x
  show "\<And>x. (d oo f)\<cdot>x \<sqsubseteq> x"
    by (simp, rule below_trans [OF d.below f])
  show "finite (range (\<lambda>x. (d oo f)\<cdot>x))"
    by (rule finite_subset [OF _ d.finite_range], auto)
qed

lemma eventual_iterate_oo_fixed_iff:
  assumes "finite_deflation d"
  assumes f: "\<And>x. f\<cdot>x \<sqsubseteq> x"
  shows "eventual (\<lambda>n. iterate n\<cdot>(d oo f))\<cdot>x = x \<longleftrightarrow> d\<cdot>x = x \<and> f\<cdot>x = x"
proof -
  interpret d: finite_deflation d by fact
  let ?e = "d oo f"
  interpret e: pre_deflation "d oo f"
    using `finite_deflation d` f
    by (rule pre_deflation_d_f)
  let ?g = "eventual (\<lambda>n. iterate n\<cdot>?e)"
  show ?thesis
    apply (subst e.d_fixed_iff)
    apply simp
    apply safe
    apply (erule subst)
    apply (rule d.idem)
    apply (rule below_antisym)
    apply (rule f)
    apply (erule subst, rule d.below)
    apply simp
    done
qed

subsection {* Type constructor for finite deflations *}

defaultsort profinite

typedef (open) 'a fin_defl = "{d::'a \<rightarrow> 'a. finite_deflation d}"
by (fast intro: finite_deflation_approx)

instantiation fin_defl :: (profinite) below
begin

definition below_fin_defl_def:
    "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep_fin_defl x \<sqsubseteq> Rep_fin_defl y"

instance ..
end

instance fin_defl :: (profinite) po
by (rule typedef_po [OF type_definition_fin_defl below_fin_defl_def])

lemma finite_deflation_Rep_fin_defl: "finite_deflation (Rep_fin_defl d)"
using Rep_fin_defl by simp

interpretation Rep_fin_defl: finite_deflation "Rep_fin_defl d"
by (rule finite_deflation_Rep_fin_defl)

lemma fin_defl_belowI:
  "(\<And>x. Rep_fin_defl a\<cdot>x = x \<Longrightarrow> Rep_fin_defl b\<cdot>x = x) \<Longrightarrow> a \<sqsubseteq> b"
unfolding below_fin_defl_def
by (rule Rep_fin_defl.belowI)

lemma fin_defl_belowD:
  "\<lbrakk>a \<sqsubseteq> b; Rep_fin_defl a\<cdot>x = x\<rbrakk> \<Longrightarrow> Rep_fin_defl b\<cdot>x = x"
unfolding below_fin_defl_def
by (rule Rep_fin_defl.belowD)

lemma fin_defl_eqI:
  "(\<And>x. Rep_fin_defl a\<cdot>x = x \<longleftrightarrow> Rep_fin_defl b\<cdot>x = x) \<Longrightarrow> a = b"
apply (rule below_antisym)
apply (rule fin_defl_belowI, simp)
apply (rule fin_defl_belowI, simp)
done

lemma Abs_fin_defl_mono:
  "\<lbrakk>finite_deflation a; finite_deflation b; a \<sqsubseteq> b\<rbrakk>
    \<Longrightarrow> Abs_fin_defl a \<sqsubseteq> Abs_fin_defl b"
unfolding below_fin_defl_def
by (simp add: Abs_fin_defl_inverse)


subsection {* Take function for finite deflations *}

definition
  fd_take :: "nat \<Rightarrow> 'a fin_defl \<Rightarrow> 'a fin_defl"
where
  "fd_take i d = Abs_fin_defl (eventual (\<lambda>n. iterate n\<cdot>(approx i oo Rep_fin_defl d)))"

lemma Rep_fin_defl_fd_take:
  "Rep_fin_defl (fd_take i d) =
    eventual (\<lambda>n. iterate n\<cdot>(approx i oo Rep_fin_defl d))"
unfolding fd_take_def
apply (rule Abs_fin_defl_inverse [unfolded mem_Collect_eq])
apply (rule pre_deflation.finite_deflation_d)
apply (rule pre_deflation_d_f)
apply (rule finite_deflation_approx)
apply (rule Rep_fin_defl.below)
done

lemma fd_take_fixed_iff:
  "Rep_fin_defl (fd_take i d)\<cdot>x = x \<longleftrightarrow>
    approx i\<cdot>x = x \<and> Rep_fin_defl d\<cdot>x = x"
unfolding Rep_fin_defl_fd_take
by (rule eventual_iterate_oo_fixed_iff
    [OF finite_deflation_approx Rep_fin_defl.below])

lemma fd_take_below: "fd_take n d \<sqsubseteq> d"
apply (rule fin_defl_belowI)
apply (simp add: fd_take_fixed_iff)
done

lemma fd_take_idem: "fd_take n (fd_take n d) = fd_take n d"
apply (rule fin_defl_eqI)
apply (simp add: fd_take_fixed_iff)
done

lemma fd_take_mono: "a \<sqsubseteq> b \<Longrightarrow> fd_take n a \<sqsubseteq> fd_take n b"
apply (rule fin_defl_belowI)
apply (simp add: fd_take_fixed_iff)
apply (simp add: fin_defl_belowD)
done

lemma approx_fixed_le_lemma: "\<lbrakk>i \<le> j; approx i\<cdot>x = x\<rbrakk> \<Longrightarrow> approx j\<cdot>x = x"
by (erule subst, simp add: min_def)

lemma fd_take_chain: "m \<le> n \<Longrightarrow> fd_take m a \<sqsubseteq> fd_take n a"
apply (rule fin_defl_belowI)
apply (simp add: fd_take_fixed_iff)
apply (simp add: approx_fixed_le_lemma)
done

lemma finite_range_fd_take: "finite (range (fd_take n))"
apply (rule finite_imageD [where f="\<lambda>a. {x. Rep_fin_defl a\<cdot>x = x}"])
apply (rule finite_subset [where B="Pow {x. approx n\<cdot>x = x}"])
apply (clarify, simp add: fd_take_fixed_iff)
apply (simp add: finite_fixes_approx)
apply (rule inj_onI, clarify)
apply (simp add: expand_set_eq fin_defl_eqI)
done

lemma fd_take_covers: "\<exists>n. fd_take n a = a"
apply (rule_tac x=
  "Max ((\<lambda>x. LEAST n. approx n\<cdot>x = x) ` {x. Rep_fin_defl a\<cdot>x = x})" in exI)
apply (rule below_antisym)
apply (rule fd_take_below)
apply (rule fin_defl_belowI)
apply (simp add: fd_take_fixed_iff)
apply (rule approx_fixed_le_lemma)
apply (rule Max_ge)
apply (rule finite_imageI)
apply (rule Rep_fin_defl.finite_fixes)
apply (rule imageI)
apply (erule CollectI)
apply (rule LeastI_ex)
apply (rule profinite_compact_eq_approx)
apply (erule subst)
apply (rule Rep_fin_defl.compact)
done

interpretation fin_defl: basis_take below fd_take
apply default
apply (rule fd_take_below)
apply (rule fd_take_idem)
apply (erule fd_take_mono)
apply (rule fd_take_chain, simp)
apply (rule finite_range_fd_take)
apply (rule fd_take_covers)
done

subsection {* Defining algebraic deflations by ideal completion *}

typedef (open) 'a alg_defl =
  "{S::'a fin_defl set. below.ideal S}"
by (fast intro: below.ideal_principal)

instantiation alg_defl :: (profinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_alg_defl x \<subseteq> Rep_alg_defl y"

instance ..
end

instance alg_defl :: (profinite) po
by (rule below.typedef_ideal_po
    [OF type_definition_alg_defl below_alg_defl_def])

instance alg_defl :: (profinite) cpo
by (rule below.typedef_ideal_cpo
    [OF type_definition_alg_defl below_alg_defl_def])

lemma Rep_alg_defl_lub:
  "chain Y \<Longrightarrow> Rep_alg_defl (\<Squnion>i. Y i) = (\<Union>i. Rep_alg_defl (Y i))"
by (rule below.typedef_ideal_rep_contlub
    [OF type_definition_alg_defl below_alg_defl_def])

lemma ideal_Rep_alg_defl: "below.ideal (Rep_alg_defl xs)"
by (rule Rep_alg_defl [unfolded mem_Collect_eq])

definition
  alg_defl_principal :: "'a fin_defl \<Rightarrow> 'a alg_defl" where
  "alg_defl_principal t = Abs_alg_defl {u. u \<sqsubseteq> t}"

lemma Rep_alg_defl_principal:
  "Rep_alg_defl (alg_defl_principal t) = {u. u \<sqsubseteq> t}"
unfolding alg_defl_principal_def
by (simp add: Abs_alg_defl_inverse below.ideal_principal)

interpretation alg_defl:
  ideal_completion below fd_take alg_defl_principal Rep_alg_defl
apply default
apply (rule ideal_Rep_alg_defl)
apply (erule Rep_alg_defl_lub)
apply (rule Rep_alg_defl_principal)
apply (simp only: below_alg_defl_def)
done

text {* Algebraic deflations are pointed *}

lemma finite_deflation_UU: "finite_deflation \<bottom>"
by default simp_all

lemma alg_defl_minimal:
  "alg_defl_principal (Abs_fin_defl \<bottom>) \<sqsubseteq> x"
apply (induct x rule: alg_defl.principal_induct, simp)
apply (rule alg_defl.principal_mono)
apply (induct_tac a)
apply (rule Abs_fin_defl_mono)
apply (rule finite_deflation_UU)
apply simp
apply (rule minimal)
done

instance alg_defl :: (bifinite) pcpo
by intro_classes (fast intro: alg_defl_minimal)

lemma inst_alg_defl_pcpo: "\<bottom> = alg_defl_principal (Abs_fin_defl \<bottom>)"
by (rule alg_defl_minimal [THEN UU_I, symmetric])

text {* Algebraic deflations are profinite *}

instantiation alg_defl :: (profinite) profinite
begin

definition
  approx_alg_defl_def: "approx = alg_defl.completion_approx"

instance
apply (intro_classes, unfold approx_alg_defl_def)
apply (rule alg_defl.chain_completion_approx)
apply (rule alg_defl.lub_completion_approx)
apply (rule alg_defl.completion_approx_idem)
apply (rule alg_defl.finite_fixes_completion_approx)
done

end

instance alg_defl :: (bifinite) bifinite ..

lemma approx_alg_defl_principal [simp]:
  "approx n\<cdot>(alg_defl_principal t) = alg_defl_principal (fd_take n t)"
unfolding approx_alg_defl_def
by (rule alg_defl.completion_approx_principal)

lemma approx_eq_alg_defl_principal:
  "\<exists>t\<in>Rep_alg_defl xs. approx n\<cdot>xs = alg_defl_principal (fd_take n t)"
unfolding approx_alg_defl_def
by (rule alg_defl.completion_approx_eq_principal)


subsection {* Applying algebraic deflations *}

definition
  cast :: "'a alg_defl \<rightarrow> 'a \<rightarrow> 'a"
where
  "cast = alg_defl.basis_fun Rep_fin_defl"

lemma cast_alg_defl_principal:
  "cast\<cdot>(alg_defl_principal a) = Rep_fin_defl a"
unfolding cast_def
apply (rule alg_defl.basis_fun_principal)
apply (simp only: below_fin_defl_def)
done

lemma deflation_cast: "deflation (cast\<cdot>d)"
apply (induct d rule: alg_defl.principal_induct)
apply (rule adm_subst [OF _ adm_deflation], simp)
apply (simp add: cast_alg_defl_principal)
apply (rule finite_deflation_imp_deflation)
apply (rule finite_deflation_Rep_fin_defl)
done

lemma finite_deflation_cast:
  "compact d \<Longrightarrow> finite_deflation (cast\<cdot>d)"
apply (drule alg_defl.compact_imp_principal, clarify)
apply (simp add: cast_alg_defl_principal)
apply (rule finite_deflation_Rep_fin_defl)
done

interpretation cast: deflation "cast\<cdot>d"
by (rule deflation_cast)

lemma "cast\<cdot>(\<Squnion>i. alg_defl_principal (Abs_fin_defl (approx i)))\<cdot>x = x"
apply (subst contlub_cfun_arg)
apply (rule chainI)
apply (rule alg_defl.principal_mono)
apply (rule Abs_fin_defl_mono)
apply (rule finite_deflation_approx)
apply (rule finite_deflation_approx)
apply (rule chainE)
apply (rule chain_approx)
apply (simp add: cast_alg_defl_principal Abs_fin_defl_inverse finite_deflation_approx)
done

text {* This lemma says that if we have an ep-pair from
a bifinite domain into a universal domain, then e oo p
is an algebraic deflation. *}

lemma
  assumes "ep_pair e p"
  constrains e :: "'a::profinite \<rightarrow> 'b::profinite"
  shows "\<exists>d. cast\<cdot>d = e oo p"
proof
  interpret ep_pair e p by fact
  let ?a = "\<lambda>i. e oo approx i oo p"
  have a: "\<And>i. finite_deflation (?a i)"
    apply (rule finite_deflation_e_d_p)
    apply (rule finite_deflation_approx)
    done
  let ?d = "\<Squnion>i. alg_defl_principal (Abs_fin_defl (?a i))"
  show "cast\<cdot>?d = e oo p"
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule alg_defl.principal_mono)
    apply (rule Abs_fin_defl_mono [OF a a])
    apply (rule chainE, simp)
    apply (subst cast_alg_defl_principal)
    apply (simp add: Abs_fin_defl_inverse a)
    apply (simp add: expand_cfun_eq lub_distribs)
    done
qed

text {* This lemma says that if we have an ep-pair
from a cpo into a bifinite domain, and e oo p is
an algebraic deflation, then the cpo is bifinite. *}

lemma
  assumes "ep_pair e p"
  constrains e :: "'a::cpo \<rightarrow> 'b::profinite"
  assumes d: "\<And>x. cast\<cdot>d\<cdot>x = e\<cdot>(p\<cdot>x)"
  obtains a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where
    "\<And>i. finite_deflation (a i)"
    "(\<Squnion>i. a i) = ID"
proof
  interpret ep_pair e p by fact
  let ?a = "\<lambda>i. p oo cast\<cdot>(approx i\<cdot>d) oo e"
  show "\<And>i. finite_deflation (?a i)"
    apply (rule finite_deflation_p_d_e)
    apply (rule finite_deflation_cast)
    apply (rule compact_approx)
    apply (rule below_eq_trans [OF _ d])
    apply (rule monofun_cfun_fun)
    apply (rule monofun_cfun_arg)
    apply (rule approx_below)
    done
  show "(\<Squnion>i. ?a i) = ID"
    apply (rule ext_cfun, simp)
    apply (simp add: lub_distribs)
    apply (simp add: d)
    done
qed

end
