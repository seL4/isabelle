(*  Title:      HOL/HOLCF/Library/Defl_Bifinite.thy
    Author:     Brian Huffman
*)

section {* Algebraic deflations are a bifinite domain *}

theory Defl_Bifinite
imports HOLCF "~~/src/HOL/Library/Infinite_Set"
begin

subsection {* Lemmas about MOST *}

default_sort type

lemma MOST_INFM:
  assumes inf: "infinite (UNIV::'a set)"
  shows "MOST x::'a. P x \<Longrightarrow> INFM x::'a. P x"
  unfolding Alm_all_def Inf_many_def
  apply (auto simp add: Collect_neg_eq)
  apply (drule (1) finite_UnI)
  apply (simp add: Compl_partition2 inf)
  done

lemma MOST_SucI: "MOST n. P n \<Longrightarrow> MOST n. P (Suc n)"
by (rule MOST_inj [OF _ inj_Suc])

lemma MOST_SucD: "MOST n. P (Suc n) \<Longrightarrow> MOST n. P n"
unfolding MOST_nat
apply (clarify, rule_tac x="Suc m" in exI, clarify)
apply (erule Suc_lessE, simp)
done

lemma MOST_Suc_iff: "(MOST n. P (Suc n)) \<longleftrightarrow> (MOST n. P n)"
by (rule iffI [OF MOST_SucD MOST_SucI])

lemma INFM_finite_Bex_distrib:
  "finite A \<Longrightarrow> (INFM y. \<exists>x\<in>A. P x y) \<longleftrightarrow> (\<exists>x\<in>A. INFM y. P x y)"
by (induct set: finite, simp, simp add: INFM_disj_distrib)

lemma MOST_finite_Ball_distrib:
  "finite A \<Longrightarrow> (MOST y. \<forall>x\<in>A. P x y) \<longleftrightarrow> (\<forall>x\<in>A. MOST y. P x y)"
by (induct set: finite, simp, simp add: MOST_conj_distrib)

lemma MOST_ge_nat: "MOST n::nat. m \<le> n"
unfolding MOST_nat_le by fast

subsection {* Eventually constant sequences *}

definition
  eventually_constant :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "eventually_constant S = (\<exists>x. MOST i. S i = x)"

lemma eventually_constant_MOST_MOST:
  "eventually_constant S \<longleftrightarrow> (MOST m. MOST n. S n = S m)"
unfolding eventually_constant_def MOST_nat
apply safe
apply (rule_tac x=m in exI, clarify)
apply (rule_tac x=m in exI, clarify)
apply simp
apply fast
done

lemma eventually_constantI: "MOST i. S i = x \<Longrightarrow> eventually_constant S"
unfolding eventually_constant_def by fast

lemma eventually_constant_comp:
  "eventually_constant (\<lambda>i. S i) \<Longrightarrow> eventually_constant (\<lambda>i. f (S i))"
unfolding eventually_constant_def
apply (erule exE, rule_tac x="f x" in exI)
apply (erule MOST_mono, simp)
done

lemma eventually_constant_Suc_iff:
  "eventually_constant (\<lambda>i. S (Suc i)) \<longleftrightarrow> eventually_constant (\<lambda>i. S i)"
unfolding eventually_constant_def
by (subst MOST_Suc_iff, rule refl)

lemma eventually_constant_SucD:
  "eventually_constant (\<lambda>i. S (Suc i)) \<Longrightarrow> eventually_constant (\<lambda>i. S i)"
by (rule eventually_constant_Suc_iff [THEN iffD1])

subsection {* Limits of eventually constant sequences *}

definition
  eventual :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "eventual S = (THE x. MOST i. S i = x)"

lemma eventual_eqI: "MOST i. S i = x \<Longrightarrow> eventual S = x"
unfolding eventual_def
apply (rule the_equality, assumption)
apply (rename_tac y)
apply (subgoal_tac "MOST i::nat. y = x", simp)
apply (erule MOST_rev_mp)
apply (erule MOST_rev_mp)
apply simp
done

lemma MOST_eq_eventual:
  "eventually_constant S \<Longrightarrow> MOST i. S i = eventual S"
unfolding eventually_constant_def
by (erule exE, simp add: eventual_eqI)

lemma eventual_mem_range:
  "eventually_constant S \<Longrightarrow> eventual S \<in> range S"
apply (drule MOST_eq_eventual)
apply (simp only: MOST_nat_le, clarify)
apply (drule spec, drule mp, rule order_refl)
apply (erule range_eqI [OF sym])
done

lemma eventually_constant_MOST_iff:
  assumes S: "eventually_constant S"
  shows "(MOST n. P (S n)) \<longleftrightarrow> P (eventual S)"
apply (subgoal_tac "(MOST n. P (S n)) \<longleftrightarrow> (MOST n::nat. P (eventual S))")
apply simp
apply (rule iffI)
apply (rule MOST_rev_mp [OF MOST_eq_eventual [OF S]])
apply (erule MOST_mono, force)
apply (rule MOST_rev_mp [OF MOST_eq_eventual [OF S]])
apply (erule MOST_mono, simp)
done

lemma MOST_eventual:
  "\<lbrakk>eventually_constant S; MOST n. P (S n)\<rbrakk> \<Longrightarrow> P (eventual S)"
proof -
  assume "eventually_constant S"
  hence "MOST n. S n = eventual S"
    by (rule MOST_eq_eventual)
  moreover assume "MOST n. P (S n)"
  ultimately have "MOST n. S n = eventual S \<and> P (S n)"
    by (rule MOST_conj_distrib [THEN iffD2, OF conjI])
  hence "MOST n::nat. P (eventual S)"
    by (rule MOST_mono) auto
  thus ?thesis by simp
qed

lemma eventually_constant_MOST_Suc_eq:
  "eventually_constant S \<Longrightarrow> MOST n. S (Suc n) = S n"
apply (drule MOST_eq_eventual)
apply (frule MOST_Suc_iff [THEN iffD2])
apply (erule MOST_rev_mp)
apply (erule MOST_rev_mp)
apply simp
done

lemma eventual_comp:
  "eventually_constant S \<Longrightarrow> eventual (\<lambda>i. f (S i)) = f (eventual (\<lambda>i. S i))"
apply (rule eventual_eqI)
apply (rule MOST_mono)
apply (erule MOST_eq_eventual)
apply simp
done

subsection {* Constructing finite deflations by iteration *}

default_sort cpo

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

definition
  eventual_iterate :: "('a \<rightarrow> 'a::cpo) \<Rightarrow> ('a \<rightarrow> 'a)"
where
  "eventual_iterate f = eventual (\<lambda>n. iterate n\<cdot>f)"

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
    by (simp only: cfun_eq_iff)
  hence "eventually_constant (\<lambda>i. iterate (Suc i)\<cdot>f)"
    unfolding eventually_constant_MOST_MOST .
  thus "eventually_constant (\<lambda>i. iterate i\<cdot>f)"
    by (rule eventually_constant_SucD)
qed

abbreviation
  d :: "'a \<rightarrow> 'a"
where
  "d \<equiv> eventual_iterate f"

lemma MOST_d: "MOST n. P (iterate n\<cdot>f) \<Longrightarrow> P d"
unfolding eventual_iterate_def
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
    unfolding eventual_iterate_def
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

lemma deflation_d: "deflation d"
using finite_deflation_d
by (rule finite_deflation_imp_deflation)

end

lemma finite_deflation_eventual_iterate:
  "pre_deflation d \<Longrightarrow> finite_deflation (eventual_iterate d)"
by (rule pre_deflation.finite_deflation_d)

lemma pre_deflation_oo:
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
  shows "eventual_iterate (d oo f)\<cdot>x = x \<longleftrightarrow> d\<cdot>x = x \<and> f\<cdot>x = x"
proof -
  interpret d: finite_deflation d by fact
  let ?e = "d oo f"
  interpret e: pre_deflation "d oo f"
    using `finite_deflation d` f
    by (rule pre_deflation_oo)
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

lemma eventual_mono:
  assumes A: "eventually_constant A"
  assumes B: "eventually_constant B"
  assumes below: "\<And>n. A n \<sqsubseteq> B n"
  shows "eventual A \<sqsubseteq> eventual B"
proof -
  from A have "MOST n. A n = eventual A"
    by (rule MOST_eq_eventual)
  then have "MOST n. eventual A \<sqsubseteq> B n"
    by (rule MOST_mono) (erule subst, rule below)
  with B show "eventual A \<sqsubseteq> eventual B"
    by (rule MOST_eventual)
qed

lemma eventual_iterate_mono:
  assumes f: "pre_deflation f" and g: "pre_deflation g" and "f \<sqsubseteq> g"
  shows "eventual_iterate f \<sqsubseteq> eventual_iterate g"
unfolding eventual_iterate_def
apply (rule eventual_mono)
apply (rule pre_deflation.eventually_constant_iterate [OF f])
apply (rule pre_deflation.eventually_constant_iterate [OF g])
apply (rule monofun_cfun_arg [OF `f \<sqsubseteq> g`])
done

lemma cont2cont_eventual_iterate_oo:
  assumes d: "finite_deflation d"
  assumes cont: "cont f" and below: "\<And>x y. f x\<cdot>y \<sqsubseteq> y"
  shows "cont (\<lambda>x. eventual_iterate (d oo f x))"
    (is "cont ?e")
proof (rule contI2)
  show "monofun ?e"
    apply (rule monofunI)
    apply (rule eventual_iterate_mono)
    apply (rule pre_deflation_oo [OF d below])
    apply (rule pre_deflation_oo [OF d below])
    apply (rule monofun_cfun_arg)
    apply (erule cont2monofunE [OF cont])
    done
next
  fix Y :: "nat \<Rightarrow> 'b"
  assume Y: "chain Y"
  with cont have fY: "chain (\<lambda>i. f (Y i))"
    by (rule ch2ch_cont)
  assume eY: "chain (\<lambda>i. ?e (Y i))"
  have lub_below: "\<And>x. f (\<Squnion>i. Y i)\<cdot>x \<sqsubseteq> x"
    by (rule admD [OF _ Y], simp add: cont, rule below)
  have "deflation (?e (\<Squnion>i. Y i))"
    apply (rule pre_deflation.deflation_d)
    apply (rule pre_deflation_oo [OF d lub_below])
    done
  then show "?e (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ?e (Y i))"
  proof (rule deflation.belowI)
    fix x :: 'a
    assume "?e (\<Squnion>i. Y i)\<cdot>x = x"
    hence "d\<cdot>x = x" and "f (\<Squnion>i. Y i)\<cdot>x = x"
      by (simp_all add: eventual_iterate_oo_fixed_iff [OF d lub_below])
    hence "(\<Squnion>i. f (Y i)\<cdot>x) = x"
      apply (simp only: cont2contlubE [OF cont Y])
      apply (simp only: contlub_cfun_fun [OF fY])
      done
    have "compact (d\<cdot>x)"
      using d by (rule finite_deflation.compact)
    then have "compact x"
      using `d\<cdot>x = x` by simp
    then have "compact (\<Squnion>i. f (Y i)\<cdot>x)"
      using `(\<Squnion>i. f (Y i)\<cdot>x) = x` by simp
    then have "\<exists>n. max_in_chain n (\<lambda>i. f (Y i)\<cdot>x)"
      by - (rule compact_imp_max_in_chain, simp add: fY, assumption)
    then obtain n where n: "max_in_chain n (\<lambda>i. f (Y i)\<cdot>x)" ..
    then have "f (Y n)\<cdot>x = x"
      using `(\<Squnion>i. f (Y i)\<cdot>x) = x` fY by (simp add: maxinch_is_thelub)
    with `d\<cdot>x = x` have "?e (Y n)\<cdot>x = x"
      by (simp add: eventual_iterate_oo_fixed_iff [OF d below])
    moreover have "?e (Y n)\<cdot>x \<sqsubseteq> (\<Squnion>i. ?e (Y i)\<cdot>x)"
      by (rule is_ub_thelub, simp add: eY)
    ultimately have "x \<sqsubseteq> (\<Squnion>i. ?e (Y i))\<cdot>x"
      by (simp add: contlub_cfun_fun eY)
    also have "(\<Squnion>i. ?e (Y i))\<cdot>x \<sqsubseteq> x"
      apply (rule deflation.below)
      apply (rule admD [OF adm_deflation eY])
      apply (rule pre_deflation.deflation_d)
      apply (rule pre_deflation_oo [OF d below])
      done
    finally show "(\<Squnion>i. ?e (Y i))\<cdot>x = x" ..
  qed
qed

subsection {* Intersection of algebraic deflations *}

default_sort bifinite

definition meet_fin_defl :: "'a fin_defl \<Rightarrow> 'a fin_defl \<Rightarrow> 'a fin_defl"
  where "meet_fin_defl a b =
    Abs_fin_defl (eventual_iterate (Rep_fin_defl a oo Rep_fin_defl b))"

lemma Rep_meet_fin_defl:
  "Rep_fin_defl (meet_fin_defl a b) =
    eventual_iterate (Rep_fin_defl a oo Rep_fin_defl b)"
unfolding meet_fin_defl_def
apply (rule Abs_fin_defl_inverse [simplified])
apply (rule finite_deflation_eventual_iterate)
apply (rule pre_deflation_oo)
apply (rule finite_deflation_Rep_fin_defl)
apply (rule Rep_fin_defl.below)
done

lemma Rep_meet_fin_defl_fixed_iff:
  "Rep_fin_defl (meet_fin_defl a b)\<cdot>x = x \<longleftrightarrow>
    Rep_fin_defl a\<cdot>x = x \<and> Rep_fin_defl b\<cdot>x = x"
unfolding Rep_meet_fin_defl
apply (rule eventual_iterate_oo_fixed_iff)
apply (rule finite_deflation_Rep_fin_defl)
apply (rule Rep_fin_defl.below)
done

lemma meet_fin_defl_mono:
  "\<lbrakk>a \<sqsubseteq> b; c \<sqsubseteq> d\<rbrakk> \<Longrightarrow> meet_fin_defl a c \<sqsubseteq> meet_fin_defl b d"
unfolding below_fin_defl_def
apply (rule Rep_fin_defl.belowI)
apply (simp add: Rep_meet_fin_defl_fixed_iff Rep_fin_defl.belowD)
done

lemma meet_fin_defl_below1: "meet_fin_defl a b \<sqsubseteq> a"
unfolding below_fin_defl_def
apply (rule Rep_fin_defl.belowI)
apply (simp add: Rep_meet_fin_defl_fixed_iff Rep_fin_defl.belowD)
done

lemma meet_fin_defl_below2: "meet_fin_defl a b \<sqsubseteq> b"
unfolding below_fin_defl_def
apply (rule Rep_fin_defl.belowI)
apply (simp add: Rep_meet_fin_defl_fixed_iff Rep_fin_defl.belowD)
done

lemma meet_fin_defl_greatest: "\<lbrakk>a \<sqsubseteq> b; a \<sqsubseteq> c\<rbrakk> \<Longrightarrow> a \<sqsubseteq> meet_fin_defl b c"
unfolding below_fin_defl_def
apply (rule Rep_fin_defl.belowI)
apply (simp add: Rep_meet_fin_defl_fixed_iff Rep_fin_defl.belowD)
done

definition meet_defl :: "'a defl \<rightarrow> 'a defl \<rightarrow> 'a defl"
  where "meet_defl = defl.extension (\<lambda>a. defl.extension (\<lambda>b.
    defl_principal (meet_fin_defl a b)))"

lemma meet_defl_principal:
  "meet_defl\<cdot>(defl_principal a)\<cdot>(defl_principal b) =
    defl_principal (meet_fin_defl a b)"
unfolding meet_defl_def
by (simp add: defl.extension_principal defl.extension_mono meet_fin_defl_mono)

lemma meet_defl_below1: "meet_defl\<cdot>a\<cdot>b \<sqsubseteq> a"
apply (induct a rule: defl.principal_induct, simp)
apply (induct b rule: defl.principal_induct, simp)
apply (simp add: meet_defl_principal meet_fin_defl_below1)
done

lemma meet_defl_below2: "meet_defl\<cdot>a\<cdot>b \<sqsubseteq> b"
apply (induct a rule: defl.principal_induct, simp)
apply (induct b rule: defl.principal_induct, simp)
apply (simp add: meet_defl_principal meet_fin_defl_below2)
done

lemma meet_defl_greatest: "\<lbrakk>a \<sqsubseteq> b; a \<sqsubseteq> c\<rbrakk> \<Longrightarrow> a \<sqsubseteq> meet_defl\<cdot>b\<cdot>c"
apply (induct a rule: defl.principal_induct, simp)
apply (induct b rule: defl.principal_induct, simp)
apply (induct c rule: defl.principal_induct, simp)
apply (simp add: meet_defl_principal meet_fin_defl_greatest)
done

lemma meet_defl_eq2: "b \<sqsubseteq> a \<Longrightarrow> meet_defl\<cdot>a\<cdot>b = b"
by (fast intro: below_antisym meet_defl_below2 meet_defl_greatest)

interpretation meet_defl: semilattice "\<lambda>a b. meet_defl\<cdot>a\<cdot>b"
by default
  (fast intro: below_antisym meet_defl_greatest
   meet_defl_below1 [THEN below_trans] meet_defl_below2 [THEN below_trans])+

lemma deflation_meet_defl: "deflation (meet_defl\<cdot>a)"
apply (rule deflation.intro)
apply (rule meet_defl.left_idem)
apply (rule meet_defl_below2)
done

lemma finite_deflation_meet_defl:
  assumes "compact a"
  shows "finite_deflation (meet_defl\<cdot>a)"
proof (rule finite_deflation_intro)
  obtain d where a: "a = defl_principal d"
    using defl.compact_imp_principal [OF assms] ..
  have "finite (defl_set -` Pow (defl_set a))"
    apply (rule finite_vimageI)
    apply (rule finite_Pow_iff [THEN iffD2])
    apply (simp add: defl_set_def a cast_defl_principal Abs_fin_defl_inverse)
    apply (rule Rep_fin_defl.finite_fixes)
    apply (rule injI)
    apply (simp add: po_eq_conv defl_set_subset_iff [symmetric])
    done
  hence "finite (range (\<lambda>b. meet_defl\<cdot>a\<cdot>b))"
    apply (rule rev_finite_subset)
    apply (clarsimp, erule rev_subsetD)
    apply (simp add: defl_set_subset_iff meet_defl_below1)
    done
  thus "finite {b. meet_defl\<cdot>a\<cdot>b = b}"
    by (rule finite_range_imp_finite_fixes)
qed (rule deflation_meet_defl)

lemma compact_iff_finite_deflation_cast:
  "compact d \<longleftrightarrow> finite_deflation (cast\<cdot>d)"
apply (safe dest!: defl.compact_imp_principal)
apply (simp add: cast_defl_principal finite_deflation_Rep_fin_defl)
apply (rule compact_cast_iff [THEN iffD1])
apply (erule finite_deflation_imp_compact)
done

lemma compact_iff_finite_defl_set:
  "compact d \<longleftrightarrow> finite (defl_set d)"
by (simp add: compact_iff_finite_deflation_cast defl_set_def
  finite_deflation_def deflation_cast finite_deflation_axioms_def)

lemma compact_meet_defl1: "compact a \<Longrightarrow> compact (meet_defl\<cdot>a\<cdot>b)"
apply (simp add: compact_iff_finite_defl_set)
apply (erule rev_finite_subset)
apply (simp add: defl_set_subset_iff meet_defl_below1)
done

lemma compact_meet_defl2: "compact b \<Longrightarrow> compact (meet_defl\<cdot>a\<cdot>b)"
by (subst meet_defl.commute, rule compact_meet_defl1)

subsection {* Chain of approx functions on algebraic deflations *}

context bifinite_approx_chain
begin

definition defl_approx :: "nat \<Rightarrow> 'a defl \<rightarrow> 'a defl"
  where "defl_approx i = meet_defl\<cdot>(defl_principal (Abs_fin_defl (approx i)))"

lemma defl_approx: "approx_chain defl_approx"
proof (rule approx_chain.intro)
  have chain1: "chain (\<lambda>i. defl_principal (Abs_fin_defl (approx i)))"
    apply (rule chainI)
    apply (rule defl.principal_mono)
    apply (simp add: below_fin_defl_def Abs_fin_defl_inverse)
    apply (rule chainE [OF chain_approx])
    done
  show chain: "chain (\<lambda>i. defl_approx i)"
    unfolding defl_approx_def by (simp add: chain1)
  have below: "\<And>i d. defl_approx i\<cdot>d \<sqsubseteq> d"
    unfolding defl_approx_def by (rule meet_defl_below2)
  show "(\<Squnion>i. defl_approx i) = ID"
    apply (rule cfun_eqI, rename_tac d, simp)
    apply (rule below_antisym)
    apply (simp add: contlub_cfun_fun chain)
    apply (simp add: lub_below chain below)
    apply (simp add: defl_approx_def)
    apply (simp add: lub_distribs chain1)
    apply (rule meet_defl_greatest [OF _ below_refl])
    apply (rule cast_below_imp_below)
    apply (simp add: contlub_cfun_arg chain1)
    apply (simp add: cast_defl_principal Abs_fin_defl_inverse)
    apply (rule cast.below_ID)
    done
  show "\<And>i. finite_deflation (defl_approx i)"
    unfolding defl_approx_def
    apply (rule finite_deflation_meet_defl)
    apply (rule defl.compact_principal)
    done
qed

end

subsection {* Algebraic deflations are a bifinite domain *}

instance defl :: (bifinite) bifinite
proof
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain a"
    using bifinite ..
  hence "bifinite_approx_chain a"
    unfolding bifinite_approx_chain_def .
  thus "\<exists>(a::nat \<Rightarrow> 'a defl \<rightarrow> 'a defl). approx_chain a"
    by (fast intro: bifinite_approx_chain.defl_approx)
qed

subsection {* Algebraic deflations are representable *}

default_sort "domain"

definition defl_emb :: "udom defl \<rightarrow> udom"
  where "defl_emb = udom_emb (bifinite_approx_chain.defl_approx udom_approx)"

definition defl_prj :: "udom \<rightarrow> udom defl"
  where "defl_prj = udom_prj (bifinite_approx_chain.defl_approx udom_approx)"

lemma ep_pair_defl: "ep_pair defl_emb defl_prj"
unfolding defl_emb_def defl_prj_def
apply (rule ep_pair_udom)
apply (rule bifinite_approx_chain.defl_approx)
apply (simp add: bifinite_approx_chain_def)
done

text "Deflation combinator for deflation type constructor"

definition defl_defl :: "udom defl \<rightarrow> udom defl"
  where defl_deflation_def:
  "defl_defl = defl.extension (\<lambda>a. defl_principal
    (Abs_fin_defl (defl_emb oo meet_defl\<cdot>(defl_principal a) oo defl_prj)))"

lemma cast_defl_defl:
  "cast\<cdot>(defl_defl\<cdot>a) = defl_emb oo meet_defl\<cdot>a oo defl_prj"
apply (induct a rule: defl.principal_induct, simp)
apply (subst defl_deflation_def)
apply (subst defl.extension_principal)
apply (simp add: below_fin_defl_def Abs_fin_defl_inverse
  ep_pair.finite_deflation_e_d_p ep_pair_defl
  finite_deflation_meet_defl monofun_cfun)
apply (simp add: cast_defl_principal
  below_fin_defl_def Abs_fin_defl_inverse
  ep_pair.finite_deflation_e_d_p ep_pair_defl
  finite_deflation_meet_defl monofun_cfun)
done

definition defl_map_emb :: "'a::domain defl \<rightarrow> udom defl"
  where "defl_map_emb = defl_fun1 emb prj ID"

definition defl_map_prj :: "udom defl \<rightarrow> 'a::domain defl"
  where "defl_map_prj = defl.extension (\<lambda>a. defl_principal (Abs_fin_defl (prj oo cast\<cdot>(meet_defl\<cdot>DEFL('a)\<cdot>(defl_principal a)) oo emb)))"

lemma defl_map_emb_principal:
  "defl_map_emb\<cdot>(defl_principal a) =
    defl_principal (Abs_fin_defl (emb oo Rep_fin_defl a oo prj))"
unfolding defl_map_emb_def defl_fun1_def
apply (subst defl.extension_principal)
apply (rule defl.principal_mono)
apply (simp add: below_fin_defl_def Abs_fin_defl_inverse monofun_cfun
       domain.finite_deflation_e_d_p finite_deflation_Rep_fin_defl)
apply simp
done

lemma defl_map_prj_principal:
  "(defl_map_prj\<cdot>(defl_principal a) :: 'a::domain defl) =
  defl_principal (Abs_fin_defl (prj oo cast\<cdot>(meet_defl\<cdot>DEFL('a)\<cdot>(defl_principal a)) oo emb))"
unfolding defl_map_prj_def
apply (rule defl.extension_principal)
apply (rule defl.principal_mono)
apply (simp add: below_fin_defl_def)
apply (subst Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_p_d_e)
apply (rule finite_deflation_cast)
apply (simp add: compact_meet_defl2)
apply (subst emb_prj)
apply (intro monofun_cfun below_refl meet_defl_below1)
apply (subst Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_p_d_e)
apply (rule finite_deflation_cast)
apply (simp add: compact_meet_defl2)
apply (subst emb_prj)
apply (intro monofun_cfun below_refl meet_defl_below1)
apply (simp add: monofun_cfun below_fin_defl_def)
done

lemma defl_map_prj_defl_map_emb: "defl_map_prj\<cdot>(defl_map_emb\<cdot>d) = d"
apply (rule cast_eq_imp_eq)
apply (induct_tac d rule: defl.principal_induct, simp)
apply (subst defl_map_emb_principal)
apply (subst defl_map_prj_principal)
apply (simp add: cast_defl_principal)
apply (subst Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_p_d_e)
apply (rule finite_deflation_cast)
apply (simp add: compact_meet_defl2)
apply (subst emb_prj)
apply (intro monofun_cfun below_refl meet_defl_below1)
apply (subst meet_defl_eq2)
apply (rule cast_below_imp_below)
apply (simp add: cast_DEFL)
apply (simp add: cast_defl_principal)
apply (subst Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_e_d_p)
apply (rule finite_deflation_Rep_fin_defl)
apply (rule cfun_belowI, simp)
apply (rule Rep_fin_defl.below)
apply (simp add: cast_defl_principal)
apply (subst Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_e_d_p)
apply (rule finite_deflation_Rep_fin_defl)
apply (simp add: cfun_eqI)
done

lemma defl_map_emb_defl_map_prj:
  "defl_map_emb\<cdot>(defl_map_prj\<cdot>d :: 'a defl) = meet_defl\<cdot>DEFL('a)\<cdot>d"
apply (induct_tac d rule: defl.principal_induct, simp)
apply (subst defl_map_prj_principal)
apply (subst defl_map_emb_principal)
apply (subst Abs_fin_defl_inverse, simp)
apply (rule domain.finite_deflation_p_d_e)
apply (rule finite_deflation_cast)
apply (simp add: compact_meet_defl2)
apply (subst emb_prj)
apply (intro monofun_cfun below_refl meet_defl_below1)
apply (rule cast_eq_imp_eq)
apply (subst cast_defl_principal)
apply (simp add: cfcomp1 emb_prj)
apply (subst deflation_below_comp2 [OF deflation_cast deflation_cast])
apply (rule monofun_cfun_arg, rule meet_defl_below1)
apply (subst deflation_below_comp1 [OF deflation_cast deflation_cast])
apply (rule monofun_cfun_arg, rule meet_defl_below1)
apply (simp add: eta_cfun)
apply (rule Abs_fin_defl_inverse, simp)
apply (rule finite_deflation_cast)
apply (rule compact_meet_defl2, simp)
done

lemma ep_pair_defl_map_emb_defl_map_prj:
  "ep_pair defl_map_emb defl_map_prj"
apply (rule ep_pair.intro)
apply (rule defl_map_prj_defl_map_emb)
apply (simp add: defl_map_emb_defl_map_prj)
apply (rule meet_defl_below2)
done

instantiation defl :: ("domain") "domain"
begin

definition
  "emb = defl_emb oo defl_map_emb"

definition
  "prj = defl_map_prj oo defl_prj"

definition
  "defl (t::'a defl itself) = defl_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a defl u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a defl u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a defl itself) = liftdefl_of\<cdot>DEFL('a defl)"

instance proof
  show ep: "ep_pair emb (prj :: udom \<rightarrow> 'a defl)"
    unfolding emb_defl_def prj_defl_def
    apply (rule ep_pair_comp [OF _ ep_pair_defl])
    apply (rule ep_pair_defl_map_emb_defl_map_prj)
    done
  show "cast\<cdot>DEFL('a defl) = emb oo (prj :: udom \<rightarrow> 'a defl)"
    unfolding defl_defl_def emb_defl_def prj_defl_def
    by (simp add: cast_defl_defl cfcomp1 defl_map_emb_defl_map_prj)
qed (fact liftemb_defl_def liftprj_defl_def liftdefl_defl_def)+

end

lemma DEFL_defl [domain_defl_simps]: "DEFL('a defl) = defl_defl\<cdot>DEFL('a)"
by (rule defl_defl_def)

end
