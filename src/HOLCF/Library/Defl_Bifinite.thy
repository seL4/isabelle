(*  Title:      HOLCF/Library/Defl_Bifinite.thy
    Author:     Brian Huffman
*)

header {* Algebraic deflations are a bifinite domain *}

theory Defl_Bifinite
imports HOLCF Infinite_Set
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

subsection {* Take function for finite deflations *}

definition
  defl_take :: "nat \<Rightarrow> (udom \<rightarrow> udom) \<Rightarrow> (udom \<rightarrow> udom)"
where
  "defl_take i d = eventual_iterate (udom_approx i oo d)"

lemma finite_deflation_defl_take:
  "deflation d \<Longrightarrow> finite_deflation (defl_take i d)"
unfolding defl_take_def
apply (rule pre_deflation.finite_deflation_d)
apply (rule pre_deflation_oo)
apply (rule finite_deflation_udom_approx)
apply (erule deflation.below)
done

lemma deflation_defl_take:
  "deflation d \<Longrightarrow> deflation (defl_take i d)"
apply (rule finite_deflation_imp_deflation)
apply (erule finite_deflation_defl_take)
done

lemma defl_take_fixed_iff:
  "deflation d \<Longrightarrow> defl_take i d\<cdot>x = x \<longleftrightarrow> udom_approx i\<cdot>x = x \<and> d\<cdot>x = x"
unfolding defl_take_def
apply (rule eventual_iterate_oo_fixed_iff)
apply (rule finite_deflation_udom_approx)
apply (erule deflation.below)
done

lemma defl_take_below:
  "\<lbrakk>a \<sqsubseteq> b; deflation a; deflation b\<rbrakk> \<Longrightarrow> defl_take i a \<sqsubseteq> defl_take i b"
apply (rule deflation.belowI)
apply (erule deflation_defl_take)
apply (simp add: defl_take_fixed_iff)
apply (erule (1) deflation.belowD)
apply (erule conjunct2)
done

lemma cont2cont_defl_take:
  assumes cont: "cont f" and below: "\<And>x y. f x\<cdot>y \<sqsubseteq> y"
  shows "cont (\<lambda>x. defl_take i (f x))"
unfolding defl_take_def
using finite_deflation_udom_approx assms
by (rule cont2cont_eventual_iterate_oo)

definition
  fd_take :: "nat \<Rightarrow> fin_defl \<Rightarrow> fin_defl"
where
  "fd_take i d = Abs_fin_defl (defl_take i (Rep_fin_defl d))"

lemma Rep_fin_defl_fd_take:
  "Rep_fin_defl (fd_take i d) = defl_take i (Rep_fin_defl d)"
unfolding fd_take_def
apply (rule Abs_fin_defl_inverse [unfolded mem_Collect_eq])
apply (rule finite_deflation_defl_take)
apply (rule deflation_Rep_fin_defl)
done

lemma fd_take_fixed_iff:
  "Rep_fin_defl (fd_take i d)\<cdot>x = x \<longleftrightarrow>
    udom_approx i\<cdot>x = x \<and> Rep_fin_defl d\<cdot>x = x"
unfolding Rep_fin_defl_fd_take
apply (rule defl_take_fixed_iff)
apply (rule deflation_Rep_fin_defl)
done

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

lemma approx_fixed_le_lemma: "\<lbrakk>i \<le> j; udom_approx i\<cdot>x = x\<rbrakk> \<Longrightarrow> udom_approx j\<cdot>x = x"
apply (rule deflation.belowD)
apply (rule finite_deflation_imp_deflation)
apply (rule finite_deflation_udom_approx)
apply (erule chain_mono [OF chain_udom_approx])
apply assumption
done

lemma fd_take_chain: "m \<le> n \<Longrightarrow> fd_take m a \<sqsubseteq> fd_take n a"
apply (rule fin_defl_belowI)
apply (simp add: fd_take_fixed_iff)
apply (simp add: approx_fixed_le_lemma)
done

lemma finite_range_fd_take: "finite (range (fd_take n))"
apply (rule finite_imageD [where f="\<lambda>a. {x. Rep_fin_defl a\<cdot>x = x}"])
apply (rule finite_subset [where B="Pow {x. udom_approx n\<cdot>x = x}"])
apply (clarify, simp add: fd_take_fixed_iff)
apply (simp add: finite_deflation.finite_fixes [OF finite_deflation_udom_approx])
apply (rule inj_onI, clarify)
apply (simp add: set_eq_iff fin_defl_eqI)
done

lemma fd_take_covers: "\<exists>n. fd_take n a = a"
apply (rule_tac x=
  "Max ((\<lambda>x. LEAST n. udom_approx n\<cdot>x = x) ` {x. Rep_fin_defl a\<cdot>x = x})" in exI)
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
apply (rule approx_chain.compact_eq_approx [OF udom_approx])
apply (erule subst)
apply (rule Rep_fin_defl.compact)
done

subsection {* Chain of approx functions on algebraic deflations *}

definition
  defl_approx :: "nat \<Rightarrow> defl \<rightarrow> defl"
where
  "defl_approx = (\<lambda>i. defl.basis_fun (\<lambda>d. defl_principal (fd_take i d)))"

lemma defl_approx_principal:
  "defl_approx i\<cdot>(defl_principal d) = defl_principal (fd_take i d)"
unfolding defl_approx_def
by (simp add: defl.basis_fun_principal fd_take_mono)

lemma defl_approx: "approx_chain defl_approx"
proof
  show chain: "chain defl_approx"
    unfolding defl_approx_def
    by (simp add: chainI defl.basis_fun_mono fd_take_mono fd_take_chain)
  show idem: "\<And>i x. defl_approx i\<cdot>(defl_approx i\<cdot>x) = defl_approx i\<cdot>x"
    apply (induct_tac x rule: defl.principal_induct, simp)
    apply (simp add: defl_approx_principal fd_take_idem)
    done
  show below: "\<And>i x. defl_approx i\<cdot>x \<sqsubseteq> x"
    apply (induct_tac x rule: defl.principal_induct, simp)
    apply (simp add: defl_approx_principal fd_take_below)
    done
  show lub: "(\<Squnion>i. defl_approx i) = ID"
    apply (rule cfun_eqI, rule below_antisym)
    apply (simp add: contlub_cfun_fun chain lub_below_iff chain below)
    apply (induct_tac x rule: defl.principal_induct, simp)
    apply (simp add: contlub_cfun_fun chain)
    apply (simp add: compact_below_lub_iff defl.compact_principal chain)
    apply (simp add: defl_approx_principal)
    apply (subgoal_tac "\<exists>i. fd_take i a = a", metis below_refl)
    apply (rule fd_take_covers)
    done
  show "\<And>i. finite {x. defl_approx i\<cdot>x = x}"
    apply (rule finite_range_imp_finite_fixes)
    apply (rule_tac B="defl_principal ` range (fd_take i)" in rev_finite_subset)
    apply (simp add: finite_range_fd_take)
    apply (clarsimp, rename_tac x)
    apply (induct_tac x rule: defl.principal_induct)
    apply (simp add: adm_mem_finite finite_range_fd_take)
    apply (simp add: defl_approx_principal)
    done
qed

subsection {* Algebraic deflations are a bifinite domain *}

instantiation defl :: bifinite
begin

definition
  "emb = udom_emb defl_approx"

definition
  "prj = udom_prj defl_approx"

definition
  "defl (t::defl itself) =
    (\<Squnion>i. defl_principal (Abs_fin_defl (emb oo defl_approx i oo prj)))"

instance proof
  show ep: "ep_pair emb (prj :: udom \<rightarrow> defl)"
    unfolding emb_defl_def prj_defl_def
    by (rule ep_pair_udom [OF defl_approx])
  show "cast\<cdot>DEFL(defl) = emb oo (prj :: udom \<rightarrow> defl)"
    unfolding defl_defl_def
    apply (subst contlub_cfun_arg)
    apply (rule chainI)
    apply (rule defl.principal_mono)
    apply (simp add: below_fin_defl_def)
    apply (simp add: Abs_fin_defl_inverse approx_chain.finite_deflation_approx [OF defl_approx]
                     ep_pair.finite_deflation_e_d_p [OF ep])
    apply (intro monofun_cfun below_refl)
    apply (rule chainE)
    apply (rule approx_chain.chain_approx [OF defl_approx])
    apply (subst cast_defl_principal)
    apply (simp add: Abs_fin_defl_inverse approx_chain.finite_deflation_approx [OF defl_approx]
                     ep_pair.finite_deflation_e_d_p [OF ep])
    apply (simp add: lub_distribs approx_chain.chain_approx [OF defl_approx]
                     approx_chain.lub_approx [OF defl_approx])
    done
qed

end

end
