(*  Title:      HOLCF/Bifinite.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Bifinite domains and approximation *}

theory Bifinite
imports Cfun
begin

subsection {* Bifinite domains *}

axclass approx < cpo

consts approx :: "nat \<Rightarrow> 'a::approx \<rightarrow> 'a"

axclass bifinite_cpo < approx
  chain_approx_app: "chain (\<lambda>i. approx i\<cdot>x)"
  lub_approx_app [simp]: "(\<Squnion>i. approx i\<cdot>x) = x"
  approx_idem: "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
  finite_fixes_approx: "finite {x. approx i\<cdot>x = x}"

axclass bifinite < bifinite_cpo, pcpo

lemma finite_range_imp_finite_fixes:
  "finite {x. \<exists>y. x = f y} \<Longrightarrow> finite {x. f x = x}"
apply (subgoal_tac "{x. f x = x} \<subseteq> {x. \<exists>y. x = f y}")
apply (erule (1) finite_subset)
apply (clarify, erule subst, rule exI, rule refl)
done

lemma chain_approx [simp]:
  "chain (approx :: nat \<Rightarrow> 'a::bifinite_cpo \<rightarrow> 'a)"
apply (rule chainI)
apply (rule less_cfun_ext)
apply (rule chainE)
apply (rule chain_approx_app)
done

lemma lub_approx [simp]: "(\<Squnion>i. approx i) = (\<Lambda>(x::'a::bifinite_cpo). x)"
by (rule ext_cfun, simp add: contlub_cfun_fun)

lemma approx_less: "approx i\<cdot>x \<sqsubseteq> (x::'a::bifinite_cpo)"
apply (subgoal_tac "approx i\<cdot>x \<sqsubseteq> (\<Squnion>i. approx i\<cdot>x)", simp)
apply (rule is_ub_thelub, simp)
done

lemma approx_strict [simp]: "approx i\<cdot>(\<bottom>::'a::bifinite) = \<bottom>"
by (rule UU_I, rule approx_less)

lemma approx_approx1:
  "i \<le> j \<Longrightarrow> approx i\<cdot>(approx j\<cdot>x) = approx i\<cdot>(x::'a::bifinite_cpo)"
apply (rule antisym_less)
apply (rule monofun_cfun_arg [OF approx_less])
apply (rule sq_ord_eq_less_trans [OF approx_idem [symmetric]])
apply (rule monofun_cfun_arg)
apply (rule monofun_cfun_fun)
apply (erule chain_mono [OF chain_approx])
done

lemma approx_approx2:
  "j \<le> i \<Longrightarrow> approx i\<cdot>(approx j\<cdot>x) = approx j\<cdot>(x::'a::bifinite_cpo)"
apply (rule antisym_less)
apply (rule approx_less)
apply (rule sq_ord_eq_less_trans [OF approx_idem [symmetric]])
apply (rule monofun_cfun_fun)
apply (erule chain_mono [OF chain_approx])
done

lemma approx_approx [simp]:
  "approx i\<cdot>(approx j\<cdot>x) = approx (min i j)\<cdot>(x::'a::bifinite_cpo)"
apply (rule_tac x=i and y=j in linorder_le_cases)
apply (simp add: approx_approx1 min_def)
apply (simp add: approx_approx2 min_def)
done

lemma idem_fixes_eq_range:
  "\<forall>x. f (f x) = f x \<Longrightarrow> {x. f x = x} = {y. \<exists>x. y = f x}"
by (auto simp add: eq_sym_conv)

lemma finite_approx: "finite {y::'a::bifinite_cpo. \<exists>x. y = approx n\<cdot>x}"
using finite_fixes_approx by (simp add: idem_fixes_eq_range)

lemma finite_range_approx:
  "finite (range (\<lambda>x::'a::bifinite_cpo. approx n\<cdot>x))"
by (simp add: image_def finite_approx)

lemma compact_approx [simp]:
  fixes x :: "'a::bifinite_cpo"
  shows "compact (approx n\<cdot>x)"
proof (rule compactI2)
  fix Y::"nat \<Rightarrow> 'a"
  assume Y: "chain Y"
  have "finite_chain (\<lambda>i. approx n\<cdot>(Y i))"
  proof (rule finite_range_imp_finch)
    show "chain (\<lambda>i. approx n\<cdot>(Y i))"
      using Y by simp
    have "range (\<lambda>i. approx n\<cdot>(Y i)) \<subseteq> {x. approx n\<cdot>x = x}"
      by clarsimp
    thus "finite (range (\<lambda>i. approx n\<cdot>(Y i)))"
      using finite_fixes_approx by (rule finite_subset)
  qed
  hence "\<exists>j. (\<Squnion>i. approx n\<cdot>(Y i)) = approx n\<cdot>(Y j)"
    by (simp add: finite_chain_def maxinch_is_thelub Y)
  then obtain j where j: "(\<Squnion>i. approx n\<cdot>(Y i)) = approx n\<cdot>(Y j)" ..

  assume "approx n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)"
  hence "approx n\<cdot>(approx n\<cdot>x) \<sqsubseteq> approx n\<cdot>(\<Squnion>i. Y i)"
    by (rule monofun_cfun_arg)
  hence "approx n\<cdot>x \<sqsubseteq> (\<Squnion>i. approx n\<cdot>(Y i))"
    by (simp add: contlub_cfun_arg Y)
  hence "approx n\<cdot>x \<sqsubseteq> approx n\<cdot>(Y j)"
    using j by simp
  hence "approx n\<cdot>x \<sqsubseteq> Y j"
    using approx_less by (rule trans_less)
  thus "\<exists>j. approx n\<cdot>x \<sqsubseteq> Y j" ..
qed

lemma bifinite_compact_eq_approx:
  fixes x :: "'a::bifinite_cpo"
  assumes x: "compact x"
  shows "\<exists>i. approx i\<cdot>x = x"
proof -
  have chain: "chain (\<lambda>i. approx i\<cdot>x)" by simp
  have less: "x \<sqsubseteq> (\<Squnion>i. approx i\<cdot>x)" by simp
  obtain i where i: "x \<sqsubseteq> approx i\<cdot>x"
    using compactD2 [OF x chain less] ..
  with approx_less have "approx i\<cdot>x = x"
    by (rule antisym_less)
  thus "\<exists>i. approx i\<cdot>x = x" ..
qed

lemma bifinite_compact_iff:
  "compact (x::'a::bifinite_cpo) = (\<exists>n. approx n\<cdot>x = x)"
 apply (rule iffI)
  apply (erule bifinite_compact_eq_approx)
 apply (erule exE)
 apply (erule subst)
 apply (rule compact_approx)
done

lemma approx_induct:
  assumes adm: "adm P" and P: "\<And>n x. P (approx n\<cdot>x)"
  shows "P (x::'a::bifinite)"
proof -
  have "P (\<Squnion>n. approx n\<cdot>x)"
    by (rule admD [OF adm], simp, simp add: P)
  thus "P x" by simp
qed

lemma bifinite_less_ext:
  fixes x y :: "'a::bifinite_cpo"
  shows "(\<And>i. approx i\<cdot>x \<sqsubseteq> approx i\<cdot>y) \<Longrightarrow> x \<sqsubseteq> y"
apply (subgoal_tac "(\<Squnion>i. approx i\<cdot>x) \<sqsubseteq> (\<Squnion>i. approx i\<cdot>y)", simp)
apply (rule lub_mono, simp, simp, simp)
done

subsection {* Instance for continuous function space *}

lemma finite_range_lemma:
  fixes h :: "'a::cpo \<rightarrow> 'b::cpo"
  fixes k :: "'c::cpo \<rightarrow> 'd::cpo"
  shows "\<lbrakk>finite {y. \<exists>x. y = h\<cdot>x}; finite {y. \<exists>x. y = k\<cdot>x}\<rbrakk>
    \<Longrightarrow> finite {g. \<exists>f. g = (\<Lambda> x. k\<cdot>(f\<cdot>(h\<cdot>x)))}"
 apply (rule_tac f="\<lambda>g. {(h\<cdot>x, y) |x y. y = g\<cdot>x}" in finite_imageD)
  apply (rule_tac B="Pow ({y. \<exists>x. y = h\<cdot>x} \<times> {y. \<exists>x. y = k\<cdot>x})"
           in finite_subset)
   apply (rule image_subsetI)
   apply (clarsimp, fast)
  apply simp
 apply (rule inj_onI)
 apply (clarsimp simp add: expand_set_eq)
 apply (rule ext_cfun, simp)
 apply (drule_tac x="h\<cdot>x" in spec)
 apply (drule_tac x="k\<cdot>(f\<cdot>(h\<cdot>x))" in spec)
 apply (drule iffD1, fast)
 apply clarsimp
done

instance "->" :: (bifinite_cpo, bifinite_cpo) approx ..

defs (overloaded)
  approx_cfun_def:
    "approx \<equiv> \<lambda>n. \<Lambda> f x. approx n\<cdot>(f\<cdot>(approx n\<cdot>x))"

instance "->" :: (bifinite_cpo, bifinite_cpo) bifinite_cpo
 apply (intro_classes, unfold approx_cfun_def)
    apply simp
   apply (simp add: lub_distribs eta_cfun)
  apply simp
 apply simp
 apply (rule finite_range_imp_finite_fixes)
 apply (intro finite_range_lemma finite_approx)
done

instance "->" :: (bifinite_cpo, bifinite) bifinite ..

lemma approx_cfun: "approx n\<cdot>f\<cdot>x = approx n\<cdot>(f\<cdot>(approx n\<cdot>x))"
by (simp add: approx_cfun_def)

end
