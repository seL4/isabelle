(*  Title:      HOL/HOLCF/Deflation.thy
    Author:     Brian Huffman
*)

header {* Continuous deflations and ep-pairs *}

theory Deflation
imports Plain_HOLCF
begin

default_sort cpo

subsection {* Continuous deflations *}

locale deflation =
  fixes d :: "'a \<rightarrow> 'a"
  assumes idem: "\<And>x. d\<cdot>(d\<cdot>x) = d\<cdot>x"
  assumes below: "\<And>x. d\<cdot>x \<sqsubseteq> x"
begin

lemma below_ID: "d \<sqsubseteq> ID"
by (rule cfun_belowI, simp add: below)

text {* The set of fixed points is the same as the range. *}

lemma fixes_eq_range: "{x. d\<cdot>x = x} = range (\<lambda>x. d\<cdot>x)"
by (auto simp add: eq_sym_conv idem)

lemma range_eq_fixes: "range (\<lambda>x. d\<cdot>x) = {x. d\<cdot>x = x}"
by (auto simp add: eq_sym_conv idem)

text {*
  The pointwise ordering on deflation functions coincides with
  the subset ordering of their sets of fixed-points.
*}

lemma belowI:
  assumes f: "\<And>x. d\<cdot>x = x \<Longrightarrow> f\<cdot>x = x" shows "d \<sqsubseteq> f"
proof (rule cfun_belowI)
  fix x
  from below have "f\<cdot>(d\<cdot>x) \<sqsubseteq> f\<cdot>x" by (rule monofun_cfun_arg)
  also from idem have "f\<cdot>(d\<cdot>x) = d\<cdot>x" by (rule f)
  finally show "d\<cdot>x \<sqsubseteq> f\<cdot>x" .
qed

lemma belowD: "\<lbrakk>f \<sqsubseteq> d; f\<cdot>x = x\<rbrakk> \<Longrightarrow> d\<cdot>x = x"
proof (rule below_antisym)
  from below show "d\<cdot>x \<sqsubseteq> x" .
next
  assume "f \<sqsubseteq> d"
  hence "f\<cdot>x \<sqsubseteq> d\<cdot>x" by (rule monofun_cfun_fun)
  also assume "f\<cdot>x = x"
  finally show "x \<sqsubseteq> d\<cdot>x" .
qed

end

lemma deflation_strict: "deflation d \<Longrightarrow> d\<cdot>\<bottom> = \<bottom>"
by (rule deflation.below [THEN bottomI])

lemma adm_deflation: "adm (\<lambda>d. deflation d)"
by (simp add: deflation_def)

lemma deflation_ID: "deflation ID"
by (simp add: deflation.intro)

lemma deflation_bottom: "deflation \<bottom>"
by (simp add: deflation.intro)

lemma deflation_below_iff:
  "\<lbrakk>deflation p; deflation q\<rbrakk> \<Longrightarrow> p \<sqsubseteq> q \<longleftrightarrow> (\<forall>x. p\<cdot>x = x \<longrightarrow> q\<cdot>x = x)"
 apply safe
  apply (simp add: deflation.belowD)
 apply (simp add: deflation.belowI)
done

text {*
  The composition of two deflations is equal to
  the lesser of the two (if they are comparable).
*}

lemma deflation_below_comp1:
  assumes "deflation f"
  assumes "deflation g"
  shows "f \<sqsubseteq> g \<Longrightarrow> f\<cdot>(g\<cdot>x) = f\<cdot>x"
proof (rule below_antisym)
  interpret g: deflation g by fact
  from g.below show "f\<cdot>(g\<cdot>x) \<sqsubseteq> f\<cdot>x" by (rule monofun_cfun_arg)
next
  interpret f: deflation f by fact
  assume "f \<sqsubseteq> g" hence "f\<cdot>x \<sqsubseteq> g\<cdot>x" by (rule monofun_cfun_fun)
  hence "f\<cdot>(f\<cdot>x) \<sqsubseteq> f\<cdot>(g\<cdot>x)" by (rule monofun_cfun_arg)
  also have "f\<cdot>(f\<cdot>x) = f\<cdot>x" by (rule f.idem)
  finally show "f\<cdot>x \<sqsubseteq> f\<cdot>(g\<cdot>x)" .
qed

lemma deflation_below_comp2:
  "\<lbrakk>deflation f; deflation g; f \<sqsubseteq> g\<rbrakk> \<Longrightarrow> g\<cdot>(f\<cdot>x) = f\<cdot>x"
by (simp only: deflation.belowD deflation.idem)


subsection {* Deflations with finite range *}

lemma finite_range_imp_finite_fixes:
  "finite (range f) \<Longrightarrow> finite {x. f x = x}"
proof -
  have "{x. f x = x} \<subseteq> range f"
    by (clarify, erule subst, rule rangeI)
  moreover assume "finite (range f)"
  ultimately show "finite {x. f x = x}"
    by (rule finite_subset)
qed

locale finite_deflation = deflation +
  assumes finite_fixes: "finite {x. d\<cdot>x = x}"
begin

lemma finite_range: "finite (range (\<lambda>x. d\<cdot>x))"
by (simp add: range_eq_fixes finite_fixes)

lemma finite_image: "finite ((\<lambda>x. d\<cdot>x) ` A)"
by (rule finite_subset [OF image_mono [OF subset_UNIV] finite_range])

lemma compact: "compact (d\<cdot>x)"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'a"
  assume Y: "chain Y"
  have "finite_chain (\<lambda>i. d\<cdot>(Y i))"
  proof (rule finite_range_imp_finch)
    show "chain (\<lambda>i. d\<cdot>(Y i))"
      using Y by simp
    have "range (\<lambda>i. d\<cdot>(Y i)) \<subseteq> range (\<lambda>x. d\<cdot>x)"
      by clarsimp
    thus "finite (range (\<lambda>i. d\<cdot>(Y i)))"
      using finite_range by (rule finite_subset)
  qed
  hence "\<exists>j. (\<Squnion>i. d\<cdot>(Y i)) = d\<cdot>(Y j)"
    by (simp add: finite_chain_def maxinch_is_thelub Y)
  then obtain j where j: "(\<Squnion>i. d\<cdot>(Y i)) = d\<cdot>(Y j)" ..

  assume "d\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)"
  hence "d\<cdot>(d\<cdot>x) \<sqsubseteq> d\<cdot>(\<Squnion>i. Y i)"
    by (rule monofun_cfun_arg)
  hence "d\<cdot>x \<sqsubseteq> (\<Squnion>i. d\<cdot>(Y i))"
    by (simp add: contlub_cfun_arg Y idem)
  hence "d\<cdot>x \<sqsubseteq> d\<cdot>(Y j)"
    using j by simp
  hence "d\<cdot>x \<sqsubseteq> Y j"
    using below by (rule below_trans)
  thus "\<exists>j. d\<cdot>x \<sqsubseteq> Y j" ..
qed

end

lemma finite_deflation_intro:
  "deflation d \<Longrightarrow> finite {x. d\<cdot>x = x} \<Longrightarrow> finite_deflation d"
by (intro finite_deflation.intro finite_deflation_axioms.intro)

lemma finite_deflation_imp_deflation:
  "finite_deflation d \<Longrightarrow> deflation d"
unfolding finite_deflation_def by simp

lemma finite_deflation_bottom: "finite_deflation \<bottom>"
by default simp_all


subsection {* Continuous embedding-projection pairs *}

locale ep_pair =
  fixes e :: "'a \<rightarrow> 'b" and p :: "'b \<rightarrow> 'a"
  assumes e_inverse [simp]: "\<And>x. p\<cdot>(e\<cdot>x) = x"
  and e_p_below: "\<And>y. e\<cdot>(p\<cdot>y) \<sqsubseteq> y"
begin

lemma e_below_iff [simp]: "e\<cdot>x \<sqsubseteq> e\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
proof
  assume "e\<cdot>x \<sqsubseteq> e\<cdot>y"
  hence "p\<cdot>(e\<cdot>x) \<sqsubseteq> p\<cdot>(e\<cdot>y)" by (rule monofun_cfun_arg)
  thus "x \<sqsubseteq> y" by simp
next
  assume "x \<sqsubseteq> y"
  thus "e\<cdot>x \<sqsubseteq> e\<cdot>y" by (rule monofun_cfun_arg)
qed

lemma e_eq_iff [simp]: "e\<cdot>x = e\<cdot>y \<longleftrightarrow> x = y"
unfolding po_eq_conv e_below_iff ..

lemma p_eq_iff:
  "\<lbrakk>e\<cdot>(p\<cdot>x) = x; e\<cdot>(p\<cdot>y) = y\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>y \<longleftrightarrow> x = y"
by (safe, erule subst, erule subst, simp)

lemma p_inverse: "(\<exists>x. y = e\<cdot>x) = (e\<cdot>(p\<cdot>y) = y)"
by (auto, rule exI, erule sym)

lemma e_below_iff_below_p: "e\<cdot>x \<sqsubseteq> y \<longleftrightarrow> x \<sqsubseteq> p\<cdot>y"
proof
  assume "e\<cdot>x \<sqsubseteq> y"
  then have "p\<cdot>(e\<cdot>x) \<sqsubseteq> p\<cdot>y" by (rule monofun_cfun_arg)
  then show "x \<sqsubseteq> p\<cdot>y" by simp
next
  assume "x \<sqsubseteq> p\<cdot>y"
  then have "e\<cdot>x \<sqsubseteq> e\<cdot>(p\<cdot>y)" by (rule monofun_cfun_arg)
  then show "e\<cdot>x \<sqsubseteq> y" using e_p_below by (rule below_trans)
qed

lemma compact_e_rev: "compact (e\<cdot>x) \<Longrightarrow> compact x"
proof -
  assume "compact (e\<cdot>x)"
  hence "adm (\<lambda>y. e\<cdot>x \<notsqsubseteq> y)" by (rule compactD)
  hence "adm (\<lambda>y. e\<cdot>x \<notsqsubseteq> e\<cdot>y)" by (rule adm_subst [OF cont_Rep_cfun2])
  hence "adm (\<lambda>y. x \<notsqsubseteq> y)" by simp
  thus "compact x" by (rule compactI)
qed

lemma compact_e: "compact x \<Longrightarrow> compact (e\<cdot>x)"
proof -
  assume "compact x"
  hence "adm (\<lambda>y. x \<notsqsubseteq> y)" by (rule compactD)
  hence "adm (\<lambda>y. x \<notsqsubseteq> p\<cdot>y)" by (rule adm_subst [OF cont_Rep_cfun2])
  hence "adm (\<lambda>y. e\<cdot>x \<notsqsubseteq> y)" by (simp add: e_below_iff_below_p)
  thus "compact (e\<cdot>x)" by (rule compactI)
qed

lemma compact_e_iff: "compact (e\<cdot>x) \<longleftrightarrow> compact x"
by (rule iffI [OF compact_e_rev compact_e])

text {* Deflations from ep-pairs *}

lemma deflation_e_p: "deflation (e oo p)"
by (simp add: deflation.intro e_p_below)

lemma deflation_e_d_p:
  assumes "deflation d"
  shows "deflation (e oo d oo p)"
proof
  interpret deflation d by fact
  fix x :: 'b
  show "(e oo d oo p)\<cdot>((e oo d oo p)\<cdot>x) = (e oo d oo p)\<cdot>x"
    by (simp add: idem)
  show "(e oo d oo p)\<cdot>x \<sqsubseteq> x"
    by (simp add: e_below_iff_below_p below)
qed

lemma finite_deflation_e_d_p:
  assumes "finite_deflation d"
  shows "finite_deflation (e oo d oo p)"
proof
  interpret finite_deflation d by fact
  fix x :: 'b
  show "(e oo d oo p)\<cdot>((e oo d oo p)\<cdot>x) = (e oo d oo p)\<cdot>x"
    by (simp add: idem)
  show "(e oo d oo p)\<cdot>x \<sqsubseteq> x"
    by (simp add: e_below_iff_below_p below)
  have "finite ((\<lambda>x. e\<cdot>x) ` (\<lambda>x. d\<cdot>x) ` range (\<lambda>x. p\<cdot>x))"
    by (simp add: finite_image)
  hence "finite (range (\<lambda>x. (e oo d oo p)\<cdot>x))"
    by (simp add: image_image)
  thus "finite {x. (e oo d oo p)\<cdot>x = x}"
    by (rule finite_range_imp_finite_fixes)
qed

lemma deflation_p_d_e:
  assumes "deflation d"
  assumes d: "\<And>x. d\<cdot>x \<sqsubseteq> e\<cdot>(p\<cdot>x)"
  shows "deflation (p oo d oo e)"
proof -
  interpret d: deflation d by fact
  {
    fix x
    have "d\<cdot>(e\<cdot>x) \<sqsubseteq> e\<cdot>x"
      by (rule d.below)
    hence "p\<cdot>(d\<cdot>(e\<cdot>x)) \<sqsubseteq> p\<cdot>(e\<cdot>x)"
      by (rule monofun_cfun_arg)
    hence "(p oo d oo e)\<cdot>x \<sqsubseteq> x"
      by simp
  }
  note p_d_e_below = this
  show ?thesis
  proof
    fix x
    show "(p oo d oo e)\<cdot>x \<sqsubseteq> x"
      by (rule p_d_e_below)
  next
    fix x
    show "(p oo d oo e)\<cdot>((p oo d oo e)\<cdot>x) = (p oo d oo e)\<cdot>x"
    proof (rule below_antisym)
      show "(p oo d oo e)\<cdot>((p oo d oo e)\<cdot>x) \<sqsubseteq> (p oo d oo e)\<cdot>x"
        by (rule p_d_e_below)
      have "p\<cdot>(d\<cdot>(d\<cdot>(d\<cdot>(e\<cdot>x)))) \<sqsubseteq> p\<cdot>(d\<cdot>(e\<cdot>(p\<cdot>(d\<cdot>(e\<cdot>x)))))"
        by (intro monofun_cfun_arg d)
      hence "p\<cdot>(d\<cdot>(e\<cdot>x)) \<sqsubseteq> p\<cdot>(d\<cdot>(e\<cdot>(p\<cdot>(d\<cdot>(e\<cdot>x)))))"
        by (simp only: d.idem)
      thus "(p oo d oo e)\<cdot>x \<sqsubseteq> (p oo d oo e)\<cdot>((p oo d oo e)\<cdot>x)"
        by simp
    qed
  qed
qed

lemma finite_deflation_p_d_e:
  assumes "finite_deflation d"
  assumes d: "\<And>x. d\<cdot>x \<sqsubseteq> e\<cdot>(p\<cdot>x)"
  shows "finite_deflation (p oo d oo e)"
proof -
  interpret d: finite_deflation d by fact
  show ?thesis
  proof (rule finite_deflation_intro)
    have "deflation d" ..
    thus "deflation (p oo d oo e)"
      using d by (rule deflation_p_d_e)
  next
    have "finite ((\<lambda>x. d\<cdot>x) ` range (\<lambda>x. e\<cdot>x))"
      by (rule d.finite_image)
    hence "finite ((\<lambda>x. p\<cdot>x) ` (\<lambda>x. d\<cdot>x) ` range (\<lambda>x. e\<cdot>x))"
      by (rule finite_imageI)
    hence "finite (range (\<lambda>x. (p oo d oo e)\<cdot>x))"
      by (simp add: image_image)
    thus "finite {x. (p oo d oo e)\<cdot>x = x}"
      by (rule finite_range_imp_finite_fixes)
  qed
qed

end

subsection {* Uniqueness of ep-pairs *}

lemma ep_pair_unique_e_lemma:
  assumes 1: "ep_pair e1 p" and 2: "ep_pair e2 p"
  shows "e1 \<sqsubseteq> e2"
proof (rule cfun_belowI)
  fix x
  have "e1\<cdot>(p\<cdot>(e2\<cdot>x)) \<sqsubseteq> e2\<cdot>x"
    by (rule ep_pair.e_p_below [OF 1])
  thus "e1\<cdot>x \<sqsubseteq> e2\<cdot>x"
    by (simp only: ep_pair.e_inverse [OF 2])
qed

lemma ep_pair_unique_e:
  "\<lbrakk>ep_pair e1 p; ep_pair e2 p\<rbrakk> \<Longrightarrow> e1 = e2"
by (fast intro: below_antisym elim: ep_pair_unique_e_lemma)

lemma ep_pair_unique_p_lemma:
  assumes 1: "ep_pair e p1" and 2: "ep_pair e p2"
  shows "p1 \<sqsubseteq> p2"
proof (rule cfun_belowI)
  fix x
  have "e\<cdot>(p1\<cdot>x) \<sqsubseteq> x"
    by (rule ep_pair.e_p_below [OF 1])
  hence "p2\<cdot>(e\<cdot>(p1\<cdot>x)) \<sqsubseteq> p2\<cdot>x"
    by (rule monofun_cfun_arg)
  thus "p1\<cdot>x \<sqsubseteq> p2\<cdot>x"
    by (simp only: ep_pair.e_inverse [OF 2])
qed

lemma ep_pair_unique_p:
  "\<lbrakk>ep_pair e p1; ep_pair e p2\<rbrakk> \<Longrightarrow> p1 = p2"
by (fast intro: below_antisym elim: ep_pair_unique_p_lemma)

subsection {* Composing ep-pairs *}

lemma ep_pair_ID_ID: "ep_pair ID ID"
by default simp_all

lemma ep_pair_comp:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (e2 oo e1) (p1 oo p2)"
proof
  interpret ep1: ep_pair e1 p1 by fact
  interpret ep2: ep_pair e2 p2 by fact
  fix x y
  show "(p1 oo p2)\<cdot>((e2 oo e1)\<cdot>x) = x"
    by simp
  have "e1\<cdot>(p1\<cdot>(p2\<cdot>y)) \<sqsubseteq> p2\<cdot>y"
    by (rule ep1.e_p_below)
  hence "e2\<cdot>(e1\<cdot>(p1\<cdot>(p2\<cdot>y))) \<sqsubseteq> e2\<cdot>(p2\<cdot>y)"
    by (rule monofun_cfun_arg)
  also have "e2\<cdot>(p2\<cdot>y) \<sqsubseteq> y"
    by (rule ep2.e_p_below)
  finally show "(e2 oo e1)\<cdot>((p1 oo p2)\<cdot>y) \<sqsubseteq> y"
    by simp
qed

locale pcpo_ep_pair = ep_pair e p
  for e :: "'a::pcpo \<rightarrow> 'b::pcpo"
  and p :: "'b::pcpo \<rightarrow> 'a::pcpo"
begin

lemma e_strict [simp]: "e\<cdot>\<bottom> = \<bottom>"
proof -
  have "\<bottom> \<sqsubseteq> p\<cdot>\<bottom>" by (rule minimal)
  hence "e\<cdot>\<bottom> \<sqsubseteq> e\<cdot>(p\<cdot>\<bottom>)" by (rule monofun_cfun_arg)
  also have "e\<cdot>(p\<cdot>\<bottom>) \<sqsubseteq> \<bottom>" by (rule e_p_below)
  finally show "e\<cdot>\<bottom> = \<bottom>" by simp
qed

lemma e_bottom_iff [simp]: "e\<cdot>x = \<bottom> \<longleftrightarrow> x = \<bottom>"
by (rule e_eq_iff [where y="\<bottom>", unfolded e_strict])

lemma e_defined: "x \<noteq> \<bottom> \<Longrightarrow> e\<cdot>x \<noteq> \<bottom>"
by simp

lemma p_strict [simp]: "p\<cdot>\<bottom> = \<bottom>"
by (rule e_inverse [where x="\<bottom>", unfolded e_strict])

lemmas stricts = e_strict p_strict

end

end
