(*  Title:      HOL/HOLCF/Deflation.thy
    Author:     Brian Huffman
*)

section \<open>Continuous deflations and ep-pairs\<close>

theory Deflation
  imports Cfun
begin

subsection \<open>Continuous deflations\<close>

locale deflation =
  fixes d :: "'a \<rightarrow> 'a"
  assumes idem: "\<And>x. d\<cdot>(d\<cdot>x) = d\<cdot>x"
  assumes below: "\<And>x. d\<cdot>x \<sqsubseteq> x"
begin

lemma below_ID: "d \<sqsubseteq> ID"
  by (rule cfun_belowI) (simp add: below)

text \<open>The set of fixed points is the same as the range.\<close>

lemma fixes_eq_range: "{x. d\<cdot>x = x} = range (\<lambda>x. d\<cdot>x)"
  by (auto simp add: eq_sym_conv idem)

lemma range_eq_fixes: "range (\<lambda>x. d\<cdot>x) = {x. d\<cdot>x = x}"
  by (auto simp add: eq_sym_conv idem)

text \<open>
  The pointwise ordering on deflation functions coincides with
  the subset ordering of their sets of fixed-points.
\<close>

lemma belowI:
  assumes f: "\<And>x. d\<cdot>x = x \<Longrightarrow> f\<cdot>x = x"
  shows "d \<sqsubseteq> f"
proof (rule cfun_belowI)
  fix x
  from below have "f\<cdot>(d\<cdot>x) \<sqsubseteq> f\<cdot>x"
    by (rule monofun_cfun_arg)
  also from idem have "f\<cdot>(d\<cdot>x) = d\<cdot>x"
    by (rule f)
  finally show "d\<cdot>x \<sqsubseteq> f\<cdot>x" .
qed

lemma belowD: "\<lbrakk>f \<sqsubseteq> d; f\<cdot>x = x\<rbrakk> \<Longrightarrow> d\<cdot>x = x"
proof (rule below_antisym)
  from below show "d\<cdot>x \<sqsubseteq> x" .
  assume "f \<sqsubseteq> d"
  then have "f\<cdot>x \<sqsubseteq> d\<cdot>x" by (rule monofun_cfun_fun)
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

lemma deflation_below_iff: "deflation p \<Longrightarrow> deflation q \<Longrightarrow> p \<sqsubseteq> q \<longleftrightarrow> (\<forall>x. p\<cdot>x = x \<longrightarrow> q\<cdot>x = x)"
  apply safe
   apply (simp add: deflation.belowD)
  apply (simp add: deflation.belowI)
  done

text \<open>
  The composition of two deflations is equal to
  the lesser of the two (if they are comparable).
\<close>

lemma deflation_below_comp1:
  assumes "deflation f"
  assumes "deflation g"
  shows "f \<sqsubseteq> g \<Longrightarrow> f\<cdot>(g\<cdot>x) = f\<cdot>x"
proof (rule below_antisym)
  interpret g: deflation g by fact
  from g.below show "f\<cdot>(g\<cdot>x) \<sqsubseteq> f\<cdot>x" by (rule monofun_cfun_arg)
next
  interpret f: deflation f by fact
  assume "f \<sqsubseteq> g"
  then have "f\<cdot>x \<sqsubseteq> g\<cdot>x" by (rule monofun_cfun_fun)
  then have "f\<cdot>(f\<cdot>x) \<sqsubseteq> f\<cdot>(g\<cdot>x)" by (rule monofun_cfun_arg)
  also have "f\<cdot>(f\<cdot>x) = f\<cdot>x" by (rule f.idem)
  finally show "f\<cdot>x \<sqsubseteq> f\<cdot>(g\<cdot>x)" .
qed

lemma deflation_below_comp2: "deflation f \<Longrightarrow> deflation g \<Longrightarrow> f \<sqsubseteq> g \<Longrightarrow> g\<cdot>(f\<cdot>x) = f\<cdot>x"
  by (simp only: deflation.belowD deflation.idem)


subsection \<open>Deflations with finite range\<close>

lemma finite_range_imp_finite_fixes:
  assumes "finite (range f)"
  shows "finite {x. f x = x}"
proof -
  have "{x. f x = x} \<subseteq> range f"
    by (clarify, erule subst, rule rangeI)
  from this assms show "finite {x. f x = x}"
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
    from Y show "chain (\<lambda>i. d\<cdot>(Y i))" by simp
    have "range (\<lambda>i. d\<cdot>(Y i)) \<subseteq> range (\<lambda>x. d\<cdot>x)" by auto
    then show "finite (range (\<lambda>i. d\<cdot>(Y i)))"
      using finite_range by (rule finite_subset)
  qed
  then have "\<exists>j. (\<Squnion>i. d\<cdot>(Y i)) = d\<cdot>(Y j)"
    by (simp add: finite_chain_def maxinch_is_thelub Y)
  then obtain j where j: "(\<Squnion>i. d\<cdot>(Y i)) = d\<cdot>(Y j)" ..

  assume "d\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)"
  then have "d\<cdot>(d\<cdot>x) \<sqsubseteq> d\<cdot>(\<Squnion>i. Y i)"
    by (rule monofun_cfun_arg)
  then have "d\<cdot>x \<sqsubseteq> (\<Squnion>i. d\<cdot>(Y i))"
    by (simp add: contlub_cfun_arg Y idem)
  with j have "d\<cdot>x \<sqsubseteq> d\<cdot>(Y j)" by simp
  then have "d\<cdot>x \<sqsubseteq> Y j"
    using below by (rule below_trans)
  then show "\<exists>j. d\<cdot>x \<sqsubseteq> Y j" ..
qed

end

lemma finite_deflation_intro: "deflation d \<Longrightarrow> finite {x. d\<cdot>x = x} \<Longrightarrow> finite_deflation d"
  by (intro finite_deflation.intro finite_deflation_axioms.intro)

lemma finite_deflation_imp_deflation: "finite_deflation d \<Longrightarrow> deflation d"
  by (simp add: finite_deflation_def)

lemma finite_deflation_bottom: "finite_deflation \<bottom>"
  by standard simp_all


subsection \<open>Continuous embedding-projection pairs\<close>

locale ep_pair =
  fixes e :: "'a \<rightarrow> 'b" and p :: "'b \<rightarrow> 'a"
  assumes e_inverse [simp]: "\<And>x. p\<cdot>(e\<cdot>x) = x"
  and e_p_below: "\<And>y. e\<cdot>(p\<cdot>y) \<sqsubseteq> y"
begin

lemma e_below_iff [simp]: "e\<cdot>x \<sqsubseteq> e\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
proof
  assume "e\<cdot>x \<sqsubseteq> e\<cdot>y"
  then have "p\<cdot>(e\<cdot>x) \<sqsubseteq> p\<cdot>(e\<cdot>y)" by (rule monofun_cfun_arg)
  then show "x \<sqsubseteq> y" by simp
next
  assume "x \<sqsubseteq> y"
  then show "e\<cdot>x \<sqsubseteq> e\<cdot>y" by (rule monofun_cfun_arg)
qed

lemma e_eq_iff [simp]: "e\<cdot>x = e\<cdot>y \<longleftrightarrow> x = y"
  unfolding po_eq_conv e_below_iff ..

lemma p_eq_iff: "e\<cdot>(p\<cdot>x) = x \<Longrightarrow> e\<cdot>(p\<cdot>y) = y \<Longrightarrow> p\<cdot>x = p\<cdot>y \<longleftrightarrow> x = y"
  by (safe, erule subst, erule subst, simp)

lemma p_inverse: "(\<exists>x. y = e\<cdot>x) \<longleftrightarrow> e\<cdot>(p\<cdot>y) = y"
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
  then have "adm (\<lambda>y. e\<cdot>x \<notsqsubseteq> y)" by (rule compactD)
  then have "adm (\<lambda>y. e\<cdot>x \<notsqsubseteq> e\<cdot>y)" by (rule adm_subst [OF cont_Rep_cfun2])
  then have "adm (\<lambda>y. x \<notsqsubseteq> y)" by simp
  then show "compact x" by (rule compactI)
qed

lemma compact_e:
  assumes "compact x"
  shows "compact (e\<cdot>x)"
proof -
  from assms have "adm (\<lambda>y. x \<notsqsubseteq> y)" by (rule compactD)
  then have "adm (\<lambda>y. x \<notsqsubseteq> p\<cdot>y)" by (rule adm_subst [OF cont_Rep_cfun2])
  then have "adm (\<lambda>y. e\<cdot>x \<notsqsubseteq> y)" by (simp add: e_below_iff_below_p)
  then show "compact (e\<cdot>x)" by (rule compactI)
qed

lemma compact_e_iff: "compact (e\<cdot>x) \<longleftrightarrow> compact x"
  by (rule iffI [OF compact_e_rev compact_e])

text \<open>Deflations from ep-pairs\<close>

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
  then have "finite (range (\<lambda>x. (e oo d oo p)\<cdot>x))"
    by (simp add: image_image)
  then show "finite {x. (e oo d oo p)\<cdot>x = x}"
    by (rule finite_range_imp_finite_fixes)
qed

lemma deflation_p_d_e:
  assumes "deflation d"
  assumes d: "\<And>x. d\<cdot>x \<sqsubseteq> e\<cdot>(p\<cdot>x)"
  shows "deflation (p oo d oo e)"
proof -
  interpret d: deflation d by fact
  have p_d_e_below: "(p oo d oo e)\<cdot>x \<sqsubseteq> x" for x
  proof -
    have "d\<cdot>(e\<cdot>x) \<sqsubseteq> e\<cdot>x"
      by (rule d.below)
    then have "p\<cdot>(d\<cdot>(e\<cdot>x)) \<sqsubseteq> p\<cdot>(e\<cdot>x)"
      by (rule monofun_cfun_arg)
    then show ?thesis by simp
  qed
  show ?thesis
  proof
    show "(p oo d oo e)\<cdot>x \<sqsubseteq> x" for x
      by (rule p_d_e_below)
    show "(p oo d oo e)\<cdot>((p oo d oo e)\<cdot>x) = (p oo d oo e)\<cdot>x" for x
    proof (rule below_antisym)
      show "(p oo d oo e)\<cdot>((p oo d oo e)\<cdot>x) \<sqsubseteq> (p oo d oo e)\<cdot>x"
        by (rule p_d_e_below)
      have "p\<cdot>(d\<cdot>(d\<cdot>(d\<cdot>(e\<cdot>x)))) \<sqsubseteq> p\<cdot>(d\<cdot>(e\<cdot>(p\<cdot>(d\<cdot>(e\<cdot>x)))))"
        by (intro monofun_cfun_arg d)
      then have "p\<cdot>(d\<cdot>(e\<cdot>x)) \<sqsubseteq> p\<cdot>(d\<cdot>(e\<cdot>(p\<cdot>(d\<cdot>(e\<cdot>x)))))"
        by (simp only: d.idem)
      then show "(p oo d oo e)\<cdot>x \<sqsubseteq> (p oo d oo e)\<cdot>((p oo d oo e)\<cdot>x)"
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
    then show "deflation (p oo d oo e)"
      using d by (rule deflation_p_d_e)
  next
    have "finite ((\<lambda>x. d\<cdot>x) ` range (\<lambda>x. e\<cdot>x))"
      by (rule d.finite_image)
    then have "finite ((\<lambda>x. p\<cdot>x) ` (\<lambda>x. d\<cdot>x) ` range (\<lambda>x. e\<cdot>x))"
      by (rule finite_imageI)
    then have "finite (range (\<lambda>x. (p oo d oo e)\<cdot>x))"
      by (simp add: image_image)
    then show "finite {x. (p oo d oo e)\<cdot>x = x}"
      by (rule finite_range_imp_finite_fixes)
  qed
qed

end


subsection \<open>Uniqueness of ep-pairs\<close>

lemma ep_pair_unique_e_lemma:
  assumes 1: "ep_pair e1 p"
    and 2: "ep_pair e2 p"
  shows "e1 \<sqsubseteq> e2"
proof (rule cfun_belowI)
  fix x
  have "e1\<cdot>(p\<cdot>(e2\<cdot>x)) \<sqsubseteq> e2\<cdot>x"
    by (rule ep_pair.e_p_below [OF 1])
  then show "e1\<cdot>x \<sqsubseteq> e2\<cdot>x"
    by (simp only: ep_pair.e_inverse [OF 2])
qed

lemma ep_pair_unique_e: "ep_pair e1 p \<Longrightarrow> ep_pair e2 p \<Longrightarrow> e1 = e2"
  by (fast intro: below_antisym elim: ep_pair_unique_e_lemma)

lemma ep_pair_unique_p_lemma:
  assumes 1: "ep_pair e p1"
    and 2: "ep_pair e p2"
  shows "p1 \<sqsubseteq> p2"
proof (rule cfun_belowI)
  fix x
  have "e\<cdot>(p1\<cdot>x) \<sqsubseteq> x"
    by (rule ep_pair.e_p_below [OF 1])
  then have "p2\<cdot>(e\<cdot>(p1\<cdot>x)) \<sqsubseteq> p2\<cdot>x"
    by (rule monofun_cfun_arg)
  then show "p1\<cdot>x \<sqsubseteq> p2\<cdot>x"
    by (simp only: ep_pair.e_inverse [OF 2])
qed

lemma ep_pair_unique_p: "ep_pair e p1 \<Longrightarrow> ep_pair e p2 \<Longrightarrow> p1 = p2"
  by (fast intro: below_antisym elim: ep_pair_unique_p_lemma)


subsection \<open>Composing ep-pairs\<close>

lemma ep_pair_ID_ID: "ep_pair ID ID"
  by standard simp_all

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
  then have "e2\<cdot>(e1\<cdot>(p1\<cdot>(p2\<cdot>y))) \<sqsubseteq> e2\<cdot>(p2\<cdot>y)"
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
  then have "e\<cdot>\<bottom> \<sqsubseteq> e\<cdot>(p\<cdot>\<bottom>)" by (rule monofun_cfun_arg)
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
