(*  Title:      HOLCF/Bifinite.thy
    Author:     Brian Huffman
*)

header {* Bifinite domains and approximation *}

theory Bifinite
imports Deflation
begin

subsection {* Omega-profinite and bifinite domains *}

class profinite =
  fixes approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assumes chain_approx [simp]: "chain approx"
  assumes lub_approx_app [simp]: "(\<Squnion>i. approx i\<cdot>x) = x"
  assumes approx_idem: "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
  assumes finite_fixes_approx: "finite {x. approx i\<cdot>x = x}"

class bifinite = profinite + pcpo

lemma approx_below: "approx i\<cdot>x \<sqsubseteq> x"
proof -
  have "chain (\<lambda>i. approx i\<cdot>x)" by simp
  hence "approx i\<cdot>x \<sqsubseteq> (\<Squnion>i. approx i\<cdot>x)" by (rule is_ub_thelub)
  thus "approx i\<cdot>x \<sqsubseteq> x" by simp
qed

lemma finite_deflation_approx: "finite_deflation (approx i)"
proof
  fix x :: 'a
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    by (rule approx_idem)
  show "approx i\<cdot>x \<sqsubseteq> x"
    by (rule approx_below)
  show "finite {x. approx i\<cdot>x = x}"
    by (rule finite_fixes_approx)
qed

interpretation approx: finite_deflation "approx i"
by (rule finite_deflation_approx)

lemma (in deflation) deflation: "deflation d" ..

lemma deflation_approx: "deflation (approx i)"
by (rule approx.deflation)

lemma lub_approx [simp]: "(\<Squnion>i. approx i) = (\<Lambda> x. x)"
by (rule ext_cfun, simp add: contlub_cfun_fun)

lemma approx_strict [simp]: "approx i\<cdot>\<bottom> = \<bottom>"
by (rule UU_I, rule approx_below)

lemma approx_approx1:
  "i \<le> j \<Longrightarrow> approx i\<cdot>(approx j\<cdot>x) = approx i\<cdot>x"
apply (rule deflation_below_comp1 [OF deflation_approx deflation_approx])
apply (erule chain_mono [OF chain_approx])
done

lemma approx_approx2:
  "j \<le> i \<Longrightarrow> approx i\<cdot>(approx j\<cdot>x) = approx j\<cdot>x"
apply (rule deflation_below_comp2 [OF deflation_approx deflation_approx])
apply (erule chain_mono [OF chain_approx])
done

lemma approx_approx [simp]:
  "approx i\<cdot>(approx j\<cdot>x) = approx (min i j)\<cdot>x"
apply (rule_tac x=i and y=j in linorder_le_cases)
apply (simp add: approx_approx1 min_def)
apply (simp add: approx_approx2 min_def)
done

lemma finite_image_approx: "finite ((\<lambda>x. approx n\<cdot>x) ` A)"
by (rule approx.finite_image)

lemma finite_range_approx: "finite (range (\<lambda>x. approx i\<cdot>x))"
by (rule approx.finite_range)

lemma compact_approx [simp]: "compact (approx n\<cdot>x)"
by (rule approx.compact)

lemma profinite_compact_eq_approx: "compact x \<Longrightarrow> \<exists>i. approx i\<cdot>x = x"
by (rule admD2, simp_all)

lemma profinite_compact_iff: "compact x \<longleftrightarrow> (\<exists>n. approx n\<cdot>x = x)"
 apply (rule iffI)
  apply (erule profinite_compact_eq_approx)
 apply (erule exE)
 apply (erule subst)
 apply (rule compact_approx)
done

lemma approx_induct:
  assumes adm: "adm P" and P: "\<And>n x. P (approx n\<cdot>x)"
  shows "P x"
proof -
  have "P (\<Squnion>n. approx n\<cdot>x)"
    by (rule admD [OF adm], simp, simp add: P)
  thus "P x" by simp
qed

lemma profinite_below_ext: "(\<And>i. approx i\<cdot>x \<sqsubseteq> approx i\<cdot>y) \<Longrightarrow> x \<sqsubseteq> y"
apply (subgoal_tac "(\<Squnion>i. approx i\<cdot>x) \<sqsubseteq> (\<Squnion>i. approx i\<cdot>y)", simp)
apply (rule lub_mono, simp, simp, simp)
done

subsection {* Instance for product type *}

definition
  cprod_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<times> 'c \<rightarrow> 'b \<times> 'd"
where
  "cprod_map = (\<Lambda> f g p. (f\<cdot>(fst p), g\<cdot>(snd p)))"

lemma cprod_map_Pair [simp]: "cprod_map\<cdot>f\<cdot>g\<cdot>(x, y) = (f\<cdot>x, g\<cdot>y)"
unfolding cprod_map_def by simp

lemma cprod_map_map:
  "cprod_map\<cdot>f1\<cdot>g1\<cdot>(cprod_map\<cdot>f2\<cdot>g2\<cdot>p) =
    cprod_map\<cdot>(\<Lambda> x. f1\<cdot>(f2\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
by (induct p) simp

lemma ep_pair_cprod_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (cprod_map\<cdot>e1\<cdot>e2) (cprod_map\<cdot>p1\<cdot>p2)"
proof
  interpret e1p1: ep_pair e1 p1 by fact
  interpret e2p2: ep_pair e2 p2 by fact
  fix x show "cprod_map\<cdot>p1\<cdot>p2\<cdot>(cprod_map\<cdot>e1\<cdot>e2\<cdot>x) = x"
    by (induct x) simp
  fix y show "cprod_map\<cdot>e1\<cdot>e2\<cdot>(cprod_map\<cdot>p1\<cdot>p2\<cdot>y) \<sqsubseteq> y"
    by (induct y) (simp add: e1p1.e_p_below e2p2.e_p_below)
qed

lemma deflation_cprod_map:
  assumes "deflation d1" and "deflation d2"
  shows "deflation (cprod_map\<cdot>d1\<cdot>d2)"
proof
  interpret d1: deflation d1 by fact
  interpret d2: deflation d2 by fact
  fix x
  show "cprod_map\<cdot>d1\<cdot>d2\<cdot>(cprod_map\<cdot>d1\<cdot>d2\<cdot>x) = cprod_map\<cdot>d1\<cdot>d2\<cdot>x"
    by (induct x) (simp add: d1.idem d2.idem)
  show "cprod_map\<cdot>d1\<cdot>d2\<cdot>x \<sqsubseteq> x"
    by (induct x) (simp add: d1.below d2.below)
qed

lemma finite_deflation_cprod_map:
  assumes "finite_deflation d1" and "finite_deflation d2"
  shows "finite_deflation (cprod_map\<cdot>d1\<cdot>d2)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (cprod_map\<cdot>d1\<cdot>d2)" by (rule deflation_cprod_map)
  have "{p. cprod_map\<cdot>d1\<cdot>d2\<cdot>p = p} \<subseteq> {x. d1\<cdot>x = x} \<times> {y. d2\<cdot>y = y}"
    by clarsimp
  thus "finite {p. cprod_map\<cdot>d1\<cdot>d2\<cdot>p = p}"
    by (rule finite_subset, simp add: d1.finite_fixes d2.finite_fixes)
qed

instantiation "*" :: (profinite, profinite) profinite
begin

definition
  approx_prod_def:
    "approx = (\<lambda>n. cprod_map\<cdot>(approx n)\<cdot>(approx n))"

instance proof
  fix i :: nat and x :: "'a \<times> 'b"
  show "chain (approx :: nat \<Rightarrow> 'a \<times> 'b \<rightarrow> 'a \<times> 'b)"
    unfolding approx_prod_def by simp
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx_prod_def cprod_map_def
    by (simp add: lub_distribs thelub_Pair)
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    unfolding approx_prod_def cprod_map_def by simp
  have "{x::'a \<times> 'b. approx i\<cdot>x = x} \<subseteq>
        {x::'a. approx i\<cdot>x = x} \<times> {x::'b. approx i\<cdot>x = x}"
    unfolding approx_prod_def by clarsimp
  thus "finite {x::'a \<times> 'b. approx i\<cdot>x = x}"
    by (rule finite_subset,
        intro finite_cartesian_product finite_fixes_approx)
qed

end

instance "*" :: (bifinite, bifinite) bifinite ..

lemma approx_Pair [simp]:
  "approx i\<cdot>(x, y) = (approx i\<cdot>x, approx i\<cdot>y)"
unfolding approx_prod_def by simp

lemma fst_approx: "fst (approx i\<cdot>p) = approx i\<cdot>(fst p)"
by (induct p, simp)

lemma snd_approx: "snd (approx i\<cdot>p) = approx i\<cdot>(snd p)"
by (induct p, simp)


subsection {* Instance for continuous function space *}

definition
  cfun_map :: "('b \<rightarrow> 'a) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'd)"
where
  "cfun_map = (\<Lambda> a b f x. b\<cdot>(f\<cdot>(a\<cdot>x)))"

lemma cfun_map_beta [simp]: "cfun_map\<cdot>a\<cdot>b\<cdot>f\<cdot>x = b\<cdot>(f\<cdot>(a\<cdot>x))"
unfolding cfun_map_def by simp

lemma cfun_map_map:
  "cfun_map\<cdot>f1\<cdot>g1\<cdot>(cfun_map\<cdot>f2\<cdot>g2\<cdot>p) =
    cfun_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
by (rule ext_cfun) simp

lemma ep_pair_cfun_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (cfun_map\<cdot>p1\<cdot>e2) (cfun_map\<cdot>e1\<cdot>p2)"
proof
  interpret e1p1: ep_pair e1 p1 by fact
  interpret e2p2: ep_pair e2 p2 by fact
  fix f show "cfun_map\<cdot>e1\<cdot>p2\<cdot>(cfun_map\<cdot>p1\<cdot>e2\<cdot>f) = f"
    by (simp add: expand_cfun_eq)
  fix g show "cfun_map\<cdot>p1\<cdot>e2\<cdot>(cfun_map\<cdot>e1\<cdot>p2\<cdot>g) \<sqsubseteq> g"
    apply (rule below_cfun_ext, simp)
    apply (rule below_trans [OF e2p2.e_p_below])
    apply (rule monofun_cfun_arg)
    apply (rule e1p1.e_p_below)
    done
qed

lemma deflation_cfun_map:
  assumes "deflation d1" and "deflation d2"
  shows "deflation (cfun_map\<cdot>d1\<cdot>d2)"
proof
  interpret d1: deflation d1 by fact
  interpret d2: deflation d2 by fact
  fix f
  show "cfun_map\<cdot>d1\<cdot>d2\<cdot>(cfun_map\<cdot>d1\<cdot>d2\<cdot>f) = cfun_map\<cdot>d1\<cdot>d2\<cdot>f"
    by (simp add: expand_cfun_eq d1.idem d2.idem)
  show "cfun_map\<cdot>d1\<cdot>d2\<cdot>f \<sqsubseteq> f"
    apply (rule below_cfun_ext, simp)
    apply (rule below_trans [OF d2.below])
    apply (rule monofun_cfun_arg)
    apply (rule d1.below)
    done
qed

lemma finite_range_cfun_map:
  assumes a: "finite (range (\<lambda>x. a\<cdot>x))"
  assumes b: "finite (range (\<lambda>y. b\<cdot>y))"
  shows "finite (range (\<lambda>f. cfun_map\<cdot>a\<cdot>b\<cdot>f))"  (is "finite (range ?h)")
proof (rule finite_imageD)
  let ?f = "\<lambda>g. range (\<lambda>x. (a\<cdot>x, g\<cdot>x))"
  show "finite (?f ` range ?h)"
  proof (rule finite_subset)
    let ?B = "Pow (range (\<lambda>x. a\<cdot>x) \<times> range (\<lambda>y. b\<cdot>y))"
    show "?f ` range ?h \<subseteq> ?B"
      by clarsimp
    show "finite ?B"
      by (simp add: a b)
  qed
  show "inj_on ?f (range ?h)"
  proof (rule inj_onI, rule ext_cfun, clarsimp)
    fix x f g
    assume "range (\<lambda>x. (a\<cdot>x, b\<cdot>(f\<cdot>(a\<cdot>x)))) = range (\<lambda>x. (a\<cdot>x, b\<cdot>(g\<cdot>(a\<cdot>x))))"
    hence "range (\<lambda>x. (a\<cdot>x, b\<cdot>(f\<cdot>(a\<cdot>x)))) \<subseteq> range (\<lambda>x. (a\<cdot>x, b\<cdot>(g\<cdot>(a\<cdot>x))))"
      by (rule equalityD1)
    hence "(a\<cdot>x, b\<cdot>(f\<cdot>(a\<cdot>x))) \<in> range (\<lambda>x. (a\<cdot>x, b\<cdot>(g\<cdot>(a\<cdot>x))))"
      by (simp add: subset_eq)
    then obtain y where "(a\<cdot>x, b\<cdot>(f\<cdot>(a\<cdot>x))) = (a\<cdot>y, b\<cdot>(g\<cdot>(a\<cdot>y)))"
      by (rule rangeE)
    thus "b\<cdot>(f\<cdot>(a\<cdot>x)) = b\<cdot>(g\<cdot>(a\<cdot>x))"
      by clarsimp
  qed
qed

lemma finite_deflation_cfun_map:
  assumes "finite_deflation d1" and "finite_deflation d2"
  shows "finite_deflation (cfun_map\<cdot>d1\<cdot>d2)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (cfun_map\<cdot>d1\<cdot>d2)" by (rule deflation_cfun_map)
  have "finite (range (\<lambda>f. cfun_map\<cdot>d1\<cdot>d2\<cdot>f))"
    using d1.finite_range d2.finite_range
    by (rule finite_range_cfun_map)
  thus "finite {f. cfun_map\<cdot>d1\<cdot>d2\<cdot>f = f}"
    by (rule finite_range_imp_finite_fixes)
qed

instantiation "->" :: (profinite, profinite) profinite
begin

definition
  approx_cfun_def:
    "approx = (\<lambda>n. cfun_map\<cdot>(approx n)\<cdot>(approx n))"

instance proof
  show "chain (approx :: nat \<Rightarrow> ('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow> 'b))"
    unfolding approx_cfun_def by simp
next
  fix x :: "'a \<rightarrow> 'b"
  show "(\<Squnion>i. approx i\<cdot>x) = x"
    unfolding approx_cfun_def cfun_map_def
    by (simp add: lub_distribs eta_cfun)
next
  fix i :: nat and x :: "'a \<rightarrow> 'b"
  show "approx i\<cdot>(approx i\<cdot>x) = approx i\<cdot>x"
    unfolding approx_cfun_def cfun_map_def by simp
next
  fix i :: nat
  show "finite {x::'a \<rightarrow> 'b. approx i\<cdot>x = x}"
    unfolding approx_cfun_def
    by (intro finite_deflation.finite_fixes
              finite_deflation_cfun_map
              finite_deflation_approx)
qed

end

instance "->" :: (profinite, bifinite) bifinite ..

lemma approx_cfun: "approx n\<cdot>f\<cdot>x = approx n\<cdot>(f\<cdot>(approx n\<cdot>x))"
by (simp add: approx_cfun_def)

end
