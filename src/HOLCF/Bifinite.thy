(*  Title:      HOLCF/Bifinite.thy
    Author:     Brian Huffman
*)

header {* Bifinite domains and approximation *}

theory Bifinite
imports Deflation
begin

subsection {* Map operator for product type *}

definition
  cprod_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<times> 'c \<rightarrow> 'b \<times> 'd"
where
  "cprod_map = (\<Lambda> f g p. (f\<cdot>(fst p), g\<cdot>(snd p)))"

lemma cprod_map_Pair [simp]: "cprod_map\<cdot>f\<cdot>g\<cdot>(x, y) = (f\<cdot>x, g\<cdot>y)"
unfolding cprod_map_def by simp

lemma cprod_map_ID: "cprod_map\<cdot>ID\<cdot>ID = ID"
unfolding expand_cfun_eq by auto

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
proof (rule finite_deflation_intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (cprod_map\<cdot>d1\<cdot>d2)" by (rule deflation_cprod_map)
  have "{p. cprod_map\<cdot>d1\<cdot>d2\<cdot>p = p} \<subseteq> {x. d1\<cdot>x = x} \<times> {y. d2\<cdot>y = y}"
    by clarsimp
  thus "finite {p. cprod_map\<cdot>d1\<cdot>d2\<cdot>p = p}"
    by (rule finite_subset, simp add: d1.finite_fixes d2.finite_fixes)
qed

subsection {* Map operator for continuous function space *}

definition
  cfun_map :: "('b \<rightarrow> 'a) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'd)"
where
  "cfun_map = (\<Lambda> a b f x. b\<cdot>(f\<cdot>(a\<cdot>x)))"

lemma cfun_map_beta [simp]: "cfun_map\<cdot>a\<cdot>b\<cdot>f\<cdot>x = b\<cdot>(f\<cdot>(a\<cdot>x))"
unfolding cfun_map_def by simp

lemma cfun_map_ID: "cfun_map\<cdot>ID\<cdot>ID = ID"
unfolding expand_cfun_eq by simp

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
proof (rule finite_deflation_intro)
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

text {* Finite deflations are compact elements of the function space *}

lemma finite_deflation_imp_compact: "finite_deflation d \<Longrightarrow> compact d"
apply (frule finite_deflation_imp_deflation)
apply (subgoal_tac "compact (cfun_map\<cdot>d\<cdot>d\<cdot>d)")
apply (simp add: cfun_map_def deflation.idem eta_cfun)
apply (rule finite_deflation.compact)
apply (simp only: finite_deflation_cfun_map)
done

end
