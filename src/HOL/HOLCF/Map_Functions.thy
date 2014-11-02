(*  Title:      HOL/HOLCF/Map_Functions.thy
    Author:     Brian Huffman
*)

section {* Map functions for various types *}

theory Map_Functions
imports Deflation
begin

subsection {* Map operator for continuous function space *}

default_sort cpo

definition
  cfun_map :: "('b \<rightarrow> 'a) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow> 'c) \<rightarrow> ('b \<rightarrow> 'd)"
where
  "cfun_map = (\<Lambda> a b f x. b\<cdot>(f\<cdot>(a\<cdot>x)))"

lemma cfun_map_beta [simp]: "cfun_map\<cdot>a\<cdot>b\<cdot>f\<cdot>x = b\<cdot>(f\<cdot>(a\<cdot>x))"
unfolding cfun_map_def by simp

lemma cfun_map_ID: "cfun_map\<cdot>ID\<cdot>ID = ID"
unfolding cfun_eq_iff by simp

lemma cfun_map_map:
  "cfun_map\<cdot>f1\<cdot>g1\<cdot>(cfun_map\<cdot>f2\<cdot>g2\<cdot>p) =
    cfun_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
by (rule cfun_eqI) simp

lemma ep_pair_cfun_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (cfun_map\<cdot>p1\<cdot>e2) (cfun_map\<cdot>e1\<cdot>p2)"
proof
  interpret e1p1: ep_pair e1 p1 by fact
  interpret e2p2: ep_pair e2 p2 by fact
  fix f show "cfun_map\<cdot>e1\<cdot>p2\<cdot>(cfun_map\<cdot>p1\<cdot>e2\<cdot>f) = f"
    by (simp add: cfun_eq_iff)
  fix g show "cfun_map\<cdot>p1\<cdot>e2\<cdot>(cfun_map\<cdot>e1\<cdot>p2\<cdot>g) \<sqsubseteq> g"
    apply (rule cfun_belowI, simp)
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
    by (simp add: cfun_eq_iff d1.idem d2.idem)
  show "cfun_map\<cdot>d1\<cdot>d2\<cdot>f \<sqsubseteq> f"
    apply (rule cfun_belowI, simp)
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
  proof (rule inj_onI, rule cfun_eqI, clarsimp)
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

subsection {* Map operator for product type *}

definition
  prod_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<times> 'c \<rightarrow> 'b \<times> 'd"
where
  "prod_map = (\<Lambda> f g p. (f\<cdot>(fst p), g\<cdot>(snd p)))"

lemma prod_map_Pair [simp]: "prod_map\<cdot>f\<cdot>g\<cdot>(x, y) = (f\<cdot>x, g\<cdot>y)"
unfolding prod_map_def by simp

lemma prod_map_ID: "prod_map\<cdot>ID\<cdot>ID = ID"
unfolding cfun_eq_iff by auto

lemma prod_map_map:
  "prod_map\<cdot>f1\<cdot>g1\<cdot>(prod_map\<cdot>f2\<cdot>g2\<cdot>p) =
    prod_map\<cdot>(\<Lambda> x. f1\<cdot>(f2\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
by (induct p) simp

lemma ep_pair_prod_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (prod_map\<cdot>e1\<cdot>e2) (prod_map\<cdot>p1\<cdot>p2)"
proof
  interpret e1p1: ep_pair e1 p1 by fact
  interpret e2p2: ep_pair e2 p2 by fact
  fix x show "prod_map\<cdot>p1\<cdot>p2\<cdot>(prod_map\<cdot>e1\<cdot>e2\<cdot>x) = x"
    by (induct x) simp
  fix y show "prod_map\<cdot>e1\<cdot>e2\<cdot>(prod_map\<cdot>p1\<cdot>p2\<cdot>y) \<sqsubseteq> y"
    by (induct y) (simp add: e1p1.e_p_below e2p2.e_p_below)
qed

lemma deflation_prod_map:
  assumes "deflation d1" and "deflation d2"
  shows "deflation (prod_map\<cdot>d1\<cdot>d2)"
proof
  interpret d1: deflation d1 by fact
  interpret d2: deflation d2 by fact
  fix x
  show "prod_map\<cdot>d1\<cdot>d2\<cdot>(prod_map\<cdot>d1\<cdot>d2\<cdot>x) = prod_map\<cdot>d1\<cdot>d2\<cdot>x"
    by (induct x) (simp add: d1.idem d2.idem)
  show "prod_map\<cdot>d1\<cdot>d2\<cdot>x \<sqsubseteq> x"
    by (induct x) (simp add: d1.below d2.below)
qed

lemma finite_deflation_prod_map:
  assumes "finite_deflation d1" and "finite_deflation d2"
  shows "finite_deflation (prod_map\<cdot>d1\<cdot>d2)"
proof (rule finite_deflation_intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (prod_map\<cdot>d1\<cdot>d2)" by (rule deflation_prod_map)
  have "{p. prod_map\<cdot>d1\<cdot>d2\<cdot>p = p} \<subseteq> {x. d1\<cdot>x = x} \<times> {y. d2\<cdot>y = y}"
    by clarsimp
  thus "finite {p. prod_map\<cdot>d1\<cdot>d2\<cdot>p = p}"
    by (rule finite_subset, simp add: d1.finite_fixes d2.finite_fixes)
qed

subsection {* Map function for lifted cpo *}

definition
  u_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a u \<rightarrow> 'b u"
where
  "u_map = (\<Lambda> f. fup\<cdot>(up oo f))"

lemma u_map_strict [simp]: "u_map\<cdot>f\<cdot>\<bottom> = \<bottom>"
unfolding u_map_def by simp

lemma u_map_up [simp]: "u_map\<cdot>f\<cdot>(up\<cdot>x) = up\<cdot>(f\<cdot>x)"
unfolding u_map_def by simp

lemma u_map_ID: "u_map\<cdot>ID = ID"
unfolding u_map_def by (simp add: cfun_eq_iff eta_cfun)

lemma u_map_map: "u_map\<cdot>f\<cdot>(u_map\<cdot>g\<cdot>p) = u_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>p"
by (induct p) simp_all

lemma u_map_oo: "u_map\<cdot>(f oo g) = u_map\<cdot>f oo u_map\<cdot>g"
by (simp add: cfcomp1 u_map_map eta_cfun)

lemma ep_pair_u_map: "ep_pair e p \<Longrightarrow> ep_pair (u_map\<cdot>e) (u_map\<cdot>p)"
apply default
apply (case_tac x, simp, simp add: ep_pair.e_inverse)
apply (case_tac y, simp, simp add: ep_pair.e_p_below)
done

lemma deflation_u_map: "deflation d \<Longrightarrow> deflation (u_map\<cdot>d)"
apply default
apply (case_tac x, simp, simp add: deflation.idem)
apply (case_tac x, simp, simp add: deflation.below)
done

lemma finite_deflation_u_map:
  assumes "finite_deflation d" shows "finite_deflation (u_map\<cdot>d)"
proof (rule finite_deflation_intro)
  interpret d: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (u_map\<cdot>d)" by (rule deflation_u_map)
  have "{x. u_map\<cdot>d\<cdot>x = x} \<subseteq> insert \<bottom> ((\<lambda>x. up\<cdot>x) ` {x. d\<cdot>x = x})"
    by (rule subsetI, case_tac x, simp_all)
  thus "finite {x. u_map\<cdot>d\<cdot>x = x}"
    by (rule finite_subset, simp add: d.finite_fixes)
qed

subsection {* Map function for strict products *}

default_sort pcpo

definition
  sprod_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<otimes> 'c \<rightarrow> 'b \<otimes> 'd"
where
  "sprod_map = (\<Lambda> f g. ssplit\<cdot>(\<Lambda> x y. (:f\<cdot>x, g\<cdot>y:)))"

lemma sprod_map_strict [simp]: "sprod_map\<cdot>a\<cdot>b\<cdot>\<bottom> = \<bottom>"
unfolding sprod_map_def by simp

lemma sprod_map_spair [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> sprod_map\<cdot>f\<cdot>g\<cdot>(:x, y:) = (:f\<cdot>x, g\<cdot>y:)"
by (simp add: sprod_map_def)

lemma sprod_map_spair':
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> g\<cdot>\<bottom> = \<bottom> \<Longrightarrow> sprod_map\<cdot>f\<cdot>g\<cdot>(:x, y:) = (:f\<cdot>x, g\<cdot>y:)"
by (cases "x = \<bottom> \<or> y = \<bottom>") auto

lemma sprod_map_ID: "sprod_map\<cdot>ID\<cdot>ID = ID"
unfolding sprod_map_def by (simp add: cfun_eq_iff eta_cfun)

lemma sprod_map_map:
  "\<lbrakk>f1\<cdot>\<bottom> = \<bottom>; g1\<cdot>\<bottom> = \<bottom>\<rbrakk> \<Longrightarrow>
    sprod_map\<cdot>f1\<cdot>g1\<cdot>(sprod_map\<cdot>f2\<cdot>g2\<cdot>p) =
     sprod_map\<cdot>(\<Lambda> x. f1\<cdot>(f2\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
apply (induct p, simp)
apply (case_tac "f2\<cdot>x = \<bottom>", simp)
apply (case_tac "g2\<cdot>y = \<bottom>", simp)
apply simp
done

lemma ep_pair_sprod_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (sprod_map\<cdot>e1\<cdot>e2) (sprod_map\<cdot>p1\<cdot>p2)"
proof
  interpret e1p1: pcpo_ep_pair e1 p1 unfolding pcpo_ep_pair_def by fact
  interpret e2p2: pcpo_ep_pair e2 p2 unfolding pcpo_ep_pair_def by fact
  fix x show "sprod_map\<cdot>p1\<cdot>p2\<cdot>(sprod_map\<cdot>e1\<cdot>e2\<cdot>x) = x"
    by (induct x) simp_all
  fix y show "sprod_map\<cdot>e1\<cdot>e2\<cdot>(sprod_map\<cdot>p1\<cdot>p2\<cdot>y) \<sqsubseteq> y"
    apply (induct y, simp)
    apply (case_tac "p1\<cdot>x = \<bottom>", simp, case_tac "p2\<cdot>y = \<bottom>", simp)
    apply (simp add: monofun_cfun e1p1.e_p_below e2p2.e_p_below)
    done
qed

lemma deflation_sprod_map:
  assumes "deflation d1" and "deflation d2"
  shows "deflation (sprod_map\<cdot>d1\<cdot>d2)"
proof
  interpret d1: deflation d1 by fact
  interpret d2: deflation d2 by fact
  fix x
  show "sprod_map\<cdot>d1\<cdot>d2\<cdot>(sprod_map\<cdot>d1\<cdot>d2\<cdot>x) = sprod_map\<cdot>d1\<cdot>d2\<cdot>x"
    apply (induct x, simp)
    apply (case_tac "d1\<cdot>x = \<bottom>", simp, case_tac "d2\<cdot>y = \<bottom>", simp)
    apply (simp add: d1.idem d2.idem)
    done
  show "sprod_map\<cdot>d1\<cdot>d2\<cdot>x \<sqsubseteq> x"
    apply (induct x, simp)
    apply (simp add: monofun_cfun d1.below d2.below)
    done
qed

lemma finite_deflation_sprod_map:
  assumes "finite_deflation d1" and "finite_deflation d2"
  shows "finite_deflation (sprod_map\<cdot>d1\<cdot>d2)"
proof (rule finite_deflation_intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (sprod_map\<cdot>d1\<cdot>d2)" by (rule deflation_sprod_map)
  have "{x. sprod_map\<cdot>d1\<cdot>d2\<cdot>x = x} \<subseteq> insert \<bottom>
        ((\<lambda>(x, y). (:x, y:)) ` ({x. d1\<cdot>x = x} \<times> {y. d2\<cdot>y = y}))"
    by (rule subsetI, case_tac x, auto simp add: spair_eq_iff)
  thus "finite {x. sprod_map\<cdot>d1\<cdot>d2\<cdot>x = x}"
    by (rule finite_subset, simp add: d1.finite_fixes d2.finite_fixes)
qed

subsection {* Map function for strict sums *}

definition
  ssum_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<oplus> 'c \<rightarrow> 'b \<oplus> 'd"
where
  "ssum_map = (\<Lambda> f g. sscase\<cdot>(sinl oo f)\<cdot>(sinr oo g))"

lemma ssum_map_strict [simp]: "ssum_map\<cdot>f\<cdot>g\<cdot>\<bottom> = \<bottom>"
unfolding ssum_map_def by simp

lemma ssum_map_sinl [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = sinl\<cdot>(f\<cdot>x)"
unfolding ssum_map_def by simp

lemma ssum_map_sinr [simp]: "x \<noteq> \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>x) = sinr\<cdot>(g\<cdot>x)"
unfolding ssum_map_def by simp

lemma ssum_map_sinl': "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinl\<cdot>x) = sinl\<cdot>(f\<cdot>x)"
by (cases "x = \<bottom>") simp_all

lemma ssum_map_sinr': "g\<cdot>\<bottom> = \<bottom> \<Longrightarrow> ssum_map\<cdot>f\<cdot>g\<cdot>(sinr\<cdot>x) = sinr\<cdot>(g\<cdot>x)"
by (cases "x = \<bottom>") simp_all

lemma ssum_map_ID: "ssum_map\<cdot>ID\<cdot>ID = ID"
unfolding ssum_map_def by (simp add: cfun_eq_iff eta_cfun)

lemma ssum_map_map:
  "\<lbrakk>f1\<cdot>\<bottom> = \<bottom>; g1\<cdot>\<bottom> = \<bottom>\<rbrakk> \<Longrightarrow>
    ssum_map\<cdot>f1\<cdot>g1\<cdot>(ssum_map\<cdot>f2\<cdot>g2\<cdot>p) =
     ssum_map\<cdot>(\<Lambda> x. f1\<cdot>(f2\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
apply (induct p, simp)
apply (case_tac "f2\<cdot>x = \<bottom>", simp, simp)
apply (case_tac "g2\<cdot>y = \<bottom>", simp, simp)
done

lemma ep_pair_ssum_map:
  assumes "ep_pair e1 p1" and "ep_pair e2 p2"
  shows "ep_pair (ssum_map\<cdot>e1\<cdot>e2) (ssum_map\<cdot>p1\<cdot>p2)"
proof
  interpret e1p1: pcpo_ep_pair e1 p1 unfolding pcpo_ep_pair_def by fact
  interpret e2p2: pcpo_ep_pair e2 p2 unfolding pcpo_ep_pair_def by fact
  fix x show "ssum_map\<cdot>p1\<cdot>p2\<cdot>(ssum_map\<cdot>e1\<cdot>e2\<cdot>x) = x"
    by (induct x) simp_all
  fix y show "ssum_map\<cdot>e1\<cdot>e2\<cdot>(ssum_map\<cdot>p1\<cdot>p2\<cdot>y) \<sqsubseteq> y"
    apply (induct y, simp)
    apply (case_tac "p1\<cdot>x = \<bottom>", simp, simp add: e1p1.e_p_below)
    apply (case_tac "p2\<cdot>y = \<bottom>", simp, simp add: e2p2.e_p_below)
    done
qed

lemma deflation_ssum_map:
  assumes "deflation d1" and "deflation d2"
  shows "deflation (ssum_map\<cdot>d1\<cdot>d2)"
proof
  interpret d1: deflation d1 by fact
  interpret d2: deflation d2 by fact
  fix x
  show "ssum_map\<cdot>d1\<cdot>d2\<cdot>(ssum_map\<cdot>d1\<cdot>d2\<cdot>x) = ssum_map\<cdot>d1\<cdot>d2\<cdot>x"
    apply (induct x, simp)
    apply (case_tac "d1\<cdot>x = \<bottom>", simp, simp add: d1.idem)
    apply (case_tac "d2\<cdot>y = \<bottom>", simp, simp add: d2.idem)
    done
  show "ssum_map\<cdot>d1\<cdot>d2\<cdot>x \<sqsubseteq> x"
    apply (induct x, simp)
    apply (case_tac "d1\<cdot>x = \<bottom>", simp, simp add: d1.below)
    apply (case_tac "d2\<cdot>y = \<bottom>", simp, simp add: d2.below)
    done
qed

lemma finite_deflation_ssum_map:
  assumes "finite_deflation d1" and "finite_deflation d2"
  shows "finite_deflation (ssum_map\<cdot>d1\<cdot>d2)"
proof (rule finite_deflation_intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (ssum_map\<cdot>d1\<cdot>d2)" by (rule deflation_ssum_map)
  have "{x. ssum_map\<cdot>d1\<cdot>d2\<cdot>x = x} \<subseteq>
        (\<lambda>x. sinl\<cdot>x) ` {x. d1\<cdot>x = x} \<union>
        (\<lambda>x. sinr\<cdot>x) ` {x. d2\<cdot>x = x} \<union> {\<bottom>}"
    by (rule subsetI, case_tac x, simp_all)
  thus "finite {x. ssum_map\<cdot>d1\<cdot>d2\<cdot>x = x}"
    by (rule finite_subset, simp add: d1.finite_fixes d2.finite_fixes)
qed

subsection {* Map operator for strict function space *}

definition
  sfun_map :: "('b \<rightarrow> 'a) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow>! 'c) \<rightarrow> ('b \<rightarrow>! 'd)"
where
  "sfun_map = (\<Lambda> a b. sfun_abs oo cfun_map\<cdot>a\<cdot>b oo sfun_rep)"

lemma sfun_map_ID: "sfun_map\<cdot>ID\<cdot>ID = ID"
  unfolding sfun_map_def
  by (simp add: cfun_map_ID cfun_eq_iff)

lemma sfun_map_map:
  assumes "f2\<cdot>\<bottom> = \<bottom>" and "g2\<cdot>\<bottom> = \<bottom>" shows
  "sfun_map\<cdot>f1\<cdot>g1\<cdot>(sfun_map\<cdot>f2\<cdot>g2\<cdot>p) =
    sfun_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
unfolding sfun_map_def
by (simp add: cfun_eq_iff strictify_cancel assms cfun_map_map)

lemma ep_pair_sfun_map:
  assumes 1: "ep_pair e1 p1"
  assumes 2: "ep_pair e2 p2"
  shows "ep_pair (sfun_map\<cdot>p1\<cdot>e2) (sfun_map\<cdot>e1\<cdot>p2)"
proof
  interpret e1p1: pcpo_ep_pair e1 p1
    unfolding pcpo_ep_pair_def by fact
  interpret e2p2: pcpo_ep_pair e2 p2
    unfolding pcpo_ep_pair_def by fact
  fix f show "sfun_map\<cdot>e1\<cdot>p2\<cdot>(sfun_map\<cdot>p1\<cdot>e2\<cdot>f) = f"
    unfolding sfun_map_def
    apply (simp add: sfun_eq_iff strictify_cancel)
    apply (rule ep_pair.e_inverse)
    apply (rule ep_pair_cfun_map [OF 1 2])
    done
  fix g show "sfun_map\<cdot>p1\<cdot>e2\<cdot>(sfun_map\<cdot>e1\<cdot>p2\<cdot>g) \<sqsubseteq> g"
    unfolding sfun_map_def
    apply (simp add: sfun_below_iff strictify_cancel)
    apply (rule ep_pair.e_p_below)
    apply (rule ep_pair_cfun_map [OF 1 2])
    done
qed

lemma deflation_sfun_map:
  assumes 1: "deflation d1"
  assumes 2: "deflation d2"
  shows "deflation (sfun_map\<cdot>d1\<cdot>d2)"
apply (simp add: sfun_map_def)
apply (rule deflation.intro)
apply simp
apply (subst strictify_cancel)
apply (simp add: cfun_map_def deflation_strict 1 2)
apply (simp add: cfun_map_def deflation.idem 1 2)
apply (simp add: sfun_below_iff)
apply (subst strictify_cancel)
apply (simp add: cfun_map_def deflation_strict 1 2)
apply (rule deflation.below)
apply (rule deflation_cfun_map [OF 1 2])
done

lemma finite_deflation_sfun_map:
  assumes 1: "finite_deflation d1"
  assumes 2: "finite_deflation d2"
  shows "finite_deflation (sfun_map\<cdot>d1\<cdot>d2)"
proof (intro finite_deflation_intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (sfun_map\<cdot>d1\<cdot>d2)" by (rule deflation_sfun_map)
  from 1 2 have "finite_deflation (cfun_map\<cdot>d1\<cdot>d2)"
    by (rule finite_deflation_cfun_map)
  then have "finite {f. cfun_map\<cdot>d1\<cdot>d2\<cdot>f = f}"
    by (rule finite_deflation.finite_fixes)
  moreover have "inj (\<lambda>f. sfun_rep\<cdot>f)"
    by (rule inj_onI, simp add: sfun_eq_iff)
  ultimately have "finite ((\<lambda>f. sfun_rep\<cdot>f) -` {f. cfun_map\<cdot>d1\<cdot>d2\<cdot>f = f})"
    by (rule finite_vimageI)
  then show "finite {f. sfun_map\<cdot>d1\<cdot>d2\<cdot>f = f}"
    unfolding sfun_map_def sfun_eq_iff
    by (simp add: strictify_cancel
         deflation_strict `deflation d1` `deflation d2`)
qed

end
