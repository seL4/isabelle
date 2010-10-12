(*  Title:      HOLCF/Cprod.thy
    Author:     Franz Regensburger
*)

header {* The cpo of cartesian products *}

theory Cprod
imports Deflation
begin

default_sort cpo

subsection {* Continuous case function for unit type *}

definition
  unit_when :: "'a \<rightarrow> unit \<rightarrow> 'a" where
  "unit_when = (\<Lambda> a _. a)"

translations
  "\<Lambda>(). t" == "CONST unit_when\<cdot>t"

lemma unit_when [simp]: "unit_when\<cdot>a\<cdot>u = a"
by (simp add: unit_when_def)

subsection {* Continuous version of split function *}

definition
  csplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a * 'b) \<rightarrow> 'c" where
  "csplit = (\<Lambda> f p. f\<cdot>(fst p)\<cdot>(snd p))"

translations
  "\<Lambda>(CONST Pair x y). t" == "CONST csplit\<cdot>(\<Lambda> x y. t)"


subsection {* Convert all lemmas to the continuous versions *}

lemma csplit1 [simp]: "csplit\<cdot>f\<cdot>\<bottom> = f\<cdot>\<bottom>\<cdot>\<bottom>"
by (simp add: csplit_def)

lemma csplit_Pair [simp]: "csplit\<cdot>f\<cdot>(x, y) = f\<cdot>x\<cdot>y"
by (simp add: csplit_def)

subsection {* Map operator for product type *}

definition
  cprod_map :: "('a \<rightarrow> 'b) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> 'a \<times> 'c \<rightarrow> 'b \<times> 'd"
where
  "cprod_map = (\<Lambda> f g p. (f\<cdot>(fst p), g\<cdot>(snd p)))"

lemma cprod_map_Pair [simp]: "cprod_map\<cdot>f\<cdot>g\<cdot>(x, y) = (f\<cdot>x, g\<cdot>y)"
unfolding cprod_map_def by simp

lemma cprod_map_ID: "cprod_map\<cdot>ID\<cdot>ID = ID"
unfolding cfun_eq_iff by auto

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

end
