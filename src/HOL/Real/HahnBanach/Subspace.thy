(*  Title:      HOL/Real/HahnBanach/Subspace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Subspaces *}

theory Subspace = VectorSpace:


subsection {* Definition *}

text {*
  A non-empty subset @{text U} of a vector space @{text V} is a
  \emph{subspace} of @{text V}, iff @{text U} is closed under addition
  and scalar multiplication.
*}

locale subspace = var U + var V +
  assumes non_empty [iff, intro]: "U \<noteq> {}"
    and subset [iff]: "U \<subseteq> V"
    and add_closed [iff]: "x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x + y \<in> U"
    and mult_closed [iff]: "x \<in> U \<Longrightarrow> a \<cdot> x \<in> U"

syntax (symbols)
  subspace :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"    (infix "\<unlhd>" 50)

lemma subspace_subset [elim]: "U \<unlhd> V \<Longrightarrow> U \<subseteq> V"
  by (rule subspace.subset)

lemma (in subspace) subsetD [iff]: "x \<in> U \<Longrightarrow> x \<in> V"
  using subset by blast

lemma subspaceD [elim]: "U \<unlhd> V \<Longrightarrow> x \<in> U \<Longrightarrow> x \<in> V"
  by (rule subspace.subsetD)

lemma rev_subspaceD [elim?]: "x \<in> U \<Longrightarrow> U \<unlhd> V \<Longrightarrow> x \<in> V"
  by (rule subspace.subsetD)


locale (open) subvectorspace =
  subspace + vectorspace

lemma (in subvectorspace) diff_closed [iff]:
    "x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x - y \<in> U"
  by (simp add: diff_eq1 negate_eq1)


text {*
  \medskip Similar as for linear spaces, the existence of the zero
  element in every subspace follows from the non-emptiness of the
  carrier set and by vector space laws.
*}

lemma (in subvectorspace) zero [intro]: "0 \<in> U"
proof -
  have "U \<noteq> {}" by (rule U_V.non_empty)
  then obtain x where x: "x \<in> U" by blast
  hence "x \<in> V" .. hence "0 = x - x" by simp
  also have "... \<in> U" by (rule U_V.diff_closed)
  finally show ?thesis .
qed

lemma (in subvectorspace) neg_closed [iff]: "x \<in> U \<Longrightarrow> - x \<in> U"
  by (simp add: negate_eq1)


text {* \medskip Further derived laws: every subspace is a vector space. *}

lemma (in subvectorspace) vectorspace [iff]:
  "vectorspace U"
proof
  show "U \<noteq> {}" ..
  fix x y z assume x: "x \<in> U" and y: "y \<in> U" and z: "z \<in> U"
  fix a b :: real
  from x y show "x + y \<in> U" by simp
  from x show "a \<cdot> x \<in> U" by simp
  from x y z show "(x + y) + z = x + (y + z)" by (simp add: add_ac)
  from x y show "x + y = y + x" by (simp add: add_ac)
  from x show "x - x = 0" by simp
  from x show "0 + x = x" by simp
  from x y show "a \<cdot> (x + y) = a \<cdot> x + a \<cdot> y" by (simp add: distrib)
  from x show "(a + b) \<cdot> x = a \<cdot> x + b \<cdot> x" by (simp add: distrib)
  from x show "(a * b) \<cdot> x = a \<cdot> b \<cdot> x" by (simp add: mult_assoc)
  from x show "1 \<cdot> x = x" by simp
  from x show "- x = - 1 \<cdot> x" by (simp add: negate_eq1)
  from x y show "x - y = x + - y" by (simp add: diff_eq1)
qed


text {* The subspace relation is reflexive. *}

lemma (in vectorspace) subspace_refl [intro]: "V \<unlhd> V"
proof
  show "V \<noteq> {}" ..
  show "V \<subseteq> V" ..
  fix x y assume x: "x \<in> V" and y: "y \<in> V"
  fix a :: real
  from x y show "x + y \<in> V" by simp
  from x show "a \<cdot> x \<in> V" by simp
qed

text {* The subspace relation is transitive. *}

lemma (in vectorspace) subspace_trans [trans]:
  "U \<unlhd> V \<Longrightarrow> V \<unlhd> W \<Longrightarrow> U \<unlhd> W"
proof
  assume uv: "U \<unlhd> V" and vw: "V \<unlhd> W"
  from uv show "U \<noteq> {}" by (rule subspace.non_empty)
  show "U \<subseteq> W"
  proof -
    from uv have "U \<subseteq> V" by (rule subspace.subset)
    also from vw have "V \<subseteq> W" by (rule subspace.subset)
    finally show ?thesis .
  qed
  fix x y assume x: "x \<in> U" and y: "y \<in> U"
  from uv and x y show "x + y \<in> U" by (rule subspace.add_closed)
  from uv and x show "\<And>a. a \<cdot> x \<in> U" by (rule subspace.mult_closed)
qed


subsection {* Linear closure *}

text {*
  The \emph{linear closure} of a vector @{text x} is the set of all
  scalar multiples of @{text x}.
*}

constdefs
  lin :: "('a::{minus, plus, zero}) \<Rightarrow> 'a set"
  "lin x \<equiv> {a \<cdot> x | a. True}"

lemma linI [intro]: "y = a \<cdot> x \<Longrightarrow> y \<in> lin x"
  by (unfold lin_def) blast

lemma linI' [iff]: "a \<cdot> x \<in> lin x"
  by (unfold lin_def) blast

lemma linE [elim]:
    "x \<in> lin v \<Longrightarrow> (\<And>a::real. x = a \<cdot> v \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold lin_def) blast


text {* Every vector is contained in its linear closure. *}

lemma (in vectorspace) x_lin_x [iff]: "x \<in> V \<Longrightarrow> x \<in> lin x"
proof -
  assume "x \<in> V"
  hence "x = 1 \<cdot> x" by simp
  also have "\<dots> \<in> lin x" ..
  finally show ?thesis .
qed

lemma (in vectorspace) "0_lin_x" [iff]: "x \<in> V \<Longrightarrow> 0 \<in> lin x"
proof
  assume "x \<in> V"
  thus "0 = 0 \<cdot> x" by simp
qed

text {* Any linear closure is a subspace. *}

lemma (in vectorspace) lin_subspace [intro]:
  "x \<in> V \<Longrightarrow> lin x \<unlhd> V"
proof
  assume x: "x \<in> V"
  thus "lin x \<noteq> {}" by (auto simp add: x_lin_x)
  show "lin x \<subseteq> V"
  proof
    fix x' assume "x' \<in> lin x"
    then obtain a where "x' = a \<cdot> x" ..
    with x show "x' \<in> V" by simp
  qed
  fix x' x'' assume x': "x' \<in> lin x" and x'': "x'' \<in> lin x"
  show "x' + x'' \<in> lin x"
  proof -
    from x' obtain a' where "x' = a' \<cdot> x" ..
    moreover from x'' obtain a'' where "x'' = a'' \<cdot> x" ..
    ultimately have "x' + x'' = (a' + a'') \<cdot> x"
      using x by (simp add: distrib)
    also have "\<dots> \<in> lin x" ..
    finally show ?thesis .
  qed
  fix a :: real
  show "a \<cdot> x' \<in> lin x"
  proof -
    from x' obtain a' where "x' = a' \<cdot> x" ..
    with x have "a \<cdot> x' = (a * a') \<cdot> x" by (simp add: mult_assoc)
    also have "\<dots> \<in> lin x" ..
    finally show ?thesis .
  qed
qed


text {* Any linear closure is a vector space. *}

lemma (in vectorspace) lin_vectorspace [intro]:
    "x \<in> V \<Longrightarrow> vectorspace (lin x)"
  by (rule subvectorspace.vectorspace) (rule lin_subspace)


subsection {* Sum of two vectorspaces *}

text {*
  The \emph{sum} of two vectorspaces @{text U} and @{text V} is the
  set of all sums of elements from @{text U} and @{text V}.
*}

instance set :: (plus) plus ..

defs (overloaded)
  sum_def: "U + V \<equiv> {u + v | u v. u \<in> U \<and> v \<in> V}"

lemma sumE [elim]:
    "x \<in> U + V \<Longrightarrow> (\<And>u v. x = u + v \<Longrightarrow> u \<in> U \<Longrightarrow> v \<in> V \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold sum_def) blast

lemma sumI [intro]:
    "u \<in> U \<Longrightarrow> v \<in> V \<Longrightarrow> x = u + v \<Longrightarrow> x \<in> U + V"
  by (unfold sum_def) blast

lemma sumI' [intro]:
    "u \<in> U \<Longrightarrow> v \<in> V \<Longrightarrow> u + v \<in> U + V"
  by (unfold sum_def) blast

text {* @{text U} is a subspace of @{text "U + V"}. *}

lemma subspace_sum1 [iff]:
  includes vectorspace U + vectorspace V
  shows "U \<unlhd> U + V"
proof
  show "U \<noteq> {}" ..
  show "U \<subseteq> U + V"
  proof
    fix x assume x: "x \<in> U"
    moreover have "0 \<in> V" ..
    ultimately have "x + 0 \<in> U + V" ..
    with x show "x \<in> U + V" by simp
  qed
  fix x y assume x: "x \<in> U" and "y \<in> U"
  thus "x + y \<in> U" by simp
  from x show "\<And>a. a \<cdot> x \<in> U" by simp
qed

text {* The sum of two subspaces is again a subspace. *}

lemma sum_subspace [intro?]:
  includes subvectorspace U E + subvectorspace V E
  shows "U + V \<unlhd> E"
proof
  have "0 \<in> U + V"
  proof
    show "0 \<in> U" ..
    show "0 \<in> V" ..
    show "(0::'a) = 0 + 0" by simp
  qed
  thus "U + V \<noteq> {}" by blast
  show "U + V \<subseteq> E"
  proof
    fix x assume "x \<in> U + V"
    then obtain u v where x: "x = u + v" and
      u: "u \<in> U" and v: "v \<in> V" ..
    have "U \<unlhd> E" . with u have "u \<in> E" ..
    moreover have "V \<unlhd> E" . with v have "v \<in> E" ..
    ultimately show "x \<in> E" using x by simp
  qed
  fix x y assume x: "x \<in> U + V" and y: "y \<in> U + V"
  show "x + y \<in> U + V"
  proof -
    from x obtain ux vx where "x = ux + vx" and "ux \<in> U" and "vx \<in> V" ..
    moreover
    from y obtain uy vy where "y = uy + vy" and "uy \<in> U" and "vy \<in> V" ..
    ultimately
    have "ux + uy \<in> U"
      and "vx + vy \<in> V"
      and "x + y = (ux + uy) + (vx + vy)"
      using x y by (simp_all add: add_ac)
    thus ?thesis ..
  qed
  fix a show "a \<cdot> x \<in> U + V"
  proof -
    from x obtain u v where "x = u + v" and "u \<in> U" and "v \<in> V" ..
    hence "a \<cdot> u \<in> U" and "a \<cdot> v \<in> V"
      and "a \<cdot> x = (a \<cdot> u) + (a \<cdot> v)" by (simp_all add: distrib)
    thus ?thesis ..
  qed
qed

text{* The sum of two subspaces is a vectorspace. *}

lemma sum_vs [intro?]:
    "U \<unlhd> E \<Longrightarrow> V \<unlhd> E \<Longrightarrow> vectorspace E \<Longrightarrow> vectorspace (U + V)"
  by (rule subvectorspace.vectorspace) (rule sum_subspace)


subsection {* Direct sums *}

text {*
  The sum of @{text U} and @{text V} is called \emph{direct}, iff the
  zero element is the only common element of @{text U} and @{text
  V}. For every element @{text x} of the direct sum of @{text U} and
  @{text V} the decomposition in @{text "x = u + v"} with
  @{text "u \<in> U"} and @{text "v \<in> V"} is unique.
*}

lemma decomp:
  includes vectorspace E + subspace U E + subspace V E
  assumes direct: "U \<inter> V = {0}"
    and u1: "u1 \<in> U" and u2: "u2 \<in> U"
    and v1: "v1 \<in> V" and v2: "v2 \<in> V"
    and sum: "u1 + v1 = u2 + v2"
  shows "u1 = u2 \<and> v1 = v2"
proof
  have U: "vectorspace U" by (rule subvectorspace.vectorspace)
  have V: "vectorspace V" by (rule subvectorspace.vectorspace)
  from u1 u2 v1 v2 and sum have eq: "u1 - u2 = v2 - v1"
    by (simp add: add_diff_swap)
  from u1 u2 have u: "u1 - u2 \<in> U"
    by (rule vectorspace.diff_closed [OF U])
  with eq have v': "v2 - v1 \<in> U" by (simp only:)
  from v2 v1 have v: "v2 - v1 \<in> V"
    by (rule vectorspace.diff_closed [OF V])
  with eq have u': " u1 - u2 \<in> V" by (simp only:)

  show "u1 = u2"
  proof (rule add_minus_eq)
    show "u1 \<in> E" ..
    show "u2 \<in> E" ..
    from u u' and direct show "u1 - u2 = 0" by blast
  qed
  show "v1 = v2"
  proof (rule add_minus_eq [symmetric])
    show "v1 \<in> E" ..
    show "v2 \<in> E" ..
    from v v' and direct show "v2 - v1 = 0" by blast
  qed
qed

text {*
  An application of the previous lemma will be used in the proof of
  the Hahn-Banach Theorem (see page \pageref{decomp-H-use}): for any
  element @{text "y + a \<cdot> x\<^sub>0"} of the direct sum of a
  vectorspace @{text H} and the linear closure of @{text "x\<^sub>0"}
  the components @{text "y \<in> H"} and @{text a} are uniquely
  determined.
*}

lemma decomp_H':
  includes vectorspace E + subvectorspace H E
  assumes y1: "y1 \<in> H" and y2: "y2 \<in> H"
    and x': "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
    and eq: "y1 + a1 \<cdot> x' = y2 + a2 \<cdot> x'"
  shows "y1 = y2 \<and> a1 = a2"
proof
  have c: "y1 = y2 \<and> a1 \<cdot> x' = a2 \<cdot> x'"
  proof (rule decomp)
    show "a1 \<cdot> x' \<in> lin x'" ..
    show "a2 \<cdot> x' \<in> lin x'" ..
    show "H \<inter> lin x' = {0}"
    proof
      show "H \<inter> lin x' \<subseteq> {0}"
      proof
        fix x assume x: "x \<in> H \<inter> lin x'"
        then obtain a where xx': "x = a \<cdot> x'"
          by blast
        have "x = 0"
        proof cases
          assume "a = 0"
          with xx' and x' show ?thesis by simp
        next
          assume a: "a \<noteq> 0"
          from x have "x \<in> H" ..
          with xx' have "inverse a \<cdot> a \<cdot> x' \<in> H" by simp
          with a and x' have "x' \<in> H" by (simp add: mult_assoc2)
          thus ?thesis by contradiction
        qed
        thus "x \<in> {0}" ..
      qed
      show "{0} \<subseteq> H \<inter> lin x'"
      proof -
        have "0 \<in> H" ..
        moreover have "0 \<in> lin x'" ..
        ultimately show ?thesis by blast
      qed
    qed
    show "lin x' \<unlhd> E" ..
  qed
  thus "y1 = y2" ..
  from c have "a1 \<cdot> x' = a2 \<cdot> x'" ..
  with x' show "a1 = a2" by (simp add: mult_right_cancel)
qed

text {*
  Since for any element @{text "y + a \<cdot> x'"} of the direct sum of a
  vectorspace @{text H} and the linear closure of @{text x'} the
  components @{text "y \<in> H"} and @{text a} are unique, it follows from
  @{text "y \<in> H"} that @{text "a = 0"}.
*}

lemma decomp_H'_H:
  includes vectorspace E + subvectorspace H E
  assumes t: "t \<in> H"
    and x': "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
  shows "(SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H) = (t, 0)"
proof (rule, simp_all only: split_paired_all split_conv)
  from t x' show "t = t + 0 \<cdot> x' \<and> t \<in> H" by simp
  fix y and a assume ya: "t = y + a \<cdot> x' \<and> y \<in> H"
  have "y = t \<and> a = 0"
  proof (rule decomp_H')
    from ya x' show "y + a \<cdot> x' = t + 0 \<cdot> x'" by simp
    from ya show "y \<in> H" ..
  qed
  with t x' show "(y, a) = (y + a \<cdot> x', 0)" by simp
qed

text {*
  The components @{text "y \<in> H"} and @{text a} in @{text "y + a \<cdot> x'"}
  are unique, so the function @{text h'} defined by
  @{text "h' (y + a \<cdot> x') = h y + a \<cdot> \<xi>"} is definite.
*}

lemma h'_definite:
  includes var H
  assumes h'_def:
    "h' \<equiv> (\<lambda>x. let (y, a) = SOME (y, a). (x = y + a \<cdot> x' \<and> y \<in> H)
                in (h y) + a * xi)"
    and x: "x = y + a \<cdot> x'"
  includes vectorspace E + subvectorspace H E
  assumes y: "y \<in> H"
    and x': "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
  shows "h' x = h y + a * xi"
proof -
  from x y x' have "x \<in> H + lin x'" by auto
  have "\<exists>!p. (\<lambda>(y, a). x = y + a \<cdot> x' \<and> y \<in> H) p" (is "\<exists>!p. ?P p")
  proof
    from x y show "\<exists>p. ?P p" by blast
    fix p q assume p: "?P p" and q: "?P q"
    show "p = q"
    proof -
      from p have xp: "x = fst p + snd p \<cdot> x' \<and> fst p \<in> H"
        by (cases p) simp
      from q have xq: "x = fst q + snd q \<cdot> x' \<and> fst q \<in> H"
        by (cases q) simp
      have "fst p = fst q \<and> snd p = snd q"
      proof (rule decomp_H')
        from xp show "fst p \<in> H" ..
        from xq show "fst q \<in> H" ..
        from xp and xq show "fst p + snd p \<cdot> x' = fst q + snd q \<cdot> x'"
          by simp
        apply_end assumption+
      qed
      thus ?thesis by (cases p, cases q) simp
    qed
  qed
  hence eq: "(SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H) = (y, a)"
    by (rule some1_equality) (simp add: x y)
  with h'_def show "h' x = h y + a * xi" by (simp add: Let_def)
qed

end
