(*  Title:      HOL/Hahn_Banach/Subspace.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>Subspaces\<close>

theory Subspace
imports Vector_Space "HOL-Library.Set_Algebras"
begin

subsection \<open>Definition\<close>

text \<open>
  A non-empty subset \<open>U\<close> of a vector space \<open>V\<close> is a \<^emph>\<open>subspace\<close> of \<open>V\<close>, iff
  \<open>U\<close> is closed under addition and scalar multiplication.
\<close>

locale subspace =
  fixes U :: "'a::{minus, plus, zero, uminus} set" and V
  assumes non_empty [iff, intro]: "U \<noteq> {}"
    and subset [iff]: "U \<subseteq> V"
    and add_closed [iff]: "x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x + y \<in> U"
    and mult_closed [iff]: "x \<in> U \<Longrightarrow> a \<cdot> x \<in> U"

notation (symbols)
  subspace  (infix \<open>\<unlhd>\<close> 50)

declare vectorspace.intro [intro?] subspace.intro [intro?]

lemma subspace_subset [elim]: "U \<unlhd> V \<Longrightarrow> U \<subseteq> V"
  by (rule subspace.subset)

lemma (in subspace) subsetD [iff]: "x \<in> U \<Longrightarrow> x \<in> V"
  using subset by blast

lemma subspaceD [elim]: "U \<unlhd> V \<Longrightarrow> x \<in> U \<Longrightarrow> x \<in> V"
  by (rule subspace.subsetD)

lemma rev_subspaceD [elim?]: "x \<in> U \<Longrightarrow> U \<unlhd> V \<Longrightarrow> x \<in> V"
  by (rule subspace.subsetD)

lemma (in subspace) diff_closed [iff]:
  assumes "vectorspace V"
  assumes x: "x \<in> U" and y: "y \<in> U"
  shows "x - y \<in> U"
proof -
  interpret vectorspace V by fact
  from x y show ?thesis by (simp add: diff_eq1 negate_eq1)
qed

text \<open>
  \<^medskip>
  Similar as for linear spaces, the existence of the zero element in every
  subspace follows from the non-emptiness of the carrier set and by vector
  space laws.
\<close>

lemma (in subspace) zero [intro]:
  assumes "vectorspace V"
  shows "0 \<in> U"
proof -
  interpret V: vectorspace V by fact
  have "U \<noteq> {}" by (rule non_empty)
  then obtain x where x: "x \<in> U" by blast
  then have "x \<in> V" .. then have "0 = x - x" by simp
  also from \<open>vectorspace V\<close> x x have "\<dots> \<in> U" by (rule diff_closed)
  finally show ?thesis .
qed

lemma (in subspace) neg_closed [iff]:
  assumes "vectorspace V"
  assumes x: "x \<in> U"
  shows "- x \<in> U"
proof -
  interpret vectorspace V by fact
  from x show ?thesis by (simp add: negate_eq1)
qed

text \<open>\<^medskip> Further derived laws: every subspace is a vector space.\<close>

lemma (in subspace) vectorspace [iff]:
  assumes "vectorspace V"
  shows "vectorspace U"
proof -
  interpret vectorspace V by fact
  show ?thesis
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
qed


text \<open>The subspace relation is reflexive.\<close>

lemma (in vectorspace) subspace_refl [intro]: "V \<unlhd> V"
proof
  show "V \<noteq> {}" ..
  show "V \<subseteq> V" ..
next
  fix x y assume x: "x \<in> V" and y: "y \<in> V"
  fix a :: real
  from x y show "x + y \<in> V" by simp
  from x show "a \<cdot> x \<in> V" by simp
qed

text \<open>The subspace relation is transitive.\<close>

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
  from uv and x show "a \<cdot> x \<in> U" for a by (rule subspace.mult_closed)
qed


subsection \<open>Linear closure\<close>

text \<open>
  The \<^emph>\<open>linear closure\<close> of a vector \<open>x\<close> is the set of all scalar multiples of
  \<open>x\<close>.
\<close>

definition lin :: "('a::{minus,plus,zero}) \<Rightarrow> 'a set"
  where "lin x = {a \<cdot> x | a. True}"

lemma linI [intro]: "y = a \<cdot> x \<Longrightarrow> y \<in> lin x"
  unfolding lin_def by blast

lemma linI' [iff]: "a \<cdot> x \<in> lin x"
  unfolding lin_def by blast

lemma linE [elim]:
  assumes "x \<in> lin v"
  obtains a :: real where "x = a \<cdot> v"
  using assms unfolding lin_def by blast


text \<open>Every vector is contained in its linear closure.\<close>

lemma (in vectorspace) x_lin_x [iff]: "x \<in> V \<Longrightarrow> x \<in> lin x"
proof -
  assume "x \<in> V"
  then have "x = 1 \<cdot> x" by simp
  also have "\<dots> \<in> lin x" ..
  finally show ?thesis .
qed

lemma (in vectorspace) "0_lin_x" [iff]: "x \<in> V \<Longrightarrow> 0 \<in> lin x"
proof
  assume "x \<in> V"
  then show "0 = 0 \<cdot> x" by simp
qed

text \<open>Any linear closure is a subspace.\<close>

lemma (in vectorspace) lin_subspace [intro]:
  assumes x: "x \<in> V"
  shows "lin x \<unlhd> V"
proof
  from x show "lin x \<noteq> {}" by auto
next
  show "lin x \<subseteq> V"
  proof
    fix x' assume "x' \<in> lin x"
    then obtain a where "x' = a \<cdot> x" ..
    with x show "x' \<in> V" by simp
  qed
next
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


text \<open>Any linear closure is a vector space.\<close>

lemma (in vectorspace) lin_vectorspace [intro]:
  assumes "x \<in> V"
  shows "vectorspace (lin x)"
proof -
  from \<open>x \<in> V\<close> have "subspace (lin x) V"
    by (rule lin_subspace)
  from this and vectorspace_axioms show ?thesis
    by (rule subspace.vectorspace)
qed


subsection \<open>Sum of two vectorspaces\<close>

text \<open>
  The \<^emph>\<open>sum\<close> of two vectorspaces \<open>U\<close> and \<open>V\<close> is the set of all sums of
  elements from \<open>U\<close> and \<open>V\<close>.
\<close>

lemma sum_def: "U + V = {u + v | u v. u \<in> U \<and> v \<in> V}"
  unfolding set_plus_def by auto

lemma sumE [elim]:
    "x \<in> U + V \<Longrightarrow> (\<And>u v. x = u + v \<Longrightarrow> u \<in> U \<Longrightarrow> v \<in> V \<Longrightarrow> C) \<Longrightarrow> C"
  unfolding sum_def by blast

lemma sumI [intro]:
    "u \<in> U \<Longrightarrow> v \<in> V \<Longrightarrow> x = u + v \<Longrightarrow> x \<in> U + V"
  unfolding sum_def by blast

lemma sumI' [intro]:
    "u \<in> U \<Longrightarrow> v \<in> V \<Longrightarrow> u + v \<in> U + V"
  unfolding sum_def by blast

text \<open>\<open>U\<close> is a subspace of \<open>U + V\<close>.\<close>

lemma subspace_sum1 [iff]:
  assumes "vectorspace U" "vectorspace V"
  shows "U \<unlhd> U + V"
proof -
  interpret vectorspace U by fact
  interpret vectorspace V by fact
  show ?thesis
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
    then show "x + y \<in> U" by simp
    from x show "a \<cdot> x \<in> U" for a by simp
  qed
qed

text \<open>The sum of two subspaces is again a subspace.\<close>

lemma sum_subspace [intro?]:
  assumes "subspace U E" "vectorspace E" "subspace V E"
  shows "U + V \<unlhd> E"
proof -
  interpret subspace U E by fact
  interpret vectorspace E by fact
  interpret subspace V E by fact
  show ?thesis
  proof
    have "0 \<in> U + V"
    proof
      show "0 \<in> U" using \<open>vectorspace E\<close> ..
      show "0 \<in> V" using \<open>vectorspace E\<close> ..
      show "(0::'a) = 0 + 0" by simp
    qed
    then show "U + V \<noteq> {}" by blast
    show "U + V \<subseteq> E"
    proof
      fix x assume "x \<in> U + V"
      then obtain u v where "x = u + v" and
        "u \<in> U" and "v \<in> V" ..
      then show "x \<in> E" by simp
    qed
  next
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
      then show ?thesis ..
    qed
    fix a show "a \<cdot> x \<in> U + V"
    proof -
      from x obtain u v where "x = u + v" and "u \<in> U" and "v \<in> V" ..
      then have "a \<cdot> u \<in> U" and "a \<cdot> v \<in> V"
        and "a \<cdot> x = (a \<cdot> u) + (a \<cdot> v)" by (simp_all add: distrib)
      then show ?thesis ..
    qed
  qed
qed

text \<open>The sum of two subspaces is a vectorspace.\<close>

lemma sum_vs [intro?]:
    "U \<unlhd> E \<Longrightarrow> V \<unlhd> E \<Longrightarrow> vectorspace E \<Longrightarrow> vectorspace (U + V)"
  by (rule subspace.vectorspace) (rule sum_subspace)


subsection \<open>Direct sums\<close>

text \<open>
  The sum of \<open>U\<close> and \<open>V\<close> is called \<^emph>\<open>direct\<close>, iff the zero element is the only
  common element of \<open>U\<close> and \<open>V\<close>. For every element \<open>x\<close> of the direct sum of
  \<open>U\<close> and \<open>V\<close> the decomposition in \<open>x = u + v\<close> with \<open>u \<in> U\<close> and \<open>v \<in> V\<close> is
  unique.
\<close>

lemma decomp:
  assumes "vectorspace E" "subspace U E" "subspace V E"
  assumes direct: "U \<inter> V = {0}"
    and u1: "u1 \<in> U" and u2: "u2 \<in> U"
    and v1: "v1 \<in> V" and v2: "v2 \<in> V"
    and sum: "u1 + v1 = u2 + v2"
  shows "u1 = u2 \<and> v1 = v2"
proof -
  interpret vectorspace E by fact
  interpret subspace U E by fact
  interpret subspace V E by fact
  show ?thesis
  proof
    have U: "vectorspace U"  (* FIXME: use interpret *)
      using \<open>subspace U E\<close> \<open>vectorspace E\<close> by (rule subspace.vectorspace)
    have V: "vectorspace V"
      using \<open>subspace V E\<close> \<open>vectorspace E\<close> by (rule subspace.vectorspace)
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
      from u1 show "u1 \<in> E" ..
      from u2 show "u2 \<in> E" ..
      from u u' and direct show "u1 - u2 = 0" by blast
    qed
    show "v1 = v2"
    proof (rule add_minus_eq [symmetric])
      from v1 show "v1 \<in> E" ..
      from v2 show "v2 \<in> E" ..
      from v v' and direct show "v2 - v1 = 0" by blast
    qed
  qed
qed

text \<open>
  An application of the previous lemma will be used in the proof of the
  Hahn-Banach Theorem (see page \pageref{decomp-H-use}): for any element
  \<open>y + a \<cdot> x\<^sub>0\<close> of the direct sum of a vectorspace \<open>H\<close> and the linear closure
  of \<open>x\<^sub>0\<close> the components \<open>y \<in> H\<close> and \<open>a\<close> are uniquely determined.
\<close>

lemma decomp_H':
  assumes "vectorspace E" "subspace H E"
  assumes y1: "y1 \<in> H" and y2: "y2 \<in> H"
    and x': "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
    and eq: "y1 + a1 \<cdot> x' = y2 + a2 \<cdot> x'"
  shows "y1 = y2 \<and> a1 = a2"
proof -
  interpret vectorspace E by fact
  interpret subspace H E by fact
  show ?thesis
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
            with \<open>x' \<notin> H\<close> show ?thesis by contradiction
          qed
          then show "x \<in> {0}" ..
        qed
        show "{0} \<subseteq> H \<inter> lin x'"
        proof -
          have "0 \<in> H" using \<open>vectorspace E\<close> ..
          moreover have "0 \<in> lin x'" using \<open>x' \<in> E\<close> ..
          ultimately show ?thesis by blast
        qed
      qed
      show "lin x' \<unlhd> E" using \<open>x' \<in> E\<close> ..
    qed (rule \<open>vectorspace E\<close>, rule \<open>subspace H E\<close>, rule y1, rule y2, rule eq)
    then show "y1 = y2" ..
    from c have "a1 \<cdot> x' = a2 \<cdot> x'" ..
    with x' show "a1 = a2" by (simp add: mult_right_cancel)
  qed
qed

text \<open>
  Since for any element \<open>y + a \<cdot> x'\<close> of the direct sum of a vectorspace \<open>H\<close>
  and the linear closure of \<open>x'\<close> the components \<open>y \<in> H\<close> and \<open>a\<close> are unique, it
  follows from \<open>y \<in> H\<close> that \<open>a = 0\<close>.
\<close>

lemma decomp_H'_H:
  assumes "vectorspace E" "subspace H E"
  assumes t: "t \<in> H"
    and x': "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
  shows "(SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H) = (t, 0)"
proof -
  interpret vectorspace E by fact
  interpret subspace H E by fact
  show ?thesis
  proof (rule, simp_all only: split_paired_all split_conv)
    from t x' show "t = t + 0 \<cdot> x' \<and> t \<in> H" by simp
    fix y and a assume ya: "t = y + a \<cdot> x' \<and> y \<in> H"
    have "y = t \<and> a = 0"
    proof (rule decomp_H')
      from ya x' show "y + a \<cdot> x' = t + 0 \<cdot> x'" by simp
      from ya show "y \<in> H" ..
    qed (rule \<open>vectorspace E\<close>, rule \<open>subspace H E\<close>, rule t, (rule x')+)
    with t x' show "(y, a) = (y + a \<cdot> x', 0)" by simp
  qed
qed

text \<open>
  The components \<open>y \<in> H\<close> and \<open>a\<close> in \<open>y + a \<cdot> x'\<close> are unique, so the function
  \<open>h'\<close> defined by \<open>h' (y + a \<cdot> x') = h y + a \<cdot> \<xi>\<close> is definite.
\<close>

lemma h'_definite:
  fixes H
  assumes h'_def:
    "\<And>x. h' x =
      (let (y, a) = SOME (y, a). (x = y + a \<cdot> x' \<and> y \<in> H)
       in (h y) + a * xi)"
    and x: "x = y + a \<cdot> x'"
  assumes "vectorspace E" "subspace H E"
  assumes y: "y \<in> H"
    and x': "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
  shows "h' x = h y + a * xi"
proof -
  interpret vectorspace E by fact
  interpret subspace H E by fact
  from x y x' have "x \<in> H + lin x'" by auto
  have "\<exists>!(y, a). x = y + a \<cdot> x' \<and> y \<in> H" (is "\<exists>!p. ?P p")
  proof (rule ex_ex1I)
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
      qed (rule \<open>vectorspace E\<close>, rule \<open>subspace H E\<close>, (rule x')+)
      then show ?thesis by (cases p, cases q) simp
    qed
  qed
  then have eq: "(SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H) = (y, a)"
    by (rule some1_equality) (simp add: x y)
  with h'_def show "h' x = h y + a * xi" by (simp add: Let_def)
qed

end
