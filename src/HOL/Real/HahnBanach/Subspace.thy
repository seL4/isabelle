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

constdefs
  is_subspace ::  "'a::{plus, minus, zero} set \<Rightarrow> 'a set \<Rightarrow> bool"
  "is_subspace U V \<equiv> U \<noteq> {} \<and> U \<subseteq> V
     \<and> (\<forall>x \<in> U. \<forall>y \<in> U. \<forall>a. x + y \<in> U \<and> a \<cdot> x \<in> U)"

lemma subspaceI [intro]:
  "0 \<in> U \<Longrightarrow> U \<subseteq> V \<Longrightarrow> \<forall>x \<in> U. \<forall>y \<in> U. (x + y \<in> U) \<Longrightarrow>
  \<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U
  \<Longrightarrow> is_subspace U V"
proof (unfold is_subspace_def, intro conjI)
  assume "0 \<in> U" thus "U \<noteq> {}" by fast
qed (simp+)

lemma subspace_not_empty [intro?]: "is_subspace U V \<Longrightarrow> U \<noteq> {}"
  by (unfold is_subspace_def) blast

lemma subspace_subset [intro?]: "is_subspace U V \<Longrightarrow> U \<subseteq> V"
  by (unfold is_subspace_def) blast

lemma subspace_subsetD [simp, intro?]:
  "is_subspace U V \<Longrightarrow> x \<in> U \<Longrightarrow> x \<in> V"
  by (unfold is_subspace_def) blast

lemma subspace_add_closed [simp, intro?]:
  "is_subspace U V \<Longrightarrow> x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> x + y \<in> U"
  by (unfold is_subspace_def) blast

lemma subspace_mult_closed [simp, intro?]:
  "is_subspace U V \<Longrightarrow> x \<in> U \<Longrightarrow> a \<cdot> x \<in> U"
  by (unfold is_subspace_def) blast

lemma subspace_diff_closed [simp, intro?]:
  "is_subspace U V \<Longrightarrow> is_vectorspace V \<Longrightarrow> x \<in> U \<Longrightarrow> y \<in> U
  \<Longrightarrow> x - y \<in> U"
  by (simp add: diff_eq1 negate_eq1)

text {* Similar as for linear spaces, the existence of the
zero element in every subspace follows from the non-emptiness
of the carrier set and by vector space laws.*}

lemma zero_in_subspace [intro?]:
  "is_subspace U V \<Longrightarrow> is_vectorspace V \<Longrightarrow> 0 \<in> U"
proof -
  assume "is_subspace U V" and v: "is_vectorspace V"
  have "U \<noteq> {}" ..
  hence "\<exists>x. x \<in> U" by blast
  thus ?thesis
  proof
    fix x assume u: "x \<in> U"
    hence "x \<in> V" by (simp!)
    with v have "0 = x - x" by (simp!)
    also have "... \<in> U" by (rule subspace_diff_closed)
    finally show ?thesis .
  qed
qed

lemma subspace_neg_closed [simp, intro?]:
  "is_subspace U V \<Longrightarrow> is_vectorspace V \<Longrightarrow> x \<in> U \<Longrightarrow> - x \<in> U"
  by (simp add: negate_eq1)

text {* \medskip Further derived laws: every subspace is a vector space. *}

lemma subspace_vs [intro?]:
  "is_subspace U V \<Longrightarrow> is_vectorspace V \<Longrightarrow> is_vectorspace U"
proof -
  assume "is_subspace U V"  "is_vectorspace V"
  show ?thesis
  proof
    show "0 \<in> U" ..
    show "\<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U" by (simp!)
    show "\<forall>x \<in> U. \<forall>y \<in> U. x + y \<in> U" by (simp!)
    show "\<forall>x \<in> U. - x = -#1 \<cdot> x" by (simp! add: negate_eq1)
    show "\<forall>x \<in> U. \<forall>y \<in> U. x - y =  x + - y"
      by (simp! add: diff_eq1)
  qed (simp! add: vs_add_mult_distrib1 vs_add_mult_distrib2)+
qed

text {* The subspace relation is reflexive. *}

lemma subspace_refl [intro]: "is_vectorspace V \<Longrightarrow> is_subspace V V"
proof
  assume "is_vectorspace V"
  show "0 \<in> V" ..
  show "V \<subseteq> V" ..
  show "\<forall>x \<in> V. \<forall>y \<in> V. x + y \<in> V" by (simp!)
  show "\<forall>x \<in> V. \<forall>a. a \<cdot> x \<in> V" by (simp!)
qed

text {* The subspace relation is transitive. *}

lemma subspace_trans:
  "is_subspace U V \<Longrightarrow> is_vectorspace V \<Longrightarrow> is_subspace V W
  \<Longrightarrow> is_subspace U W"
proof
  assume "is_subspace U V"  "is_subspace V W"  "is_vectorspace V"
  show "0 \<in> U" ..

  have "U \<subseteq> V" ..
  also have "V \<subseteq> W" ..
  finally show "U \<subseteq> W" .

  show "\<forall>x \<in> U. \<forall>y \<in> U. x + y \<in> U"
  proof (intro ballI)
    fix x y assume "x \<in> U"  "y \<in> U"
    show "x + y \<in> U" by (simp!)
  qed

  show "\<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U"
  proof (intro ballI allI)
    fix x a assume "x \<in> U"
    show "a \<cdot> x \<in> U" by (simp!)
  qed
qed



subsection {* Linear closure *}

text {*
  The \emph{linear closure} of a vector @{text x} is the set of all
  scalar multiples of @{text x}.
*}

constdefs
  lin :: "('a::{minus,plus,zero}) \<Rightarrow> 'a set"
  "lin x \<equiv> {a \<cdot> x | a. True}"

lemma linD: "x \<in> lin v = (\<exists>a::real. x = a \<cdot> v)"
  by (unfold lin_def) fast

lemma linI [intro?]: "a \<cdot> x0 \<in> lin x0"
  by (unfold lin_def) fast

text {* Every vector is contained in its linear closure. *}

lemma x_lin_x: "is_vectorspace V \<Longrightarrow> x \<in> V \<Longrightarrow> x \<in> lin x"
proof (unfold lin_def, intro CollectI exI conjI)
  assume "is_vectorspace V"  "x \<in> V"
  show "x = #1 \<cdot> x" by (simp!)
qed simp

text {* Any linear closure is a subspace. *}

lemma lin_subspace [intro?]:
  "is_vectorspace V \<Longrightarrow> x \<in> V \<Longrightarrow> is_subspace (lin x) V"
proof
  assume "is_vectorspace V"  "x \<in> V"
  show "0 \<in> lin x"
  proof (unfold lin_def, intro CollectI exI conjI)
    show "0 = (#0::real) \<cdot> x" by (simp!)
  qed simp

  show "lin x \<subseteq> V"
  proof (unfold lin_def, intro subsetI, elim CollectE exE conjE)
    fix xa a assume "xa = a \<cdot> x"
    show "xa \<in> V" by (simp!)
  qed

  show "\<forall>x1 \<in> lin x. \<forall>x2 \<in> lin x. x1 + x2 \<in> lin x"
  proof (intro ballI)
    fix x1 x2 assume "x1 \<in> lin x"  "x2 \<in> lin x"
    thus "x1 + x2 \<in> lin x"
    proof (unfold lin_def, elim CollectE exE conjE,
      intro CollectI exI conjI)
      fix a1 a2 assume "x1 = a1 \<cdot> x"  "x2 = a2 \<cdot> x"
      show "x1 + x2 = (a1 + a2) \<cdot> x"
        by (simp! add: vs_add_mult_distrib2)
    qed simp
  qed

  show "\<forall>xa \<in> lin x. \<forall>a. a \<cdot> xa \<in> lin x"
  proof (intro ballI allI)
    fix x1 a assume "x1 \<in> lin x"
    thus "a \<cdot> x1 \<in> lin x"
    proof (unfold lin_def, elim CollectE exE conjE,
      intro CollectI exI conjI)
      fix a1 assume "x1 = a1 \<cdot> x"
      show "a \<cdot> x1 = (a * a1) \<cdot> x" by (simp!)
    qed simp
  qed
qed

text {* Any linear closure is a vector space. *}

lemma lin_vs [intro?]:
  "is_vectorspace V \<Longrightarrow> x \<in> V \<Longrightarrow> is_vectorspace (lin x)"
proof (rule subspace_vs)
  assume "is_vectorspace V"  "x \<in> V"
  show "is_subspace (lin x) V" ..
qed



subsection {* Sum of two vectorspaces *}

text {*
  The \emph{sum} of two vectorspaces @{text U} and @{text V} is the
  set of all sums of elements from @{text U} and @{text V}.
*}

instance set :: (plus) plus ..

defs (overloaded)
  vs_sum_def: "U + V \<equiv> {u + v | u v. u \<in> U \<and> v \<in> V}"

lemma vs_sumD:
  "x \<in> U + V = (\<exists>u \<in> U. \<exists>v \<in> V. x = u + v)"
    by (unfold vs_sum_def) fast

lemmas vs_sumE = vs_sumD [THEN iffD1, elim_format, standard]

lemma vs_sumI [intro?]:
  "x \<in> U \<Longrightarrow> y \<in> V \<Longrightarrow> t = x + y \<Longrightarrow> t \<in> U + V"
  by (unfold vs_sum_def) fast

text {* @{text U} is a subspace of @{text "U + V"}. *}

lemma subspace_vs_sum1 [intro?]:
  "is_vectorspace U \<Longrightarrow> is_vectorspace V
  \<Longrightarrow> is_subspace U (U + V)"
proof
  assume "is_vectorspace U"  "is_vectorspace V"
  show "0 \<in> U" ..
  show "U \<subseteq> U + V"
  proof (intro subsetI vs_sumI)
  fix x assume "x \<in> U"
    show "x = x + 0" by (simp!)
    show "0 \<in> V" by (simp!)
  qed
  show "\<forall>x \<in> U. \<forall>y \<in> U. x + y \<in> U"
  proof (intro ballI)
    fix x y assume "x \<in> U"  "y \<in> U" show "x + y \<in> U" by (simp!)
  qed
  show "\<forall>x \<in> U. \<forall>a. a \<cdot> x \<in> U"
  proof (intro ballI allI)
    fix x a assume "x \<in> U" show "a \<cdot> x \<in> U" by (simp!)
  qed
qed

text{* The sum of two subspaces is again a subspace.*}

lemma vs_sum_subspace [intro?]:
  "is_subspace U E \<Longrightarrow> is_subspace V E \<Longrightarrow> is_vectorspace E
  \<Longrightarrow> is_subspace (U + V) E"
proof
  assume "is_subspace U E"  "is_subspace V E"  "is_vectorspace E"
  show "0 \<in> U + V"
  proof (intro vs_sumI)
    show "0 \<in> U" ..
    show "0 \<in> V" ..
    show "(0::'a) = 0 + 0" by (simp!)
  qed

  show "U + V \<subseteq> E"
  proof (intro subsetI, elim vs_sumE bexE)
    fix x u v assume "u \<in> U"  "v \<in> V"  "x = u + v"
    show "x \<in> E" by (simp!)
  qed

  show "\<forall>x \<in> U + V. \<forall>y \<in> U + V. x + y \<in> U + V"
  proof (intro ballI)
    fix x y assume "x \<in> U + V"  "y \<in> U + V"
    thus "x + y \<in> U + V"
    proof (elim vs_sumE bexE, intro vs_sumI)
      fix ux vx uy vy
      assume "ux \<in> U"  "vx \<in> V"  "x = ux + vx"
        and "uy \<in> U"  "vy \<in> V"  "y = uy + vy"
      show "x + y = (ux + uy) + (vx + vy)" by (simp!)
    qed (simp_all!)
  qed

  show "\<forall>x \<in> U + V. \<forall>a. a \<cdot> x \<in> U + V"
  proof (intro ballI allI)
    fix x a assume "x \<in> U + V"
    thus "a \<cdot> x \<in> U + V"
    proof (elim vs_sumE bexE, intro vs_sumI)
      fix a x u v assume "u \<in> U"  "v \<in> V"  "x = u + v"
      show "a \<cdot> x = (a \<cdot> u) + (a \<cdot> v)"
        by (simp! add: vs_add_mult_distrib1)
    qed (simp_all!)
  qed
qed

text{* The sum of two subspaces is a vectorspace. *}

lemma vs_sum_vs [intro?]:
  "is_subspace U E \<Longrightarrow> is_subspace V E \<Longrightarrow> is_vectorspace E
  \<Longrightarrow> is_vectorspace (U + V)"
proof (rule subspace_vs)
  assume "is_subspace U E"  "is_subspace V E"  "is_vectorspace E"
  show "is_subspace (U + V) E" ..
qed



subsection {* Direct sums *}


text {*
  The sum of @{text U} and @{text V} is called \emph{direct}, iff the
  zero element is the only common element of @{text U} and @{text
  V}. For every element @{text x} of the direct sum of @{text U} and
  @{text V} the decomposition in @{text "x = u + v"} with
  @{text "u \<in> U"} and @{text "v \<in> V"} is unique.
*}

lemma decomp:
  "is_vectorspace E \<Longrightarrow> is_subspace U E \<Longrightarrow> is_subspace V E \<Longrightarrow>
  U \<inter> V = {0} \<Longrightarrow> u1 \<in> U \<Longrightarrow> u2 \<in> U \<Longrightarrow> v1 \<in> V \<Longrightarrow> v2 \<in> V \<Longrightarrow>
  u1 + v1 = u2 + v2 \<Longrightarrow> u1 = u2 \<and> v1 = v2"
proof
  assume "is_vectorspace E"  "is_subspace U E"  "is_subspace V E"
    "U \<inter> V = {0}"  "u1 \<in> U"  "u2 \<in> U"  "v1 \<in> V"  "v2 \<in> V"
    "u1 + v1 = u2 + v2"
  have eq: "u1 - u2 = v2 - v1" by (simp! add: vs_add_diff_swap)
  have u: "u1 - u2 \<in> U" by (simp!)
  with eq have v': "v2 - v1 \<in> U" by simp
  have v: "v2 - v1 \<in> V" by (simp!)
  with eq have u': "u1 - u2 \<in> V" by simp

  show "u1 = u2"
  proof (rule vs_add_minus_eq)
    show "u1 - u2 = 0" by (rule Int_singletonD [OF _ u u'])
    show "u1 \<in> E" ..
    show "u2 \<in> E" ..
  qed

  show "v1 = v2"
  proof (rule vs_add_minus_eq [symmetric])
    show "v2 - v1 = 0" by (rule Int_singletonD [OF _ v' v])
    show "v1 \<in> E" ..
    show "v2 \<in> E" ..
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
  "is_vectorspace E \<Longrightarrow> is_subspace H E \<Longrightarrow> y1 \<in> H \<Longrightarrow> y2 \<in> H \<Longrightarrow>
  x' \<notin> H \<Longrightarrow> x' \<in> E \<Longrightarrow> x' \<noteq> 0 \<Longrightarrow> y1 + a1 \<cdot> x' = y2 + a2 \<cdot> x'
  \<Longrightarrow> y1 = y2 \<and> a1 = a2"
proof
  assume "is_vectorspace E" and h: "is_subspace H E"
     and "y1 \<in> H"  "y2 \<in> H"  "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
         "y1 + a1 \<cdot> x' = y2 + a2 \<cdot> x'"

  have c: "y1 = y2 \<and> a1 \<cdot> x' = a2 \<cdot> x'"
  proof (rule decomp)
    show "a1 \<cdot> x' \<in> lin x'" ..
    show "a2 \<cdot> x' \<in> lin x'" ..
    show "H \<inter> (lin x') = {0}"
    proof
      show "H \<inter> lin x' \<subseteq> {0}"
      proof (intro subsetI, elim IntE, rule singleton_iff [THEN iffD2])
        fix x assume "x \<in> H"  "x \<in> lin x'"
        thus "x = 0"
        proof (unfold lin_def, elim CollectE exE conjE)
          fix a assume "x = a \<cdot> x'"
          show ?thesis
          proof cases
            assume "a = (#0::real)" show ?thesis by (simp!)
          next
            assume "a \<noteq> (#0::real)"
            from h have "inverse a \<cdot> a \<cdot> x' \<in> H"
              by (rule subspace_mult_closed) (simp!)
            also have "inverse a \<cdot> a \<cdot> x' = x'" by (simp!)
            finally have "x' \<in> H" .
            thus ?thesis by contradiction
          qed
       qed
      qed
      show "{0} \<subseteq> H \<inter> lin x'"
      proof -
        have "0 \<in> H \<inter> lin x'"
        proof (rule IntI)
          show "0 \<in> H" ..
          from lin_vs show "0 \<in> lin x'" ..
        qed
        thus ?thesis by simp
      qed
    qed
    show "is_subspace (lin x') E" ..
  qed

  from c show "y1 = y2" by simp

  show  "a1 = a2"
  proof (rule vs_mult_right_cancel [THEN iffD1])
    from c show "a1 \<cdot> x' = a2 \<cdot> x'" by simp
  qed
qed

text {*
  Since for any element @{text "y + a \<cdot> x'"} of the direct sum of a
  vectorspace @{text H} and the linear closure of @{text x'} the
  components @{text "y \<in> H"} and @{text a} are unique, it follows from
  @{text "y \<in> H"} that @{text "a = 0"}.
*}

lemma decomp_H'_H:
  "is_vectorspace E \<Longrightarrow> is_subspace H E \<Longrightarrow> t \<in> H \<Longrightarrow> x' \<notin> H \<Longrightarrow> x' \<in> E
  \<Longrightarrow> x' \<noteq> 0
  \<Longrightarrow> (SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H) = (t, (#0::real))"
proof (rule, unfold split_tupled_all)
  assume "is_vectorspace E"  "is_subspace H E"  "t \<in> H"  "x' \<notin> H"  "x' \<in> E"
    "x' \<noteq> 0"
  have h: "is_vectorspace H" ..
  fix y a presume t1: "t = y + a \<cdot> x'" and "y \<in> H"
  have "y = t \<and> a = (#0::real)"
    by (rule decomp_H') (auto!)
  thus "(y, a) = (t, (#0::real))" by (simp!)
qed (simp_all!)

text {*
  The components @{text "y \<in> H"} and @{text a} in @{text "y + a \<cdot> x'"}
  are unique, so the function @{text h'} defined by
  @{text "h' (y + a \<cdot> x') = h y + a \<cdot> \<xi>"} is definite.
*}

lemma h'_definite:
  "h' \<equiv> (\<lambda>x. let (y, a) = SOME (y, a). (x = y + a \<cdot> x' \<and> y \<in> H)
                in (h y) + a * xi) \<Longrightarrow>
  x = y + a \<cdot> x' \<Longrightarrow> is_vectorspace E \<Longrightarrow> is_subspace H E \<Longrightarrow>
  y \<in> H \<Longrightarrow> x' \<notin> H \<Longrightarrow> x' \<in> E \<Longrightarrow> x' \<noteq> 0
  \<Longrightarrow> h' x = h y + a * xi"
proof -
  assume
    "h' \<equiv> (\<lambda>x. let (y, a) = SOME (y, a). (x = y + a \<cdot> x' \<and> y \<in> H)
               in (h y) + a * xi)"
    "x = y + a \<cdot> x'"  "is_vectorspace E"  "is_subspace H E"
    "y \<in> H"  "x' \<notin> H"  "x' \<in> E"  "x' \<noteq> 0"
  hence "x \<in> H + (lin x')"
    by (auto simp add: vs_sum_def lin_def)
  have "\<exists>! xa. ((\<lambda>(y, a). x = y + a \<cdot> x' \<and> y \<in> H) xa)"
  proof
    show "\<exists>xa. ((\<lambda>(y, a). x = y + a \<cdot> x' \<and> y \<in> H) xa)"
      by (blast!)
  next
    fix xa ya
    assume "(\<lambda>(y,a). x = y + a \<cdot> x' \<and> y \<in> H) xa"
           "(\<lambda>(y,a). x = y + a \<cdot> x' \<and> y \<in> H) ya"
    show "xa = ya"
    proof -
      show "fst xa = fst ya \<and> snd xa = snd ya \<Longrightarrow> xa = ya"
        by (simp add: Pair_fst_snd_eq)
      have x: "x = fst xa + snd xa \<cdot> x' \<and> fst xa \<in> H"
        by (auto!)
      have y: "x = fst ya + snd ya \<cdot> x' \<and> fst ya \<in> H"
        by (auto!)
      from x y show "fst xa = fst ya \<and> snd xa = snd ya"
        by (elim conjE) (rule decomp_H', (simp!)+)
    qed
  qed
  hence eq: "(SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H) = (y, a)"
    by (rule some1_equality) (blast!)
  thus "h' x = h y + a * xi" by (simp! add: Let_def)
qed

end
