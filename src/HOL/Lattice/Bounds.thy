(*  Title:      HOL/Lattice/Bounds.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Bounds *}

theory Bounds = Orders:

subsection {* Infimum and supremum *}

text {*
  Given a partial order, we define infimum (greatest lower bound) and
  supremum (least upper bound) wrt.\ @{text \<sqsubseteq>} for two and for any
  number of elements.
*}

constdefs
  is_inf :: "'a::partial_order \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  "is_inf x y inf \<equiv> inf \<sqsubseteq> x \<and> inf \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> inf)"

  is_sup :: "'a::partial_order \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  "is_sup x y sup \<equiv> x \<sqsubseteq> sup \<and> y \<sqsubseteq> sup \<and> (\<forall>z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> sup \<sqsubseteq> z)"

  is_Inf :: "'a::partial_order set \<Rightarrow> 'a \<Rightarrow> bool"
  "is_Inf A inf \<equiv> (\<forall>x \<in> A. inf \<sqsubseteq> x) \<and> (\<forall>z. (\<forall>x \<in> A. z \<sqsubseteq> x) \<longrightarrow> z \<sqsubseteq> inf)"

  is_Sup :: "'a::partial_order set \<Rightarrow> 'a \<Rightarrow> bool"
  "is_Sup A sup \<equiv> (\<forall>x \<in> A. x \<sqsubseteq> sup) \<and> (\<forall>z. (\<forall>x \<in> A. x \<sqsubseteq> z) \<longrightarrow> sup \<sqsubseteq> z)"

text {*
  These definitions entail the following basic properties of boundary
  elements.
*}

lemma is_infI [intro?]: "inf \<sqsubseteq> x \<Longrightarrow> inf \<sqsubseteq> y \<Longrightarrow>
    (\<And>z. z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> inf) \<Longrightarrow> is_inf x y inf"
  by (unfold is_inf_def) blast

lemma is_inf_greatest [elim?]:
    "is_inf x y inf \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> inf"
  by (unfold is_inf_def) blast

lemma is_inf_lower [elim?]:
    "is_inf x y inf \<Longrightarrow> (inf \<sqsubseteq> x \<Longrightarrow> inf \<sqsubseteq> y \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold is_inf_def) blast


lemma is_supI [intro?]: "x \<sqsubseteq> sup \<Longrightarrow> y \<sqsubseteq> sup \<Longrightarrow>
    (\<And>z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> sup \<sqsubseteq> z) \<Longrightarrow> is_sup x y sup"
  by (unfold is_sup_def) blast

lemma is_sup_least [elim?]:
    "is_sup x y sup \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> sup \<sqsubseteq> z"
  by (unfold is_sup_def) blast

lemma is_sup_upper [elim?]:
    "is_sup x y sup \<Longrightarrow> (x \<sqsubseteq> sup \<Longrightarrow> y \<sqsubseteq> sup \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold is_sup_def) blast


lemma is_InfI [intro?]: "(\<And>x. x \<in> A \<Longrightarrow> inf \<sqsubseteq> x) \<Longrightarrow>
    (\<And>z. (\<forall>x \<in> A. z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> inf) \<Longrightarrow> is_Inf A inf"
  by (unfold is_Inf_def) blast

lemma is_Inf_greatest [elim?]:
    "is_Inf A inf \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> inf"
  by (unfold is_Inf_def) blast

lemma is_Inf_lower [dest?]:
    "is_Inf A inf \<Longrightarrow> x \<in> A \<Longrightarrow> inf \<sqsubseteq> x"
  by (unfold is_Inf_def) blast


lemma is_SupI [intro?]: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> sup) \<Longrightarrow>
    (\<And>z. (\<forall>x \<in> A. x \<sqsubseteq> z) \<Longrightarrow> sup \<sqsubseteq> z) \<Longrightarrow> is_Sup A sup"
  by (unfold is_Sup_def) blast

lemma is_Sup_least [elim?]:
    "is_Sup A sup \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> sup \<sqsubseteq> z"
  by (unfold is_Sup_def) blast

lemma is_Sup_upper [dest?]:
    "is_Sup A sup \<Longrightarrow> x \<in> A \<Longrightarrow> x \<sqsubseteq> sup"
  by (unfold is_Sup_def) blast


subsection {* Duality *}

text {*
  Infimum and supremum are dual to each other.
*}

theorem dual_inf [iff?]:
    "is_inf (dual x) (dual y) (dual sup) = is_sup x y sup"
  by (simp add: is_inf_def is_sup_def dual_all [symmetric] dual_leq)

theorem dual_sup [iff?]:
    "is_sup (dual x) (dual y) (dual inf) = is_inf x y inf"
  by (simp add: is_inf_def is_sup_def dual_all [symmetric] dual_leq)

theorem dual_Inf [iff?]:
    "is_Inf (dual `` A) (dual sup) = is_Sup A sup"
  by (simp add: is_Inf_def is_Sup_def dual_all [symmetric] dual_leq)

theorem dual_Sup [iff?]:
    "is_Sup (dual `` A) (dual inf) = is_Inf A inf"
  by (simp add: is_Inf_def is_Sup_def dual_all [symmetric] dual_leq)


subsection {* Uniqueness *}

text {*
  Infima and suprema on partial orders are unique; this is mainly due
  to anti-symmetry of the underlying relation.
*}

theorem is_inf_uniq: "is_inf x y inf \<Longrightarrow> is_inf x y inf' \<Longrightarrow> inf = inf'"
proof -
  assume inf: "is_inf x y inf"
  assume inf': "is_inf x y inf'"
  show ?thesis
  proof (rule leq_antisym)
    from inf' show "inf \<sqsubseteq> inf'"
    proof (rule is_inf_greatest)
      from inf show "inf \<sqsubseteq> x" ..
      from inf show "inf \<sqsubseteq> y" ..
    qed
    from inf show "inf' \<sqsubseteq> inf"
    proof (rule is_inf_greatest)
      from inf' show "inf' \<sqsubseteq> x" ..
      from inf' show "inf' \<sqsubseteq> y" ..
    qed
  qed
qed

theorem is_sup_uniq: "is_sup x y sup \<Longrightarrow> is_sup x y sup' \<Longrightarrow> sup = sup'"
proof -
  assume sup: "is_sup x y sup" and sup': "is_sup x y sup'"
  have "dual sup = dual sup'"
  proof (rule is_inf_uniq)
    from sup show "is_inf (dual x) (dual y) (dual sup)" ..
    from sup' show "is_inf (dual x) (dual y) (dual sup')" ..
  qed
  thus "sup = sup'" ..
qed

theorem is_Inf_uniq: "is_Inf A inf \<Longrightarrow> is_Inf A inf' \<Longrightarrow> inf = inf'"
proof -
  assume inf: "is_Inf A inf"
  assume inf': "is_Inf A inf'"
  show ?thesis
  proof (rule leq_antisym)
    from inf' show "inf \<sqsubseteq> inf'"
    proof (rule is_Inf_greatest)
      fix x assume "x \<in> A"
      from inf show "inf \<sqsubseteq> x" ..
    qed
    from inf show "inf' \<sqsubseteq> inf"
    proof (rule is_Inf_greatest)
      fix x assume "x \<in> A"
      from inf' show "inf' \<sqsubseteq> x" ..
    qed
  qed
qed

theorem is_Sup_uniq: "is_Sup A sup \<Longrightarrow> is_Sup A sup' \<Longrightarrow> sup = sup'"
proof -
  assume sup: "is_Sup A sup" and sup': "is_Sup A sup'"
  have "dual sup = dual sup'"
  proof (rule is_Inf_uniq)
    from sup show "is_Inf (dual `` A) (dual sup)" ..
    from sup' show "is_Inf (dual `` A) (dual sup')" ..
  qed
  thus "sup = sup'" ..
qed


subsection {* Related elements *}

text {*
  The binary bound of related elements is either one of the argument.
*}

theorem is_inf_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> is_inf x y x"
proof -
  assume "x \<sqsubseteq> y"
  show ?thesis
  proof
    show "x \<sqsubseteq> x" ..
    show "x \<sqsubseteq> y" .
    fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y" show "z \<sqsubseteq> x" .
  qed
qed

theorem is_sup_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> is_sup x y y"
proof -
  assume "x \<sqsubseteq> y"
  show ?thesis
  proof
    show "x \<sqsubseteq> y" .
    show "y \<sqsubseteq> y" ..
    fix z assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    show "y \<sqsubseteq> z" .
  qed
qed


subsection {* General versus binary bounds \label{sec:gen-bin-bounds} *}

text {*
  General bounds of two-element sets coincide with binary bounds.
*}

theorem is_Inf_binary: "is_Inf {x, y} inf = is_inf x y inf"
proof -
  let ?A = "{x, y}"
  show ?thesis
  proof
    assume is_Inf: "is_Inf ?A inf"
    show "is_inf x y inf"
    proof
      have "x \<in> ?A" by simp
      with is_Inf show "inf \<sqsubseteq> x" ..
      have "y \<in> ?A" by simp
      with is_Inf show "inf \<sqsubseteq> y" ..
      fix z assume zx: "z \<sqsubseteq> x" and zy: "z \<sqsubseteq> y"
      from is_Inf show "z \<sqsubseteq> inf"
      proof (rule is_Inf_greatest)
        fix a assume "a \<in> ?A"
        hence "a = x \<or> a = y" by blast
        thus "z \<sqsubseteq> a"
        proof
          assume "a = x"
          with zx show ?thesis by simp
        next
          assume "a = y"
          with zy show ?thesis by simp
        qed
      qed
    qed
  next
    assume is_inf: "is_inf x y inf"
    show "is_Inf {x, y} inf"
    proof
      fix a assume "a \<in> ?A"
      hence "a = x \<or> a = y" by blast
      thus "inf \<sqsubseteq> a"
      proof
        assume "a = x"
        also from is_inf have "inf \<sqsubseteq> x" ..
        finally show ?thesis .
      next
        assume "a = y"
        also from is_inf have "inf \<sqsubseteq> y" ..
        finally show ?thesis .
      qed
    next
      fix z assume z: "\<forall>a \<in> ?A. z \<sqsubseteq> a"
      from is_inf show "z \<sqsubseteq> inf"
      proof (rule is_inf_greatest)
        from z show "z \<sqsubseteq> x" by blast
        from z show "z \<sqsubseteq> y" by blast
      qed
    qed
  qed
qed

theorem is_Sup_binary: "is_Sup {x, y} sup = is_sup x y sup"
proof -
  have "is_Sup {x, y} sup = is_Inf (dual `` {x, y}) (dual sup)"
    by (simp only: dual_Inf)
  also have "dual `` {x, y} = {dual x, dual y}"
    by simp
  also have "is_Inf \<dots> (dual sup) = is_inf (dual x) (dual y) (dual sup)"
    by (rule is_Inf_binary)
  also have "\<dots> = is_sup x y sup"
    by (simp only: dual_inf)
  finally show ?thesis .
qed


subsection {* Connecting general bounds \label{sec:connect-bounds} *}

text {*
  Either kind of general bounds is sufficient to express the other.
  The least upper bound (supremum) is the same as the the greatest
  lower bound of the set of all upper bounds; the dual statements
  holds as well; the dual statement holds as well.
*}

theorem Inf_Sup: "is_Inf {b. \<forall>a \<in> A. a \<sqsubseteq> b} sup \<Longrightarrow> is_Sup A sup"
proof -
  let ?B = "{b. \<forall>a \<in> A. a \<sqsubseteq> b}"
  assume is_Inf: "is_Inf ?B sup"
  show "is_Sup A sup"
  proof
    fix x assume x: "x \<in> A"
    from is_Inf show "x \<sqsubseteq> sup"
    proof (rule is_Inf_greatest)
      fix y assume "y \<in> ?B"
      hence "\<forall>a \<in> A. a \<sqsubseteq> y" ..
      from this x show "x \<sqsubseteq> y" ..
    qed
  next
    fix z assume "\<forall>x \<in> A. x \<sqsubseteq> z"
    hence "z \<in> ?B" ..
    with is_Inf show "sup \<sqsubseteq> z" ..
  qed
qed

theorem Sup_Inf: "is_Sup {b. \<forall>a \<in> A. b \<sqsubseteq> a} inf \<Longrightarrow> is_Inf A inf"
proof -
  assume "is_Sup {b. \<forall>a \<in> A. b \<sqsubseteq> a} inf"
  hence "is_Inf (dual `` {b. \<forall>a \<in> A. dual a \<sqsubseteq> dual b}) (dual inf)"
    by (simp only: dual_Inf dual_leq)
  also have "dual `` {b. \<forall>a \<in> A. dual a \<sqsubseteq> dual b} = {b'. \<forall>a' \<in> dual `` A. a' \<sqsubseteq> b'}"
    by (auto iff: dual_ball dual_Collect)  (* FIXME !? *)
  finally have "is_Inf \<dots> (dual inf)" .
  hence "is_Sup (dual `` A) (dual inf)"
    by (rule Inf_Sup)
  thus ?thesis ..
qed

end
