(*  Title:      HOL/Isar_examples/MutilatedCheckerboard.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen (Isar document)
                Lawrence C Paulson, Cambridge University Computer Laboratory (original scripts)
*)

header {* The Mutilated Checker Board Problem *}

theory MutilatedCheckerboard = Main:

text {*
 The Mutilated Checker Board Problem, formalized inductively.  See
 \cite{paulson-mutilated-board} and
 \url{http://isabelle.in.tum.de/library/HOL/Induct/Mutil.html} for the
 original tactic script version.
*}

subsection {* Tilings *}

consts
  tiling :: "'a set set => 'a set set"

inductive "tiling A"
  intros
    empty: "{} : tiling A"
    Un: "a : A ==> t : tiling A ==> a <= - t ==> a Un t : tiling A"


text "The union of two disjoint tilings is a tiling."

lemma tiling_Un:
  "t : tiling A ==> u : tiling A ==> t Int u = {}
    ==> t Un u : tiling A"
proof -
  let ?T = "tiling A"
  assume u: "u : ?T"
  assume "t : ?T"
  thus "t Int u = {} ==> t Un u : ?T" (is "PROP ?P t")
  proof (induct t)
    from u show "{} Un u : ?T" by simp
  next
    fix a t
    assume "a : A" and hyp: "PROP ?P t"
      and at: "a <= - t" and atu: "(a Un t) Int u = {}"
    show "(a Un t) Un u : ?T"
    proof -
      have "a Un (t Un u) : ?T"
      proof (rule tiling.Un)
        show "a : A" .
        from atu have "t Int u = {}" by blast
        thus "t Un u: ?T" by (rule hyp)
        from at atu show "a <= - (t Un u)" by blast
      qed
      also have "a Un (t Un u) = (a Un t) Un u"
        by (simp only: Un_assoc)
      finally show ?thesis .
    qed
  qed
qed


subsection {* Basic properties of ``below'' *}

constdefs
  below :: "nat => nat set"
  "below n == {i. i < n}"

lemma below_less_iff [iff]: "(i: below k) = (i < k)"
  by (simp add: below_def)

lemma below_0: "below 0 = {}"
  by (simp add: below_def)

lemma Sigma_Suc1:
    "m = n + 1 ==> below m <*> B = ({n} <*> B) Un (below n <*> B)"
  by (simp add: below_def less_Suc_eq) blast

lemma Sigma_Suc2:
    "m = n + # 2 ==> A <*> below m =
      (A <*> {n}) Un (A <*> {n + 1}) Un (A <*> below n)"
  by (auto simp add: below_def) arith

lemmas Sigma_Suc = Sigma_Suc1 Sigma_Suc2


subsection {* Basic properties of ``evnodd'' *}

constdefs
  evnodd :: "(nat * nat) set => nat => (nat * nat) set"
  "evnodd A b == A Int {(i, j). (i + j) mod # 2 = b}"

lemma evnodd_iff:
    "(i, j): evnodd A b = ((i, j): A  & (i + j) mod # 2 = b)"
  by (simp add: evnodd_def)

lemma evnodd_subset: "evnodd A b <= A"
  by (unfold evnodd_def, rule Int_lower1)

lemma evnoddD: "x : evnodd A b ==> x : A"
  by (rule subsetD, rule evnodd_subset)

lemma evnodd_finite: "finite A ==> finite (evnodd A b)"
  by (rule finite_subset, rule evnodd_subset)

lemma evnodd_Un: "evnodd (A Un B) b = evnodd A b Un evnodd B b"
  by (unfold evnodd_def) blast

lemma evnodd_Diff: "evnodd (A - B) b = evnodd A b - evnodd B b"
  by (unfold evnodd_def) blast

lemma evnodd_empty: "evnodd {} b = {}"
  by (simp add: evnodd_def)

lemma evnodd_insert: "evnodd (insert (i, j) C) b =
    (if (i + j) mod # 2 = b
      then insert (i, j) (evnodd C b) else evnodd C b)"
  by (simp add: evnodd_def) blast


subsection {* Dominoes *}

consts
  domino :: "(nat * nat) set set"

inductive domino
  intros
    horiz: "{(i, j), (i, j + 1)} : domino"
    vertl: "{(i, j), (i + 1, j)} : domino"

lemma dominoes_tile_row:
  "{i} <*> below (# 2 * n) : tiling domino"
  (is "?P n" is "?B n : ?T")
proof (induct n)
  show "?P 0" by (simp add: below_0 tiling.empty)

  fix n assume hyp: "?P n"
  let ?a = "{i} <*> {# 2 * n + 1} Un {i} <*> {# 2 * n}"

  have "?B (Suc n) = ?a Un ?B n"
    by (auto simp add: Sigma_Suc Un_assoc)
  also have "... : ?T"
  proof (rule tiling.Un)
    have "{(i, # 2 * n), (i, # 2 * n + 1)} : domino"
      by (rule domino.horiz)
    also have "{(i, # 2 * n), (i, # 2 * n + 1)} = ?a" by blast
    finally show "... : domino" .
    from hyp show "?B n : ?T" .
    show "?a <= - ?B n" by blast
  qed
  finally show "?P (Suc n)" .
qed

lemma dominoes_tile_matrix:
  "below m <*> below (# 2 * n) : tiling domino"
  (is "?P m" is "?B m : ?T")
proof (induct m)
  show "?P 0" by (simp add: below_0 tiling.empty)

  fix m assume hyp: "?P m"
  let ?t = "{m} <*> below (# 2 * n)"

  have "?B (Suc m) = ?t Un ?B m" by (simp add: Sigma_Suc)
  also have "... : ?T"
  proof (rule tiling_Un)
    show "?t : ?T" by (rule dominoes_tile_row)
    from hyp show "?B m : ?T" .
    show "?t Int ?B m = {}" by blast
  qed
  finally show "?P (Suc m)" .
qed

lemma domino_singleton:
  "d : domino ==> b < # 2 ==> EX i j. evnodd d b = {(i, j)}"
proof -
  assume b: "b < # 2"
  assume "d : domino"
  thus ?thesis (is "?P d")
  proof induct
    from b have b_cases: "b = 0 | b = 1" by arith
    fix i j
    note [simp] = evnodd_empty evnodd_insert mod_Suc
    from b_cases show "?P {(i, j), (i, j + 1)}" by rule auto
    from b_cases show "?P {(i, j), (i + 1, j)}" by rule auto
  qed
qed

lemma domino_finite: "d: domino ==> finite d"
proof -
  assume "d: domino"
  thus ?thesis
  proof induct
    fix i j :: nat
    show "finite {(i, j), (i, j + 1)}" by (intro Finites.intros)
    show "finite {(i, j), (i + 1, j)}" by (intro Finites.intros)
  qed
qed


subsection {* Tilings of dominoes *}

lemma tiling_domino_finite:
  "t : tiling domino ==> finite t" (is "t : ?T ==> ?F t")
proof -
  assume "t : ?T"
  thus "?F t"
  proof induct
    show "?F {}" by (rule Finites.emptyI)
    fix a t assume "?F t"
    assume "a : domino" hence "?F a" by (rule domino_finite)
    thus "?F (a Un t)" by (rule finite_UnI)
  qed
qed

lemma tiling_domino_01:
  "t : tiling domino ==> card (evnodd t 0) = card (evnodd t 1)"
  (is "t : ?T ==> ?P t")
proof -
  assume "t : ?T"
  thus "?P t"
  proof induct
    show "?P {}" by (simp add: evnodd_def)

    fix a t
    let ?e = evnodd
    assume "a : domino" and "t : ?T"
      and hyp: "card (?e t 0) = card (?e t 1)"
      and at: "a <= - t"

    have card_suc:
      "!!b. b < # 2 ==> card (?e (a Un t) b) = Suc (card (?e t b))"
    proof -
      fix b :: nat assume "b < # 2"
      have "?e (a Un t) b = ?e a b Un ?e t b" by (rule evnodd_Un)
      also obtain i j where e: "?e a b = {(i, j)}"
      proof -
        have "EX i j. ?e a b = {(i, j)}" by (rule domino_singleton)
        thus ?thesis by (blast intro: that)
      qed
      also have "... Un ?e t b = insert (i, j) (?e t b)" by simp
      also have "card ... = Suc (card (?e t b))"
      proof (rule card_insert_disjoint)
        show "finite (?e t b)"
          by (rule evnodd_finite, rule tiling_domino_finite)
        from e have "(i, j) : ?e a b" by simp
        with at show "(i, j) ~: ?e t b" by (blast dest: evnoddD)
      qed
      finally show "?thesis b" .
    qed
    hence "card (?e (a Un t) 0) = Suc (card (?e t 0))" by simp
    also from hyp have "card (?e t 0) = card (?e t 1)" .
    also from card_suc have "Suc ... = card (?e (a Un t) 1)"
      by simp
    finally show "?P (a Un t)" .
  qed
qed


subsection {* Main theorem *}

constdefs
  mutilated_board :: "nat => nat => (nat * nat) set"
  "mutilated_board m n ==
    below (# 2 * (m + 1)) <*> below (# 2 * (n + 1))
      - {(0, 0)} - {(# 2 * m + 1, # 2 * n + 1)}"

theorem mutil_not_tiling: "mutilated_board m n ~: tiling domino"
proof (unfold mutilated_board_def)
  let ?T = "tiling domino"
  let ?t = "below (# 2 * (m + 1)) <*> below (# 2 * (n + 1))"
  let ?t' = "?t - {(0, 0)}"
  let ?t'' = "?t' - {(# 2 * m + 1, # 2 * n + 1)}"

  show "?t'' ~: ?T"
  proof
    have t: "?t : ?T" by (rule dominoes_tile_matrix)
    assume t'': "?t'' : ?T"

    let ?e = evnodd
    have fin: "finite (?e ?t 0)"
      by (rule evnodd_finite, rule tiling_domino_finite, rule t)

    note [simp] = evnodd_iff evnodd_empty evnodd_insert evnodd_Diff
    have "card (?e ?t'' 0) < card (?e ?t' 0)"
    proof -
      have "card (?e ?t' 0 - {(# 2 * m + 1, # 2 * n + 1)})
        < card (?e ?t' 0)"
      proof (rule card_Diff1_less)
        from _ fin show "finite (?e ?t' 0)"
          by (rule finite_subset) auto
        show "(# 2 * m + 1, # 2 * n + 1) : ?e ?t' 0" by simp
      qed
      thus ?thesis by simp
    qed
    also have "... < card (?e ?t 0)"
    proof -
      have "(0, 0) : ?e ?t 0" by simp
      with fin have "card (?e ?t 0 - {(0, 0)}) < card (?e ?t 0)"
        by (rule card_Diff1_less)
      thus ?thesis by simp
    qed
    also from t have "... = card (?e ?t 1)"
      by (rule tiling_domino_01)
    also have "?e ?t 1 = ?e ?t'' 1" by simp
    also from t'' have "card ... = card (?e ?t'' 0)"
      by (rule tiling_domino_01 [symmetric])
    finally have "... < ..." . thus False ..
  qed
qed

end
