theory Product_Measure
imports Lebesgue_Integration
begin

lemma times_Int_times: "A \<times> B \<inter> C \<times> D = (A \<inter> C) \<times> (B \<inter> D)"
  by auto

lemma Pair_vimage_times[simp]: "\<And>A B x. Pair x -` (A \<times> B) = (if x \<in> A then B else {})"
  by auto

lemma rev_Pair_vimage_times[simp]: "\<And>A B y. (\<lambda>x. (x, y)) -` (A \<times> B) = (if y \<in> B then A else {})"
  by auto

lemma case_prod_distrib: "f (case x of (x, y) \<Rightarrow> g x y) = (case x of (x, y) \<Rightarrow> f (g x y))"
  by (cases x) simp

abbreviation
  "Pi\<^isub>E A B \<equiv> Pi A B \<inter> extensional A"

abbreviation
  funcset_extensional :: "['a set, 'b set] => ('a => 'b) set"
    (infixr "->\<^isub>E" 60) where
  "A ->\<^isub>E B \<equiv> Pi\<^isub>E A (%_. B)"

notation (xsymbols)
  funcset_extensional  (infixr "\<rightarrow>\<^isub>E" 60)

lemma extensional_empty[simp]: "extensional {} = {\<lambda>x. undefined}"
  by safe (auto simp add: extensional_def fun_eq_iff)

lemma extensional_insert[intro, simp]:
  assumes "a \<in> extensional (insert i I)"
  shows "a(i := b) \<in> extensional (insert i I)"
  using assms unfolding extensional_def by auto

lemma extensional_Int[simp]:
  "extensional I \<inter> extensional I' = extensional (I \<inter> I')"
  unfolding extensional_def by auto

definition
  "merge I x J y = (\<lambda>i. if i \<in> I then x i else if i \<in> J then y i else undefined)"

lemma merge_apply[simp]:
  "I \<inter> J = {} \<Longrightarrow> i \<in> I \<Longrightarrow> merge I x J y i = x i"
  "I \<inter> J = {} \<Longrightarrow> i \<in> J \<Longrightarrow> merge I x J y i = y i"
  "J \<inter> I = {} \<Longrightarrow> i \<in> I \<Longrightarrow> merge I x J y i = x i"
  "J \<inter> I = {} \<Longrightarrow> i \<in> J \<Longrightarrow> merge I x J y i = y i"
  "i \<notin> I \<Longrightarrow> i \<notin> J \<Longrightarrow> merge I x J y i = undefined"
  unfolding merge_def by auto

lemma merge_commute:
  "I \<inter> J = {} \<Longrightarrow> merge I x J y = merge J y I x"
  by (auto simp: merge_def intro!: ext)

lemma Pi_cancel_merge_range[simp]:
  "I \<inter> J = {} \<Longrightarrow> x \<in> Pi I (merge I A J B) \<longleftrightarrow> x \<in> Pi I A"
  "I \<inter> J = {} \<Longrightarrow> x \<in> Pi I (merge J B I A) \<longleftrightarrow> x \<in> Pi I A"
  "J \<inter> I = {} \<Longrightarrow> x \<in> Pi I (merge I A J B) \<longleftrightarrow> x \<in> Pi I A"
  "J \<inter> I = {} \<Longrightarrow> x \<in> Pi I (merge J B I A) \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: Pi_def)

lemma Pi_cancel_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow> merge I x J y \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  "J \<inter> I = {} \<Longrightarrow> merge I x J y \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  "I \<inter> J = {} \<Longrightarrow> merge I x J y \<in> Pi J B \<longleftrightarrow> y \<in> Pi J B"
  "J \<inter> I = {} \<Longrightarrow> merge I x J y \<in> Pi J B \<longleftrightarrow> y \<in> Pi J B"
  by (auto simp: Pi_def)

lemma extensional_merge[simp]: "merge I x J y \<in> extensional (I \<union> J)"
  by (auto simp: extensional_def)

lemma restrict_Pi_cancel: "restrict x I \<in> Pi I A \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: restrict_def Pi_def)

lemma restrict_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow> restrict (merge I x J y) I = restrict x I"
  "I \<inter> J = {} \<Longrightarrow> restrict (merge I x J y) J = restrict y J"
  "J \<inter> I = {} \<Longrightarrow> restrict (merge I x J y) I = restrict x I"
  "J \<inter> I = {} \<Longrightarrow> restrict (merge I x J y) J = restrict y J"
  by (auto simp: restrict_def intro!: ext)

lemma extensional_insert_undefined[intro, simp]:
  assumes "a \<in> extensional (insert i I)"
  shows "a(i := undefined) \<in> extensional I"
  using assms unfolding extensional_def by auto

lemma extensional_insert_cancel[intro, simp]:
  assumes "a \<in> extensional I"
  shows "a \<in> extensional (insert i I)"
  using assms unfolding extensional_def by auto

lemma PiE_Int: "(Pi\<^isub>E I A) \<inter> (Pi\<^isub>E I B) = Pi\<^isub>E I (\<lambda>x. A x \<inter> B x)"
  by auto

lemma Pi_cancel_fupd_range[simp]: "i \<notin> I \<Longrightarrow> x \<in> Pi I (B(i := b)) \<longleftrightarrow> x \<in> Pi I B"
  by (auto simp: Pi_def)

lemma Pi_split_insert_domain[simp]: "x \<in> Pi (insert i I) X \<longleftrightarrow> x \<in> Pi I X \<and> x i \<in> X i"
  by (auto simp: Pi_def)

lemma Pi_split_domain[simp]: "x \<in> Pi (I \<union> J) X \<longleftrightarrow> x \<in> Pi I X \<and> x \<in> Pi J X"
  by (auto simp: Pi_def)

lemma Pi_cancel_fupd[simp]: "i \<notin> I \<Longrightarrow> x(i := a) \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  by (auto simp: Pi_def)

section "Binary products"

definition
  "pair_algebra A B = \<lparr> space = space A \<times> space B,
                           sets = {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B} \<rparr>"

locale pair_sigma_algebra = M1: sigma_algebra M1 + M2: sigma_algebra M2
  for M1 M2

abbreviation (in pair_sigma_algebra)
  "E \<equiv> pair_algebra M1 M2"

abbreviation (in pair_sigma_algebra)
  "P \<equiv> sigma E"

sublocale pair_sigma_algebra \<subseteq> sigma_algebra P
  using M1.sets_into_space M2.sets_into_space
  by (force simp: pair_algebra_def intro!: sigma_algebra_sigma)

lemma pair_algebraI[intro, simp]:
  "x \<in> sets A \<Longrightarrow> y \<in> sets B \<Longrightarrow> x \<times> y \<in> sets (pair_algebra A B)"
  by (auto simp add: pair_algebra_def)

lemma space_pair_algebra:
  "space (pair_algebra A B) = space A \<times> space B"
  by (simp add: pair_algebra_def)

lemma pair_algebra_Int_snd:
  assumes "sets S1 \<subseteq> Pow (space S1)"
  shows "pair_algebra S1 (algebra.restricted_space S2 A) =
         algebra.restricted_space (pair_algebra S1 S2) (space S1 \<times> A)"
  (is "?L = ?R")
proof (intro algebra.equality set_eqI iffI)
  fix X assume "X \<in> sets ?L"
  then obtain A1 A2 where X: "X = A1 \<times> (A \<inter> A2)" and "A1 \<in> sets S1" "A2 \<in> sets S2"
    by (auto simp: pair_algebra_def)
  then show "X \<in> sets ?R" unfolding pair_algebra_def
    using assms apply simp by (intro image_eqI[of _ _ "A1 \<times> A2"]) auto
next
  fix X assume "X \<in> sets ?R"
  then obtain A1 A2 where "X = space S1 \<times> A \<inter> A1 \<times> A2" "A1 \<in> sets S1" "A2 \<in> sets S2"
    by (auto simp: pair_algebra_def)
  moreover then have "X = A1 \<times> (A \<inter> A2)"
    using assms by auto
  ultimately show "X \<in> sets ?L"
    unfolding pair_algebra_def by auto
qed (auto simp add: pair_algebra_def)

lemma (in pair_sigma_algebra)
  shows measurable_fst[intro!, simp]:
    "fst \<in> measurable P M1" (is ?fst)
  and measurable_snd[intro!, simp]:
    "snd \<in> measurable P M2" (is ?snd)
proof -
  { fix X assume "X \<in> sets M1"
    then have "\<exists>X1\<in>sets M1. \<exists>X2\<in>sets M2. fst -` X \<inter> space M1 \<times> space M2 = X1 \<times> X2"
      apply - apply (rule bexI[of _ X]) apply (rule bexI[of _ "space M2"])
      using M1.sets_into_space by force+ }
  moreover
  { fix X assume "X \<in> sets M2"
    then have "\<exists>X1\<in>sets M1. \<exists>X2\<in>sets M2. snd -` X \<inter> space M1 \<times> space M2 = X1 \<times> X2"
      apply - apply (rule bexI[of _ "space M1"]) apply (rule bexI[of _ X])
      using M2.sets_into_space by force+ }
  ultimately have "?fst \<and> ?snd"
    by (fastsimp simp: measurable_def sets_sigma space_pair_algebra
                 intro!: sigma_sets.Basic)
  then show ?fst ?snd by auto
qed

lemma (in pair_sigma_algebra) measurable_pair:
  assumes "sigma_algebra M"
  shows "f \<in> measurable M P \<longleftrightarrow>
    (fst \<circ> f) \<in> measurable M M1 \<and> (snd \<circ> f) \<in> measurable M M2"
proof -
  interpret M: sigma_algebra M by fact
  from assms show ?thesis
  proof (safe intro!: measurable_comp[where b=P])
    assume f: "(fst \<circ> f) \<in> measurable M M1" and s: "(snd \<circ> f) \<in> measurable M M2"
    show "f \<in> measurable M P"
    proof (rule M.measurable_sigma)
      show "sets (pair_algebra M1 M2) \<subseteq> Pow (space E)"
        unfolding pair_algebra_def using M1.sets_into_space M2.sets_into_space by auto
      show "f \<in> space M \<rightarrow> space E"
        using f s by (auto simp: mem_Times_iff measurable_def comp_def space_sigma space_pair_algebra)
      fix A assume "A \<in> sets E"
      then obtain B C where "B \<in> sets M1" "C \<in> sets M2" "A = B \<times> C"
        unfolding pair_algebra_def by auto
      moreover have "(fst \<circ> f) -` B \<inter> space M \<in> sets M"
        using f `B \<in> sets M1` unfolding measurable_def by auto
      moreover have "(snd \<circ> f) -` C \<inter> space M \<in> sets M"
        using s `C \<in> sets M2` unfolding measurable_def by auto
      moreover have "f -` A \<inter> space M = ((fst \<circ> f) -` B \<inter> space M) \<inter> ((snd \<circ> f) -` C \<inter> space M)"
        unfolding `A = B \<times> C` by (auto simp: vimage_Times)
      ultimately show "f -` A \<inter> space M \<in> sets M" by auto
    qed
  qed
qed

lemma (in pair_sigma_algebra) measurable_prod_sigma:
  assumes "sigma_algebra M"
  assumes 1: "(fst \<circ> f) \<in> measurable M M1" and 2: "(snd \<circ> f) \<in> measurable M M2"
  shows "f \<in> measurable M P"
proof -
  interpret M: sigma_algebra M by fact
  from 1 have fn1: "fst \<circ> f \<in> space M \<rightarrow> space M1"
     and q1: "\<forall>y\<in>sets M1. (fst \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def)
  from 2 have fn2: "snd \<circ> f \<in> space M \<rightarrow> space M2"
     and q2: "\<forall>y\<in>sets M2. (snd \<circ> f) -` y \<inter> space M \<in> sets M"
    by (auto simp add: measurable_def)
  show ?thesis
  proof (rule M.measurable_sigma)
    show "sets E \<subseteq> Pow (space E)"
      using M1.space_closed M2.space_closed
      by (auto simp add: sigma_algebra_iff pair_algebra_def)
  next
    show "f \<in> space M \<rightarrow> space E"
      by (simp add: space_pair_algebra) (rule prod_final [OF fn1 fn2])
  next
    fix z
    assume z: "z \<in> sets E"
    thus "f -` z \<inter> space M \<in> sets M"
    proof (auto simp add: pair_algebra_def vimage_Times)
      fix x y
      assume x: "x \<in> sets M1" and y: "y \<in> sets M2"
      have "(fst \<circ> f) -` x \<inter> (snd \<circ> f) -` y \<inter> space M =
            ((fst \<circ> f) -` x \<inter> space M) \<inter> ((snd \<circ> f) -` y \<inter> space M)"
        by blast
      also have "...  \<in> sets M" using x y q1 q2
        by blast
      finally show "(fst \<circ> f) -` x \<inter> (snd \<circ> f) -` y \<inter> space M \<in> sets M" .
    qed
  qed
qed

lemma pair_algebraE:
  assumes "X \<in> sets (pair_algebra M1 M2)"
  obtains A B where "X = A \<times> B" "A \<in> sets M1" "B \<in> sets M2"
  using assms unfolding pair_algebra_def by auto

lemma (in pair_sigma_algebra) pair_algebra_swap:
  "(\<lambda>X. (\<lambda>(x,y). (y,x)) -` X \<inter> space M2 \<times> space M1) ` sets E = sets (pair_algebra M2 M1)"
proof (safe elim!: pair_algebraE)
  fix A B assume "A \<in> sets M1" "B \<in> sets M2"
  moreover then have "(\<lambda>(x, y). (y, x)) -` (A \<times> B) \<inter> space M2 \<times> space M1 = B \<times> A"
    using M1.sets_into_space M2.sets_into_space by auto
  ultimately show "(\<lambda>(x, y). (y, x)) -` (A \<times> B) \<inter> space M2 \<times> space M1 \<in> sets (pair_algebra M2 M1)"
    by (auto intro: pair_algebraI)
next
  fix A B assume "A \<in> sets M1" "B \<in> sets M2"
  then show "B \<times> A \<in> (\<lambda>X. (\<lambda>(x, y). (y, x)) -` X \<inter> space M2 \<times> space M1) ` sets E"
    using M1.sets_into_space M2.sets_into_space
    by (auto intro!: image_eqI[where x="A \<times> B"] pair_algebraI)
qed

lemma (in pair_sigma_algebra) sets_pair_sigma_algebra_swap:
  assumes Q: "Q \<in> sets P"
  shows "(\<lambda>(x,y). (y, x)) ` Q \<in> sets (sigma (pair_algebra M2 M1))" (is "_ \<in> sets ?Q")
proof -
  have *: "(\<lambda>(x,y). (y, x)) \<in> space M2 \<times> space M1 \<rightarrow> (space M1 \<times> space M2)"
       "sets (pair_algebra M1 M2) \<subseteq> Pow (space M1 \<times> space M2)"
    using M1.sets_into_space M2.sets_into_space by (auto elim!: pair_algebraE)
  from Q sets_into_space show ?thesis
    by (auto intro!: image_eqI[where x=Q]
             simp: pair_algebra_swap[symmetric] sets_sigma
                   sigma_sets_vimage[OF *] space_pair_algebra)
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_swap_measurable:
  shows "(\<lambda>(x,y). (y, x)) \<in> measurable P (sigma (pair_algebra M2 M1))"
    (is "?f \<in> measurable ?P ?Q")
  unfolding measurable_def
proof (intro CollectI conjI Pi_I ballI)
  fix x assume "x \<in> space ?P" then show "(case x of (x, y) \<Rightarrow> (y, x)) \<in> space ?Q"
    unfolding pair_algebra_def by auto
next
  fix A assume "A \<in> sets ?Q"
  interpret Q: pair_sigma_algebra M2 M1 by default
  have "?f -` A \<inter> space ?P = (\<lambda>(x,y). (y, x)) ` A"
    using Q.sets_into_space `A \<in> sets ?Q` by (auto simp: pair_algebra_def)
  with Q.sets_pair_sigma_algebra_swap[OF `A \<in> sets ?Q`]
  show "?f -` A \<inter> space ?P \<in> sets ?P" by simp
qed

lemma (in pair_sigma_algebra) measurable_cut_fst:
  assumes "Q \<in> sets P" shows "Pair x -` Q \<in> sets M2"
proof -
  let ?Q' = "{Q. Q \<subseteq> space P \<and> Pair x -` Q \<in> sets M2}"
  let ?Q = "\<lparr> space = space P, sets = ?Q' \<rparr>"
  interpret Q: sigma_algebra ?Q
    proof qed (auto simp: vimage_UN vimage_Diff space_pair_algebra)
  have "sets E \<subseteq> sets ?Q"
    using M1.sets_into_space M2.sets_into_space
    by (auto simp: pair_algebra_def space_pair_algebra)
  then have "sets P \<subseteq> sets ?Q"
    by (subst pair_algebra_def, intro Q.sets_sigma_subset)
       (simp_all add: pair_algebra_def)
  with assms show ?thesis by auto
qed

lemma (in pair_sigma_algebra) measurable_cut_snd:
  assumes Q: "Q \<in> sets P" shows "(\<lambda>x. (x, y)) -` Q \<in> sets M1" (is "?cut Q \<in> sets M1")
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  have "Pair y -` (\<lambda>(x, y). (y, x)) ` Q = (\<lambda>x. (x, y)) -` Q" by auto
  with Q.measurable_cut_fst[OF sets_pair_sigma_algebra_swap[OF Q], of y]
  show ?thesis by simp
qed

lemma (in pair_sigma_algebra) measurable_pair_image_snd:
  assumes m: "f \<in> measurable P M" and "x \<in> space M1"
  shows "(\<lambda>y. f (x, y)) \<in> measurable M2 M"
  unfolding measurable_def
proof (intro CollectI conjI Pi_I ballI)
  fix y assume "y \<in> space M2" with `f \<in> measurable P M` `x \<in> space M1`
  show "f (x, y) \<in> space M" unfolding measurable_def pair_algebra_def by auto
next
  fix A assume "A \<in> sets M"
  then have "Pair x -` (f -` A \<inter> space P) \<in> sets M2" (is "?C \<in> _")
    using `f \<in> measurable P M`
    by (intro measurable_cut_fst) (auto simp: measurable_def)
  also have "?C = (\<lambda>y. f (x, y)) -` A \<inter> space M2"
    using `x \<in> space M1` by (auto simp: pair_algebra_def)
  finally show "(\<lambda>y. f (x, y)) -` A \<inter> space M2 \<in> sets M2" .
qed

lemma (in pair_sigma_algebra) measurable_pair_image_fst:
  assumes m: "f \<in> measurable P M" and "y \<in> space M2"
  shows "(\<lambda>x. f (x, y)) \<in> measurable M1 M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  from Q.measurable_pair_image_snd[OF measurable_comp `y \<in> space M2`,
                                      OF Q.pair_sigma_algebra_swap_measurable m]
  show ?thesis by simp
qed

lemma (in pair_sigma_algebra) Int_stable_pair_algebra: "Int_stable E"
  unfolding Int_stable_def
proof (intro ballI)
  fix A B assume "A \<in> sets E" "B \<in> sets E"
  then obtain A1 A2 B1 B2 where "A = A1 \<times> A2" "B = B1 \<times> B2"
    "A1 \<in> sets M1" "A2 \<in> sets M2" "B1 \<in> sets M1" "B2 \<in> sets M2"
    unfolding pair_algebra_def by auto
  then show "A \<inter> B \<in> sets E"
    by (auto simp add: times_Int_times pair_algebra_def)
qed

lemma finite_measure_cut_measurable:
  fixes M1 :: "'a algebra" and M2 :: "'b algebra"
  assumes "sigma_finite_measure M1 \<mu>1" "finite_measure M2 \<mu>2"
  assumes "Q \<in> sets (sigma (pair_algebra M1 M2))"
  shows "(\<lambda>x. \<mu>2 (Pair x -` Q)) \<in> borel_measurable M1"
    (is "?s Q \<in> _")
proof -
  interpret M1: sigma_finite_measure M1 \<mu>1 by fact
  interpret M2: finite_measure M2 \<mu>2 by fact
  interpret pair_sigma_algebra M1 M2 by default
  have [intro]: "sigma_algebra M1" by fact
  have [intro]: "sigma_algebra M2" by fact
  let ?D = "\<lparr> space = space P, sets = {A\<in>sets P. ?s A \<in> borel_measurable M1}  \<rparr>"
  note space_pair_algebra[simp]
  interpret dynkin_system ?D
  proof (intro dynkin_systemI)
    fix A assume "A \<in> sets ?D" then show "A \<subseteq> space ?D"
      using sets_into_space by simp
  next
    from top show "space ?D \<in> sets ?D"
      by (auto simp add: if_distrib intro!: M1.measurable_If)
  next
    fix A assume "A \<in> sets ?D"
    with sets_into_space have "\<And>x. \<mu>2 (Pair x -` (space M1 \<times> space M2 - A)) =
        (if x \<in> space M1 then \<mu>2 (space M2) - ?s A x else 0)"
      by (auto intro!: M2.finite_measure_compl measurable_cut_fst
               simp: vimage_Diff)
    with `A \<in> sets ?D` top show "space ?D - A \<in> sets ?D"
      by (auto intro!: Diff M1.measurable_If M1.borel_measurable_pinfreal_diff)
  next
    fix F :: "nat \<Rightarrow> ('a\<times>'b) set" assume "disjoint_family F" "range F \<subseteq> sets ?D"
    moreover then have "\<And>x. \<mu>2 (\<Union>i. Pair x -` F i) = (\<Sum>\<^isub>\<infinity> i. ?s (F i) x)"
      by (intro M2.measure_countably_additive[symmetric])
         (auto intro!: measurable_cut_fst simp: disjoint_family_on_def)
    ultimately show "(\<Union>i. F i) \<in> sets ?D"
      by (auto simp: vimage_UN intro!: M1.borel_measurable_psuminf)
  qed
  have "P = ?D"
  proof (intro dynkin_lemma)
    show "Int_stable E" by (rule Int_stable_pair_algebra)
    from M1.sets_into_space have "\<And>A. A \<in> sets M1 \<Longrightarrow> {x \<in> space M1. x \<in> A} = A"
      by auto
    then show "sets E \<subseteq> sets ?D"
      by (auto simp: pair_algebra_def sets_sigma if_distrib
               intro: sigma_sets.Basic intro!: M1.measurable_If)
  qed auto
  with `Q \<in> sets P` have "Q \<in> sets ?D" by simp
  then show "?s Q \<in> borel_measurable M1" by simp
qed

subsection {* Binary products of $\sigma$-finite measure spaces *}

locale pair_sigma_finite = M1: sigma_finite_measure M1 \<mu>1 + M2: sigma_finite_measure M2 \<mu>2
  for M1 \<mu>1 M2 \<mu>2

sublocale pair_sigma_finite \<subseteq> pair_sigma_algebra M1 M2
  by default

lemma (in pair_sigma_finite) measure_cut_measurable_fst:
  assumes "Q \<in> sets P" shows "(\<lambda>x. \<mu>2 (Pair x -` Q)) \<in> borel_measurable M1" (is "?s Q \<in> _")
proof -
  have [intro]: "sigma_algebra M1" and [intro]: "sigma_algebra M2" by default+
  have M1: "sigma_finite_measure M1 \<mu>1" by default

  from M2.disjoint_sigma_finite guess F .. note F = this
  let "?C x i" = "F i \<inter> Pair x -` Q"
  { fix i
    let ?R = "M2.restricted_space (F i)"
    have [simp]: "space M1 \<times> F i \<inter> space M1 \<times> space M2 = space M1 \<times> F i"
      using F M2.sets_into_space by auto
    have "(\<lambda>x. \<mu>2 (Pair x -` (space M1 \<times> F i \<inter> Q))) \<in> borel_measurable M1"
    proof (intro finite_measure_cut_measurable[OF M1])
      show "finite_measure (M2.restricted_space (F i)) \<mu>2"
        using F by (intro M2.restricted_to_finite_measure) auto
      have "space M1 \<times> F i \<in> sets P"
        using M1.top F by blast
      from sigma_sets_Int[symmetric,
        OF this[unfolded pair_sigma_algebra_def sets_sigma]]
      show "(space M1 \<times> F i) \<inter> Q \<in> sets (sigma (pair_algebra M1 ?R))"
        using `Q \<in> sets P`
        using pair_algebra_Int_snd[OF M1.space_closed, of "F i" M2]
        by (auto simp: pair_algebra_def sets_sigma)
    qed
    moreover have "\<And>x. Pair x -` (space M1 \<times> F i \<inter> Q) = ?C x i"
      using `Q \<in> sets P` sets_into_space by (auto simp: space_pair_algebra)
    ultimately have "(\<lambda>x. \<mu>2 (?C x i)) \<in> borel_measurable M1"
      by simp }
  moreover
  { fix x
    have "(\<Sum>\<^isub>\<infinity>i. \<mu>2 (?C x i)) = \<mu>2 (\<Union>i. ?C x i)"
    proof (intro M2.measure_countably_additive)
      show "range (?C x) \<subseteq> sets M2"
        using F `Q \<in> sets P` by (auto intro!: M2.Int measurable_cut_fst)
      have "disjoint_family F" using F by auto
      show "disjoint_family (?C x)"
        by (rule disjoint_family_on_bisimulation[OF `disjoint_family F`]) auto
    qed
    also have "(\<Union>i. ?C x i) = Pair x -` Q"
      using F sets_into_space `Q \<in> sets P`
      by (auto simp: space_pair_algebra)
    finally have "\<mu>2 (Pair x -` Q) = (\<Sum>\<^isub>\<infinity>i. \<mu>2 (?C x i))"
      by simp }
  ultimately show ?thesis
    by (auto intro!: M1.borel_measurable_psuminf)
qed

lemma (in pair_sigma_finite) measure_cut_measurable_snd:
  assumes "Q \<in> sets P" shows "(\<lambda>y. \<mu>1 ((\<lambda>x. (x, y)) -` Q)) \<in> borel_measurable M2"
proof -
  interpret Q: pair_sigma_finite M2 \<mu>2 M1 \<mu>1 by default
  have [simp]: "\<And>y. (Pair y -` (\<lambda>(x, y). (y, x)) ` Q) = (\<lambda>x. (x, y)) -` Q"
    by auto
  note sets_pair_sigma_algebra_swap[OF assms]
  from Q.measure_cut_measurable_fst[OF this]
  show ?thesis by simp
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_measurable:
  assumes "f \<in> measurable P M"
  shows "(\<lambda>(x,y). f (y, x)) \<in> measurable (sigma (pair_algebra M2 M1)) M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  have *: "(\<lambda>(x,y). f (y, x)) = f \<circ> (\<lambda>(x,y). (y, x))" by (simp add: fun_eq_iff)
  show ?thesis
    using Q.pair_sigma_algebra_swap_measurable assms
    unfolding * by (rule measurable_comp)
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_swap:
  "sigma (pair_algebra M2 M1) = (vimage_algebra (space M2 \<times> space M1) (\<lambda>(x, y). (y, x)))"
  unfolding vimage_algebra_def
  apply (simp add: sets_sigma)
  apply (subst sigma_sets_vimage[symmetric])
  apply (fastsimp simp: pair_algebra_def)
  using M1.sets_into_space M2.sets_into_space apply (fastsimp simp: pair_algebra_def)
proof -
  have "(\<lambda>X. (\<lambda>(x, y). (y, x)) -` X \<inter> space M2 \<times> space M1) ` sets E
    = sets (pair_algebra M2 M1)" (is "?S = _")
    by (rule pair_algebra_swap)
  then show "sigma (pair_algebra M2 M1) = \<lparr>space = space M2 \<times> space M1,
       sets = sigma_sets (space M2 \<times> space M1) ?S\<rparr>"
    by (simp add: pair_algebra_def sigma_def)
qed

definition (in pair_sigma_finite)
  "pair_measure A = M1.positive_integral (\<lambda>x.
    M2.positive_integral (\<lambda>y. indicator A (x, y)))"

lemma (in pair_sigma_finite) pair_measure_alt:
  assumes "A \<in> sets P"
  shows "pair_measure A = M1.positive_integral (\<lambda>x. \<mu>2 (Pair x -` A))"
  unfolding pair_measure_def
proof (rule M1.positive_integral_cong)
  fix x assume "x \<in> space M1"
  have *: "\<And>y. indicator A (x, y) = (indicator (Pair x -` A) y :: pinfreal)"
    unfolding indicator_def by auto
  show "M2.positive_integral (\<lambda>y. indicator A (x, y)) = \<mu>2 (Pair x -` A)"
    unfolding *
    apply (subst M2.positive_integral_indicator)
    apply (rule measurable_cut_fst[OF assms])
    by simp
qed

lemma (in pair_sigma_finite) pair_measure_times:
  assumes A: "A \<in> sets M1" and "B \<in> sets M2"
  shows "pair_measure (A \<times> B) = \<mu>1 A * \<mu>2 B"
proof -
  from assms have "pair_measure (A \<times> B) =
      M1.positive_integral (\<lambda>x. \<mu>2 B * indicator A x)"
    by (auto intro!: M1.positive_integral_cong simp: pair_measure_alt)
  with assms show ?thesis
    by (simp add: M1.positive_integral_cmult_indicator ac_simps)
qed

lemma (in pair_sigma_finite) sigma_finite_up_in_pair_algebra:
  "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> sets E \<and> F \<up> space E \<and>
    (\<forall>i. pair_measure (F i) \<noteq> \<omega>)"
proof -
  obtain F1 :: "nat \<Rightarrow> 'a set" and F2 :: "nat \<Rightarrow> 'b set" where
    F1: "range F1 \<subseteq> sets M1" "F1 \<up> space M1" "\<And>i. \<mu>1 (F1 i) \<noteq> \<omega>" and
    F2: "range F2 \<subseteq> sets M2" "F2 \<up> space M2" "\<And>i. \<mu>2 (F2 i) \<noteq> \<omega>"
    using M1.sigma_finite_up M2.sigma_finite_up by auto
  then have space: "space M1 = (\<Union>i. F1 i)" "space M2 = (\<Union>i. F2 i)"
    unfolding isoton_def by auto
  let ?F = "\<lambda>i. F1 i \<times> F2 i"
  show ?thesis unfolding isoton_def space_pair_algebra
  proof (intro exI[of _ ?F] conjI allI)
    show "range ?F \<subseteq> sets E" using F1 F2
      by (fastsimp intro!: pair_algebraI)
  next
    have "space M1 \<times> space M2 \<subseteq> (\<Union>i. ?F i)"
    proof (intro subsetI)
      fix x assume "x \<in> space M1 \<times> space M2"
      then obtain i j where "fst x \<in> F1 i" "snd x \<in> F2 j"
        by (auto simp: space)
      then have "fst x \<in> F1 (max i j)" "snd x \<in> F2 (max j i)"
        using `F1 \<up> space M1` `F2 \<up> space M2`
        by (auto simp: max_def dest: isoton_mono_le)
      then have "(fst x, snd x) \<in> F1 (max i j) \<times> F2 (max i j)"
        by (intro SigmaI) (auto simp add: min_max.sup_commute)
      then show "x \<in> (\<Union>i. ?F i)" by auto
    qed
    then show "(\<Union>i. ?F i) = space M1 \<times> space M2"
      using space by (auto simp: space)
  next
    fix i show "F1 i \<times> F2 i \<subseteq> F1 (Suc i) \<times> F2 (Suc i)"
      using `F1 \<up> space M1` `F2 \<up> space M2` unfolding isoton_def
      by auto
  next
    fix i
    from F1 F2 have "F1 i \<in> sets M1" "F2 i \<in> sets M2" by auto
    with F1 F2 show "pair_measure (F1 i \<times> F2 i) \<noteq> \<omega>"
      by (simp add: pair_measure_times)
  qed
qed

sublocale pair_sigma_finite \<subseteq> sigma_finite_measure P pair_measure
proof
  show "pair_measure {} = 0"
    unfolding pair_measure_def by auto

  show "countably_additive P pair_measure"
    unfolding countably_additive_def
  proof (intro allI impI)
    fix F :: "nat \<Rightarrow> ('a \<times> 'b) set"
    assume F: "range F \<subseteq> sets P" "disjoint_family F"
    from F have *: "\<And>i. F i \<in> sets P" "(\<Union>i. F i) \<in> sets P" by auto
    moreover from F have "\<And>i. (\<lambda>x. \<mu>2 (Pair x -` F i)) \<in> borel_measurable M1"
      by (intro measure_cut_measurable_fst) auto
    moreover have "\<And>x. disjoint_family (\<lambda>i. Pair x -` F i)"
      by (intro disjoint_family_on_bisimulation[OF F(2)]) auto
    moreover have "\<And>x. x \<in> space M1 \<Longrightarrow> range (\<lambda>i. Pair x -` F i) \<subseteq> sets M2"
      using F by (auto intro!: measurable_cut_fst)
    ultimately show "(\<Sum>\<^isub>\<infinity>n. pair_measure (F n)) = pair_measure (\<Union>i. F i)"
      by (simp add: pair_measure_alt vimage_UN M1.positive_integral_psuminf[symmetric]
                    M2.measure_countably_additive
               cong: M1.positive_integral_cong)
  qed

  from sigma_finite_up_in_pair_algebra guess F :: "nat \<Rightarrow> ('a \<times> 'c) set" .. note F = this
  show "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> sets P \<and> (\<Union>i. F i) = space P \<and> (\<forall>i. pair_measure (F i) \<noteq> \<omega>)"
  proof (rule exI[of _ F], intro conjI)
    show "range F \<subseteq> sets P" using F by auto
    show "(\<Union>i. F i) = space P"
      using F by (auto simp: space_pair_algebra isoton_def)
    show "\<forall>i. pair_measure (F i) \<noteq> \<omega>" using F by auto
  qed
qed

lemma (in pair_sigma_finite) pair_measure_alt2:
  assumes "A \<in> sets P"
  shows "pair_measure A = M2.positive_integral (\<lambda>y. \<mu>1 ((\<lambda>x. (x, y)) -` A))"
    (is "_ = ?\<nu> A")
proof -
  from sigma_finite_up_in_pair_algebra guess F :: "nat \<Rightarrow> ('a \<times> 'c) set" .. note F = this
  show ?thesis
  proof (rule measure_unique_Int_stable[where \<nu>="?\<nu>", OF Int_stable_pair_algebra],
         simp_all add: pair_sigma_algebra_def[symmetric])
    show "range F \<subseteq> sets E" "F \<up> space E" "\<And>i. pair_measure (F i) \<noteq> \<omega>"
      using F by auto
    show "measure_space P pair_measure" by default
  next
    show "measure_space P ?\<nu>"
    proof
      show "?\<nu> {} = 0" by auto
      show "countably_additive P ?\<nu>"
        unfolding countably_additive_def
      proof (intro allI impI)
        fix F :: "nat \<Rightarrow> ('a \<times> 'b) set"
        assume F: "range F \<subseteq> sets P" "disjoint_family F"
        from F have *: "\<And>i. F i \<in> sets P" "(\<Union>i. F i) \<in> sets P" by auto
        moreover from F have "\<And>i. (\<lambda>y. \<mu>1 ((\<lambda>x. (x, y)) -` F i)) \<in> borel_measurable M2"
          by (intro measure_cut_measurable_snd) auto
        moreover have "\<And>y. disjoint_family (\<lambda>i. (\<lambda>x. (x, y)) -` F i)"
          by (intro disjoint_family_on_bisimulation[OF F(2)]) auto
        moreover have "\<And>y. y \<in> space M2 \<Longrightarrow> range (\<lambda>i. (\<lambda>x. (x, y)) -` F i) \<subseteq> sets M1"
          using F by (auto intro!: measurable_cut_snd)
        ultimately show "(\<Sum>\<^isub>\<infinity>n. ?\<nu> (F n)) = ?\<nu> (\<Union>i. F i)"
          by (simp add: vimage_UN M2.positive_integral_psuminf[symmetric]
                        M1.measure_countably_additive
                   cong: M2.positive_integral_cong)
      qed
    qed
  next
    fix X assume "X \<in> sets E"
    then obtain A B where X: "X = A \<times> B" and AB: "A \<in> sets M1" "B \<in> sets M2"
      unfolding pair_algebra_def by auto
    show "pair_measure X = ?\<nu> X"
    proof -
      from AB have "?\<nu> (A \<times> B) =
          M2.positive_integral (\<lambda>y. \<mu>1 A * indicator B y)"
        by (auto intro!: M2.positive_integral_cong)
      with AB show ?thesis
        unfolding pair_measure_times[OF AB] X
        by (simp add: M2.positive_integral_cmult_indicator ac_simps)
    qed
  qed fact
qed

section "Fubinis theorem"

lemma (in pair_sigma_finite) simple_function_cut:
  assumes f: "simple_function f"
  shows "(\<lambda>x. M2.positive_integral (\<lambda> y. f (x, y))) \<in> borel_measurable M1"
    and "M1.positive_integral (\<lambda>x. M2.positive_integral (\<lambda>y. f (x, y)))
      = positive_integral f"
proof -
  have f_borel: "f \<in> borel_measurable P"
    using f by (rule borel_measurable_simple_function)
  let "?F z" = "f -` {z} \<inter> space P"
  let "?F' x z" = "Pair x -` ?F z"
  { fix x assume "x \<in> space M1"
    have [simp]: "\<And>z y. indicator (?F z) (x, y) = indicator (?F' x z) y"
      by (auto simp: indicator_def)
    have "\<And>y. y \<in> space M2 \<Longrightarrow> (x, y) \<in> space P" using `x \<in> space M1`
      by (simp add: space_pair_algebra)
    moreover have "\<And>x z. ?F' x z \<in> sets M2" using f_borel
      by (intro borel_measurable_vimage measurable_cut_fst)
    ultimately have "M2.simple_function (\<lambda> y. f (x, y))"
      apply (rule_tac M2.simple_function_cong[THEN iffD2, OF _])
      apply (rule simple_function_indicator_representation[OF f])
      using `x \<in> space M1` by (auto simp del: space_sigma) }
  note M2_sf = this
  { fix x assume x: "x \<in> space M1"
    then have "M2.positive_integral (\<lambda> y. f (x, y)) =
        (\<Sum>z\<in>f ` space P. z * \<mu>2 (?F' x z))"
      unfolding M2.positive_integral_eq_simple_integral[OF M2_sf[OF x]]
      unfolding M2.simple_integral_def
    proof (safe intro!: setsum_mono_zero_cong_left)
      from f show "finite (f ` space P)" by (rule simple_functionD)
    next
      fix y assume "y \<in> space M2" then show "f (x, y) \<in> f ` space P"
        using `x \<in> space M1` by (auto simp: space_pair_algebra)
    next
      fix x' y assume "(x', y) \<in> space P"
        "f (x', y) \<notin> (\<lambda>y. f (x, y)) ` space M2"
      then have *: "?F' x (f (x', y)) = {}"
        by (force simp: space_pair_algebra)
      show  "f (x', y) * \<mu>2 (?F' x (f (x', y))) = 0"
        unfolding * by simp
    qed (simp add: vimage_compose[symmetric] comp_def
                   space_pair_algebra) }
  note eq = this
  moreover have "\<And>z. ?F z \<in> sets P"
    by (auto intro!: f_borel borel_measurable_vimage simp del: space_sigma)
  moreover then have "\<And>z. (\<lambda>x. \<mu>2 (?F' x z)) \<in> borel_measurable M1"
    by (auto intro!: measure_cut_measurable_fst simp del: vimage_Int)
  ultimately
  show "(\<lambda> x. M2.positive_integral (\<lambda> y. f (x, y))) \<in> borel_measurable M1"
    and "M1.positive_integral (\<lambda>x. M2.positive_integral (\<lambda>y. f (x, y)))
    = positive_integral f"
    by (auto simp del: vimage_Int cong: measurable_cong
             intro!: M1.borel_measurable_pinfreal_setsum
             simp add: M1.positive_integral_setsum simple_integral_def
                       M1.positive_integral_cmult
                       M1.positive_integral_cong[OF eq]
                       positive_integral_eq_simple_integral[OF f]
                       pair_measure_alt[symmetric])
qed

lemma (in pair_sigma_finite) positive_integral_fst_measurable:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<lambda> x. M2.positive_integral (\<lambda> y. f (x, y))) \<in> borel_measurable M1"
      (is "?C f \<in> borel_measurable M1")
    and "M1.positive_integral (\<lambda> x. M2.positive_integral (\<lambda> y. f (x, y))) =
      positive_integral f"
proof -
  from borel_measurable_implies_simple_function_sequence[OF f]
  obtain F where F: "\<And>i. simple_function (F i)" "F \<up> f" by auto
  then have F_borel: "\<And>i. F i \<in> borel_measurable P"
    and F_mono: "\<And>i x. F i x \<le> F (Suc i) x"
    and F_SUPR: "\<And>x. (SUP i. F i x) = f x"
    unfolding isoton_def le_fun_def SUPR_fun_expand
    by (auto intro: borel_measurable_simple_function)
  note sf = simple_function_cut[OF F(1)]
  then have "(SUP i. ?C (F i)) \<in> borel_measurable M1"
    using F(1) by (auto intro!: M1.borel_measurable_SUP)
  moreover
  { fix x assume "x \<in> space M1"
    have isotone: "(\<lambda> i y. F i (x, y)) \<up> (\<lambda>y. f (x, y))"
      using `F \<up> f` unfolding isoton_fun_expand
      by (auto simp: isoton_def)
    note measurable_pair_image_snd[OF F_borel`x \<in> space M1`]
    from M2.positive_integral_isoton[OF isotone this]
    have "(SUP i. ?C (F i) x) = ?C f x"
      by (simp add: isoton_def) }
  note SUPR_C = this
  ultimately show "?C f \<in> borel_measurable M1"
    unfolding SUPR_fun_expand by (simp cong: measurable_cong)
  have "positive_integral (\<lambda>x. SUP i. F i x) = (SUP i. positive_integral (F i))"
    using F_borel F_mono
    by (auto intro!: positive_integral_monotone_convergence_SUP[symmetric])
  also have "(SUP i. positive_integral (F i)) =
    (SUP i. M1.positive_integral (\<lambda>x. M2.positive_integral (\<lambda>y. F i (x, y))))"
    unfolding sf(2) by simp
  also have "\<dots> = M1.positive_integral (\<lambda>x. SUP i. M2.positive_integral (\<lambda>y. F i (x, y)))"
    by (auto intro!: M1.positive_integral_monotone_convergence_SUP[OF _ sf(1)]
                     M2.positive_integral_mono F_mono)
  also have "\<dots> = M1.positive_integral (\<lambda>x. M2.positive_integral (\<lambda>y. SUP i. F i (x, y)))"
    using F_borel F_mono
    by (auto intro!: M2.positive_integral_monotone_convergence_SUP
                     M1.positive_integral_cong measurable_pair_image_snd)
  finally show "M1.positive_integral (\<lambda> x. M2.positive_integral (\<lambda> y. f (x, y))) =
      positive_integral f"
    unfolding F_SUPR by simp
qed

lemma (in pair_sigma_finite) positive_integral_snd_measurable:
  assumes f: "f \<in> borel_measurable P"
  shows "M2.positive_integral (\<lambda>y. M1.positive_integral (\<lambda>x. f (x, y))) =
      positive_integral f"
proof -
  interpret Q: pair_sigma_finite M2 \<mu>2 M1 \<mu>1 by default
  have s: "\<And>x y. (case (x, y) of (x, y) \<Rightarrow> f (y, x)) = f (y, x)" by simp
  have t: "(\<lambda>x. f (case x of (x, y) \<Rightarrow> (y, x))) = (\<lambda>(x, y). f (y, x))" by (auto simp: fun_eq_iff)
  have bij: "bij_betw (\<lambda>(x, y). (y, x)) (space M2 \<times> space M1) (space P)"
    by (auto intro!: inj_onI simp: space_pair_algebra bij_betw_def)
  note pair_sigma_algebra_measurable[OF f]
  from Q.positive_integral_fst_measurable[OF this]
  have "M2.positive_integral (\<lambda>y. M1.positive_integral (\<lambda>x. f (x, y))) =
    Q.positive_integral (\<lambda>(x, y). f (y, x))"
    by simp
  also have "\<dots> = positive_integral f"
    unfolding positive_integral_vimage[OF bij, of f] t
    unfolding pair_sigma_algebra_swap[symmetric]
  proof (rule Q.positive_integral_cong_measure[symmetric])
    fix A assume "A \<in> sets Q.P"
    from this Q.sets_pair_sigma_algebra_swap[OF this]
    show "pair_measure ((\<lambda>(x, y). (y, x)) ` A) = Q.pair_measure A"
      by (auto intro!: M1.positive_integral_cong arg_cong[where f=\<mu>2]
               simp: pair_measure_alt Q.pair_measure_alt2)
  qed
  finally show ?thesis .
qed

lemma (in pair_sigma_finite) Fubini:
  assumes f: "f \<in> borel_measurable P"
  shows "M2.positive_integral (\<lambda>y. M1.positive_integral (\<lambda>x. f (x, y))) =
      M1.positive_integral (\<lambda>x. M2.positive_integral (\<lambda>y. f (x, y)))"
  unfolding positive_integral_snd_measurable[OF assms]
  unfolding positive_integral_fst_measurable[OF assms] ..

lemma (in pair_sigma_finite) AE_pair:
  assumes "almost_everywhere (\<lambda>x. Q x)"
  shows "M1.almost_everywhere (\<lambda>x. M2.almost_everywhere (\<lambda>y. Q (x, y)))"
proof -
  obtain N where N: "N \<in> sets P" "pair_measure N = 0" "{x\<in>space P. \<not> Q x} \<subseteq> N"
    using assms unfolding almost_everywhere_def by auto
  show ?thesis
  proof (rule M1.AE_I)
    from N measure_cut_measurable_fst[OF `N \<in> sets P`]
    show "\<mu>1 {x\<in>space M1. \<mu>2 (Pair x -` N) \<noteq> 0} = 0"
      by (simp add: M1.positive_integral_0_iff pair_measure_alt vimage_def)
    show "{x \<in> space M1. \<mu>2 (Pair x -` N) \<noteq> 0} \<in> sets M1"
      by (intro M1.borel_measurable_pinfreal_neq_const measure_cut_measurable_fst N)
    { fix x assume "x \<in> space M1" "\<mu>2 (Pair x -` N) = 0"
      have "M2.almost_everywhere (\<lambda>y. Q (x, y))"
      proof (rule M2.AE_I)
        show "\<mu>2 (Pair x -` N) = 0" by fact
        show "Pair x -` N \<in> sets M2" by (intro measurable_cut_fst N)
        show "{y \<in> space M2. \<not> Q (x, y)} \<subseteq> Pair x -` N"
          using N `x \<in> space M1` unfolding space_sigma space_pair_algebra by auto
      qed }
    then show "{x \<in> space M1. \<not> M2.almost_everywhere (\<lambda>y. Q (x, y))} \<subseteq> {x \<in> space M1. \<mu>2 (Pair x -` N) \<noteq> 0}"
      by auto
  qed
qed

section "Finite product spaces"

section "Products"

locale product_sigma_algebra =
  fixes M :: "'i \<Rightarrow> 'a algebra"
  assumes sigma_algebras: "\<And>i. sigma_algebra (M i)"

locale finite_product_sigma_algebra = product_sigma_algebra M for M :: "'i \<Rightarrow> 'a algebra" +
  fixes I :: "'i set"
  assumes finite_index: "finite I"

syntax
  "_PiE"  :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3PIE _:_./ _)" 10)

syntax (xsymbols)
  "_PiE" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>\<^isub>E _\<in>_./ _)"   10)

syntax (HTML output)
  "_PiE" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>\<^isub>E _\<in>_./ _)"   10)

translations
  "PIE x:A. B" == "CONST Pi\<^isub>E A (%x. B)"

definition
  "product_algebra M I = \<lparr> space = (\<Pi>\<^isub>E i\<in>I. space (M i)), sets = Pi\<^isub>E I ` (\<Pi> i \<in> I. sets (M i)) \<rparr>"

abbreviation (in finite_product_sigma_algebra) "G \<equiv> product_algebra M I"
abbreviation (in finite_product_sigma_algebra) "P \<equiv> sigma G"

sublocale product_sigma_algebra \<subseteq> M: sigma_algebra "M i" for i by (rule sigma_algebras)

lemma (in finite_product_sigma_algebra) product_algebra_into_space:
  "sets G \<subseteq> Pow (space G)"
  using M.sets_into_space unfolding product_algebra_def
  by auto blast

sublocale finite_product_sigma_algebra \<subseteq> sigma_algebra P
  using product_algebra_into_space by (rule sigma_algebra_sigma)

lemma space_product_algebra[simp]:
  "space (product_algebra M I) = Pi\<^isub>E I (\<lambda>i. space (M i))"
  unfolding product_algebra_def by simp

lemma (in finite_product_sigma_algebra) P_empty:
  "I = {} \<Longrightarrow> P = \<lparr> space = {\<lambda>k. undefined}, sets = { {}, {\<lambda>k. undefined} }\<rparr>"
  unfolding product_algebra_def by (simp add: sigma_def image_constant)

lemma (in finite_product_sigma_algebra) in_P[simp, intro]:
  "\<lbrakk> \<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i) \<rbrakk> \<Longrightarrow> Pi\<^isub>E I A \<in> sets P"
  by (auto simp: product_algebra_def sets_sigma intro!: sigma_sets.Basic)

lemma bij_betw_prod_fold:
  assumes "i \<notin> I"
  shows "bij_betw (\<lambda>x. (x(i:=undefined), x i)) (\<Pi>\<^isub>E j\<in>insert i I. space (M j)) ((\<Pi>\<^isub>E j\<in>I. space (M j)) \<times> space (M i))"
    (is "bij_betw ?f ?P ?F")
    using `i \<notin> I`
proof (unfold bij_betw_def, intro conjI set_eqI iffI)
  show "inj_on ?f ?P"
  proof (safe intro!: inj_onI ext)
    fix a b x assume "a(i:=undefined) = b(i:=undefined)" "a i = b i"
    then show "a x = b x"
      by (cases "x = i") (auto simp: fun_eq_iff split: split_if_asm)
  qed
next
  fix X assume *: "X \<in> ?F" show "X \<in> ?f ` ?P"
  proof (cases X)
    case (Pair a b) with * `i \<notin> I` show ?thesis
      by (auto intro!: image_eqI[where x="a (i := b)"] ext simp: extensional_def)
  qed
qed auto

section "Generating set generates also product algebra"

lemma pair_sigma_algebra_sigma:
  assumes 1: "S1 \<up> (space E1)" "range S1 \<subseteq> sets E1" and E1: "sets E1 \<subseteq> Pow (space E1)"
  assumes 2: "S2 \<up> (space E2)" "range S2 \<subseteq> sets E2" and E2: "sets E2 \<subseteq> Pow (space E2)"
  shows "sigma (pair_algebra (sigma E1) (sigma E2)) = sigma (pair_algebra E1 E2)"
    (is "?S = ?E")
proof -
  interpret M1: sigma_algebra "sigma E1" using E1 by (rule sigma_algebra_sigma)
  interpret M2: sigma_algebra "sigma E2" using E2 by (rule sigma_algebra_sigma)
  have P: "sets (pair_algebra E1 E2) \<subseteq> Pow (space E1 \<times> space E2)"
    using E1 E2 by (auto simp add: pair_algebra_def)
  interpret E: sigma_algebra ?E unfolding pair_algebra_def
    using E1 E2 by (intro sigma_algebra_sigma) auto
  { fix A assume "A \<in> sets E1"
    then have "fst -` A \<inter> space ?E = A \<times> (\<Union>i. S2 i)"
      using E1 2 unfolding isoton_def pair_algebra_def by auto
    also have "\<dots> = (\<Union>i. A \<times> S2 i)" by auto
    also have "\<dots> \<in> sets ?E" unfolding pair_algebra_def sets_sigma
      using 2 `A \<in> sets E1`
      by (intro sigma_sets.Union)
         (auto simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "fst -` A \<inter> space ?E \<in> sets ?E" . }
  moreover
  { fix B assume "B \<in> sets E2"
    then have "snd -` B \<inter> space ?E = (\<Union>i. S1 i) \<times> B"
      using E2 1 unfolding isoton_def pair_algebra_def by auto
    also have "\<dots> = (\<Union>i. S1 i \<times> B)" by auto
    also have "\<dots> \<in> sets ?E"
      using 1 `B \<in> sets E2` unfolding pair_algebra_def sets_sigma
      by (intro sigma_sets.Union)
         (auto simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "snd -` B \<inter> space ?E \<in> sets ?E" . }
  ultimately have proj:
    "fst \<in> measurable ?E (sigma E1) \<and> snd \<in> measurable ?E (sigma E2)"
    using E1 E2 by (subst (1 2) E.measurable_iff_sigma)
                   (auto simp: pair_algebra_def sets_sigma)
  { fix A B assume A: "A \<in> sets (sigma E1)" and B: "B \<in> sets (sigma E2)"
    with proj have "fst -` A \<inter> space ?E \<in> sets ?E" "snd -` B \<inter> space ?E \<in> sets ?E"
      unfolding measurable_def by simp_all
    moreover have "A \<times> B = (fst -` A \<inter> space ?E) \<inter> (snd -` B \<inter> space ?E)"
      using A B M1.sets_into_space M2.sets_into_space
      by (auto simp: pair_algebra_def)
    ultimately have "A \<times> B \<in> sets ?E" by auto }
  then have "sigma_sets (space ?E) (sets (pair_algebra (sigma E1) (sigma E2))) \<subseteq> sets ?E"
    by (intro E.sigma_sets_subset) (auto simp add: pair_algebra_def sets_sigma)
  then have subset: "sets ?S \<subseteq> sets ?E"
    by (simp add: sets_sigma pair_algebra_def)
  have "sets ?S = sets ?E"
  proof (intro set_eqI iffI)
    fix A assume "A \<in> sets ?E" then show "A \<in> sets ?S"
      unfolding sets_sigma
    proof induct
      case (Basic A) then show ?case
        by (auto simp: pair_algebra_def sets_sigma intro: sigma_sets.Basic)
    qed (auto intro: sigma_sets.intros simp: pair_algebra_def)
  next
    fix A assume "A \<in> sets ?S" then show "A \<in> sets ?E" using subset by auto
  qed
  then show ?thesis
    by (simp add: pair_algebra_def sigma_def)
qed

lemma Pi_fupd_iff: "i \<in> I \<Longrightarrow> f \<in> Pi I (B(i := A)) \<longleftrightarrow> f \<in> Pi (I - {i}) B \<and> f i \<in> A"
  apply auto
  apply (drule_tac x=x in Pi_mem)
  apply (simp_all split: split_if_asm)
  apply (drule_tac x=i in Pi_mem)
  apply (auto dest!: Pi_mem)
  done

lemma Pi_UN:
  fixes A :: "nat \<Rightarrow> 'i \<Rightarrow> 'a set"
  assumes "finite I" and mono: "\<And>i n m. i \<in> I \<Longrightarrow> n \<le> m \<Longrightarrow> A n i \<subseteq> A m i"
  shows "(\<Union>n. Pi I (A n)) = (\<Pi> i\<in>I. \<Union>n. A n i)"
proof (intro set_eqI iffI)
  fix f assume "f \<in> (\<Pi> i\<in>I. \<Union>n. A n i)"
  then have "\<forall>i\<in>I. \<exists>n. f i \<in> A n i" by auto
  from bchoice[OF this] obtain n where n: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> (A (n i) i)" by auto
  obtain k where k: "\<And>i. i \<in> I \<Longrightarrow> n i \<le> k"
    using `finite I` finite_nat_set_iff_bounded_le[of "n`I"] by auto
  have "f \<in> Pi I (A k)"
  proof (intro Pi_I)
    fix i assume "i \<in> I"
    from mono[OF this, of "n i" k] k[OF this] n[OF this]
    show "f i \<in> A k i" by auto
  qed
  then show "f \<in> (\<Union>n. Pi I (A n))" by auto
qed auto

lemma PiE_cong:
  assumes "\<And>i. i\<in>I \<Longrightarrow> A i = B i"
  shows "Pi\<^isub>E I A = Pi\<^isub>E I B"
  using assms by (auto intro!: Pi_cong)

lemma sigma_product_algebra_sigma_eq:
  assumes "finite I"
  assumes isotone: "\<And>i. i \<in> I \<Longrightarrow> (S i) \<up> (space (E i))"
  assumes sets_into: "\<And>i. i \<in> I \<Longrightarrow> range (S i) \<subseteq> sets (E i)"
  and E: "\<And>i. sets (E i) \<subseteq> Pow (space (E i))"
  shows "sigma (product_algebra (\<lambda>i. sigma (E i)) I) = sigma (product_algebra E I)"
    (is "?S = ?E")
proof cases
  assume "I = {}" then show ?thesis by (simp add: product_algebra_def)
next
  assume "I \<noteq> {}"
  interpret E: sigma_algebra "sigma (E i)" for i
    using E by (rule sigma_algebra_sigma)

  have into_space[intro]: "\<And>i x A. A \<in> sets (E i) \<Longrightarrow> x i \<in> A \<Longrightarrow> x i \<in> space (E i)"
    using E by auto

  interpret G: sigma_algebra ?E
    unfolding product_algebra_def using E
    by (intro sigma_algebra_sigma) (auto dest: Pi_mem)

  { fix A i assume "i \<in> I" and A: "A \<in> sets (E i)"
    then have "(\<lambda>x. x i) -` A \<inter> space ?E = (\<Pi>\<^isub>E j\<in>I. if j = i then A else \<Union>n. S j n) \<inter> space ?E"
      using isotone unfolding isoton_def product_algebra_def by (auto dest: Pi_mem)
    also have "\<dots> = (\<Union>n. (\<Pi>\<^isub>E j\<in>I. if j = i then A else S j n))"
      unfolding product_algebra_def
      apply simp
      apply (subst Pi_UN[OF `finite I`])
      using isotone[THEN isoton_mono_le] apply simp
      apply (simp add: PiE_Int)
      apply (intro PiE_cong)
      using A sets_into by (auto intro!: into_space)
    also have "\<dots> \<in> sets ?E" unfolding product_algebra_def sets_sigma
      using sets_into `A \<in> sets (E i)`
      by (intro sigma_sets.Union)
         (auto simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "(\<lambda>x. x i) -` A \<inter> space ?E \<in> sets ?E" . }
  then have proj:
    "\<And>i. i\<in>I \<Longrightarrow> (\<lambda>x. x i) \<in> measurable ?E (sigma (E i))"
    using E by (subst G.measurable_iff_sigma)
               (auto simp: product_algebra_def sets_sigma)

  { fix A assume A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (sigma (E i))"
    with proj have basic: "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. x i) -` (A i) \<inter> space ?E \<in> sets ?E"
      unfolding measurable_def by simp
    have "Pi\<^isub>E I A = (\<Inter>i\<in>I. (\<lambda>x. x i) -` (A i) \<inter> space ?E)"
      using A E.sets_into_space `I \<noteq> {}` unfolding product_algebra_def by auto blast
    then have "Pi\<^isub>E I A \<in> sets ?E"
      using G.finite_INT[OF `finite I` `I \<noteq> {}` basic, of "\<lambda>i. i"] by simp }
  then have "sigma_sets (space ?E) (sets (product_algebra (\<lambda>i. sigma (E i)) I)) \<subseteq> sets ?E"
    by (intro G.sigma_sets_subset) (auto simp add: sets_sigma product_algebra_def)
  then have subset: "sets ?S \<subseteq> sets ?E"
    by (simp add: sets_sigma product_algebra_def)

  have "sets ?S = sets ?E"
  proof (intro set_eqI iffI)
    fix A assume "A \<in> sets ?E" then show "A \<in> sets ?S"
      unfolding sets_sigma
    proof induct
      case (Basic A) then show ?case
        by (auto simp: sets_sigma product_algebra_def intro: sigma_sets.Basic)
    qed (auto intro: sigma_sets.intros simp: product_algebra_def)
  next
    fix A assume "A \<in> sets ?S" then show "A \<in> sets ?E" using subset by auto
  qed
  then show ?thesis
    by (simp add: product_algebra_def sigma_def)
qed

lemma (in finite_product_sigma_algebra) pair_sigma_algebra_finite_product_space:
  "sigma (pair_algebra P (M i)) = sigma (pair_algebra G (M i))"
proof -
  have "sigma (pair_algebra P (M i)) = sigma (pair_algebra P (sigma (M i)))" by simp
  also have "\<dots> = sigma (pair_algebra G (M i))"
  proof (rule pair_sigma_algebra_sigma)
    show "(\<lambda>_. \<Pi>\<^isub>E i\<in>I. space (M i)) \<up> space G"
      "(\<lambda>_. space (M i)) \<up> space (M i)"
      by (simp_all add: isoton_const)
    show "range (\<lambda>_. \<Pi>\<^isub>E i\<in>I. space (M i)) \<subseteq> sets G" "range (\<lambda>_. space (M i)) \<subseteq> sets (M i)"
      by (auto intro!: image_eqI[where x="\<lambda>i\<in>I. space (M i)"] dest: Pi_mem
               simp: product_algebra_def)
    show "sets G \<subseteq> Pow (space G)" "sets (M i) \<subseteq> Pow (space (M i))"
      using product_algebra_into_space M.sets_into_space by auto
  qed
  finally show ?thesis .
qed

lemma sets_pair_algebra: "sets (pair_algebra N M) = (\<lambda>(x, y). x \<times> y) ` (sets N \<times> sets M)"
  unfolding pair_algebra_def by auto

lemma (in finite_product_sigma_algebra) sigma_pair_algebra_sigma_eq:
  "sigma (pair_algebra (sigma (product_algebra M I)) (sigma (product_algebra M J))) =
   sigma (pair_algebra (product_algebra M I) (product_algebra M J))"
  using M.sets_into_space
  by (intro pair_sigma_algebra_sigma[of "\<lambda>_. \<Pi>\<^isub>E i\<in>I. space (M i)", of _ "\<lambda>_. \<Pi>\<^isub>E i\<in>J. space (M i)"])
     (auto simp: isoton_const product_algebra_def, blast+)

lemma (in product_sigma_algebra) product_product_vimage_algebra:
  assumes [simp]: "I \<inter> J = {}" and "finite I" "finite J"
  shows "sigma_algebra.vimage_algebra
    (sigma (pair_algebra (sigma (product_algebra M I)) (sigma (product_algebra M J))))
    (space (product_algebra M (I \<union> J))) (\<lambda>x. ((\<lambda>i\<in>I. x i), (\<lambda>i\<in>J. x i))) =
    sigma (product_algebra M (I \<union> J))"
    (is "sigma_algebra.vimage_algebra _ (space ?IJ) ?f = sigma ?IJ")
proof -
  have "finite (I \<union> J)" using assms by auto
  interpret I: finite_product_sigma_algebra M I by default fact
  interpret J: finite_product_sigma_algebra M J by default fact
  interpret IJ: finite_product_sigma_algebra M "I \<union> J" by default fact
  interpret pair_sigma_algebra I.P J.P by default

  show "vimage_algebra (space ?IJ) ?f = sigma ?IJ"
    unfolding I.sigma_pair_algebra_sigma_eq
  proof (rule vimage_algebra_sigma)
    from M.sets_into_space
    show "sets (pair_algebra I.G J.G) \<subseteq> Pow (space (pair_algebra I.G J.G))"
      by (auto simp: sets_pair_algebra space_pair_algebra product_algebra_def) blast+
    show "?f \<in> space IJ.G \<rightarrow> space (pair_algebra I.G J.G)"
      by (auto simp: space_pair_algebra product_algebra_def)
    let ?F = "\<lambda>A. ?f -` A \<inter> (space IJ.G)"
    let ?s = "\<lambda>I. Pi\<^isub>E I ` (\<Pi> i\<in>I. sets (M i))"
    { fix A assume "A \<in> sets IJ.G"
      then obtain F where A: "A = Pi\<^isub>E (I \<union> J) F" "F \<in> (\<Pi> i\<in>I. sets (M i))" "F \<in> (\<Pi> i\<in>J. sets (M i))"
        by (auto simp: product_algebra_def)
      show "A \<in> ?F ` sets (pair_algebra I.G J.G)"
          using A M.sets_into_space
          by (auto simp: restrict_Pi_cancel product_algebra_def
                   intro!: image_eqI[where x="Pi\<^isub>E I F \<times> Pi\<^isub>E J F"]) blast+ }
    { fix A assume "A \<in> sets (pair_algebra I.G J.G)"
      then obtain E F where A: "A = Pi\<^isub>E I E \<times> Pi\<^isub>E J F" "E \<in> (\<Pi> i\<in>I. sets (M i))" "F \<in> (\<Pi> i\<in>J. sets (M i))"
        by (auto simp: product_algebra_def sets_pair_algebra)
      then show "?F A \<in> sets IJ.G"
          using A M.sets_into_space
          by (auto simp: restrict_Pi_cancel product_algebra_def
                   intro!: image_eqI[where x="merge I E J F"]) blast+ }
  qed
qed

lemma (in finite_product_sigma_algebra) sigma_pair_algebra_sigma_M_eq:
  "sigma (pair_algebra P (M i)) = sigma (pair_algebra G (M i))"
proof -
  have "sigma (pair_algebra P (sigma (M i))) = sigma (pair_algebra G (M i))"
    using M.sets_into_space
    by (intro pair_sigma_algebra_sigma[of "\<lambda>_. \<Pi>\<^isub>E i\<in>I. space (M i)", of _ "\<lambda>_. space (M i)"])
       (auto simp: isoton_const product_algebra_def, blast+)
  then show ?thesis by simp
qed

lemma (in product_sigma_algebra) product_singleton_vimage_algebra_eq:
  assumes [simp]: "i \<notin> I" "finite I"
  shows "sigma_algebra.vimage_algebra
    (sigma (pair_algebra (sigma (product_algebra M I)) (M i)))
    (space (product_algebra M (insert i I))) (\<lambda>x. ((\<lambda>i\<in>I. x i), x i)) =
    sigma (product_algebra M (insert i I))"
    (is "sigma_algebra.vimage_algebra _ (space ?I') ?f = sigma ?I'")
proof -
  have "finite (insert i I)" using assms by auto
  interpret I: finite_product_sigma_algebra M I by default fact
  interpret I': finite_product_sigma_algebra M "insert i I" by default fact
  interpret pair_sigma_algebra I.P "M i" by default
  show "vimage_algebra (space ?I') ?f = sigma ?I'"
    unfolding I.sigma_pair_algebra_sigma_M_eq
  proof (rule vimage_algebra_sigma)
    from M.sets_into_space
    show "sets (pair_algebra I.G (M i)) \<subseteq> Pow (space (pair_algebra I.G (M i)))"
      by (auto simp: sets_pair_algebra space_pair_algebra product_algebra_def) blast
    show "?f \<in> space I'.G \<rightarrow> space (pair_algebra I.G (M i))"
      by (auto simp: space_pair_algebra product_algebra_def)
    let ?F = "\<lambda>A. ?f -` A \<inter> (space I'.G)"
    { fix A assume "A \<in> sets I'.G"
      then obtain F where A: "A = Pi\<^isub>E (insert i I) F" "F \<in> (\<Pi> i\<in>I. sets (M i))" "F i \<in> sets (M i)"
        by (auto simp: product_algebra_def)
      show "A \<in> ?F ` sets (pair_algebra I.G (M i))"
          using A M.sets_into_space
          by (auto simp: restrict_Pi_cancel product_algebra_def
                   intro!: image_eqI[where x="Pi\<^isub>E I F \<times> F i"]) blast+ }
    { fix A assume "A \<in> sets (pair_algebra I.G (M i))"
      then obtain E F where A: "A = Pi\<^isub>E I E \<times> F" "E \<in> (\<Pi> i\<in>I. sets (M i))" "F \<in> sets (M i)"
        by (auto simp: product_algebra_def sets_pair_algebra)
      then show "?F A \<in> sets I'.G"
          using A M.sets_into_space
          by (auto simp: restrict_Pi_cancel product_algebra_def
                   intro!: image_eqI[where x="E(i:= F)"]) blast+ }
  qed
qed

lemma restrict_fupd[simp]: "i \<notin> I \<Longrightarrow> restrict (f (i := x)) I = restrict f I"
  by (auto simp: restrict_def intro!: ext)

lemma bij_betw_restrict_I_i:
  "i \<notin> I \<Longrightarrow> bij_betw (\<lambda>x. (restrict x I, x i))
    (space (product_algebra M (insert i I)))
    (space (pair_algebra (sigma (product_algebra M I)) (M i)))"
  by (intro bij_betwI[where g="(\<lambda>(x,y). x(i:=y))"])
     (auto simp: space_pair_algebra extensional_def intro!: ext)

lemma (in product_sigma_algebra) product_singleton_vimage_algebra_inv_eq:
  assumes [simp]: "i \<notin> I" "finite I"
  shows "sigma_algebra.vimage_algebra
    (sigma (product_algebra M (insert i I)))
    (space (pair_algebra (sigma (product_algebra M I)) (M i))) (\<lambda>(x,y). x(i:=y)) =
    sigma (pair_algebra (sigma (product_algebra M I)) (M i))"
proof -
  have "finite (insert i I)" using `finite I` by auto
  interpret I: finite_product_sigma_algebra M I by default fact
  interpret I': finite_product_sigma_algebra M "insert i I" by default fact
  interpret pair_sigma_algebra I.P "M i" by default
  show ?thesis
    unfolding product_singleton_vimage_algebra_eq[OF assms, symmetric]
    using bij_betw_restrict_I_i[OF `i \<notin> I`, of M]
    by (rule vimage_vimage_inv[unfolded space_sigma])
       (auto simp: space_pair_algebra product_algebra_def dest: extensional_restrict)
qed

locale product_sigma_finite =
  fixes M :: "'i \<Rightarrow> 'a algebra" and \<mu> :: "'i \<Rightarrow> 'a set \<Rightarrow> pinfreal"
  assumes sigma_finite_measures: "\<And>i. sigma_finite_measure (M i) (\<mu> i)"

locale finite_product_sigma_finite = product_sigma_finite M \<mu> for M :: "'i \<Rightarrow> 'a algebra" and \<mu> +
  fixes I :: "'i set" assumes finite_index': "finite I"

sublocale product_sigma_finite \<subseteq> M: sigma_finite_measure "M i" "\<mu> i" for i
  by (rule sigma_finite_measures)

sublocale product_sigma_finite \<subseteq> product_sigma_algebra
  by default

sublocale finite_product_sigma_finite \<subseteq> finite_product_sigma_algebra
  by default (fact finite_index')

lemma (in finite_product_sigma_finite) sigma_finite_pairs:
  "\<exists>F::'i \<Rightarrow> nat \<Rightarrow> 'a set.
    (\<forall>i\<in>I. range (F i) \<subseteq> sets (M i)) \<and>
    (\<forall>k. \<forall>i\<in>I. \<mu> i (F i k) \<noteq> \<omega>) \<and>
    (\<lambda>k. \<Pi>\<^isub>E i\<in>I. F i k) \<up> space G"
proof -
  have "\<forall>i::'i. \<exists>F::nat \<Rightarrow> 'a set. range F \<subseteq> sets (M i) \<and> F \<up> space (M i) \<and> (\<forall>k. \<mu> i (F k) \<noteq> \<omega>)"
    using M.sigma_finite_up by simp
  from choice[OF this] guess F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set" ..
  then have "\<And>i. range (F i) \<subseteq> sets (M i)" "\<And>i. F i \<up> space (M i)" "\<And>i k. \<mu> i (F i k) \<noteq> \<omega>"
    by auto
  let ?F = "\<lambda>k. \<Pi>\<^isub>E i\<in>I. F i k"
  note space_product_algebra[simp]
  show ?thesis
  proof (intro exI[of _ F] conjI allI isotoneI set_eqI iffI ballI)
    fix i show "range (F i) \<subseteq> sets (M i)" by fact
  next
    fix i k show "\<mu> i (F i k) \<noteq> \<omega>" by fact
  next
    fix A assume "A \<in> (\<Union>i. ?F i)" then show "A \<in> space G"
      using `\<And>i. range (F i) \<subseteq> sets (M i)` M.sets_into_space by auto blast
  next
    fix f assume "f \<in> space G"
    with Pi_UN[OF finite_index, of "\<lambda>k i. F i k"]
      `\<And>i. F i \<up> space (M i)`[THEN isotonD(2)]
      `\<And>i. F i \<up> space (M i)`[THEN isoton_mono_le]
    show "f \<in> (\<Union>i. ?F i)" by auto
  next
    fix i show "?F i \<subseteq> ?F (Suc i)"
      using `\<And>i. F i \<up> space (M i)`[THEN isotonD(1)] by auto
  qed
qed

lemma (in product_sigma_finite) product_measure_exists:
  assumes "finite I"
  shows "\<exists>\<nu>. (\<forall>A\<in>(\<Pi> i\<in>I. sets (M i)). \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. \<mu> i (A i))) \<and>
     sigma_finite_measure (sigma (product_algebra M I)) \<nu>"
using `finite I` proof induct
  case empty then show ?case unfolding product_algebra_def
    by (auto intro!: exI[of _ "\<lambda>A. if A = {} then 0 else 1"] sigma_algebra_sigma
                     sigma_algebra.finite_additivity_sufficient
             simp add: positive_def additive_def sets_sigma sigma_finite_measure_def
                       sigma_finite_measure_axioms_def image_constant)
next
  case (insert i I)
  interpret finite_product_sigma_finite M \<mu> I by default fact
  have "finite (insert i I)" using `finite I` by auto
  interpret I': finite_product_sigma_finite M \<mu> "insert i I" by default fact
  from insert obtain \<nu> where
    prod: "\<And>A. A \<in> (\<Pi> i\<in>I. sets (M i)) \<Longrightarrow> \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. \<mu> i (A i))" and
    "sigma_finite_measure P \<nu>" by auto
  interpret I: sigma_finite_measure P \<nu> by fact
  interpret P: pair_sigma_finite P \<nu> "M i" "\<mu> i" ..

  let ?h = "\<lambda>x. (restrict x I, x i)"
  let ?\<nu> = "\<lambda>A. P.pair_measure (?h ` A)"
  interpret I': measure_space "sigma (product_algebra M (insert i I))" ?\<nu>
    unfolding product_singleton_vimage_algebra_eq[OF `i \<notin> I` `finite I`, symmetric]
    using bij_betw_restrict_I_i[OF `i \<notin> I`, of M]
    by (intro P.measure_space_isomorphic) auto
  show ?case
  proof (intro exI[of _ ?\<nu>] conjI ballI)
    { fix A assume A: "A \<in> (\<Pi> i\<in>insert i I. sets (M i))"
      moreover then have "A \<in> (\<Pi> i\<in>I. sets (M i))" by auto
      moreover have "(\<lambda>x. (restrict x I, x i)) ` Pi\<^isub>E (insert i I) A = Pi\<^isub>E I A \<times> A i"
        using `i \<notin> I`
        apply auto
        apply (rule_tac x="a(i:=b)" in image_eqI)
        apply (auto simp: extensional_def fun_eq_iff)
        done
      ultimately show "?\<nu> (Pi\<^isub>E (insert i I) A) = (\<Prod>i\<in>insert i I. \<mu> i (A i))"
        apply simp
        apply (subst P.pair_measure_times)
        apply fastsimp
        apply fastsimp
        using `i \<notin> I` `finite I` prod[of A] by (auto simp: ac_simps) }
    note product = this
    show "sigma_finite_measure I'.P ?\<nu>"
    proof
      from I'.sigma_finite_pairs guess F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set" ..
      then have F: "\<And>j. j \<in> insert i I \<Longrightarrow> range (F j) \<subseteq> sets (M j)"
        "(\<lambda>k. \<Pi>\<^isub>E j \<in> insert i I. F j k) \<up> space I'.G"
        "\<And>k. \<And>j. j \<in> insert i I \<Longrightarrow> \<mu> j (F j k) \<noteq> \<omega>"
        by blast+
      let "?F k" = "\<Pi>\<^isub>E j \<in> insert i I. F j k"
      show "\<exists>F::nat \<Rightarrow> ('i \<Rightarrow> 'a) set. range F \<subseteq> sets I'.P \<and>
          (\<Union>i. F i) = space I'.P \<and> (\<forall>i. ?\<nu> (F i) \<noteq> \<omega>)"
      proof (intro exI[of _ ?F] conjI allI)
        show "range ?F \<subseteq> sets I'.P" using F(1) by auto
      next
        from F(2)[THEN isotonD(2)]
        show "(\<Union>i. ?F i) = space I'.P" by simp
      next
        fix j
        show "?\<nu> (?F j) \<noteq> \<omega>"
          using F `finite I`
          by (subst product) (auto simp: setprod_\<omega>)
      qed
    qed
  qed
qed

definition (in finite_product_sigma_finite)
  measure :: "('i \<Rightarrow> 'a) set \<Rightarrow> pinfreal" where
  "measure = (SOME \<nu>.
     (\<forall>A\<in>\<Pi> i\<in>I. sets (M i). \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. \<mu> i (A i))) \<and>
     sigma_finite_measure P \<nu>)"

sublocale finite_product_sigma_finite \<subseteq> sigma_finite_measure P measure
proof -
  show "sigma_finite_measure P measure"
    unfolding measure_def
    by (rule someI2_ex[OF product_measure_exists[OF finite_index]]) auto
qed

lemma (in finite_product_sigma_finite) measure_times:
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  shows "measure (Pi\<^isub>E I A) = (\<Prod>i\<in>I. \<mu> i (A i))"
proof -
  note ex = product_measure_exists[OF finite_index]
  show ?thesis
    unfolding measure_def
  proof (rule someI2_ex[OF ex], elim conjE)
    fix \<nu> assume *: "\<forall>A\<in>\<Pi> i\<in>I. sets (M i). \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. \<mu> i (A i))"
    have "Pi\<^isub>E I A = Pi\<^isub>E I (\<lambda>i\<in>I. A i)" by (auto dest: Pi_mem)
    then have "\<nu> (Pi\<^isub>E I A) = \<nu> (Pi\<^isub>E I (\<lambda>i\<in>I. A i))" by simp
    also have "\<dots> = (\<Prod>i\<in>I. \<mu> i ((\<lambda>i\<in>I. A i) i))" using assms * by auto
    finally show "\<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. \<mu> i (A i))" by simp
  qed
qed

abbreviation (in product_sigma_finite)
  "product_measure I \<equiv> finite_product_sigma_finite.measure M \<mu> I"

abbreviation (in product_sigma_finite)
  "product_positive_integral I \<equiv>
    measure_space.positive_integral (sigma (product_algebra M I)) (product_measure I)"

abbreviation (in product_sigma_finite)
  "product_integral I \<equiv>
    measure_space.integral (sigma (product_algebra M I)) (product_measure I)"

lemma (in product_sigma_finite) positive_integral_empty:
  "product_positive_integral {} f = f (\<lambda>k. undefined)"
proof -
  interpret finite_product_sigma_finite M \<mu> "{}" by default (fact finite.emptyI)
  have "\<And>A. measure (Pi\<^isub>E {} A) = 1"
    using assms by (subst measure_times) auto
  then show ?thesis
    unfolding positive_integral_alt simple_function_def simple_integral_def_raw
  proof (simp add: P_empty, intro antisym)
    show "f (\<lambda>k. undefined) \<le> (SUP f:{g. g \<le> f}. f (\<lambda>k. undefined))"
      by (intro le_SUPI) auto
    show "(SUP f:{g. g \<le> f}. f (\<lambda>k. undefined)) \<le> f (\<lambda>k. undefined)"
      by (intro SUP_leI) (auto simp: le_fun_def)
  qed
qed

lemma merge_restrict[simp]:
  "merge I (restrict x I) J y = merge I x J y"
  "merge I x J (restrict y J) = merge I x J y"
  unfolding merge_def by (auto intro!: ext)

lemma merge_x_x_eq_restrict[simp]:
  "merge I x J x = restrict x (I \<union> J)"
  unfolding merge_def by (auto intro!: ext)

lemma bij_betw_restrict_I_J:
  "I \<inter> J = {} \<Longrightarrow> bij_betw (\<lambda>x. (restrict x I, restrict x J))
    (space (product_algebra M (I \<union> J)))
    (space (pair_algebra (sigma (product_algebra M I)) (sigma (product_algebra M J))))"
  by (intro bij_betwI[where g="\<lambda>(x,y). merge I x J y"])
     (auto dest: extensional_restrict simp: space_pair_algebra)

lemma (in product_sigma_algebra) product_product_vimage_algebra_eq:
  assumes [simp]: "I \<inter> J = {}" and "finite I" "finite J"
  shows "sigma_algebra.vimage_algebra
    (sigma (product_algebra M (I \<union> J)))
    (space (sigma (pair_algebra (sigma (product_algebra M I)) (sigma (product_algebra M J)))))
    (\<lambda>(x, y). merge I x J y) =
    sigma (pair_algebra (sigma (product_algebra M I)) (sigma (product_algebra M J)))"
  (is "sigma_algebra.vimage_algebra ?IJ ?S ?m = ?P")
proof -
  interpret I: finite_product_sigma_algebra M I by default fact
  interpret J: finite_product_sigma_algebra M J by default fact
  have "finite (I \<union> J)" using assms by auto
  interpret IJ: finite_product_sigma_algebra M "I \<union> J" by default fact
  interpret P: pair_sigma_algebra I.P J.P by default

  let ?g = "\<lambda>x. (restrict x I, restrict x J)"
  let ?f = "\<lambda>(x, y). merge I x J y"
  show "IJ.vimage_algebra (space P.P) ?f = P.P"
    using bij_betw_restrict_I_J[OF `I \<inter> J = {}`]
    by (subst P.vimage_vimage_inv[of ?g "space IJ.G" ?f,
                   unfolded product_product_vimage_algebra[OF assms]])
       (auto simp: pair_algebra_def dest: extensional_restrict)
qed

lemma (in product_sigma_finite) measure_fold_left:
  assumes IJ[simp]: "I \<inter> J = {}" and fin: "finite I" "finite J"
  and f: "f \<in> borel_measurable (sigma (product_algebra M (I \<union> J)))"
  shows "product_positive_integral (I \<union> J) f =
    product_positive_integral I (\<lambda>x. product_positive_integral J (\<lambda>y. f (merge I x J y)))"
proof -
  interpret I: finite_product_sigma_finite M \<mu> I by default fact
  interpret J: finite_product_sigma_finite M \<mu> J by default fact
  have "finite (I \<union> J)" using fin by auto
  interpret IJ: finite_product_sigma_finite M \<mu> "I \<union> J" by default fact
  interpret P: pair_sigma_finite I.P I.measure J.P J.measure by default
  let ?f = "\<lambda>x. ((\<lambda>i\<in>I. x i), (\<lambda>i\<in>J. x i))"
  have P_borel: "(\<lambda>x. f (case x of (x, y) \<Rightarrow> merge I x J y)) \<in> borel_measurable P.P"
    by (subst product_product_vimage_algebra_eq[OF IJ fin, symmetric])
       (auto simp: space_pair_algebra intro!: IJ.measurable_vimage f)
  have split_f_image[simp]: "\<And>F. ?f ` (Pi\<^isub>E (I \<union> J) F) = (Pi\<^isub>E I F) \<times> (Pi\<^isub>E J F)"
    apply auto apply (rule_tac x="merge I a J b" in image_eqI)
    by (auto dest: extensional_restrict)
  have "IJ.positive_integral f =  IJ.positive_integral (\<lambda>x. f (restrict x (I \<union> J)))"
    by (auto intro!: IJ.positive_integral_cong arg_cong[where f=f] dest!: extensional_restrict)
  also have "\<dots> = I.positive_integral (\<lambda>x. J.positive_integral (\<lambda>y. f (merge I x J y)))"
    unfolding P.positive_integral_fst_measurable[OF P_borel, simplified]
    unfolding P.positive_integral_vimage[unfolded space_sigma, OF bij_betw_restrict_I_J[OF IJ]]
    unfolding product_product_vimage_algebra[OF IJ fin]
  proof (simp, rule IJ.positive_integral_cong_measure[symmetric])
    fix A assume *: "A \<in> sets IJ.P"
    from IJ.sigma_finite_pairs obtain F where
      F: "\<And>i. i\<in> I \<union> J \<Longrightarrow> range (F i) \<subseteq> sets (M i)"
         "(\<lambda>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k) \<up> space IJ.G"
         "\<And>k. \<forall>i\<in>I\<union>J. \<mu> i (F i k) \<noteq> \<omega>"
      by auto
    let ?F = "\<lambda>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k"
    show "P.pair_measure (?f ` A) = IJ.measure A"
    proof (rule measure_unique_Int_stable[OF _ _ _ _ _ _ _ _ *])
      show "Int_stable IJ.G" by (simp add: PiE_Int Int_stable_def product_algebra_def) auto
      show "range ?F \<subseteq> sets IJ.G" using F by (simp add: image_subset_iff product_algebra_def)
      show "?F \<up> space IJ.G " using F(2) by simp
      show "measure_space IJ.P (\<lambda>A. P.pair_measure (?f ` A))"
        unfolding product_product_vimage_algebra[OF IJ fin, symmetric]
        using bij_betw_restrict_I_J[OF IJ, of M]
        by (auto intro!: P.measure_space_isomorphic)
      show "measure_space IJ.P IJ.measure" by fact
    next
      fix A assume "A \<in> sets IJ.G"
      then obtain F where A[simp]: "A = Pi\<^isub>E (I \<union> J) F" "F \<in> (\<Pi> i\<in>I \<union> J. sets (M i))"
        by (auto simp: product_algebra_def)
      then have F: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets (M i)" "\<And>i. i \<in> J \<Longrightarrow> F i \<in> sets (M i)"
        by auto
      have "P.pair_measure (?f ` A) = (\<Prod>i\<in>I. \<mu> i (F i)) * (\<Prod>i\<in>J. \<mu> i (F i))"
        using `finite J` `finite I` F
        by (simp add: P.pair_measure_times I.measure_times J.measure_times)
      also have "\<dots> = (\<Prod>i\<in>I \<union> J. \<mu> i (F i))"
        using `finite J` `finite I` `I \<inter> J = {}`  by (simp add: setprod_Un_one)
      also have "\<dots> = IJ.measure A"
        using `finite J` `finite I` F unfolding A
        by (intro IJ.measure_times[symmetric]) auto
      finally show "P.pair_measure (?f ` A) = IJ.measure A" .
    next
      fix k
      have "\<And>i. i \<in> I \<union> J \<Longrightarrow> F i k \<in> sets (M i)" using F by auto
      then have "P.pair_measure (?f ` ?F k) = (\<Prod>i\<in>I. \<mu> i (F i k)) * (\<Prod>i\<in>J. \<mu> i (F i k))"
        by (simp add: P.pair_measure_times I.measure_times J.measure_times)
      then show "P.pair_measure (?f ` ?F k) \<noteq> \<omega>"
        using `finite I` F by (simp add: setprod_\<omega>)
    qed simp
  qed
  finally show ?thesis .
qed

lemma (in product_sigma_finite) finite_pair_measure_singleton:
  assumes f: "f \<in> borel_measurable (M i)"
  shows "product_positive_integral {i} (\<lambda>x. f (x i)) = M.positive_integral i f"
proof -
  interpret I: finite_product_sigma_finite M \<mu> "{i}" by default simp
  have bij: "bij_betw (\<lambda>x. \<lambda>j\<in>{i}. x) (space (M i)) (space I.P)"
    by (auto intro!: bij_betwI ext simp: extensional_def)
  have *: "(\<lambda>x. (\<lambda>x. \<lambda>j\<in>{i}. x) -` Pi\<^isub>E {i} x \<inter> space (M i)) ` (\<Pi> i\<in>{i}. sets (M i)) = sets (M i)"
  proof (subst image_cong, rule refl)
    fix x assume "x \<in> (\<Pi> i\<in>{i}. sets (M i))"
    then show "(\<lambda>x. \<lambda>j\<in>{i}. x) -` Pi\<^isub>E {i} x \<inter> space (M i) = x i"
      using sets_into_space by auto
  qed auto
  have vimage: "I.vimage_algebra (space (M i)) (\<lambda>x. \<lambda>j\<in>{i}. x) = M i"
    unfolding I.vimage_algebra_def
    unfolding product_sigma_algebra_def sets_sigma
    apply (subst sigma_sets_vimage[symmetric])
    apply (simp_all add: image_image sigma_sets_eq product_algebra_def * del: vimage_Int)
    using sets_into_space by blast
  show "I.positive_integral (\<lambda>x. f (x i)) = M.positive_integral i f"
    unfolding I.positive_integral_vimage[OF bij]
    unfolding vimage
    apply (subst positive_integral_cong_measure)
  proof -
    fix A assume A: "A \<in> sets (M i)"
    have "(\<lambda>x. \<lambda>j\<in>{i}. x) ` A = (\<Pi>\<^isub>E i\<in>{i}. A)"
      by (auto intro!: image_eqI ext[where 'b='a] simp: extensional_def)
    with A show "product_measure {i} ((\<lambda>x. \<lambda>j\<in>{i}. x) ` A) = \<mu> i A"
      using I.measure_times[of "\<lambda>i. A"] by simp
  qed simp
qed

section "Products on finite spaces"

lemma sigma_sets_pair_algebra_finite:
  assumes "finite A" and "finite B"
  shows "sigma_sets (A \<times> B) ((\<lambda>(x,y). x \<times> y) ` (Pow A \<times> Pow B)) = Pow (A \<times> B)"
  (is "sigma_sets ?prod ?sets = _")
proof safe
  have fin: "finite (A \<times> B)" using assms by (rule finite_cartesian_product)
  fix x assume subset: "x \<subseteq> A \<times> B"
  hence "finite x" using fin by (rule finite_subset)
  from this subset show "x \<in> sigma_sets ?prod ?sets"
  proof (induct x)
    case empty show ?case by (rule sigma_sets.Empty)
  next
    case (insert a x)
    hence "{a} \<in> sigma_sets ?prod ?sets"
      by (auto simp: pair_algebra_def intro!: sigma_sets.Basic)
    moreover have "x \<in> sigma_sets ?prod ?sets" using insert by auto
    ultimately show ?case unfolding insert_is_Un[of a x] by (rule sigma_sets_Un)
  qed
next
  fix x a b
  assume "x \<in> sigma_sets ?prod ?sets" and "(a, b) \<in> x"
  from sigma_sets_into_sp[OF _ this(1)] this(2)
  show "a \<in> A" and "b \<in> B" by auto
qed

locale pair_finite_sigma_algebra = M1: finite_sigma_algebra M1 + M2: finite_sigma_algebra M2 for M1 M2

sublocale pair_finite_sigma_algebra \<subseteq> pair_sigma_algebra by default

lemma (in pair_finite_sigma_algebra) finite_pair_sigma_algebra[simp]:
  shows "P = (| space = space M1 \<times> space M2, sets = Pow (space M1 \<times> space M2) |)"
proof -
  show ?thesis using M1.finite_space M2.finite_space
    by (simp add: sigma_def space_pair_algebra sets_pair_algebra
                  sigma_sets_pair_algebra_finite M1.sets_eq_Pow M2.sets_eq_Pow)
qed

sublocale pair_finite_sigma_algebra \<subseteq> finite_sigma_algebra P
proof
  show "finite (space P)" "sets P = Pow (space P)"
    using M1.finite_space M2.finite_space by auto
qed

locale pair_finite_space = M1: finite_measure_space M1 \<mu>1 + M2: finite_measure_space M2 \<mu>2
  for M1 \<mu>1 M2 \<mu>2

sublocale pair_finite_space \<subseteq> pair_finite_sigma_algebra
  by default

sublocale pair_finite_space \<subseteq> pair_sigma_finite
  by default

lemma (in pair_finite_space) finite_pair_sigma_algebra[simp]:
  shows "P = (| space = space M1 \<times> space M2, sets = Pow (space M1 \<times> space M2) |)"
proof -
  show ?thesis using M1.finite_space M2.finite_space
    by (simp add: sigma_def space_pair_algebra sets_pair_algebra
                  sigma_sets_pair_algebra_finite M1.sets_eq_Pow M2.sets_eq_Pow)
qed

lemma (in pair_finite_space) pair_measure_Pair[simp]:
  assumes "a \<in> space M1" "b \<in> space M2"
  shows "pair_measure {(a, b)} = \<mu>1 {a} * \<mu>2 {b}"
proof -
  have "pair_measure ({a}\<times>{b}) = \<mu>1 {a} * \<mu>2 {b}"
    using M1.sets_eq_Pow M2.sets_eq_Pow assms
    by (subst pair_measure_times) auto
  then show ?thesis by simp
qed

lemma (in pair_finite_space) pair_measure_singleton[simp]:
  assumes "x \<in> space M1 \<times> space M2"
  shows "pair_measure {x} = \<mu>1 {fst x} * \<mu>2 {snd x}"
  using pair_measure_Pair assms by (cases x) auto

sublocale pair_finite_space \<subseteq> finite_measure_space P pair_measure
  by default auto

lemma (in pair_finite_space) finite_measure_space_finite_prod_measure_alterantive:
  "finite_measure_space \<lparr>space = space M1 \<times> space M2, sets = Pow (space M1 \<times> space M2)\<rparr> pair_measure"
  unfolding finite_pair_sigma_algebra[symmetric]
  by default

end