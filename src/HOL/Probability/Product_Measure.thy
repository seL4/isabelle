(*  Title:      HOL/Probability/Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Product measure spaces*}

theory Product_Measure
imports Lebesgue_Integration
begin

lemma sigma_sets_subseteq: assumes "A \<subseteq> B" shows "sigma_sets X A \<subseteq> sigma_sets X B"
proof
  fix x assume "x \<in> sigma_sets X A" then show "x \<in> sigma_sets X B"
    by induct (insert `A \<subseteq> B`, auto intro: sigma_sets.intros)
qed

lemma times_Int_times: "A \<times> B \<inter> C \<times> D = (A \<inter> C) \<times> (B \<inter> D)"
  by auto

lemma Pair_vimage_times[simp]: "\<And>A B x. Pair x -` (A \<times> B) = (if x \<in> A then B else {})"
  by auto

lemma rev_Pair_vimage_times[simp]: "\<And>A B y. (\<lambda>x. (x, y)) -` (A \<times> B) = (if y \<in> B then A else {})"
  by auto

lemma case_prod_distrib: "f (case x of (x, y) \<Rightarrow> g x y) = (case x of (x, y) \<Rightarrow> f (g x y))"
  by (cases x) simp

lemma split_beta': "(\<lambda>(x,y). f x y) = (\<lambda>x. f (fst x) (snd x))"
  by (auto simp: fun_eq_iff)

abbreviation
  "Pi\<^isub>E A B \<equiv> Pi A B \<inter> extensional A"

syntax
  "_PiE"  :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3PIE _:_./ _)" 10)

syntax (xsymbols)
  "_PiE" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>\<^isub>E _\<in>_./ _)"   10)

syntax (HTML output)
  "_PiE" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>\<^isub>E _\<in>_./ _)"   10)

translations
  "PIE x:A. B" == "CONST Pi\<^isub>E A (%x. B)"

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

lemma merge_singleton[simp]: "i \<notin> I \<Longrightarrow> merge I x {i} y = restrict (x(i := y i)) (insert i I)"
  unfolding merge_def by (auto simp: fun_eq_iff)

lemma Pi_Int: "Pi I E \<inter> Pi I F = (\<Pi> i\<in>I. E i \<inter> F i)"
  by auto

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

lemma restrict_vimage:
  assumes "I \<inter> J = {}"
  shows "(\<lambda>x. (restrict x I, restrict x J)) -` (Pi\<^isub>E I E \<times> Pi\<^isub>E J F) = Pi (I \<union> J) (merge I E J F)"
  using assms by (auto simp: restrict_Pi_cancel)

lemma merge_vimage:
  assumes "I \<inter> J = {}"
  shows "(\<lambda>(x,y). merge I x J y) -` Pi\<^isub>E (I \<union> J) E = Pi I E \<times> Pi J E"
  using assms by (auto simp: restrict_Pi_cancel)

lemma restrict_fupd[simp]: "i \<notin> I \<Longrightarrow> restrict (f (i := x)) I = restrict f I"
  by (auto simp: restrict_def intro!: ext)

lemma merge_restrict[simp]:
  "merge I (restrict x I) J y = merge I x J y"
  "merge I x J (restrict y J) = merge I x J y"
  unfolding merge_def by (auto intro!: ext)

lemma merge_x_x_eq_restrict[simp]:
  "merge I x J x = restrict x (I \<union> J)"
  unfolding merge_def by (auto intro!: ext)

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

lemma restrict_upd[simp]:
  "i \<notin> I \<Longrightarrow> (restrict f I)(i := y) = restrict (f(i := y)) (insert i I)"
  by (auto simp: fun_eq_iff)

lemma Pi_eq_subset:
  assumes ne: "\<And>i. i \<in> I \<Longrightarrow> F i \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> F' i \<noteq> {}"
  assumes eq: "Pi\<^isub>E I F = Pi\<^isub>E I F'" and "i \<in> I"
  shows "F i \<subseteq> F' i"
proof
  fix x assume "x \<in> F i"
  with ne have "\<forall>j. \<exists>y. ((j \<in> I \<longrightarrow> y \<in> F j \<and> (i = j \<longrightarrow> x = y)) \<and> (j \<notin> I \<longrightarrow> y = undefined))" by auto
  from choice[OF this] guess f .. note f = this
  then have "f \<in> Pi\<^isub>E I F" by (auto simp: extensional_def)
  then have "f \<in> Pi\<^isub>E I F'" using assms by simp
  then show "x \<in> F' i" using f `i \<in> I` by auto
qed

lemma Pi_eq_iff_not_empty:
  assumes ne: "\<And>i. i \<in> I \<Longrightarrow> F i \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> F' i \<noteq> {}"
  shows "Pi\<^isub>E I F = Pi\<^isub>E I F' \<longleftrightarrow> (\<forall>i\<in>I. F i = F' i)"
proof (intro iffI ballI)
  fix i assume eq: "Pi\<^isub>E I F = Pi\<^isub>E I F'" and i: "i \<in> I"
  show "F i = F' i"
    using Pi_eq_subset[of I F F', OF ne eq i]
    using Pi_eq_subset[of I F' F, OF ne(2,1) eq[symmetric] i]
    by auto
qed auto

lemma Pi_eq_empty_iff:
  "Pi\<^isub>E I F = {} \<longleftrightarrow> (\<exists>i\<in>I. F i = {})"
proof
  assume "Pi\<^isub>E I F = {}"
  show "\<exists>i\<in>I. F i = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<forall>i. \<exists>y. (i \<in> I \<longrightarrow> y \<in> F i) \<and> (i \<notin> I \<longrightarrow> y = undefined)" by auto
    from choice[OF this] guess f ..
    then have "f \<in> Pi\<^isub>E I F" by (auto simp: extensional_def)
    with `Pi\<^isub>E I F = {}` show False by auto
  qed
qed auto

lemma Pi_eq_iff:
  "Pi\<^isub>E I F = Pi\<^isub>E I F' \<longleftrightarrow> (\<forall>i\<in>I. F i = F' i) \<or> ((\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {}))"
proof (intro iffI disjCI)
  assume eq[simp]: "Pi\<^isub>E I F = Pi\<^isub>E I F'"
  assume "\<not> ((\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {}))"
  then have "(\<forall>i\<in>I. F i \<noteq> {}) \<and> (\<forall>i\<in>I. F' i \<noteq> {})"
    using Pi_eq_empty_iff[of I F] Pi_eq_empty_iff[of I F'] by auto
  with Pi_eq_iff_not_empty[of I F F'] show "\<forall>i\<in>I. F i = F' i" by auto
next
  assume "(\<forall>i\<in>I. F i = F' i) \<or> (\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {})"
  then show "Pi\<^isub>E I F = Pi\<^isub>E I F'"
    using Pi_eq_empty_iff[of I F] Pi_eq_empty_iff[of I F'] by auto
qed

section "Binary products"

definition
  "pair_measure_generator A B =
    \<lparr> space = space A \<times> space B,
      sets = {a \<times> b | a b. a \<in> sets A \<and> b \<in> sets B},
      measure = \<lambda>X. \<integral>\<^isup>+x. (\<integral>\<^isup>+y. indicator X (x,y) \<partial>B) \<partial>A \<rparr>"

definition pair_measure (infixr "\<Otimes>\<^isub>M" 80) where
  "A \<Otimes>\<^isub>M B = sigma (pair_measure_generator A B)"

locale pair_sigma_algebra = M1: sigma_algebra M1 + M2: sigma_algebra M2
  for M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"

abbreviation (in pair_sigma_algebra)
  "E \<equiv> pair_measure_generator M1 M2"

abbreviation (in pair_sigma_algebra)
  "P \<equiv> M1 \<Otimes>\<^isub>M M2"

lemma sigma_algebra_pair_measure:
  "sets M1 \<subseteq> Pow (space M1) \<Longrightarrow> sets M2 \<subseteq> Pow (space M2) \<Longrightarrow> sigma_algebra (pair_measure M1 M2)"
  by (force simp: pair_measure_def pair_measure_generator_def intro!: sigma_algebra_sigma)

sublocale pair_sigma_algebra \<subseteq> sigma_algebra P
  using M1.space_closed M2.space_closed
  by (rule sigma_algebra_pair_measure)

lemma pair_measure_generatorI[intro, simp]:
  "x \<in> sets A \<Longrightarrow> y \<in> sets B \<Longrightarrow> x \<times> y \<in> sets (pair_measure_generator A B)"
  by (auto simp add: pair_measure_generator_def)

lemma pair_measureI[intro, simp]:
  "x \<in> sets A \<Longrightarrow> y \<in> sets B \<Longrightarrow> x \<times> y \<in> sets (A \<Otimes>\<^isub>M B)"
  by (auto simp add: pair_measure_def)

lemma space_pair_measure:
  "space (A \<Otimes>\<^isub>M B) = space A \<times> space B"
  by (simp add: pair_measure_def pair_measure_generator_def)

lemma sets_pair_measure_generator:
  "sets (pair_measure_generator N M) = (\<lambda>(x, y). x \<times> y) ` (sets N \<times> sets M)"
  unfolding pair_measure_generator_def by auto

lemma pair_measure_generator_sets_into_space:
  assumes "sets M \<subseteq> Pow (space M)" "sets N \<subseteq> Pow (space N)"
  shows "sets (pair_measure_generator M N) \<subseteq> Pow (space (pair_measure_generator M N))"
  using assms by (auto simp: pair_measure_generator_def)

lemma pair_measure_generator_Int_snd:
  assumes "sets S1 \<subseteq> Pow (space S1)"
  shows "sets (pair_measure_generator S1 (algebra.restricted_space S2 A)) =
         sets (algebra.restricted_space (pair_measure_generator S1 S2) (space S1 \<times> A))"
  (is "?L = ?R")
  apply (auto simp: pair_measure_generator_def image_iff)
  using assms
  apply (rule_tac x="a \<times> xa" in exI)
  apply force
  using assms
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="b \<inter> A" in exI)
  apply auto
  done

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
    by (fastsimp simp: measurable_def sets_sigma space_pair_measure
                 intro!: sigma_sets.Basic)
  then show ?fst ?snd by auto
qed

lemma (in pair_sigma_algebra) measurable_pair_iff:
  assumes "sigma_algebra M"
  shows "f \<in> measurable M P \<longleftrightarrow>
    (fst \<circ> f) \<in> measurable M M1 \<and> (snd \<circ> f) \<in> measurable M M2"
proof -
  interpret M: sigma_algebra M by fact
  from assms show ?thesis
  proof (safe intro!: measurable_comp[where b=P])
    assume f: "(fst \<circ> f) \<in> measurable M M1" and s: "(snd \<circ> f) \<in> measurable M M2"
    show "f \<in> measurable M P" unfolding pair_measure_def
    proof (rule M.measurable_sigma)
      show "sets (pair_measure_generator M1 M2) \<subseteq> Pow (space E)"
        unfolding pair_measure_generator_def using M1.sets_into_space M2.sets_into_space by auto
      show "f \<in> space M \<rightarrow> space E"
        using f s by (auto simp: mem_Times_iff measurable_def comp_def space_sigma pair_measure_generator_def)
      fix A assume "A \<in> sets E"
      then obtain B C where "B \<in> sets M1" "C \<in> sets M2" "A = B \<times> C"
        unfolding pair_measure_generator_def by auto
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

lemma (in pair_sigma_algebra) measurable_pair:
  assumes "sigma_algebra M"
  assumes "(fst \<circ> f) \<in> measurable M M1" "(snd \<circ> f) \<in> measurable M M2"
  shows "f \<in> measurable M P"
  unfolding measurable_pair_iff[OF assms(1)] using assms(2,3) by simp

lemma pair_measure_generatorE:
  assumes "X \<in> sets (pair_measure_generator M1 M2)"
  obtains A B where "X = A \<times> B" "A \<in> sets M1" "B \<in> sets M2"
  using assms unfolding pair_measure_generator_def by auto

lemma (in pair_sigma_algebra) pair_measure_generator_swap:
  "(\<lambda>X. (\<lambda>(x,y). (y,x)) -` X \<inter> space M2 \<times> space M1) ` sets E = sets (pair_measure_generator M2 M1)"
proof (safe elim!: pair_measure_generatorE)
  fix A B assume "A \<in> sets M1" "B \<in> sets M2"
  moreover then have "(\<lambda>(x, y). (y, x)) -` (A \<times> B) \<inter> space M2 \<times> space M1 = B \<times> A"
    using M1.sets_into_space M2.sets_into_space by auto
  ultimately show "(\<lambda>(x, y). (y, x)) -` (A \<times> B) \<inter> space M2 \<times> space M1 \<in> sets (pair_measure_generator M2 M1)"
    by (auto intro: pair_measure_generatorI)
next
  fix A B assume "A \<in> sets M1" "B \<in> sets M2"
  then show "B \<times> A \<in> (\<lambda>X. (\<lambda>(x, y). (y, x)) -` X \<inter> space M2 \<times> space M1) ` sets E"
    using M1.sets_into_space M2.sets_into_space
    by (auto intro!: image_eqI[where x="A \<times> B"] pair_measure_generatorI)
qed

lemma (in pair_sigma_algebra) sets_pair_sigma_algebra_swap:
  assumes Q: "Q \<in> sets P"
  shows "(\<lambda>(x,y). (y, x)) -` Q \<in> sets (M2 \<Otimes>\<^isub>M M1)" (is "_ \<in> sets ?Q")
proof -
  let "?f Q" = "(\<lambda>(x,y). (y, x)) -` Q \<inter> space M2 \<times> space M1"
  have *: "(\<lambda>(x,y). (y, x)) -` Q = ?f Q"
    using sets_into_space[OF Q] by (auto simp: space_pair_measure)
  have "sets (M2 \<Otimes>\<^isub>M M1) = sets (sigma (pair_measure_generator M2 M1))"
    unfolding pair_measure_def ..
  also have "\<dots> = sigma_sets (space M2 \<times> space M1) (?f ` sets E)"
    unfolding sigma_def pair_measure_generator_swap[symmetric]
    by (simp add: pair_measure_generator_def)
  also have "\<dots> = ?f ` sigma_sets (space M1 \<times> space M2) (sets E)"
    using M1.sets_into_space M2.sets_into_space
    by (intro sigma_sets_vimage) (auto simp: pair_measure_generator_def)
  also have "\<dots> = ?f ` sets P"
    unfolding pair_measure_def pair_measure_generator_def sigma_def by simp
  finally show ?thesis
    using Q by (subst *) auto
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_swap_measurable:
  shows "(\<lambda>(x,y). (y, x)) \<in> measurable P (M2 \<Otimes>\<^isub>M M1)"
    (is "?f \<in> measurable ?P ?Q")
  unfolding measurable_def
proof (intro CollectI conjI Pi_I ballI)
  fix x assume "x \<in> space ?P" then show "(case x of (x, y) \<Rightarrow> (y, x)) \<in> space ?Q"
    unfolding pair_measure_generator_def pair_measure_def by auto
next
  fix A assume "A \<in> sets (M2 \<Otimes>\<^isub>M M1)"
  interpret Q: pair_sigma_algebra M2 M1 by default
  with Q.sets_pair_sigma_algebra_swap[OF `A \<in> sets (M2 \<Otimes>\<^isub>M M1)`]
  show "?f -` A \<inter> space ?P \<in> sets ?P" by simp
qed

lemma (in pair_sigma_algebra) measurable_cut_fst[simp,intro]:
  assumes "Q \<in> sets P" shows "Pair x -` Q \<in> sets M2"
proof -
  let ?Q' = "{Q. Q \<subseteq> space P \<and> Pair x -` Q \<in> sets M2}"
  let ?Q = "\<lparr> space = space P, sets = ?Q' \<rparr>"
  interpret Q: sigma_algebra ?Q
    proof qed (auto simp: vimage_UN vimage_Diff space_pair_measure)
  have "sets E \<subseteq> sets ?Q"
    using M1.sets_into_space M2.sets_into_space
    by (auto simp: pair_measure_generator_def space_pair_measure)
  then have "sets P \<subseteq> sets ?Q"
    apply (subst pair_measure_def, intro Q.sets_sigma_subset)
    by (simp add: pair_measure_def)
  with assms show ?thesis by auto
qed

lemma (in pair_sigma_algebra) measurable_cut_snd:
  assumes Q: "Q \<in> sets P" shows "(\<lambda>x. (x, y)) -` Q \<in> sets M1" (is "?cut Q \<in> sets M1")
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  with Q.measurable_cut_fst[OF sets_pair_sigma_algebra_swap[OF Q], of y]
  show ?thesis by (simp add: vimage_compose[symmetric] comp_def)
qed

lemma (in pair_sigma_algebra) measurable_pair_image_snd:
  assumes m: "f \<in> measurable P M" and "x \<in> space M1"
  shows "(\<lambda>y. f (x, y)) \<in> measurable M2 M"
  unfolding measurable_def
proof (intro CollectI conjI Pi_I ballI)
  fix y assume "y \<in> space M2" with `f \<in> measurable P M` `x \<in> space M1`
  show "f (x, y) \<in> space M"
    unfolding measurable_def pair_measure_generator_def pair_measure_def by auto
next
  fix A assume "A \<in> sets M"
  then have "Pair x -` (f -` A \<inter> space P) \<in> sets M2" (is "?C \<in> _")
    using `f \<in> measurable P M`
    by (intro measurable_cut_fst) (auto simp: measurable_def)
  also have "?C = (\<lambda>y. f (x, y)) -` A \<inter> space M2"
    using `x \<in> space M1` by (auto simp: pair_measure_generator_def pair_measure_def)
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

lemma (in pair_sigma_algebra) Int_stable_pair_measure_generator: "Int_stable E"
  unfolding Int_stable_def
proof (intro ballI)
  fix A B assume "A \<in> sets E" "B \<in> sets E"
  then obtain A1 A2 B1 B2 where "A = A1 \<times> A2" "B = B1 \<times> B2"
    "A1 \<in> sets M1" "A2 \<in> sets M2" "B1 \<in> sets M1" "B2 \<in> sets M2"
    unfolding pair_measure_generator_def by auto
  then show "A \<inter> B \<in> sets E"
    by (auto simp add: times_Int_times pair_measure_generator_def)
qed

lemma finite_measure_cut_measurable:
  fixes M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"
  assumes "sigma_finite_measure M1" "finite_measure M2"
  assumes "Q \<in> sets (M1 \<Otimes>\<^isub>M M2)"
  shows "(\<lambda>x. measure M2 (Pair x -` Q)) \<in> borel_measurable M1"
    (is "?s Q \<in> _")
proof -
  interpret M1: sigma_finite_measure M1 by fact
  interpret M2: finite_measure M2 by fact
  interpret pair_sigma_algebra M1 M2 by default
  have [intro]: "sigma_algebra M1" by fact
  have [intro]: "sigma_algebra M2" by fact
  let ?D = "\<lparr> space = space P, sets = {A\<in>sets P. ?s A \<in> borel_measurable M1}  \<rparr>"
  note space_pair_measure[simp]
  interpret dynkin_system ?D
  proof (intro dynkin_systemI)
    fix A assume "A \<in> sets ?D" then show "A \<subseteq> space ?D"
      using sets_into_space by simp
  next
    from top show "space ?D \<in> sets ?D"
      by (auto simp add: if_distrib intro!: M1.measurable_If)
  next
    fix A assume "A \<in> sets ?D"
    with sets_into_space have "\<And>x. measure M2 (Pair x -` (space M1 \<times> space M2 - A)) =
        (if x \<in> space M1 then measure M2 (space M2) - ?s A x else 0)"
      by (auto intro!: M2.measure_compl simp: vimage_Diff)
    with `A \<in> sets ?D` top show "space ?D - A \<in> sets ?D"
      by (auto intro!: Diff M1.measurable_If M1.borel_measurable_extreal_diff)
  next
    fix F :: "nat \<Rightarrow> ('a\<times>'b) set" assume "disjoint_family F" "range F \<subseteq> sets ?D"
    moreover then have "\<And>x. measure M2 (\<Union>i. Pair x -` F i) = (\<Sum>i. ?s (F i) x)"
      by (intro M2.measure_countably_additive[symmetric])
         (auto simp: disjoint_family_on_def)
    ultimately show "(\<Union>i. F i) \<in> sets ?D"
      by (auto simp: vimage_UN intro!: M1.borel_measurable_psuminf)
  qed
  have "sets P = sets ?D" apply (subst pair_measure_def)
  proof (intro dynkin_lemma)
    show "Int_stable E" by (rule Int_stable_pair_measure_generator)
    from M1.sets_into_space have "\<And>A. A \<in> sets M1 \<Longrightarrow> {x \<in> space M1. x \<in> A} = A"
      by auto
    then show "sets E \<subseteq> sets ?D"
      by (auto simp: pair_measure_generator_def sets_sigma if_distrib
               intro: sigma_sets.Basic intro!: M1.measurable_If)
  qed (auto simp: pair_measure_def)
  with `Q \<in> sets P` have "Q \<in> sets ?D" by simp
  then show "?s Q \<in> borel_measurable M1" by simp
qed

subsection {* Binary products of $\sigma$-finite measure spaces *}

locale pair_sigma_finite = M1: sigma_finite_measure M1 + M2: sigma_finite_measure M2
  for M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"

sublocale pair_sigma_finite \<subseteq> pair_sigma_algebra M1 M2
  by default

lemma times_eq_iff: "A \<times> B = C \<times> D \<longleftrightarrow> A = C \<and> B = D \<or> ((A = {} \<or> B = {}) \<and> (C = {} \<or> D = {}))"
  by auto

lemma (in pair_sigma_finite) measure_cut_measurable_fst:
  assumes "Q \<in> sets P" shows "(\<lambda>x. measure M2 (Pair x -` Q)) \<in> borel_measurable M1" (is "?s Q \<in> _")
proof -
  have [intro]: "sigma_algebra M1" and [intro]: "sigma_algebra M2" by default+
  have M1: "sigma_finite_measure M1" by default
  from M2.disjoint_sigma_finite guess F .. note F = this
  then have F_sets: "\<And>i. F i \<in> sets M2" by auto
  let "?C x i" = "F i \<inter> Pair x -` Q"
  { fix i
    let ?R = "M2.restricted_space (F i)"
    have [simp]: "space M1 \<times> F i \<inter> space M1 \<times> space M2 = space M1 \<times> F i"
      using F M2.sets_into_space by auto
    let ?R2 = "M2.restricted_space (F i)"
    have "(\<lambda>x. measure ?R2 (Pair x -` (space M1 \<times> space ?R2 \<inter> Q))) \<in> borel_measurable M1"
    proof (intro finite_measure_cut_measurable[OF M1])
      show "finite_measure ?R2"
        using F by (intro M2.restricted_to_finite_measure) auto
      have "(space M1 \<times> space ?R2) \<inter> Q \<in> (op \<inter> (space M1 \<times> F i)) ` sets P"
        using `Q \<in> sets P` by (auto simp: image_iff)
      also have "\<dots> = sigma_sets (space M1 \<times> F i) ((op \<inter> (space M1 \<times> F i)) ` sets E)"
        unfolding pair_measure_def pair_measure_generator_def sigma_def
        using `F i \<in> sets M2` M2.sets_into_space
        by (auto intro!: sigma_sets_Int sigma_sets.Basic)
      also have "\<dots> \<subseteq> sets (M1 \<Otimes>\<^isub>M ?R2)"
        using M1.sets_into_space
        apply (auto simp: times_Int_times pair_measure_def pair_measure_generator_def sigma_def
                    intro!: sigma_sets_subseteq)
        apply (rule_tac x="a" in exI)
        apply (rule_tac x="b \<inter> F i" in exI)
        by auto
      finally show "(space M1 \<times> space ?R2) \<inter> Q \<in> sets (M1 \<Otimes>\<^isub>M ?R2)" .
    qed
    moreover have "\<And>x. Pair x -` (space M1 \<times> F i \<inter> Q) = ?C x i"
      using `Q \<in> sets P` sets_into_space by (auto simp: space_pair_measure)
    ultimately have "(\<lambda>x. measure M2 (?C x i)) \<in> borel_measurable M1"
      by simp }
  moreover
  { fix x
    have "(\<Sum>i. measure M2 (?C x i)) = measure M2 (\<Union>i. ?C x i)"
    proof (intro M2.measure_countably_additive)
      show "range (?C x) \<subseteq> sets M2"
        using F `Q \<in> sets P` by (auto intro!: M2.Int)
      have "disjoint_family F" using F by auto
      show "disjoint_family (?C x)"
        by (rule disjoint_family_on_bisimulation[OF `disjoint_family F`]) auto
    qed
    also have "(\<Union>i. ?C x i) = Pair x -` Q"
      using F sets_into_space `Q \<in> sets P`
      by (auto simp: space_pair_measure)
    finally have "measure M2 (Pair x -` Q) = (\<Sum>i. measure M2 (?C x i))"
      by simp }
  ultimately show ?thesis using `Q \<in> sets P` F_sets
    by (auto intro!: M1.borel_measurable_psuminf M2.Int)
qed

lemma (in pair_sigma_finite) measure_cut_measurable_snd:
  assumes "Q \<in> sets P" shows "(\<lambda>y. M1.\<mu> ((\<lambda>x. (x, y)) -` Q)) \<in> borel_measurable M2"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  note sets_pair_sigma_algebra_swap[OF assms]
  from Q.measure_cut_measurable_fst[OF this]
  show ?thesis by (simp add: vimage_compose[symmetric] comp_def)
qed

lemma (in pair_sigma_algebra) pair_sigma_algebra_measurable:
  assumes "f \<in> measurable P M" shows "(\<lambda>(x,y). f (y, x)) \<in> measurable (M2 \<Otimes>\<^isub>M M1) M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  have *: "(\<lambda>(x,y). f (y, x)) = f \<circ> (\<lambda>(x,y). (y, x))" by (simp add: fun_eq_iff)
  show ?thesis
    using Q.pair_sigma_algebra_swap_measurable assms
    unfolding * by (rule measurable_comp)
qed

lemma (in pair_sigma_finite) pair_measure_alt:
  assumes "A \<in> sets P"
  shows "measure (M1 \<Otimes>\<^isub>M M2) A = (\<integral>\<^isup>+ x. measure M2 (Pair x -` A) \<partial>M1)"
  apply (simp add: pair_measure_def pair_measure_generator_def)
proof (rule M1.positive_integral_cong)
  fix x assume "x \<in> space M1"
  have *: "\<And>y. indicator A (x, y) = (indicator (Pair x -` A) y :: extreal)"
    unfolding indicator_def by auto
  show "(\<integral>\<^isup>+ y. indicator A (x, y) \<partial>M2) = measure M2 (Pair x -` A)"
    unfolding *
    apply (subst M2.positive_integral_indicator)
    apply (rule measurable_cut_fst[OF assms])
    by simp
qed

lemma (in pair_sigma_finite) pair_measure_times:
  assumes A: "A \<in> sets M1" and "B \<in> sets M2"
  shows "measure (M1 \<Otimes>\<^isub>M M2) (A \<times> B) = M1.\<mu> A * measure M2 B"
proof -
  have "measure (M1 \<Otimes>\<^isub>M M2) (A \<times> B) = (\<integral>\<^isup>+ x. measure M2 B * indicator A x \<partial>M1)"
    using assms by (auto intro!: M1.positive_integral_cong simp: pair_measure_alt)
  with assms show ?thesis
    by (simp add: M1.positive_integral_cmult_indicator ac_simps)
qed

lemma (in measure_space) measure_not_negative[simp,intro]:
  assumes A: "A \<in> sets M" shows "\<mu> A \<noteq> - \<infinity>"
  using positive_measure[OF A] by auto

lemma (in pair_sigma_finite) sigma_finite_up_in_pair_measure_generator:
  "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> sets E \<and> incseq F \<and> (\<Union>i. F i) = space E \<and>
    (\<forall>i. measure (M1 \<Otimes>\<^isub>M M2) (F i) \<noteq> \<infinity>)"
proof -
  obtain F1 :: "nat \<Rightarrow> 'a set" and F2 :: "nat \<Rightarrow> 'b set" where
    F1: "range F1 \<subseteq> sets M1" "incseq F1" "(\<Union>i. F1 i) = space M1" "\<And>i. M1.\<mu> (F1 i) \<noteq> \<infinity>" and
    F2: "range F2 \<subseteq> sets M2" "incseq F2" "(\<Union>i. F2 i) = space M2" "\<And>i. M2.\<mu> (F2 i) \<noteq> \<infinity>"
    using M1.sigma_finite_up M2.sigma_finite_up by auto
  then have space: "space M1 = (\<Union>i. F1 i)" "space M2 = (\<Union>i. F2 i)" by auto
  let ?F = "\<lambda>i. F1 i \<times> F2 i"
  show ?thesis unfolding space_pair_measure
  proof (intro exI[of _ ?F] conjI allI)
    show "range ?F \<subseteq> sets E" using F1 F2
      by (fastsimp intro!: pair_measure_generatorI)
  next
    have "space M1 \<times> space M2 \<subseteq> (\<Union>i. ?F i)"
    proof (intro subsetI)
      fix x assume "x \<in> space M1 \<times> space M2"
      then obtain i j where "fst x \<in> F1 i" "snd x \<in> F2 j"
        by (auto simp: space)
      then have "fst x \<in> F1 (max i j)" "snd x \<in> F2 (max j i)"
        using `incseq F1` `incseq F2` unfolding incseq_def
        by (force split: split_max)+
      then have "(fst x, snd x) \<in> F1 (max i j) \<times> F2 (max i j)"
        by (intro SigmaI) (auto simp add: min_max.sup_commute)
      then show "x \<in> (\<Union>i. ?F i)" by auto
    qed
    then show "(\<Union>i. ?F i) = space E"
      using space by (auto simp: space pair_measure_generator_def)
  next
    fix i show "incseq (\<lambda>i. F1 i \<times> F2 i)"
      using `incseq F1` `incseq F2` unfolding incseq_Suc_iff by auto
  next
    fix i
    from F1 F2 have "F1 i \<in> sets M1" "F2 i \<in> sets M2" by auto
    with F1 F2 M1.positive_measure[OF this(1)] M2.positive_measure[OF this(2)]
    show "measure P (F1 i \<times> F2 i) \<noteq> \<infinity>"
      by (simp add: pair_measure_times)
  qed
qed

sublocale pair_sigma_finite \<subseteq> sigma_finite_measure P
proof
  show "positive P (measure P)"
    unfolding pair_measure_def pair_measure_generator_def sigma_def positive_def
    by (auto intro: M1.positive_integral_positive M2.positive_integral_positive)

  show "countably_additive P (measure P)"
    unfolding countably_additive_def
  proof (intro allI impI)
    fix F :: "nat \<Rightarrow> ('a \<times> 'b) set"
    assume F: "range F \<subseteq> sets P" "disjoint_family F"
    from F have *: "\<And>i. F i \<in> sets P" "(\<Union>i. F i) \<in> sets P" by auto
    moreover from F have "\<And>i. (\<lambda>x. measure M2 (Pair x -` F i)) \<in> borel_measurable M1"
      by (intro measure_cut_measurable_fst) auto
    moreover have "\<And>x. disjoint_family (\<lambda>i. Pair x -` F i)"
      by (intro disjoint_family_on_bisimulation[OF F(2)]) auto
    moreover have "\<And>x. x \<in> space M1 \<Longrightarrow> range (\<lambda>i. Pair x -` F i) \<subseteq> sets M2"
      using F by auto
    ultimately show "(\<Sum>n. measure P (F n)) = measure P (\<Union>i. F i)"
      by (simp add: pair_measure_alt vimage_UN M1.positive_integral_suminf[symmetric]
                    M2.measure_countably_additive
               cong: M1.positive_integral_cong)
  qed

  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  show "\<exists>F::nat \<Rightarrow> ('a \<times> 'b) set. range F \<subseteq> sets P \<and> (\<Union>i. F i) = space P \<and> (\<forall>i. measure P (F i) \<noteq> \<infinity>)"
  proof (rule exI[of _ F], intro conjI)
    show "range F \<subseteq> sets P" using F by (auto simp: pair_measure_def)
    show "(\<Union>i. F i) = space P"
      using F by (auto simp: pair_measure_def pair_measure_generator_def)
    show "\<forall>i. measure P (F i) \<noteq> \<infinity>" using F by auto
  qed
qed

lemma (in pair_sigma_algebra) sets_swap:
  assumes "A \<in> sets P"
  shows "(\<lambda>(x, y). (y, x)) -` A \<inter> space (M2 \<Otimes>\<^isub>M M1) \<in> sets (M2 \<Otimes>\<^isub>M M1)"
    (is "_ -` A \<inter> space ?Q \<in> sets ?Q")
proof -
  have *: "(\<lambda>(x, y). (y, x)) -` A \<inter> space ?Q = (\<lambda>(x, y). (y, x)) -` A"
    using `A \<in> sets P` sets_into_space by (auto simp: space_pair_measure)
  show ?thesis
    unfolding * using assms by (rule sets_pair_sigma_algebra_swap)
qed

lemma (in pair_sigma_finite) pair_measure_alt2:
  assumes A: "A \<in> sets P"
  shows "\<mu> A = (\<integral>\<^isup>+y. M1.\<mu> ((\<lambda>x. (x, y)) -` A) \<partial>M2)"
    (is "_ = ?\<nu> A")
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  from sigma_finite_up_in_pair_measure_generator guess F :: "nat \<Rightarrow> ('a \<times> 'b) set" .. note F = this
  have [simp]: "\<And>m. \<lparr> space = space E, sets = sets (sigma E), measure = m \<rparr> = P\<lparr> measure := m \<rparr>"
    unfolding pair_measure_def by simp

  have "\<mu> A = Q.\<mu> ((\<lambda>(y, x). (x, y)) -` A \<inter> space Q.P)"
  proof (rule measure_unique_Int_stable_vimage[OF Int_stable_pair_measure_generator])
    show "measure_space P" "measure_space Q.P" by default
    show "(\<lambda>(y, x). (x, y)) \<in> measurable Q.P P" by (rule Q.pair_sigma_algebra_swap_measurable)
    show "sets (sigma E) = sets P" "space E = space P" "A \<in> sets (sigma E)"
      using assms unfolding pair_measure_def by auto
    show "range F \<subseteq> sets E" "incseq F" "(\<Union>i. F i) = space E" "\<And>i. \<mu> (F i) \<noteq> \<infinity>"
      using F `A \<in> sets P` by (auto simp: pair_measure_def)
    fix X assume "X \<in> sets E"
    then obtain A B where X[simp]: "X = A \<times> B" and AB: "A \<in> sets M1" "B \<in> sets M2"
      unfolding pair_measure_def pair_measure_generator_def by auto
    then have "(\<lambda>(y, x). (x, y)) -` X \<inter> space Q.P = B \<times> A"
      using M1.sets_into_space M2.sets_into_space by (auto simp: space_pair_measure)
    then show "\<mu> X = Q.\<mu> ((\<lambda>(y, x). (x, y)) -` X \<inter> space Q.P)"
      using AB by (simp add: pair_measure_times Q.pair_measure_times ac_simps)
  qed
  then show ?thesis
    using sets_into_space[OF A] Q.pair_measure_alt[OF sets_swap[OF A]]
    by (auto simp add: Q.pair_measure_alt space_pair_measure
             intro!: M2.positive_integral_cong arg_cong[where f="M1.\<mu>"])
qed

lemma pair_sigma_algebra_sigma:
  assumes 1: "incseq S1" "(\<Union>i. S1 i) = space E1" "range S1 \<subseteq> sets E1" and E1: "sets E1 \<subseteq> Pow (space E1)"
  assumes 2: "decseq S2" "(\<Union>i. S2 i) = space E2" "range S2 \<subseteq> sets E2" and E2: "sets E2 \<subseteq> Pow (space E2)"
  shows "sets (sigma (pair_measure_generator (sigma E1) (sigma E2))) = sets (sigma (pair_measure_generator E1 E2))"
    (is "sets ?S = sets ?E")
proof -
  interpret M1: sigma_algebra "sigma E1" using E1 by (rule sigma_algebra_sigma)
  interpret M2: sigma_algebra "sigma E2" using E2 by (rule sigma_algebra_sigma)
  have P: "sets (pair_measure_generator E1 E2) \<subseteq> Pow (space E1 \<times> space E2)"
    using E1 E2 by (auto simp add: pair_measure_generator_def)
  interpret E: sigma_algebra ?E unfolding pair_measure_generator_def
    using E1 E2 by (intro sigma_algebra_sigma) auto
  { fix A assume "A \<in> sets E1"
    then have "fst -` A \<inter> space ?E = A \<times> (\<Union>i. S2 i)"
      using E1 2 unfolding pair_measure_generator_def by auto
    also have "\<dots> = (\<Union>i. A \<times> S2 i)" by auto
    also have "\<dots> \<in> sets ?E" unfolding pair_measure_generator_def sets_sigma
      using 2 `A \<in> sets E1`
      by (intro sigma_sets.Union)
         (force simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "fst -` A \<inter> space ?E \<in> sets ?E" . }
  moreover
  { fix B assume "B \<in> sets E2"
    then have "snd -` B \<inter> space ?E = (\<Union>i. S1 i) \<times> B"
      using E2 1 unfolding pair_measure_generator_def by auto
    also have "\<dots> = (\<Union>i. S1 i \<times> B)" by auto
    also have "\<dots> \<in> sets ?E"
      using 1 `B \<in> sets E2` unfolding pair_measure_generator_def sets_sigma
      by (intro sigma_sets.Union)
         (force simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "snd -` B \<inter> space ?E \<in> sets ?E" . }
  ultimately have proj:
    "fst \<in> measurable ?E (sigma E1) \<and> snd \<in> measurable ?E (sigma E2)"
    using E1 E2 by (subst (1 2) E.measurable_iff_sigma)
                   (auto simp: pair_measure_generator_def sets_sigma)
  { fix A B assume A: "A \<in> sets (sigma E1)" and B: "B \<in> sets (sigma E2)"
    with proj have "fst -` A \<inter> space ?E \<in> sets ?E" "snd -` B \<inter> space ?E \<in> sets ?E"
      unfolding measurable_def by simp_all
    moreover have "A \<times> B = (fst -` A \<inter> space ?E) \<inter> (snd -` B \<inter> space ?E)"
      using A B M1.sets_into_space M2.sets_into_space
      by (auto simp: pair_measure_generator_def)
    ultimately have "A \<times> B \<in> sets ?E" by auto }
  then have "sigma_sets (space ?E) (sets (pair_measure_generator (sigma E1) (sigma E2))) \<subseteq> sets ?E"
    by (intro E.sigma_sets_subset) (auto simp add: pair_measure_generator_def sets_sigma)
  then have subset: "sets ?S \<subseteq> sets ?E"
    by (simp add: sets_sigma pair_measure_generator_def)
  show "sets ?S = sets ?E"
  proof (intro set_eqI iffI)
    fix A assume "A \<in> sets ?E" then show "A \<in> sets ?S"
      unfolding sets_sigma
    proof induct
      case (Basic A) then show ?case
        by (auto simp: pair_measure_generator_def sets_sigma intro: sigma_sets.Basic)
    qed (auto intro: sigma_sets.intros simp: pair_measure_generator_def)
  next
    fix A assume "A \<in> sets ?S" then show "A \<in> sets ?E" using subset by auto
  qed
qed

section "Fubinis theorem"

lemma (in pair_sigma_finite) simple_function_cut:
  assumes f: "simple_function P f" "\<And>x. 0 \<le> f x"
  shows "(\<lambda>x. \<integral>\<^isup>+y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
    and "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f"
proof -
  have f_borel: "f \<in> borel_measurable P"
    using f(1) by (rule borel_measurable_simple_function)
  let "?F z" = "f -` {z} \<inter> space P"
  let "?F' x z" = "Pair x -` ?F z"
  { fix x assume "x \<in> space M1"
    have [simp]: "\<And>z y. indicator (?F z) (x, y) = indicator (?F' x z) y"
      by (auto simp: indicator_def)
    have "\<And>y. y \<in> space M2 \<Longrightarrow> (x, y) \<in> space P" using `x \<in> space M1`
      by (simp add: space_pair_measure)
    moreover have "\<And>x z. ?F' x z \<in> sets M2" using f_borel
      by (intro borel_measurable_vimage measurable_cut_fst)
    ultimately have "simple_function M2 (\<lambda> y. f (x, y))"
      apply (rule_tac M2.simple_function_cong[THEN iffD2, OF _])
      apply (rule simple_function_indicator_representation[OF f(1)])
      using `x \<in> space M1` by (auto simp del: space_sigma) }
  note M2_sf = this
  { fix x assume x: "x \<in> space M1"
    then have "(\<integral>\<^isup>+y. f (x, y) \<partial>M2) = (\<Sum>z\<in>f ` space P. z * M2.\<mu> (?F' x z))"
      unfolding M2.positive_integral_eq_simple_integral[OF M2_sf[OF x] f(2)]
      unfolding simple_integral_def
    proof (safe intro!: setsum_mono_zero_cong_left)
      from f(1) show "finite (f ` space P)" by (rule simple_functionD)
    next
      fix y assume "y \<in> space M2" then show "f (x, y) \<in> f ` space P"
        using `x \<in> space M1` by (auto simp: space_pair_measure)
    next
      fix x' y assume "(x', y) \<in> space P"
        "f (x', y) \<notin> (\<lambda>y. f (x, y)) ` space M2"
      then have *: "?F' x (f (x', y)) = {}"
        by (force simp: space_pair_measure)
      show  "f (x', y) * M2.\<mu> (?F' x (f (x', y))) = 0"
        unfolding * by simp
    qed (simp add: vimage_compose[symmetric] comp_def
                   space_pair_measure) }
  note eq = this
  moreover have "\<And>z. ?F z \<in> sets P"
    by (auto intro!: f_borel borel_measurable_vimage simp del: space_sigma)
  moreover then have "\<And>z. (\<lambda>x. M2.\<mu> (?F' x z)) \<in> borel_measurable M1"
    by (auto intro!: measure_cut_measurable_fst simp del: vimage_Int)
  moreover have *: "\<And>i x. 0 \<le> M2.\<mu> (Pair x -` (f -` {i} \<inter> space P))"
    using f(1)[THEN simple_functionD(2)] f(2) by (intro M2.positive_measure measurable_cut_fst)
  moreover { fix i assume "i \<in> f`space P"
    with * have "\<And>x. 0 \<le> i * M2.\<mu> (Pair x -` (f -` {i} \<inter> space P))"
      using f(2) by auto }
  ultimately
  show "(\<lambda>x. \<integral>\<^isup>+y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
    and "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f" using f(2)
    by (auto simp del: vimage_Int cong: measurable_cong
             intro!: M1.borel_measurable_extreal_setsum setsum_cong
             simp add: M1.positive_integral_setsum simple_integral_def
                       M1.positive_integral_cmult
                       M1.positive_integral_cong[OF eq]
                       positive_integral_eq_simple_integral[OF f]
                       pair_measure_alt[symmetric])
qed

lemma (in pair_sigma_finite) positive_integral_fst_measurable:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<lambda>x. \<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<in> borel_measurable M1"
      (is "?C f \<in> borel_measurable M1")
    and "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f"
proof -
  from borel_measurable_implies_simple_function_sequence'[OF f] guess F . note F = this
  then have F_borel: "\<And>i. F i \<in> borel_measurable P"
    by (auto intro: borel_measurable_simple_function)
  note sf = simple_function_cut[OF F(1,5)]
  then have "(\<lambda>x. SUP i. ?C (F i) x) \<in> borel_measurable M1"
    using F(1) by auto
  moreover
  { fix x assume "x \<in> space M1"
    from F measurable_pair_image_snd[OF F_borel`x \<in> space M1`]
    have "(\<integral>\<^isup>+y. (SUP i. F i (x, y)) \<partial>M2) = (SUP i. ?C (F i) x)"
      by (intro M2.positive_integral_monotone_convergence_SUP)
         (auto simp: incseq_Suc_iff le_fun_def)
    then have "(SUP i. ?C (F i) x) = ?C f x"
      unfolding F(4) positive_integral_max_0 by simp }
  note SUPR_C = this
  ultimately show "?C f \<in> borel_measurable M1"
    by (simp cong: measurable_cong)
  have "(\<integral>\<^isup>+x. (SUP i. F i x) \<partial>P) = (SUP i. integral\<^isup>P P (F i))"
    using F_borel F
    by (intro positive_integral_monotone_convergence_SUP) auto
  also have "(SUP i. integral\<^isup>P P (F i)) = (SUP i. \<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. F i (x, y) \<partial>M2) \<partial>M1)"
    unfolding sf(2) by simp
  also have "\<dots> = \<integral>\<^isup>+ x. (SUP i. \<integral>\<^isup>+ y. F i (x, y) \<partial>M2) \<partial>M1" using F sf(1)
    by (intro M1.positive_integral_monotone_convergence_SUP[symmetric])
       (auto intro!: M2.positive_integral_mono M2.positive_integral_positive
                simp: incseq_Suc_iff le_fun_def)
  also have "\<dots> = \<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. (SUP i. F i (x, y)) \<partial>M2) \<partial>M1"
    using F_borel F(2,5)
    by (auto intro!: M1.positive_integral_cong M2.positive_integral_monotone_convergence_SUP[symmetric]
             simp: incseq_Suc_iff le_fun_def measurable_pair_image_snd)
  finally show "(\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>P P f"
    using F by (simp add: positive_integral_max_0)
qed

lemma (in pair_sigma_finite) measure_preserving_swap:
  "(\<lambda>(x,y). (y, x)) \<in> measure_preserving (M1 \<Otimes>\<^isub>M M2) (M2 \<Otimes>\<^isub>M M1)"
proof
  interpret Q: pair_sigma_finite M2 M1 by default
  show *: "(\<lambda>(x,y). (y, x)) \<in> measurable (M1 \<Otimes>\<^isub>M M2) (M2 \<Otimes>\<^isub>M M1)"
    using pair_sigma_algebra_swap_measurable .
  fix X assume "X \<in> sets (M2 \<Otimes>\<^isub>M M1)"
  from measurable_sets[OF * this] this Q.sets_into_space[OF this]
  show "measure (M1 \<Otimes>\<^isub>M M2) ((\<lambda>(x, y). (y, x)) -` X \<inter> space P) = measure (M2 \<Otimes>\<^isub>M M1) X"
    by (auto intro!: M1.positive_integral_cong arg_cong[where f="M2.\<mu>"]
      simp: pair_measure_alt Q.pair_measure_alt2 space_pair_measure)
qed

lemma (in pair_sigma_finite) positive_integral_product_swap:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<integral>\<^isup>+x. f (case x of (x,y)\<Rightarrow>(y,x)) \<partial>(M2 \<Otimes>\<^isub>M M1)) = integral\<^isup>P P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have "sigma_algebra P" by default
  with f show ?thesis
    by (subst Q.positive_integral_vimage[OF _ Q.measure_preserving_swap]) auto
qed

lemma (in pair_sigma_finite) positive_integral_snd_measurable:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<integral>\<^isup>+ y. (\<integral>\<^isup>+ x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^isup>P P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  note pair_sigma_algebra_measurable[OF f]
  from Q.positive_integral_fst_measurable[OF this]
  have "(\<integral>\<^isup>+ y. (\<integral>\<^isup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^isup>+ (x, y). f (y, x) \<partial>Q.P)"
    by simp
  also have "(\<integral>\<^isup>+ (x, y). f (y, x) \<partial>Q.P) = integral\<^isup>P P f"
    unfolding positive_integral_product_swap[OF f, symmetric]
    by (auto intro!: Q.positive_integral_cong)
  finally show ?thesis .
qed

lemma (in pair_sigma_finite) Fubini:
  assumes f: "f \<in> borel_measurable P"
  shows "(\<integral>\<^isup>+ y. (\<integral>\<^isup>+ x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x, y) \<partial>M2) \<partial>M1)"
  unfolding positive_integral_snd_measurable[OF assms]
  unfolding positive_integral_fst_measurable[OF assms] ..

lemma (in pair_sigma_finite) AE_pair:
  assumes "AE x in P. Q x"
  shows "AE x in M1. (AE y in M2. Q (x, y))"
proof -
  obtain N where N: "N \<in> sets P" "\<mu> N = 0" "{x\<in>space P. \<not> Q x} \<subseteq> N"
    using assms unfolding almost_everywhere_def by auto
  show ?thesis
  proof (rule M1.AE_I)
    from N measure_cut_measurable_fst[OF `N \<in> sets P`]
    show "M1.\<mu> {x\<in>space M1. M2.\<mu> (Pair x -` N) \<noteq> 0} = 0"
      by (auto simp: pair_measure_alt M1.positive_integral_0_iff)
    show "{x \<in> space M1. M2.\<mu> (Pair x -` N) \<noteq> 0} \<in> sets M1"
      by (intro M1.borel_measurable_extreal_neq_const measure_cut_measurable_fst N)
    { fix x assume "x \<in> space M1" "M2.\<mu> (Pair x -` N) = 0"
      have "M2.almost_everywhere (\<lambda>y. Q (x, y))"
      proof (rule M2.AE_I)
        show "M2.\<mu> (Pair x -` N) = 0" by fact
        show "Pair x -` N \<in> sets M2" by (intro measurable_cut_fst N)
        show "{y \<in> space M2. \<not> Q (x, y)} \<subseteq> Pair x -` N"
          using N `x \<in> space M1` unfolding space_sigma space_pair_measure by auto
      qed }
    then show "{x \<in> space M1. \<not> M2.almost_everywhere (\<lambda>y. Q (x, y))} \<subseteq> {x \<in> space M1. M2.\<mu> (Pair x -` N) \<noteq> 0}"
      by auto
  qed
qed

lemma (in pair_sigma_algebra) measurable_product_swap:
  "f \<in> measurable (M2 \<Otimes>\<^isub>M M1) M \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) \<in> measurable P M"
proof -
  interpret Q: pair_sigma_algebra M2 M1 by default
  show ?thesis
    using pair_sigma_algebra_measurable[of "\<lambda>(x,y). f (y, x)"]
    by (auto intro!: pair_sigma_algebra_measurable Q.pair_sigma_algebra_measurable iffI)
qed

lemma (in pair_sigma_finite) integrable_product_swap:
  assumes "integrable P f"
  shows "integrable (M2 \<Otimes>\<^isub>M M1) (\<lambda>(x,y). f (y,x))"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding *
    using assms unfolding integrable_def
    apply (subst (1 2) positive_integral_product_swap)
    using `integrable P f` unfolding integrable_def
    by (auto simp: *[symmetric] Q.measurable_product_swap[symmetric])
qed

lemma (in pair_sigma_finite) integrable_product_swap_iff:
  "integrable (M2 \<Otimes>\<^isub>M M1) (\<lambda>(x,y). f (y,x)) \<longleftrightarrow> integrable P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  from Q.integrable_product_swap[of "\<lambda>(x,y). f (y,x)"] integrable_product_swap[of f]
  show ?thesis by auto
qed

lemma (in pair_sigma_finite) integral_product_swap:
  assumes "integrable P f"
  shows "(\<integral>(x,y). f (y,x) \<partial>(M2 \<Otimes>\<^isub>M M1)) = integral\<^isup>L P f"
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have *: "(\<lambda>(x,y). f (y,x)) = (\<lambda>x. f (case x of (x,y)\<Rightarrow>(y,x)))" by (auto simp: fun_eq_iff)
  show ?thesis
    unfolding lebesgue_integral_def *
    apply (subst (1 2) positive_integral_product_swap)
    using `integrable P f` unfolding integrable_def
    by (auto simp: *[symmetric] Q.measurable_product_swap[symmetric])
qed

lemma (in pair_sigma_finite) integrable_fst_measurable:
  assumes f: "integrable P f"
  shows "M1.almost_everywhere (\<lambda>x. integrable M2 (\<lambda> y. f (x, y)))" (is "?AE")
    and "(\<integral>x. (\<integral>y. f (x, y) \<partial>M2) \<partial>M1) = integral\<^isup>L P f" (is "?INT")
proof -
  let "?pf x" = "extreal (f x)" and "?nf x" = "extreal (- f x)"
  have
    borel: "?nf \<in> borel_measurable P""?pf \<in> borel_measurable P" and
    int: "integral\<^isup>P P ?nf \<noteq> \<infinity>" "integral\<^isup>P P ?pf \<noteq> \<infinity>"
    using assms by auto
  have "(\<integral>\<^isup>+x. (\<integral>\<^isup>+y. extreal (f (x, y)) \<partial>M2) \<partial>M1) \<noteq> \<infinity>"
     "(\<integral>\<^isup>+x. (\<integral>\<^isup>+y. extreal (- f (x, y)) \<partial>M2) \<partial>M1) \<noteq> \<infinity>"
    using borel[THEN positive_integral_fst_measurable(1)] int
    unfolding borel[THEN positive_integral_fst_measurable(2)] by simp_all
  with borel[THEN positive_integral_fst_measurable(1)]
  have AE_pos: "AE x in M1. (\<integral>\<^isup>+y. extreal (f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    "AE x in M1. (\<integral>\<^isup>+y. extreal (- f (x, y)) \<partial>M2) \<noteq> \<infinity>"
    by (auto intro!: M1.positive_integral_PInf_AE )
  then have AE: "AE x in M1. \<bar>\<integral>\<^isup>+y. extreal (f (x, y)) \<partial>M2\<bar> \<noteq> \<infinity>"
    "AE x in M1. \<bar>\<integral>\<^isup>+y. extreal (- f (x, y)) \<partial>M2\<bar> \<noteq> \<infinity>"
    by (auto simp: M2.positive_integral_positive)
  from AE_pos show ?AE using assms
    by (simp add: measurable_pair_image_snd integrable_def)
  { fix f have "(\<integral>\<^isup>+ x. - \<integral>\<^isup>+ y. extreal (f x y) \<partial>M2 \<partial>M1) = (\<integral>\<^isup>+x. 0 \<partial>M1)"
      using M2.positive_integral_positive
      by (intro M1.positive_integral_cong_pos) (auto simp: extreal_uminus_le_reorder)
    then have "(\<integral>\<^isup>+ x. - \<integral>\<^isup>+ y. extreal (f x y) \<partial>M2 \<partial>M1) = 0" by simp }
  note this[simp]
  { fix f assume borel: "(\<lambda>x. extreal (f x)) \<in> borel_measurable P"
      and int: "integral\<^isup>P P (\<lambda>x. extreal (f x)) \<noteq> \<infinity>"
      and AE: "M1.almost_everywhere (\<lambda>x. (\<integral>\<^isup>+y. extreal (f (x, y)) \<partial>M2) \<noteq> \<infinity>)"
    have "integrable M1 (\<lambda>x. real (\<integral>\<^isup>+y. extreal (f (x, y)) \<partial>M2))" (is "integrable M1 ?f")
    proof (intro integrable_def[THEN iffD2] conjI)
      show "?f \<in> borel_measurable M1"
        using borel by (auto intro!: M1.borel_measurable_real_of_extreal positive_integral_fst_measurable)
      have "(\<integral>\<^isup>+x. extreal (?f x) \<partial>M1) = (\<integral>\<^isup>+x. (\<integral>\<^isup>+y. extreal (f (x, y))  \<partial>M2) \<partial>M1)"
        using AE M2.positive_integral_positive
        by (auto intro!: M1.positive_integral_cong_AE simp: extreal_real)
      then show "(\<integral>\<^isup>+x. extreal (?f x) \<partial>M1) \<noteq> \<infinity>"
        using positive_integral_fst_measurable[OF borel] int by simp
      have "(\<integral>\<^isup>+x. extreal (- ?f x) \<partial>M1) = (\<integral>\<^isup>+x. 0 \<partial>M1)"
        by (intro M1.positive_integral_cong_pos)
           (simp add: M2.positive_integral_positive real_of_extreal_pos)
      then show "(\<integral>\<^isup>+x. extreal (- ?f x) \<partial>M1) \<noteq> \<infinity>" by simp
    qed }
  with this[OF borel(1) int(1) AE_pos(2)] this[OF borel(2) int(2) AE_pos(1)]
  show ?INT
    unfolding lebesgue_integral_def[of P] lebesgue_integral_def[of M2]
      borel[THEN positive_integral_fst_measurable(2), symmetric]
    using AE[THEN M1.integral_real]
    by simp
qed

lemma (in pair_sigma_finite) integrable_snd_measurable:
  assumes f: "integrable P f"
  shows "M2.almost_everywhere (\<lambda>y. integrable M1 (\<lambda>x. f (x, y)))" (is "?AE")
    and "(\<integral>y. (\<integral>x. f (x, y) \<partial>M1) \<partial>M2) = integral\<^isup>L P f" (is "?INT")
proof -
  interpret Q: pair_sigma_finite M2 M1 by default
  have Q_int: "integrable Q.P (\<lambda>(x, y). f (y, x))"
    using f unfolding integrable_product_swap_iff .
  show ?INT
    using Q.integrable_fst_measurable(2)[OF Q_int]
    using integral_product_swap[OF f] by simp
  show ?AE
    using Q.integrable_fst_measurable(1)[OF Q_int]
    by simp
qed

lemma (in pair_sigma_finite) Fubini_integral:
  assumes f: "integrable P f"
  shows "(\<integral>y. (\<integral>x. f (x, y) \<partial>M1) \<partial>M2) = (\<integral>x. (\<integral>y. f (x, y) \<partial>M2) \<partial>M1)"
  unfolding integrable_snd_measurable[OF assms]
  unfolding integrable_fst_measurable[OF assms] ..

section "Finite product spaces"

section "Products"

locale product_sigma_algebra =
  fixes M :: "'i \<Rightarrow> ('a, 'b) measure_space_scheme"
  assumes sigma_algebras: "\<And>i. sigma_algebra (M i)"

locale finite_product_sigma_algebra = product_sigma_algebra M
  for M :: "'i \<Rightarrow> ('a, 'b) measure_space_scheme" +
  fixes I :: "'i set"
  assumes finite_index: "finite I"

definition
  "product_algebra_generator I M = \<lparr> space = (\<Pi>\<^isub>E i \<in> I. space (M i)),
    sets = Pi\<^isub>E I ` (\<Pi> i \<in> I. sets (M i)),
    measure = \<lambda>A. (\<Prod>i\<in>I. measure (M i) ((SOME F. A = Pi\<^isub>E I F) i)) \<rparr>"

definition product_algebra_def:
  "Pi\<^isub>M I M = sigma (product_algebra_generator I M)
    \<lparr> measure := (SOME \<mu>. sigma_finite_measure (sigma (product_algebra_generator I M) \<lparr> measure := \<mu> \<rparr>) \<and>
      (\<forall>A\<in>\<Pi> i\<in>I. sets (M i). \<mu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. measure (M i) (A i))))\<rparr>"

syntax
  "_PiM"  :: "[pttrn, 'i set, ('a, 'b) measure_space_scheme] =>
              ('i => 'a, 'b) measure_space_scheme"  ("(3PIM _:_./ _)" 10)

syntax (xsymbols)
  "_PiM" :: "[pttrn, 'i set, ('a, 'b) measure_space_scheme] =>
             ('i => 'a, 'b) measure_space_scheme"  ("(3\<Pi>\<^isub>M _\<in>_./ _)"   10)

syntax (HTML output)
  "_PiM" :: "[pttrn, 'i set, ('a, 'b) measure_space_scheme] =>
             ('i => 'a, 'b) measure_space_scheme"  ("(3\<Pi>\<^isub>M _\<in>_./ _)"   10)

translations
  "PIM x:I. M" == "CONST Pi\<^isub>M I (%x. M)"

abbreviation (in finite_product_sigma_algebra) "G \<equiv> product_algebra_generator I M"
abbreviation (in finite_product_sigma_algebra) "P \<equiv> Pi\<^isub>M I M"

sublocale product_sigma_algebra \<subseteq> M: sigma_algebra "M i" for i by (rule sigma_algebras)

lemma sigma_into_space:
  assumes "sets M \<subseteq> Pow (space M)"
  shows "sets (sigma M) \<subseteq> Pow (space M)"
  using sigma_sets_into_sp[OF assms] unfolding sigma_def by auto

lemma (in product_sigma_algebra) product_algebra_generator_into_space:
  "sets (product_algebra_generator I M) \<subseteq> Pow (space (product_algebra_generator I M))"
  using M.sets_into_space unfolding product_algebra_generator_def
  by auto blast

lemma (in product_sigma_algebra) product_algebra_into_space:
  "sets (Pi\<^isub>M I M) \<subseteq> Pow (space (Pi\<^isub>M I M))"
  using product_algebra_generator_into_space
  by (auto intro!: sigma_into_space simp add: product_algebra_def)

lemma (in product_sigma_algebra) sigma_algebra_product_algebra: "sigma_algebra (Pi\<^isub>M I M)"
  using product_algebra_generator_into_space unfolding product_algebra_def
  by (rule sigma_algebra.sigma_algebra_cong[OF sigma_algebra_sigma]) simp_all

sublocale finite_product_sigma_algebra \<subseteq> sigma_algebra P
  using sigma_algebra_product_algebra .

lemma product_algebraE:
  assumes "A \<in> sets (product_algebra_generator I M)"
  obtains E where "A = Pi\<^isub>E I E" "E \<in> (\<Pi> i\<in>I. sets (M i))"
  using assms unfolding product_algebra_generator_def by auto

lemma product_algebra_generatorI[intro]:
  assumes "E \<in> (\<Pi> i\<in>I. sets (M i))"
  shows "Pi\<^isub>E I E \<in> sets (product_algebra_generator I M)"
  using assms unfolding product_algebra_generator_def by auto

lemma space_product_algebra_generator[simp]:
  "space (product_algebra_generator I M) = Pi\<^isub>E I (\<lambda>i. space (M i))"
  unfolding product_algebra_generator_def by simp

lemma space_product_algebra[simp]:
  "space (Pi\<^isub>M I M) = (\<Pi>\<^isub>E i\<in>I. space (M i))"
  unfolding product_algebra_def product_algebra_generator_def by simp

lemma sets_product_algebra:
  "sets (Pi\<^isub>M I M) = sets (sigma (product_algebra_generator I M))"
  unfolding product_algebra_def sigma_def by simp

lemma product_algebra_generator_sets_into_space:
  assumes "\<And>i. i\<in>I \<Longrightarrow> sets (M i) \<subseteq> Pow (space (M i))"
  shows "sets (product_algebra_generator I M) \<subseteq> Pow (space (product_algebra_generator I M))"
  using assms by (auto simp: product_algebra_generator_def) blast

lemma (in finite_product_sigma_algebra) in_P[simp, intro]:
  "\<lbrakk> \<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i) \<rbrakk> \<Longrightarrow> Pi\<^isub>E I A \<in> sets P"
  by (auto simp: sets_product_algebra)

section "Generating set generates also product algebra"

lemma sigma_product_algebra_sigma_eq:
  assumes "finite I"
  assumes mono: "\<And>i. i \<in> I \<Longrightarrow> incseq (S i)"
  assumes union: "\<And>i. i \<in> I \<Longrightarrow> (\<Union>j. S i j) = space (E i)"
  assumes sets_into: "\<And>i. i \<in> I \<Longrightarrow> range (S i) \<subseteq> sets (E i)"
  and E: "\<And>i. sets (E i) \<subseteq> Pow (space (E i))"
  shows "sets (\<Pi>\<^isub>M i\<in>I. sigma (E i)) = sets (\<Pi>\<^isub>M i\<in>I. E i)"
    (is "sets ?S = sets ?E")
proof cases
  assume "I = {}" then show ?thesis
    by (simp add: product_algebra_def product_algebra_generator_def)
next
  assume "I \<noteq> {}"
  interpret E: sigma_algebra "sigma (E i)" for i
    using E by (rule sigma_algebra_sigma)
  have into_space[intro]: "\<And>i x A. A \<in> sets (E i) \<Longrightarrow> x i \<in> A \<Longrightarrow> x i \<in> space (E i)"
    using E by auto
  interpret G: sigma_algebra ?E
    unfolding product_algebra_def product_algebra_generator_def using E
    by (intro sigma_algebra.sigma_algebra_cong[OF sigma_algebra_sigma]) (auto dest: Pi_mem)
  { fix A i assume "i \<in> I" and A: "A \<in> sets (E i)"
    then have "(\<lambda>x. x i) -` A \<inter> space ?E = (\<Pi>\<^isub>E j\<in>I. if j = i then A else \<Union>n. S j n) \<inter> space ?E"
      using mono union unfolding incseq_Suc_iff space_product_algebra
      by (auto dest: Pi_mem)
    also have "\<dots> = (\<Union>n. (\<Pi>\<^isub>E j\<in>I. if j = i then A else S j n))"
      unfolding space_product_algebra
      apply simp
      apply (subst Pi_UN[OF `finite I`])
      using mono[THEN incseqD] apply simp
      apply (simp add: PiE_Int)
      apply (intro PiE_cong)
      using A sets_into by (auto intro!: into_space)
    also have "\<dots> \<in> sets ?E"
      using sets_into `A \<in> sets (E i)`
      unfolding sets_product_algebra sets_sigma
      by (intro sigma_sets.Union)
         (auto simp: image_subset_iff intro!: sigma_sets.Basic)
    finally have "(\<lambda>x. x i) -` A \<inter> space ?E \<in> sets ?E" . }
  then have proj:
    "\<And>i. i\<in>I \<Longrightarrow> (\<lambda>x. x i) \<in> measurable ?E (sigma (E i))"
    using E by (subst G.measurable_iff_sigma)
               (auto simp: sets_product_algebra sets_sigma)
  { fix A assume A: "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (sigma (E i))"
    with proj have basic: "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. x i) -` (A i) \<inter> space ?E \<in> sets ?E"
      unfolding measurable_def by simp
    have "Pi\<^isub>E I A = (\<Inter>i\<in>I. (\<lambda>x. x i) -` (A i) \<inter> space ?E)"
      using A E.sets_into_space `I \<noteq> {}` unfolding product_algebra_def by auto blast
    then have "Pi\<^isub>E I A \<in> sets ?E"
      using G.finite_INT[OF `finite I` `I \<noteq> {}` basic, of "\<lambda>i. i"] by simp }
  then have "sigma_sets (space ?E) (sets (product_algebra_generator I (\<lambda>i. sigma (E i)))) \<subseteq> sets ?E"
    by (intro G.sigma_sets_subset) (auto simp add: product_algebra_generator_def)
  then have subset: "sets ?S \<subseteq> sets ?E"
    by (simp add: sets_sigma sets_product_algebra)
  show "sets ?S = sets ?E"
  proof (intro set_eqI iffI)
    fix A assume "A \<in> sets ?E" then show "A \<in> sets ?S"
      unfolding sets_sigma sets_product_algebra
    proof induct
      case (Basic A) then show ?case
        by (auto simp: sets_sigma product_algebra_generator_def intro: sigma_sets.Basic)
    qed (auto intro: sigma_sets.intros simp: product_algebra_generator_def)
  next
    fix A assume "A \<in> sets ?S" then show "A \<in> sets ?E" using subset by auto
  qed
qed

lemma product_algebraI[intro]:
    "E \<in> (\<Pi> i\<in>I. sets (M i)) \<Longrightarrow> Pi\<^isub>E I E \<in> sets (Pi\<^isub>M I M)"
  using assms unfolding product_algebra_def by (auto intro: product_algebra_generatorI)

lemma (in product_sigma_algebra) measurable_component_update:
  assumes "x \<in> space (Pi\<^isub>M I M)" and "i \<notin> I"
  shows "(\<lambda>v. x(i := v)) \<in> measurable (M i) (Pi\<^isub>M (insert i I) M)" (is "?f \<in> _")
  unfolding product_algebra_def apply simp
proof (intro measurable_sigma)
  let ?G = "product_algebra_generator (insert i I) M"
  show "sets ?G \<subseteq> Pow (space ?G)" using product_algebra_generator_into_space .
  show "?f \<in> space (M i) \<rightarrow> space ?G"
    using M.sets_into_space assms by auto
  fix A assume "A \<in> sets ?G"
  from product_algebraE[OF this] guess E . note E = this
  then have "?f -` A \<inter> space (M i) = E i \<or> ?f -` A \<inter> space (M i) = {}"
    using M.sets_into_space assms by auto
  then show "?f -` A \<inter> space (M i) \<in> sets (M i)"
    using E by (auto intro!: product_algebraI)
qed

lemma (in product_sigma_algebra) measurable_add_dim:
  assumes "i \<notin> I"
  shows "(\<lambda>(f, y). f(i := y)) \<in> measurable (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) (Pi\<^isub>M (insert i I) M)"
proof -
  let ?f = "(\<lambda>(f, y). f(i := y))" and ?G = "product_algebra_generator (insert i I) M"
  interpret Ii: pair_sigma_algebra "Pi\<^isub>M I M" "M i"
    unfolding pair_sigma_algebra_def
    by (intro sigma_algebra_product_algebra sigma_algebras conjI)
  have "?f \<in> measurable Ii.P (sigma ?G)"
  proof (rule Ii.measurable_sigma)
    show "sets ?G \<subseteq> Pow (space ?G)"
      using product_algebra_generator_into_space .
    show "?f \<in> space (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) \<rightarrow> space ?G"
      by (auto simp: space_pair_measure)
  next
    fix A assume "A \<in> sets ?G"
    then obtain F where "A = Pi\<^isub>E (insert i I) F"
      and F: "\<And>j. j \<in> I \<Longrightarrow> F j \<in> sets (M j)" "F i \<in> sets (M i)"
      by (auto elim!: product_algebraE)
    then have "?f -` A \<inter> space (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) = Pi\<^isub>E I F \<times> (F i)"
      using sets_into_space `i \<notin> I`
      by (auto simp add: space_pair_measure) blast+
    then show "?f -` A \<inter> space (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) \<in> sets (Pi\<^isub>M I M \<Otimes>\<^isub>M M i)"
      using F by (auto intro!: pair_measureI)
  qed
  then show ?thesis
    by (simp add: product_algebra_def)
qed

lemma (in product_sigma_algebra) measurable_merge:
  assumes [simp]: "I \<inter> J = {}"
  shows "(\<lambda>(x, y). merge I x J y) \<in> measurable (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) (Pi\<^isub>M (I \<union> J) M)"
proof -
  let ?I = "Pi\<^isub>M I M" and ?J = "Pi\<^isub>M J M"
  interpret P: sigma_algebra "?I \<Otimes>\<^isub>M ?J"
    by (intro sigma_algebra_pair_measure product_algebra_into_space)
  let ?f = "\<lambda>(x, y). merge I x J y"
  let ?G = "product_algebra_generator (I \<union> J) M"
  have "?f \<in> measurable (?I \<Otimes>\<^isub>M ?J) (sigma ?G)"
  proof (rule P.measurable_sigma)
    fix A assume "A \<in> sets ?G"
    from product_algebraE[OF this]
    obtain E where E: "A = Pi\<^isub>E (I \<union> J) E" "E \<in> (\<Pi> i\<in>I \<union> J. sets (M i))" .
    then have *: "?f -` A \<inter> space (?I \<Otimes>\<^isub>M ?J) = Pi\<^isub>E I E \<times> Pi\<^isub>E J E"
      using sets_into_space `I \<inter> J = {}`
      by (auto simp add: space_pair_measure) fast+
    then show "?f -` A \<inter> space (?I \<Otimes>\<^isub>M ?J) \<in> sets (?I \<Otimes>\<^isub>M ?J)"
      using E unfolding * by (auto intro!: pair_measureI in_sigma product_algebra_generatorI
        simp: product_algebra_def)
  qed (insert product_algebra_generator_into_space, auto simp: space_pair_measure)
  then show "?f \<in> measurable (?I \<Otimes>\<^isub>M ?J) (Pi\<^isub>M (I \<union> J) M)"
    unfolding product_algebra_def[of "I \<union> J"] by simp
qed

lemma (in product_sigma_algebra) measurable_component_singleton:
  assumes "i \<in> I" shows "(\<lambda>x. x i) \<in> measurable (Pi\<^isub>M I M) (M i)"
proof (unfold measurable_def, intro CollectI conjI ballI)
  fix A assume "A \<in> sets (M i)"
  then have "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>M I M) = (\<Pi>\<^isub>E j\<in>I. if i = j then A else space (M j))"
    using M.sets_into_space `i \<in> I` by (fastsimp dest: Pi_mem split: split_if_asm)
  then show "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>M I M) \<in> sets (Pi\<^isub>M I M)"
    using `A \<in> sets (M i)` by (auto intro!: product_algebraI)
qed (insert `i \<in> I`, auto)

locale product_sigma_finite =
  fixes M :: "'i \<Rightarrow> ('a,'b) measure_space_scheme"
  assumes sigma_finite_measures: "\<And>i. sigma_finite_measure (M i)"

locale finite_product_sigma_finite = product_sigma_finite M
  for M :: "'i \<Rightarrow> ('a,'b) measure_space_scheme" +
  fixes I :: "'i set" assumes finite_index'[intro]: "finite I"

sublocale product_sigma_finite \<subseteq> M: sigma_finite_measure "M i" for i
  by (rule sigma_finite_measures)

sublocale product_sigma_finite \<subseteq> product_sigma_algebra
  by default

sublocale finite_product_sigma_finite \<subseteq> finite_product_sigma_algebra
  by default (fact finite_index')

lemma setprod_extreal_0:
  fixes f :: "'a \<Rightarrow> extreal"
  shows "(\<Prod>i\<in>A. f i) = 0 \<longleftrightarrow> (finite A \<and> (\<exists>i\<in>A. f i = 0))"
proof cases
  assume "finite A"
  then show ?thesis by (induct A) auto
qed auto

lemma setprod_extreal_pos:
  fixes f :: "'a \<Rightarrow> extreal" assumes pos: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i" shows "0 \<le> (\<Prod>i\<in>I. f i)"
proof cases
  assume "finite I" from this pos show ?thesis by induct auto
qed simp

lemma setprod_PInf:
  assumes "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "(\<Prod>i\<in>I. f i) = \<infinity> \<longleftrightarrow> finite I \<and> (\<exists>i\<in>I. f i = \<infinity>) \<and> (\<forall>i\<in>I. f i \<noteq> 0)"
proof cases
  assume "finite I" from this assms show ?thesis
  proof (induct I)
    case (insert i I)
    then have pos: "0 \<le> f i" "0 \<le> setprod f I" by (auto intro!: setprod_extreal_pos)
    from insert have "(\<Prod>j\<in>insert i I. f j) = \<infinity> \<longleftrightarrow> setprod f I * f i = \<infinity>" by auto
    also have "\<dots> \<longleftrightarrow> (setprod f I = \<infinity> \<or> f i = \<infinity>) \<and> f i \<noteq> 0 \<and> setprod f I \<noteq> 0"
      using setprod_extreal_pos[of I f] pos
      by (cases rule: extreal2_cases[of "f i" "setprod f I"]) auto
    also have "\<dots> \<longleftrightarrow> finite (insert i I) \<and> (\<exists>j\<in>insert i I. f j = \<infinity>) \<and> (\<forall>j\<in>insert i I. f j \<noteq> 0)"
      using insert by (auto simp: setprod_extreal_0)
    finally show ?case .
  qed simp
qed simp

lemma setprod_extreal: "(\<Prod>i\<in>A. extreal (f i)) = extreal (setprod f A)"
proof cases
  assume "finite A" then show ?thesis
    by induct (auto simp: one_extreal_def)
qed (simp add: one_extreal_def)

lemma (in finite_product_sigma_finite) product_algebra_generator_measure:
  assumes "Pi\<^isub>E I F \<in> sets G"
  shows "measure G (Pi\<^isub>E I F) = (\<Prod>i\<in>I. M.\<mu> i (F i))"
proof cases
  assume ne: "\<forall>i\<in>I. F i \<noteq> {}"
  have "\<forall>i\<in>I. (SOME F'. Pi\<^isub>E I F = Pi\<^isub>E I F') i = F i"
    by (rule someI2[where P="\<lambda>F'. Pi\<^isub>E I F = Pi\<^isub>E I F'"])
       (insert ne, auto simp: Pi_eq_iff)
  then show ?thesis
    unfolding product_algebra_generator_def by simp
next
  assume empty: "\<not> (\<forall>j\<in>I. F j \<noteq> {})"
  then have "(\<Prod>j\<in>I. M.\<mu> j (F j)) = 0"
    by (auto simp: setprod_extreal_0 intro!: bexI)
  moreover
  have "\<exists>j\<in>I. (SOME F'. Pi\<^isub>E I F = Pi\<^isub>E I F') j = {}"
    by (rule someI2[where P="\<lambda>F'. Pi\<^isub>E I F = Pi\<^isub>E I F'"])
       (insert empty, auto simp: Pi_eq_empty_iff[symmetric])
  then have "(\<Prod>j\<in>I. M.\<mu> j ((SOME F'. Pi\<^isub>E I F = Pi\<^isub>E I F') j)) = 0"
    by (auto simp: setprod_extreal_0 intro!: bexI)
  ultimately show ?thesis
    unfolding product_algebra_generator_def by simp
qed

lemma (in finite_product_sigma_finite) sigma_finite_pairs:
  "\<exists>F::'i \<Rightarrow> nat \<Rightarrow> 'a set.
    (\<forall>i\<in>I. range (F i) \<subseteq> sets (M i)) \<and>
    (\<forall>k. \<forall>i\<in>I. \<mu> i (F i k) \<noteq> \<infinity>) \<and> incseq (\<lambda>k. \<Pi>\<^isub>E i\<in>I. F i k) \<and>
    (\<Union>k. \<Pi>\<^isub>E i\<in>I. F i k) = space G"
proof -
  have "\<forall>i::'i. \<exists>F::nat \<Rightarrow> 'a set. range F \<subseteq> sets (M i) \<and> incseq F \<and> (\<Union>i. F i) = space (M i) \<and> (\<forall>k. \<mu> i (F k) \<noteq> \<infinity>)"
    using M.sigma_finite_up by simp
  from choice[OF this] guess F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set" ..
  then have F: "\<And>i. range (F i) \<subseteq> sets (M i)" "\<And>i. incseq (F i)" "\<And>i. (\<Union>j. F i j) = space (M i)" "\<And>i k. \<mu> i (F i k) \<noteq> \<infinity>"
    by auto
  let ?F = "\<lambda>k. \<Pi>\<^isub>E i\<in>I. F i k"
  note space_product_algebra[simp]
  show ?thesis
  proof (intro exI[of _ F] conjI allI incseq_SucI set_eqI iffI ballI)
    fix i show "range (F i) \<subseteq> sets (M i)" by fact
  next
    fix i k show "\<mu> i (F i k) \<noteq> \<infinity>" by fact
  next
    fix A assume "A \<in> (\<Union>i. ?F i)" then show "A \<in> space G"
      using `\<And>i. range (F i) \<subseteq> sets (M i)` M.sets_into_space
      by (force simp: image_subset_iff)
  next
    fix f assume "f \<in> space G"
    with Pi_UN[OF finite_index, of "\<lambda>k i. F i k"] F
    show "f \<in> (\<Union>i. ?F i)" by (auto simp: incseq_def)
  next
    fix i show "?F i \<subseteq> ?F (Suc i)"
      using `\<And>i. incseq (F i)`[THEN incseq_SucD] by auto
  qed
qed

lemma sets_pair_cancel_measure[simp]:
  "sets (M1\<lparr>measure := m1\<rparr> \<Otimes>\<^isub>M M2) = sets (M1 \<Otimes>\<^isub>M M2)"
  "sets (M1 \<Otimes>\<^isub>M M2\<lparr>measure := m2\<rparr>) = sets (M1 \<Otimes>\<^isub>M M2)"
  unfolding pair_measure_def pair_measure_generator_def sets_sigma
  by simp_all

lemma measurable_pair_cancel_measure[simp]:
  "measurable (M1\<lparr>measure := m1\<rparr> \<Otimes>\<^isub>M M2) M = measurable (M1 \<Otimes>\<^isub>M M2) M"
  "measurable (M1 \<Otimes>\<^isub>M M2\<lparr>measure := m2\<rparr>) M = measurable (M1 \<Otimes>\<^isub>M M2) M"
  "measurable M (M1\<lparr>measure := m3\<rparr> \<Otimes>\<^isub>M M2) = measurable M (M1 \<Otimes>\<^isub>M M2)"
  "measurable M (M1 \<Otimes>\<^isub>M M2\<lparr>measure := m4\<rparr>) = measurable M (M1 \<Otimes>\<^isub>M M2)"
  unfolding measurable_def by (auto simp add: space_pair_measure)

lemma (in product_sigma_finite) product_measure_exists:
  assumes "finite I"
  shows "\<exists>\<nu>. sigma_finite_measure (sigma (product_algebra_generator I M) \<lparr> measure := \<nu> \<rparr>) \<and>
    (\<forall>A\<in>\<Pi> i\<in>I. sets (M i). \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. M.\<mu> i (A i)))"
using `finite I` proof induct
  case empty
  interpret finite_product_sigma_finite M "{}" by default simp
  let ?\<nu> = "(\<lambda>A. if A = {} then 0 else 1) :: 'd set \<Rightarrow> extreal"
  show ?case
  proof (intro exI conjI ballI)
    have "sigma_algebra (sigma G \<lparr>measure := ?\<nu>\<rparr>)"
      by (rule sigma_algebra_cong) (simp_all add: product_algebra_def)
    then have "measure_space (sigma G\<lparr>measure := ?\<nu>\<rparr>)"
      by (rule finite_additivity_sufficient)
         (simp_all add: positive_def additive_def sets_sigma
                        product_algebra_generator_def image_constant)
    then show "sigma_finite_measure (sigma G\<lparr>measure := ?\<nu>\<rparr>)"
      by (auto intro!: exI[of _ "\<lambda>i. {\<lambda>_. undefined}"]
               simp: sigma_finite_measure_def sigma_finite_measure_axioms_def
                     product_algebra_generator_def)
  qed auto
next
  case (insert i I)
  interpret finite_product_sigma_finite M I by default fact
  have "finite (insert i I)" using `finite I` by auto
  interpret I': finite_product_sigma_finite M "insert i I" by default fact
  from insert obtain \<nu> where
    prod: "\<And>A. A \<in> (\<Pi> i\<in>I. sets (M i)) \<Longrightarrow> \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. M.\<mu> i (A i))" and
    "sigma_finite_measure (sigma G\<lparr> measure := \<nu> \<rparr>)" by auto
  then interpret I: sigma_finite_measure "P\<lparr> measure := \<nu>\<rparr>" unfolding product_algebra_def by simp
  interpret P: pair_sigma_finite "P\<lparr> measure := \<nu>\<rparr>" "M i" ..
  let ?h = "(\<lambda>(f, y). f(i := y))"
  let ?\<nu> = "\<lambda>A. P.\<mu> (?h -` A \<inter> space P.P)"
  have I': "sigma_algebra (I'.P\<lparr> measure := ?\<nu> \<rparr>)"
    by (rule I'.sigma_algebra_cong) simp_all
  interpret I'': measure_space "I'.P\<lparr> measure := ?\<nu> \<rparr>"
    using measurable_add_dim[OF `i \<notin> I`]
    by (intro P.measure_space_vimage[OF I']) (auto simp add: measure_preserving_def)
  show ?case
  proof (intro exI[of _ ?\<nu>] conjI ballI)
    let "?m A" = "measure (Pi\<^isub>M I M\<lparr>measure := \<nu>\<rparr> \<Otimes>\<^isub>M M i) (?h -` A \<inter> space P.P)"
    { fix A assume A: "A \<in> (\<Pi> i\<in>insert i I. sets (M i))"
      then have *: "?h -` Pi\<^isub>E (insert i I) A \<inter> space P.P = Pi\<^isub>E I A \<times> A i"
        using `i \<notin> I` M.sets_into_space by (auto simp: space_pair_measure space_product_algebra) blast
      show "?m (Pi\<^isub>E (insert i I) A) = (\<Prod>i\<in>insert i I. M.\<mu> i (A i))"
        unfolding * using A
        apply (subst P.pair_measure_times)
        using A apply fastsimp
        using A apply fastsimp
        using `i \<notin> I` `finite I` prod[of A] A by (auto simp: ac_simps) }
    note product = this
    have *: "sigma I'.G\<lparr> measure := ?\<nu> \<rparr> = I'.P\<lparr> measure := ?\<nu> \<rparr>"
      by (simp add: product_algebra_def)
    show "sigma_finite_measure (sigma I'.G\<lparr> measure := ?\<nu> \<rparr>)"
    proof (unfold *, default, simp)
      from I'.sigma_finite_pairs guess F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set" ..
      then have F: "\<And>j. j \<in> insert i I \<Longrightarrow> range (F j) \<subseteq> sets (M j)"
        "incseq (\<lambda>k. \<Pi>\<^isub>E j \<in> insert i I. F j k)"
        "(\<Union>k. \<Pi>\<^isub>E j \<in> insert i I. F j k) = space I'.G"
        "\<And>k. \<And>j. j \<in> insert i I \<Longrightarrow> \<mu> j (F j k) \<noteq> \<infinity>"
        by blast+
      let "?F k" = "\<Pi>\<^isub>E j \<in> insert i I. F j k"
      show "\<exists>F::nat \<Rightarrow> ('i \<Rightarrow> 'a) set. range F \<subseteq> sets I'.P \<and>
          (\<Union>i. F i) = (\<Pi>\<^isub>E i\<in>insert i I. space (M i)) \<and> (\<forall>i. ?m (F i) \<noteq> \<infinity>)"
      proof (intro exI[of _ ?F] conjI allI)
        show "range ?F \<subseteq> sets I'.P" using F(1) by auto
      next
        from F(3) show "(\<Union>i. ?F i) = (\<Pi>\<^isub>E i\<in>insert i I. space (M i))" by simp
      next
        fix j
        have "\<And>k. k \<in> insert i I \<Longrightarrow> 0 \<le> measure (M k) (F k j)"
          using F(1) by auto
        with F `finite I` setprod_PInf[of "insert i I", OF this] show "?\<nu> (?F j) \<noteq> \<infinity>"
          by (subst product) auto
      qed
    qed
  qed
qed

sublocale finite_product_sigma_finite \<subseteq> sigma_finite_measure P
  unfolding product_algebra_def
  using product_measure_exists[OF finite_index]
  by (rule someI2_ex) auto

lemma (in finite_product_sigma_finite) measure_times:
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  shows "\<mu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. M.\<mu> i (A i))"
  unfolding product_algebra_def
  using product_measure_exists[OF finite_index]
  proof (rule someI2_ex, elim conjE)
    fix \<nu> assume *: "\<forall>A\<in>\<Pi> i\<in>I. sets (M i). \<nu> (Pi\<^isub>E I A) = (\<Prod>i\<in>I. M.\<mu> i (A i))"
    have "Pi\<^isub>E I A = Pi\<^isub>E I (\<lambda>i\<in>I. A i)" by (auto dest: Pi_mem)
    then have "\<nu> (Pi\<^isub>E I A) = \<nu> (Pi\<^isub>E I (\<lambda>i\<in>I. A i))" by simp
    also have "\<dots> = (\<Prod>i\<in>I. M.\<mu> i ((\<lambda>i\<in>I. A i) i))" using assms * by auto
    finally show "measure (sigma G\<lparr>measure := \<nu>\<rparr>) (Pi\<^isub>E I A) = (\<Prod>i\<in>I. M.\<mu> i (A i))"
      by (simp add: sigma_def)
  qed

lemma (in product_sigma_finite) product_measure_empty[simp]:
  "measure (Pi\<^isub>M {} M) {\<lambda>x. undefined} = 1"
proof -
  interpret finite_product_sigma_finite M "{}" by default auto
  from measure_times[of "\<lambda>x. {}"] show ?thesis by simp
qed

lemma (in finite_product_sigma_algebra) P_empty:
  assumes "I = {}"
  shows "space P = {\<lambda>k. undefined}" "sets P = { {}, {\<lambda>k. undefined} }"
  unfolding product_algebra_def product_algebra_generator_def `I = {}`
  by (simp_all add: sigma_def image_constant)

lemma (in product_sigma_finite) positive_integral_empty:
  assumes pos: "0 \<le> f (\<lambda>k. undefined)"
  shows "integral\<^isup>P (Pi\<^isub>M {} M) f = f (\<lambda>k. undefined)"
proof -
  interpret finite_product_sigma_finite M "{}" by default (fact finite.emptyI)
  have "\<And>A. measure (Pi\<^isub>M {} M) (Pi\<^isub>E {} A) = 1"
    using assms by (subst measure_times) auto
  then show ?thesis
    unfolding positive_integral_def simple_function_def simple_integral_def_raw
  proof (simp add: P_empty, intro antisym)
    show "f (\<lambda>k. undefined) \<le> (SUP f:{g. g \<le> max 0 \<circ> f}. f (\<lambda>k. undefined))"
      by (intro le_SUPI) (auto simp: le_fun_def split: split_max)
    show "(SUP f:{g. g \<le> max 0 \<circ> f}. f (\<lambda>k. undefined)) \<le> f (\<lambda>k. undefined)" using pos
      by (intro SUP_leI) (auto simp: le_fun_def simp: max_def split: split_if_asm)
  qed
qed

lemma (in product_sigma_finite) measure_fold:
  assumes IJ[simp]: "I \<inter> J = {}" and fin: "finite I" "finite J"
  assumes A: "A \<in> sets (Pi\<^isub>M (I \<union> J) M)"
  shows "measure (Pi\<^isub>M (I \<union> J) M) A =
    measure (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) ((\<lambda>(x,y). merge I x J y) -` A \<inter> space (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M))"
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  have "finite (I \<union> J)" using fin by auto
  interpret IJ: finite_product_sigma_finite M "I \<union> J" by default fact
  interpret P: pair_sigma_finite I.P J.P by default
  let ?g = "\<lambda>(x,y). merge I x J y"
  let "?X S" = "?g -` S \<inter> space P.P"
  from IJ.sigma_finite_pairs obtain F where
    F: "\<And>i. i\<in> I \<union> J \<Longrightarrow> range (F i) \<subseteq> sets (M i)"
       "incseq (\<lambda>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k)"
       "(\<Union>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k) = space IJ.G"
       "\<And>k. \<forall>i\<in>I\<union>J. \<mu> i (F i k) \<noteq> \<infinity>"
    by auto
  let ?F = "\<lambda>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k"
  show "IJ.\<mu> A = P.\<mu> (?X A)"
  proof (rule measure_unique_Int_stable_vimage)
    show "measure_space IJ.P" "measure_space P.P" by default
    show "sets (sigma IJ.G) = sets IJ.P" "space IJ.G = space IJ.P" "A \<in> sets (sigma IJ.G)"
      using A unfolding product_algebra_def by auto
  next
    show "Int_stable IJ.G"
      by (simp add: PiE_Int Int_stable_def product_algebra_def
                    product_algebra_generator_def)
          auto
    show "range ?F \<subseteq> sets IJ.G" using F
      by (simp add: image_subset_iff product_algebra_def
                    product_algebra_generator_def)
    show "incseq ?F" "(\<Union>i. ?F i) = space IJ.G " by fact+
  next
    fix k
    have "\<And>j. j \<in> I \<union> J \<Longrightarrow> 0 \<le> measure (M j) (F j k)"
      using F(1) by auto
    with F `finite I` setprod_PInf[of "I \<union> J", OF this]
    show "IJ.\<mu> (?F k) \<noteq> \<infinity>" by (subst IJ.measure_times) auto
  next
    fix A assume "A \<in> sets IJ.G"
    then obtain F where A: "A = Pi\<^isub>E (I \<union> J) F"
      and F: "\<And>i. i \<in> I \<union> J \<Longrightarrow> F i \<in> sets (M i)"
      by (auto simp: product_algebra_generator_def)
    then have X: "?X A = (Pi\<^isub>E I F \<times> Pi\<^isub>E J F)"
      using sets_into_space by (auto simp: space_pair_measure) blast+
    then have "P.\<mu> (?X A) = (\<Prod>i\<in>I. \<mu> i (F i)) * (\<Prod>i\<in>J. \<mu> i (F i))"
      using `finite J` `finite I` F
      by (simp add: P.pair_measure_times I.measure_times J.measure_times)
    also have "\<dots> = (\<Prod>i\<in>I \<union> J. \<mu> i (F i))"
      using `finite J` `finite I` `I \<inter> J = {}`  by (simp add: setprod_Un_one)
    also have "\<dots> = IJ.\<mu> A"
      using `finite J` `finite I` F unfolding A
      by (intro IJ.measure_times[symmetric]) auto
    finally show "IJ.\<mu> A = P.\<mu> (?X A)" by (rule sym)
  qed (rule measurable_merge[OF IJ])
qed

lemma (in product_sigma_finite) measure_preserving_merge:
  assumes IJ: "I \<inter> J = {}" and "finite I" "finite J"
  shows "(\<lambda>(x,y). merge I x J y) \<in> measure_preserving (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) (Pi\<^isub>M (I \<union> J) M)"
  by (intro measure_preservingI measurable_merge[OF IJ] measure_fold[symmetric] assms)

lemma (in product_sigma_finite) product_positive_integral_fold:
  assumes IJ[simp]: "I \<inter> J = {}" "finite I" "finite J"
  and f: "f \<in> borel_measurable (Pi\<^isub>M (I \<union> J) M)"
  shows "integral\<^isup>P (Pi\<^isub>M (I \<union> J) M) f =
    (\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (merge I x J y) \<partial>(Pi\<^isub>M J M)) \<partial>(Pi\<^isub>M I M))"
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  interpret P: pair_sigma_finite "Pi\<^isub>M I M" "Pi\<^isub>M J M" by default
  interpret IJ: finite_product_sigma_finite M "I \<union> J" by default simp
  have P_borel: "(\<lambda>x. f (case x of (x, y) \<Rightarrow> merge I x J y)) \<in> borel_measurable P.P"
    using measurable_comp[OF measurable_merge[OF IJ(1)] f] by (simp add: comp_def)
  show ?thesis
    unfolding P.positive_integral_fst_measurable[OF P_borel, simplified]
  proof (rule P.positive_integral_vimage)
    show "sigma_algebra IJ.P" by default
    show "(\<lambda>(x, y). merge I x J y) \<in> measure_preserving P.P IJ.P"
      using IJ by (rule measure_preserving_merge)
    show "f \<in> borel_measurable IJ.P" using f by simp
  qed
qed

lemma (in product_sigma_finite) measure_preserving_component_singelton:
  "(\<lambda>x. x i) \<in> measure_preserving (Pi\<^isub>M {i} M) (M i)"
proof (intro measure_preservingI measurable_component_singleton)
  interpret I: finite_product_sigma_finite M "{i}" by default simp
  fix A let ?P = "(\<lambda>x. x i) -` A \<inter> space I.P"
  assume A: "A \<in> sets (M i)"
  then have *: "?P = {i} \<rightarrow>\<^isub>E A" using sets_into_space by auto
  show "I.\<mu> ?P = M.\<mu> i A" unfolding *
    using A I.measure_times[of "\<lambda>_. A"] by auto
qed auto

lemma (in product_sigma_finite) product_positive_integral_singleton:
  assumes f: "f \<in> borel_measurable (M i)"
  shows "integral\<^isup>P (Pi\<^isub>M {i} M) (\<lambda>x. f (x i)) = integral\<^isup>P (M i) f"
proof -
  interpret I: finite_product_sigma_finite M "{i}" by default simp
  show ?thesis
  proof (rule I.positive_integral_vimage[symmetric])
    show "sigma_algebra (M i)" by (rule sigma_algebras)
    show "(\<lambda>x. x i) \<in> measure_preserving (Pi\<^isub>M {i} M) (M i)"
      by (rule measure_preserving_component_singelton)
    show "f \<in> borel_measurable (M i)" by fact
  qed
qed

lemma (in product_sigma_finite) product_positive_integral_insert:
  assumes [simp]: "finite I" "i \<notin> I"
    and f: "f \<in> borel_measurable (Pi\<^isub>M (insert i I) M)"
  shows "integral\<^isup>P (Pi\<^isub>M (insert i I) M) f = (\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x(i := y)) \<partial>(M i)) \<partial>(Pi\<^isub>M I M))"
proof -
  interpret I: finite_product_sigma_finite M I by default auto
  interpret i: finite_product_sigma_finite M "{i}" by default auto
  interpret P: pair_sigma_algebra I.P i.P ..
  have IJ: "I \<inter> {i} = {}" and insert: "I \<union> {i} = insert i I"
    using f by auto
  show ?thesis
    unfolding product_positive_integral_fold[OF IJ, unfolded insert, simplified, OF f]
  proof (rule I.positive_integral_cong, subst product_positive_integral_singleton)
    fix x assume x: "x \<in> space I.P"
    let "?f y" = "f (restrict (x(i := y)) (insert i I))"
    have f'_eq: "\<And>y. ?f y = f (x(i := y))"
      using x by (auto intro!: arg_cong[where f=f] simp: fun_eq_iff extensional_def)
    show "?f \<in> borel_measurable (M i)" unfolding f'_eq
      using measurable_comp[OF measurable_component_update f] x `i \<notin> I`
      by (simp add: comp_def)
    show "integral\<^isup>P (M i) ?f = \<integral>\<^isup>+ y. f (x(i:=y)) \<partial>M i"
      unfolding f'_eq by simp
  qed
qed

lemma (in product_sigma_finite) product_positive_integral_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> extreal"
  assumes "finite I" and borel: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable (M i)"
  and pos: "\<And>i x. i \<in> I \<Longrightarrow> 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^isub>M I M) = (\<Prod>i\<in>I. integral\<^isup>P (M i) (f i))"
using assms proof induct
  case empty
  interpret finite_product_sigma_finite M "{}" by default auto
  then show ?case by simp
next
  case (insert i I)
  note `finite I`[intro, simp]
  interpret I: finite_product_sigma_finite M I by default auto
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using insert by (auto intro!: setprod_cong)
  have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow> (\<lambda>x. (\<Prod>i\<in>J. f i (x i))) \<in> borel_measurable (Pi\<^isub>M J M)"
    using sets_into_space insert
    by (intro sigma_algebra.borel_measurable_extreal_setprod sigma_algebra_product_algebra
              measurable_comp[OF measurable_component_singleton, unfolded comp_def])
       auto
  then show ?case
    apply (simp add: product_positive_integral_insert[OF insert(1,2) prod])
    apply (simp add: insert * pos borel setprod_extreal_pos M.positive_integral_multc)
    apply (subst I.positive_integral_cmult)
    apply (auto simp add: pos borel insert setprod_extreal_pos positive_integral_positive)
    done
qed

lemma (in product_sigma_finite) product_integral_singleton:
  assumes f: "f \<in> borel_measurable (M i)"
  shows "(\<integral>x. f (x i) \<partial>Pi\<^isub>M {i} M) = integral\<^isup>L (M i) f"
proof -
  interpret I: finite_product_sigma_finite M "{i}" by default simp
  have *: "(\<lambda>x. extreal (f x)) \<in> borel_measurable (M i)"
    "(\<lambda>x. extreal (- f x)) \<in> borel_measurable (M i)"
    using assms by auto
  show ?thesis
    unfolding lebesgue_integral_def *[THEN product_positive_integral_singleton] ..
qed

lemma (in product_sigma_finite) product_integral_fold:
  assumes IJ[simp]: "I \<inter> J = {}" and fin: "finite I" "finite J"
  and f: "integrable (Pi\<^isub>M (I \<union> J) M) f"
  shows "integral\<^isup>L (Pi\<^isub>M (I \<union> J) M) f = (\<integral>x. (\<integral>y. f (merge I x J y) \<partial>Pi\<^isub>M J M) \<partial>Pi\<^isub>M I M)"
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  have "finite (I \<union> J)" using fin by auto
  interpret IJ: finite_product_sigma_finite M "I \<union> J" by default fact
  interpret P: pair_sigma_finite I.P J.P by default
  let ?M = "\<lambda>(x, y). merge I x J y"
  let ?f = "\<lambda>x. f (?M x)"
  show ?thesis
  proof (subst P.integrable_fst_measurable(2)[of ?f, simplified])
    have 1: "sigma_algebra IJ.P" by default
    have 2: "?M \<in> measure_preserving P.P IJ.P" using measure_preserving_merge[OF assms(1,2,3)] .
    have 3: "integrable (Pi\<^isub>M (I \<union> J) M) f" by fact
    then have 4: "f \<in> borel_measurable (Pi\<^isub>M (I \<union> J) M)"
      by (simp add: integrable_def)
    show "integrable P.P ?f"
      by (rule P.integrable_vimage[where f=f, OF 1 2 3])
    show "integral\<^isup>L IJ.P f = integral\<^isup>L P.P ?f"
      by (rule P.integral_vimage[where f=f, OF 1 2 4])
  qed
qed

lemma (in product_sigma_finite) product_integral_insert:
  assumes [simp]: "finite I" "i \<notin> I"
    and f: "integrable (Pi\<^isub>M (insert i I) M) f"
  shows "integral\<^isup>L (Pi\<^isub>M (insert i I) M) f = (\<integral>x. (\<integral>y. f (x(i:=y)) \<partial>M i) \<partial>Pi\<^isub>M I M)"
proof -
  interpret I: finite_product_sigma_finite M I by default auto
  interpret I': finite_product_sigma_finite M "insert i I" by default auto
  interpret i: finite_product_sigma_finite M "{i}" by default auto
  interpret P: pair_sigma_finite I.P i.P ..
  have IJ: "I \<inter> {i} = {}" by auto
  show ?thesis
    unfolding product_integral_fold[OF IJ, simplified, OF f]
  proof (rule I.integral_cong, subst product_integral_singleton)
    fix x assume x: "x \<in> space I.P"
    let "?f y" = "f (restrict (x(i := y)) (insert i I))"
    have f'_eq: "\<And>y. ?f y = f (x(i := y))"
      using x by (auto intro!: arg_cong[where f=f] simp: fun_eq_iff extensional_def)
    have f: "f \<in> borel_measurable I'.P" using f unfolding integrable_def by auto
    show "?f \<in> borel_measurable (M i)"
      unfolding measurable_cong[OF f'_eq]
      using measurable_comp[OF measurable_component_update f] x `i \<notin> I`
      by (simp add: comp_def)
    show "integral\<^isup>L (M i) ?f = integral\<^isup>L (M i) (\<lambda>y. f (x(i := y)))"
      unfolding f'_eq by simp
  qed
qed

lemma (in product_sigma_finite) product_integrable_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes [simp]: "finite I" and integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (M i) (f i)"
  shows "integrable (Pi\<^isub>M I M) (\<lambda>x. (\<Prod>i\<in>I. f i (x i)))" (is "integrable _ ?f")
proof -
  interpret finite_product_sigma_finite M I by default fact
  have f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable (M i)"
    using integrable unfolding integrable_def by auto
  then have borel: "?f \<in> borel_measurable P"
    using measurable_comp[OF measurable_component_singleton f]
    by (auto intro!: borel_measurable_setprod simp: comp_def)
  moreover have "integrable (Pi\<^isub>M I M) (\<lambda>x. \<bar>\<Prod>i\<in>I. f i (x i)\<bar>)"
  proof (unfold integrable_def, intro conjI)
    show "(\<lambda>x. abs (?f x)) \<in> borel_measurable P"
      using borel by auto
    have "(\<integral>\<^isup>+x. extreal (abs (?f x)) \<partial>P) = (\<integral>\<^isup>+x. (\<Prod>i\<in>I. extreal (abs (f i (x i)))) \<partial>P)"
      by (simp add: setprod_extreal abs_setprod)
    also have "\<dots> = (\<Prod>i\<in>I. (\<integral>\<^isup>+x. extreal (abs (f i x)) \<partial>M i))"
      using f by (subst product_positive_integral_setprod) auto
    also have "\<dots> < \<infinity>"
      using integrable[THEN M.integrable_abs]
      by (simp add: setprod_PInf integrable_def M.positive_integral_positive)
    finally show "(\<integral>\<^isup>+x. extreal (abs (?f x)) \<partial>P) \<noteq> \<infinity>" by auto
    have "(\<integral>\<^isup>+x. extreal (- abs (?f x)) \<partial>P) = (\<integral>\<^isup>+x. 0 \<partial>P)"
      by (intro positive_integral_cong_pos) auto
    then show "(\<integral>\<^isup>+x. extreal (- abs (?f x)) \<partial>P) \<noteq> \<infinity>" by simp
  qed
  ultimately show ?thesis
    by (rule integrable_abs_iff[THEN iffD1])
qed

lemma (in product_sigma_finite) product_integral_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I" "I \<noteq> {}" and integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (M i) (f i)"
  shows "(\<integral>x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^isub>M I M) = (\<Prod>i\<in>I. integral\<^isup>L (M i) (f i))"
using assms proof (induct rule: finite_ne_induct)
  case (singleton i)
  then show ?case by (simp add: product_integral_singleton integrable_def)
next
  case (insert i I)
  then have iI: "finite (insert i I)" by auto
  then have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow>
    integrable (Pi\<^isub>M J M) (\<lambda>x. (\<Prod>i\<in>J. f i (x i)))"
    by (intro product_integrable_setprod insert(5)) (auto intro: finite_subset)
  interpret I: finite_product_sigma_finite M I by default fact
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using `i \<notin> I` by (auto intro!: setprod_cong)
  show ?case
    unfolding product_integral_insert[OF insert(1,3) prod[OF subset_refl]]
    by (simp add: * insert integral_multc I.integral_cmult[OF prod] subset_insertI)
qed

section "Products on finite spaces"

lemma sigma_sets_pair_measure_generator_finite:
  assumes "finite A" and "finite B"
  shows "sigma_sets (A \<times> B) { a \<times> b | a b. a \<in> Pow A \<and> b \<in> Pow B} = Pow (A \<times> B)"
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
      by (auto simp: pair_measure_generator_def intro!: sigma_sets.Basic)
    moreover have "x \<in> sigma_sets ?prod ?sets" using insert by auto
    ultimately show ?case unfolding insert_is_Un[of a x] by (rule sigma_sets_Un)
  qed
next
  fix x a b
  assume "x \<in> sigma_sets ?prod ?sets" and "(a, b) \<in> x"
  from sigma_sets_into_sp[OF _ this(1)] this(2)
  show "a \<in> A" and "b \<in> B" by auto
qed

locale pair_finite_sigma_algebra = M1: finite_sigma_algebra M1 + M2: finite_sigma_algebra M2
  for M1 :: "('a, 'c) measure_space_scheme" and M2 :: "('b, 'd) measure_space_scheme"

sublocale pair_finite_sigma_algebra \<subseteq> pair_sigma_algebra by default

lemma (in pair_finite_sigma_algebra) finite_pair_sigma_algebra:
  shows "P = \<lparr> space = space M1 \<times> space M2, sets = Pow (space M1 \<times> space M2), \<dots> = algebra.more P \<rparr>"
proof -
  show ?thesis
    using sigma_sets_pair_measure_generator_finite[OF M1.finite_space M2.finite_space]
    by (intro algebra.equality) (simp_all add: pair_measure_def pair_measure_generator_def sigma_def)
qed

sublocale pair_finite_sigma_algebra \<subseteq> finite_sigma_algebra P
  apply default
  using M1.finite_space M2.finite_space
  apply (subst finite_pair_sigma_algebra) apply simp
  apply (subst (1 2) finite_pair_sigma_algebra) apply simp
  done

locale pair_finite_space = M1: finite_measure_space M1 + M2: finite_measure_space M2
  for M1 M2

sublocale pair_finite_space \<subseteq> pair_finite_sigma_algebra
  by default

sublocale pair_finite_space \<subseteq> pair_sigma_finite
  by default

lemma (in pair_finite_space) pair_measure_Pair[simp]:
  assumes "a \<in> space M1" "b \<in> space M2"
  shows "\<mu> {(a, b)} = M1.\<mu> {a} * M2.\<mu> {b}"
proof -
  have "\<mu> ({a}\<times>{b}) = M1.\<mu> {a} * M2.\<mu> {b}"
    using M1.sets_eq_Pow M2.sets_eq_Pow assms
    by (subst pair_measure_times) auto
  then show ?thesis by simp
qed

lemma (in pair_finite_space) pair_measure_singleton[simp]:
  assumes "x \<in> space M1 \<times> space M2"
  shows "\<mu> {x} = M1.\<mu> {fst x} * M2.\<mu> {snd x}"
  using pair_measure_Pair assms by (cases x) auto

sublocale pair_finite_space \<subseteq> finite_measure_space P
  by default (auto simp: space_pair_measure)

end