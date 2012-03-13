(*  Title:      HOL/Probability/Finite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Finite product measures*}

theory Finite_Product_Measure
imports Binary_Product_Measure
begin

lemma Pi_iff: "f \<in> Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i)"
  unfolding Pi_def by auto

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

section "Finite product spaces"

section "Products"

locale product_sigma_algebra =
  fixes M :: "'i \<Rightarrow> ('a, 'b) measure_space_scheme"
  assumes sigma_algebras: "\<And>i. sigma_algebra (M i)"

locale finite_product_sigma_algebra = product_sigma_algebra M
  for M :: "'i \<Rightarrow> ('a, 'b) measure_space_scheme" +
  fixes I :: "'i set"
  assumes finite_index[simp, intro]: "finite I"

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

lemma Int_stable_product_algebra_generator:
  "(\<And>i. i \<in> I \<Longrightarrow> Int_stable (M i)) \<Longrightarrow> Int_stable (product_algebra_generator I M)"
  by (auto simp add: product_algebra_generator_def Int_stable_def PiE_Int Pi_iff)

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
    using M.sets_into_space `i \<in> I` by (fastforce dest: Pi_mem split: split_if_asm)
  then show "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>M I M) \<in> sets (Pi\<^isub>M I M)"
    using `A \<in> sets (M i)` by (auto intro!: product_algebraI)
qed (insert `i \<in> I`, auto)

lemma (in sigma_algebra) measurable_restrict:
  assumes I: "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> sets (N i) \<subseteq> Pow (space (N i))"
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> measurable M (N i)"
  shows "(\<lambda>x. \<lambda>i\<in>I. X i x) \<in> measurable M (Pi\<^isub>M I N)"
  unfolding product_algebra_def
proof (simp, rule measurable_sigma)
  show "sets (product_algebra_generator I N) \<subseteq> Pow (space (product_algebra_generator I N))"
    by (rule product_algebra_generator_sets_into_space) fact
  show "(\<lambda>x. \<lambda>i\<in>I. X i x) \<in> space M \<rightarrow> space (product_algebra_generator I N)"
    using X by (auto simp: measurable_def)
  fix E assume "E \<in> sets (product_algebra_generator I N)"
  then obtain F where "E = Pi\<^isub>E I F" and F: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> sets (N i)"
    by (auto simp: product_algebra_generator_def)
  then have "(\<lambda>x. \<lambda>i\<in>I. X i x) -` E \<inter> space M = (\<Inter>i\<in>I. X i -` F i \<inter> space M) \<inter> space M"
    by (auto simp: Pi_iff)
  also have "\<dots> \<in> sets M"
  proof cases
    assume "I = {}" then show ?thesis by simp
  next
    assume "I \<noteq> {}" with X F I show ?thesis
      by (intro finite_INT measurable_sets Int) auto
  qed
  finally show "(\<lambda>x. \<lambda>i\<in>I. X i x) -` E \<inter> space M \<in> sets M" .
qed

locale product_sigma_finite = product_sigma_algebra M
  for M :: "'i \<Rightarrow> ('a,'b) measure_space_scheme" +
  assumes sigma_finite_measures: "\<And>i. sigma_finite_measure (M i)"

sublocale product_sigma_finite \<subseteq> M: sigma_finite_measure "M i" for i
  by (rule sigma_finite_measures)

locale finite_product_sigma_finite = finite_product_sigma_algebra M I + product_sigma_finite M
  for M :: "'i \<Rightarrow> ('a,'b) measure_space_scheme" and I :: "'i set"

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
    by (auto simp: setprod_ereal_0 intro!: bexI)
  moreover
  have "\<exists>j\<in>I. (SOME F'. Pi\<^isub>E I F = Pi\<^isub>E I F') j = {}"
    by (rule someI2[where P="\<lambda>F'. Pi\<^isub>E I F = Pi\<^isub>E I F'"])
       (insert empty, auto simp: Pi_eq_empty_iff[symmetric])
  then have "(\<Prod>j\<in>I. M.\<mu> j ((SOME F'. Pi\<^isub>E I F = Pi\<^isub>E I F') j)) = 0"
    by (auto simp: setprod_ereal_0 intro!: bexI)
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
  let ?\<nu> = "(\<lambda>A. if A = {} then 0 else 1) :: 'd set \<Rightarrow> ereal"
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
    let ?m = "\<lambda>A. measure (Pi\<^isub>M I M\<lparr>measure := \<nu>\<rparr> \<Otimes>\<^isub>M M i) (?h -` A \<inter> space P.P)"
    { fix A assume A: "A \<in> (\<Pi> i\<in>insert i I. sets (M i))"
      then have *: "?h -` Pi\<^isub>E (insert i I) A \<inter> space P.P = Pi\<^isub>E I A \<times> A i"
        using `i \<notin> I` M.sets_into_space by (auto simp: space_pair_measure space_product_algebra) blast
      show "?m (Pi\<^isub>E (insert i I) A) = (\<Prod>i\<in>insert i I. M.\<mu> i (A i))"
        unfolding * using A
        apply (subst P.pair_measure_times)
        using A apply fastforce
        using A apply fastforce
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
      let ?F = "\<lambda>k. \<Pi>\<^isub>E j \<in> insert i I. F j k"
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
    unfolding positive_integral_def simple_function_def simple_integral_def [abs_def]
  proof (simp add: P_empty, intro antisym)
    show "f (\<lambda>k. undefined) \<le> (SUP f:{g. g \<le> max 0 \<circ> f}. f (\<lambda>k. undefined))"
      by (intro SUP_upper) (auto simp: le_fun_def split: split_max)
    show "(SUP f:{g. g \<le> max 0 \<circ> f}. f (\<lambda>k. undefined)) \<le> f (\<lambda>k. undefined)" using pos
      by (intro SUP_least) (auto simp: le_fun_def simp: max_def split: split_if_asm)
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
  let ?X = "\<lambda>S. ?g -` S \<inter> space P.P"
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
      by (rule Int_stable_product_algebra_generator)
         (auto simp: Int_stable_def)
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
    let ?f = "\<lambda>y. f (restrict (x(i := y)) (insert i I))"
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
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "finite I" and borel: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable (M i)"
  and pos: "\<And>i x. i \<in> I \<Longrightarrow> 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^isub>M I M) = (\<Prod>i\<in>I. integral\<^isup>P (M i) (f i))"
using assms proof induct
  case empty
  interpret finite_product_sigma_finite M "{}" by default auto
  show ?case by simp
next
  case (insert i I)
  note `finite I`[intro, simp]
  interpret I: finite_product_sigma_finite M I by default auto
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using insert by (auto intro!: setprod_cong)
  have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow> (\<lambda>x. (\<Prod>i\<in>J. f i (x i))) \<in> borel_measurable (Pi\<^isub>M J M)"
    using sets_into_space insert
    by (intro sigma_algebra.borel_measurable_ereal_setprod sigma_algebra_product_algebra
              measurable_comp[OF measurable_component_singleton, unfolded comp_def])
       auto
  then show ?case
    apply (simp add: product_positive_integral_insert[OF insert(1,2) prod])
    apply (simp add: insert * pos borel setprod_ereal_pos M.positive_integral_multc)
    apply (subst I.positive_integral_cmult)
    apply (auto simp add: pos borel insert setprod_ereal_pos positive_integral_positive)
    done
qed

lemma (in product_sigma_finite) product_integral_singleton:
  assumes f: "f \<in> borel_measurable (M i)"
  shows "(\<integral>x. f (x i) \<partial>Pi\<^isub>M {i} M) = integral\<^isup>L (M i) f"
proof -
  interpret I: finite_product_sigma_finite M "{i}" by default simp
  have *: "(\<lambda>x. ereal (f x)) \<in> borel_measurable (M i)"
    "(\<lambda>x. ereal (- f x)) \<in> borel_measurable (M i)"
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
    let ?f = "\<lambda>y. f (restrict (x(i := y)) (insert i I))"
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
    have "(\<integral>\<^isup>+x. ereal (abs (?f x)) \<partial>P) = (\<integral>\<^isup>+x. (\<Prod>i\<in>I. ereal (abs (f i (x i)))) \<partial>P)"
      by (simp add: setprod_ereal abs_setprod)
    also have "\<dots> = (\<Prod>i\<in>I. (\<integral>\<^isup>+x. ereal (abs (f i x)) \<partial>M i))"
      using f by (subst product_positive_integral_setprod) auto
    also have "\<dots> < \<infinity>"
      using integrable[THEN M.integrable_abs]
      by (simp add: setprod_PInf integrable_def M.positive_integral_positive)
    finally show "(\<integral>\<^isup>+x. ereal (abs (?f x)) \<partial>P) \<noteq> \<infinity>" by auto
    have "(\<integral>\<^isup>+x. ereal (- abs (?f x)) \<partial>P) = (\<integral>\<^isup>+x. 0 \<partial>P)"
      by (intro positive_integral_cong_pos) auto
    then show "(\<integral>\<^isup>+x. ereal (- abs (?f x)) \<partial>P) \<noteq> \<infinity>" by simp
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

end