(*  Title:      HOL/Probability/Finite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Finite product measures*}

theory Finite_Product_Measure
imports Binary_Product_Measure
begin

lemma split_const: "(\<lambda>(i, j). c) = (\<lambda>_. c)"
  by auto

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

lemma extensional_insert[intro, simp]:
  assumes "a \<in> extensional (insert i I)"
  shows "a(i := b) \<in> extensional (insert i I)"
  using assms unfolding extensional_def by auto

lemma extensional_Int[simp]:
  "extensional I \<inter> extensional I' = extensional (I \<inter> I')"
  unfolding extensional_def by auto

definition
  "merge I J = (\<lambda>(x, y) i. if i \<in> I then x i else if i \<in> J then y i else undefined)"

lemma merge_apply[simp]:
  "I \<inter> J = {} \<Longrightarrow> i \<in> I \<Longrightarrow> merge I J (x, y) i = x i"
  "I \<inter> J = {} \<Longrightarrow> i \<in> J \<Longrightarrow> merge I J (x, y) i = y i"
  "J \<inter> I = {} \<Longrightarrow> i \<in> I \<Longrightarrow> merge I J (x, y) i = x i"
  "J \<inter> I = {} \<Longrightarrow> i \<in> J \<Longrightarrow> merge I J (x, y) i = y i"
  "i \<notin> I \<Longrightarrow> i \<notin> J \<Longrightarrow> merge I J (x, y) i = undefined"
  unfolding merge_def by auto

lemma merge_commute:
  "I \<inter> J = {} \<Longrightarrow> merge I J (x, y) = merge J I (y, x)"
  by (auto simp: merge_def intro!: ext)

lemma Pi_cancel_merge_range[simp]:
  "I \<inter> J = {} \<Longrightarrow> x \<in> Pi I (merge I J (A, B)) \<longleftrightarrow> x \<in> Pi I A"
  "I \<inter> J = {} \<Longrightarrow> x \<in> Pi I (merge J I (B, A)) \<longleftrightarrow> x \<in> Pi I A"
  "J \<inter> I = {} \<Longrightarrow> x \<in> Pi I (merge I J (A, B)) \<longleftrightarrow> x \<in> Pi I A"
  "J \<inter> I = {} \<Longrightarrow> x \<in> Pi I (merge J I (B, A)) \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: Pi_def)

lemma Pi_cancel_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow> merge I J (x, y) \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  "J \<inter> I = {} \<Longrightarrow> merge I J (x, y) \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  "I \<inter> J = {} \<Longrightarrow> merge I J (x, y) \<in> Pi J B \<longleftrightarrow> y \<in> Pi J B"
  "J \<inter> I = {} \<Longrightarrow> merge I J (x, y) \<in> Pi J B \<longleftrightarrow> y \<in> Pi J B"
  by (auto simp: Pi_def)

lemma extensional_merge[simp]: "merge I J (x, y) \<in> extensional (I \<union> J)"
  by (auto simp: extensional_def)

lemma restrict_Pi_cancel: "restrict x I \<in> Pi I A \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: restrict_def Pi_def)

lemma restrict_merge[simp]:
  "I \<inter> J = {} \<Longrightarrow> restrict (merge I J (x, y)) I = restrict x I"
  "I \<inter> J = {} \<Longrightarrow> restrict (merge I J (x, y)) J = restrict y J"
  "J \<inter> I = {} \<Longrightarrow> restrict (merge I J (x, y)) I = restrict x I"
  "J \<inter> I = {} \<Longrightarrow> restrict (merge I J (x, y)) J = restrict y J"
  by (auto simp: restrict_def)

lemma extensional_insert_undefined[intro, simp]:
  assumes "a \<in> extensional (insert i I)"
  shows "a(i := undefined) \<in> extensional I"
  using assms unfolding extensional_def by auto

lemma extensional_insert_cancel[intro, simp]:
  assumes "a \<in> extensional I"
  shows "a \<in> extensional (insert i I)"
  using assms unfolding extensional_def by auto

lemma merge_singleton[simp]: "i \<notin> I \<Longrightarrow> merge I {i} (x,y) = restrict (x(i := y i)) (insert i I)"
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
  shows "(\<lambda>x. (restrict x I, restrict x J)) -` (Pi\<^isub>E I E \<times> Pi\<^isub>E J F) = Pi (I \<union> J) (merge I J (E, F))"
  using assms by (auto simp: restrict_Pi_cancel)

lemma merge_vimage:
  assumes "I \<inter> J = {}"
  shows "merge I J -` Pi\<^isub>E (I \<union> J) E = Pi I E \<times> Pi J E"
  using assms by (auto simp: restrict_Pi_cancel)

lemma restrict_fupd[simp]: "i \<notin> I \<Longrightarrow> restrict (f (i := x)) I = restrict f I"
  by (auto simp: restrict_def)

lemma merge_restrict[simp]:
  "merge I J (restrict x I, y) = merge I J (x, y)"
  "merge I J (x, restrict y J) = merge I J (x, y)"
  unfolding merge_def by auto

lemma merge_x_x_eq_restrict[simp]:
  "merge I J (x, x) = restrict x (I \<union> J)"
  unfolding merge_def by auto

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

definition prod_emb where
  "prod_emb I M K X = (\<lambda>x. restrict x K) -` X \<inter> (PIE i:I. space (M i))"

lemma prod_emb_iff: 
  "f \<in> prod_emb I M K X \<longleftrightarrow> f \<in> extensional I \<and> (restrict f K \<in> X) \<and> (\<forall>i\<in>I. f i \<in> space (M i))"
  unfolding prod_emb_def by auto

lemma
  shows prod_emb_empty[simp]: "prod_emb M L K {} = {}"
    and prod_emb_Un[simp]: "prod_emb M L K (A \<union> B) = prod_emb M L K A \<union> prod_emb M L K B"
    and prod_emb_Int: "prod_emb M L K (A \<inter> B) = prod_emb M L K A \<inter> prod_emb M L K B"
    and prod_emb_UN[simp]: "prod_emb M L K (\<Union>i\<in>I. F i) = (\<Union>i\<in>I. prod_emb M L K (F i))"
    and prod_emb_INT[simp]: "I \<noteq> {} \<Longrightarrow> prod_emb M L K (\<Inter>i\<in>I. F i) = (\<Inter>i\<in>I. prod_emb M L K (F i))"
    and prod_emb_Diff[simp]: "prod_emb M L K (A - B) = prod_emb M L K A - prod_emb M L K B"
  by (auto simp: prod_emb_def)

lemma prod_emb_PiE: "J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> E i \<subseteq> space (M i)) \<Longrightarrow>
    prod_emb I M J (\<Pi>\<^isub>E i\<in>J. E i) = (\<Pi>\<^isub>E i\<in>I. if i \<in> J then E i else space (M i))"
  by (force simp: prod_emb_def Pi_iff split_if_mem2)

lemma prod_emb_PiE_same_index[simp]: "(\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> space (M i)) \<Longrightarrow> prod_emb I M I (Pi\<^isub>E I E) = Pi\<^isub>E I E"
  by (auto simp: prod_emb_def Pi_iff)

definition PiM :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<Rightarrow> 'a) measure" where
  "PiM I M = extend_measure (\<Pi>\<^isub>E i\<in>I. space (M i))
    {(J, X). (J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}
    (\<lambda>(J, X). prod_emb I M J (\<Pi>\<^isub>E j\<in>J. X j))
    (\<lambda>(J, X). \<Prod>j\<in>J \<union> {i\<in>I. emeasure (M i) (space (M i)) \<noteq> 1}. if j \<in> J then emeasure (M j) (X j) else emeasure (M j) (space (M j)))"

definition prod_algebra :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<Rightarrow> 'a) set set" where
  "prod_algebra I M = (\<lambda>(J, X). prod_emb I M J (\<Pi>\<^isub>E j\<in>J. X j)) `
    {(J, X). (J \<noteq> {} \<or> I = {}) \<and> finite J \<and> J \<subseteq> I \<and> X \<in> (\<Pi> j\<in>J. sets (M j))}"

abbreviation
  "Pi\<^isub>M I M \<equiv> PiM I M"

syntax
  "_PiM" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a measure \<Rightarrow> ('i => 'a) measure"  ("(3PIM _:_./ _)" 10)

syntax (xsymbols)
  "_PiM" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a measure \<Rightarrow> ('i => 'a) measure"  ("(3\<Pi>\<^isub>M _\<in>_./ _)"  10)

syntax (HTML output)
  "_PiM" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a measure \<Rightarrow> ('i => 'a) measure"  ("(3\<Pi>\<^isub>M _\<in>_./ _)"  10)

translations
  "PIM x:I. M" == "CONST PiM I (%x. M)"

lemma prod_algebra_sets_into_space:
  "prod_algebra I M \<subseteq> Pow (\<Pi>\<^isub>E i\<in>I. space (M i))"
  using assms by (auto simp: prod_emb_def prod_algebra_def)

lemma prod_algebra_eq_finite:
  assumes I: "finite I"
  shows "prod_algebra I M = {(\<Pi>\<^isub>E i\<in>I. X i) |X. X \<in> (\<Pi> j\<in>I. sets (M j))}" (is "?L = ?R")
proof (intro iffI set_eqI)
  fix A assume "A \<in> ?L"
  then obtain J E where J: "J \<noteq> {} \<or> I = {}" "finite J" "J \<subseteq> I" "\<forall>i\<in>J. E i \<in> sets (M i)"
    and A: "A = prod_emb I M J (PIE j:J. E j)"
    by (auto simp: prod_algebra_def)
  let ?A = "\<Pi>\<^isub>E i\<in>I. if i \<in> J then E i else space (M i)"
  have A: "A = ?A"
    unfolding A using J by (intro prod_emb_PiE sets_into_space) auto
  show "A \<in> ?R" unfolding A using J top
    by (intro CollectI exI[of _ "\<lambda>i. if i \<in> J then E i else space (M i)"]) simp
next
  fix A assume "A \<in> ?R"
  then obtain X where "A = (\<Pi>\<^isub>E i\<in>I. X i)" and X: "X \<in> (\<Pi> j\<in>I. sets (M j))" by auto
  then have A: "A = prod_emb I M I (\<Pi>\<^isub>E i\<in>I. X i)"
    using sets_into_space by (force simp: prod_emb_def Pi_iff)
  from X I show "A \<in> ?L" unfolding A
    by (auto simp: prod_algebra_def)
qed

lemma prod_algebraI:
  "finite J \<Longrightarrow> (J \<noteq> {} \<or> I = {}) \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> E i \<in> sets (M i))
    \<Longrightarrow> prod_emb I M J (PIE j:J. E j) \<in> prod_algebra I M"
  by (auto simp: prod_algebra_def Pi_iff)

lemma prod_algebraE:
  assumes A: "A \<in> prod_algebra I M"
  obtains J E where "A = prod_emb I M J (PIE j:J. E j)"
    "finite J" "J \<noteq> {} \<or> I = {}" "J \<subseteq> I" "\<And>i. i \<in> J \<Longrightarrow> E i \<in> sets (M i)" 
  using A by (auto simp: prod_algebra_def)

lemma prod_algebraE_all:
  assumes A: "A \<in> prod_algebra I M"
  obtains E where "A = Pi\<^isub>E I E" "E \<in> (\<Pi> i\<in>I. sets (M i))"
proof -
  from A obtain E J where A: "A = prod_emb I M J (Pi\<^isub>E J E)"
    and J: "J \<subseteq> I" and E: "E \<in> (\<Pi> i\<in>J. sets (M i))"
    by (auto simp: prod_algebra_def)
  from E have "\<And>i. i \<in> J \<Longrightarrow> E i \<subseteq> space (M i)"
    using sets_into_space by auto
  then have "A = (\<Pi>\<^isub>E i\<in>I. if i\<in>J then E i else space (M i))"
    using A J by (auto simp: prod_emb_PiE)
  moreover then have "(\<lambda>i. if i\<in>J then E i else space (M i)) \<in> (\<Pi> i\<in>I. sets (M i))"
    using top E by auto
  ultimately show ?thesis using that by auto
qed

lemma Int_stable_prod_algebra: "Int_stable (prod_algebra I M)"
proof (unfold Int_stable_def, safe)
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] guess J E . note A = this
  fix B assume "B \<in> prod_algebra I M"
  from prod_algebraE[OF this] guess K F . note B = this
  have "A \<inter> B = prod_emb I M (J \<union> K) (\<Pi>\<^isub>E i\<in>J \<union> K. (if i \<in> J then E i else space (M i)) \<inter> 
      (if i \<in> K then F i else space (M i)))"
    unfolding A B using A(2,3,4) A(5)[THEN sets_into_space] B(2,3,4) B(5)[THEN sets_into_space]
    apply (subst (1 2 3) prod_emb_PiE)
    apply (simp_all add: subset_eq PiE_Int)
    apply blast
    apply (intro PiE_cong)
    apply auto
    done
  also have "\<dots> \<in> prod_algebra I M"
    using A B by (auto intro!: prod_algebraI)
  finally show "A \<inter> B \<in> prod_algebra I M" .
qed

lemma prod_algebra_mono:
  assumes space: "\<And>i. i \<in> I \<Longrightarrow> space (E i) = space (F i)"
  assumes sets: "\<And>i. i \<in> I \<Longrightarrow> sets (E i) \<subseteq> sets (F i)"
  shows "prod_algebra I E \<subseteq> prod_algebra I F"
proof
  fix A assume "A \<in> prod_algebra I E"
  then obtain J G where J: "J \<noteq> {} \<or> I = {}" "finite J" "J \<subseteq> I"
    and A: "A = prod_emb I E J (\<Pi>\<^isub>E i\<in>J. G i)"
    and G: "\<And>i. i \<in> J \<Longrightarrow> G i \<in> sets (E i)"
    by (auto simp: prod_algebra_def)
  moreover
  from space have "(\<Pi>\<^isub>E i\<in>I. space (E i)) = (\<Pi>\<^isub>E i\<in>I. space (F i))"
    by (rule PiE_cong)
  with A have "A = prod_emb I F J (\<Pi>\<^isub>E i\<in>J. G i)"
    by (simp add: prod_emb_def)
  moreover
  from sets G J have "\<And>i. i \<in> J \<Longrightarrow> G i \<in> sets (F i)"
    by auto
  ultimately show "A \<in> prod_algebra I F"
    apply (simp add: prod_algebra_def image_iff)
    apply (intro exI[of _ J] exI[of _ G] conjI)
    apply auto
    done
qed

lemma space_PiM: "space (\<Pi>\<^isub>M i\<in>I. M i) = (\<Pi>\<^isub>E i\<in>I. space (M i))"
  using prod_algebra_sets_into_space unfolding PiM_def prod_algebra_def by (intro space_extend_measure) simp

lemma sets_PiM: "sets (\<Pi>\<^isub>M i\<in>I. M i) = sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) (prod_algebra I M)"
  using prod_algebra_sets_into_space unfolding PiM_def prod_algebra_def by (intro sets_extend_measure) simp

lemma sets_PiM_single: "sets (PiM I M) =
    sigma_sets (\<Pi>\<^isub>E i\<in>I. space (M i)) {{f\<in>\<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A} | i A. i \<in> I \<and> A \<in> sets (M i)}"
    (is "_ = sigma_sets ?\<Omega> ?R")
  unfolding sets_PiM
proof (rule sigma_sets_eqI)
  interpret R: sigma_algebra ?\<Omega> "sigma_sets ?\<Omega> ?R" by (rule sigma_algebra_sigma_sets) auto
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] guess J X . note X = this
  show "A \<in> sigma_sets ?\<Omega> ?R"
  proof cases
    assume "I = {}"
    with X have "A = {\<lambda>x. undefined}" by (auto simp: prod_emb_def)
    with `I = {}` show ?thesis by (auto intro!: sigma_sets_top)
  next
    assume "I \<noteq> {}"
    with X have "A = (\<Inter>j\<in>J. {f\<in>(\<Pi>\<^isub>E i\<in>I. space (M i)). f j \<in> X j})"
      using sets_into_space[OF X(5)]
      by (auto simp: prod_emb_PiE[OF _ sets_into_space] Pi_iff split: split_if_asm) blast
    also have "\<dots> \<in> sigma_sets ?\<Omega> ?R"
      using X `I \<noteq> {}` by (intro R.finite_INT sigma_sets.Basic) auto
    finally show "A \<in> sigma_sets ?\<Omega> ?R" .
  qed
next
  fix A assume "A \<in> ?R"
  then obtain i B where A: "A = {f\<in>\<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> B}" "i \<in> I" "B \<in> sets (M i)" 
    by auto
  then have "A = prod_emb I M {i} (\<Pi>\<^isub>E i\<in>{i}. B)"
    using sets_into_space[OF A(3)]
    apply (subst prod_emb_PiE)
    apply (auto simp: Pi_iff split: split_if_asm)
    apply blast
    done
  also have "\<dots> \<in> sigma_sets ?\<Omega> (prod_algebra I M)"
    using A by (intro sigma_sets.Basic prod_algebraI) auto
  finally show "A \<in> sigma_sets ?\<Omega> (prod_algebra I M)" .
qed

lemma sets_PiM_I:
  assumes "finite J" "J \<subseteq> I" "\<forall>i\<in>J. E i \<in> sets (M i)"
  shows "prod_emb I M J (PIE j:J. E j) \<in> sets (PIM i:I. M i)"
proof cases
  assume "J = {}"
  then have "prod_emb I M J (PIE j:J. E j) = (PIE j:I. space (M j))"
    by (auto simp: prod_emb_def)
  then show ?thesis
    by (auto simp add: sets_PiM intro!: sigma_sets_top)
next
  assume "J \<noteq> {}" with assms show ?thesis
    by (auto simp add: sets_PiM prod_algebra_def intro!: sigma_sets.Basic)
qed

lemma measurable_PiM:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^isub>E i\<in>I. space (M i))"
  assumes sets: "\<And>X J. J \<noteq> {} \<or> I = {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)) \<Longrightarrow>
    f -` prod_emb I M J (Pi\<^isub>E J X) \<inter> space N \<in> sets N" 
  shows "f \<in> measurable N (PiM I M)"
  using sets_PiM prod_algebra_sets_into_space space
proof (rule measurable_sigma_sets)
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] guess J X .
  with sets[of J X] show "f -` A \<inter> space N \<in> sets N" by auto
qed

lemma measurable_PiM_Collect:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^isub>E i\<in>I. space (M i))"
  assumes sets: "\<And>X J. J \<noteq> {} \<or> I = {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> (\<And>i. i \<in> J \<Longrightarrow> X i \<in> sets (M i)) \<Longrightarrow>
    {\<omega>\<in>space N. \<forall>i\<in>J. f \<omega> i \<in> X i} \<in> sets N" 
  shows "f \<in> measurable N (PiM I M)"
  using sets_PiM prod_algebra_sets_into_space space
proof (rule measurable_sigma_sets)
  fix A assume "A \<in> prod_algebra I M"
  from prod_algebraE[OF this] guess J X . note X = this
  have "f -` A \<inter> space N = {\<omega> \<in> space N. \<forall>i\<in>J. f \<omega> i \<in> X i}"
    using sets_into_space[OF X(5)] X(2-) space unfolding X(1)
    by (subst prod_emb_PiE) (auto simp: Pi_iff split: split_if_asm)
  also have "\<dots> \<in> sets N" using X(3,2,4,5) by (rule sets)
  finally show "f -` A \<inter> space N \<in> sets N" .
qed

lemma measurable_PiM_single:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^isub>E i\<in>I. space (M i))"
  assumes sets: "\<And>A i. i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow> {\<omega> \<in> space N. f \<omega> i \<in> A} \<in> sets N" 
  shows "f \<in> measurable N (PiM I M)"
  using sets_PiM_single
proof (rule measurable_sigma_sets)
  fix A assume "A \<in> {{f \<in> \<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A} |i A. i \<in> I \<and> A \<in> sets (M i)}"
  then obtain B i where "A = {f \<in> \<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> B}" and B: "i \<in> I" "B \<in> sets (M i)"
    by auto
  with space have "f -` A \<inter> space N = {\<omega> \<in> space N. f \<omega> i \<in> B}" by auto
  also have "\<dots> \<in> sets N" using B by (rule sets)
  finally show "f -` A \<inter> space N \<in> sets N" .
qed (auto simp: space)

lemma sets_PiM_I_finite[simp, intro]:
  assumes "finite I" and sets: "(\<And>i. i \<in> I \<Longrightarrow> E i \<in> sets (M i))"
  shows "(PIE j:I. E j) \<in> sets (PIM i:I. M i)"
  using sets_PiM_I[of I I E M] sets_into_space[OF sets] `finite I` sets by auto

lemma measurable_component_update:
  assumes "x \<in> space (Pi\<^isub>M I M)" and "i \<notin> I"
  shows "(\<lambda>v. x(i := v)) \<in> measurable (M i) (Pi\<^isub>M (insert i I) M)" (is "?f \<in> _")
proof (intro measurable_PiM_single)
  fix j A assume "j \<in> insert i I" "A \<in> sets (M j)"
  moreover have "{\<omega> \<in> space (M i). (x(i := \<omega>)) j \<in> A} =
    (if i = j then space (M i) \<inter> A else if x j \<in> A then space (M i) else {})"
    by auto
  ultimately show "{\<omega> \<in> space (M i). (x(i := \<omega>)) j \<in> A} \<in> sets (M i)"
    by auto
qed (insert sets_into_space assms, auto simp: space_PiM)

lemma measurable_component_singleton:
  assumes "i \<in> I" shows "(\<lambda>x. x i) \<in> measurable (Pi\<^isub>M I M) (M i)"
proof (unfold measurable_def, intro CollectI conjI ballI)
  fix A assume "A \<in> sets (M i)"
  then have "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>M I M) = prod_emb I M {i} (\<Pi>\<^isub>E j\<in>{i}. A)"
    using sets_into_space `i \<in> I`
    by (fastforce dest: Pi_mem simp: prod_emb_def space_PiM split: split_if_asm)
  then show "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>M I M) \<in> sets (Pi\<^isub>M I M)"
    using `A \<in> sets (M i)` `i \<in> I` by (auto intro!: sets_PiM_I)
qed (insert `i \<in> I`, auto simp: space_PiM)

lemma measurable_add_dim:
  "(\<lambda>(f, y). f(i := y)) \<in> measurable (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) (Pi\<^isub>M (insert i I) M)"
    (is "?f \<in> measurable ?P ?I")
proof (rule measurable_PiM_single)
  fix j A assume j: "j \<in> insert i I" and A: "A \<in> sets (M j)"
  have "{\<omega> \<in> space ?P. (\<lambda>(f, x). fun_upd f i x) \<omega> j \<in> A} =
    (if j = i then space (Pi\<^isub>M I M) \<times> A else ((\<lambda>x. x j) \<circ> fst) -` A \<inter> space ?P)"
    using sets_into_space[OF A] by (auto simp add: space_pair_measure space_PiM)
  also have "\<dots> \<in> sets ?P"
    using A j
    by (auto intro!: measurable_sets[OF measurable_comp, OF _ measurable_component_singleton])
  finally show "{\<omega> \<in> space ?P. prod_case (\<lambda>f. fun_upd f i) \<omega> j \<in> A} \<in> sets ?P" .
qed (auto simp: space_pair_measure space_PiM)

lemma measurable_merge:
  "merge I J \<in> measurable (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) (Pi\<^isub>M (I \<union> J) M)"
    (is "?f \<in> measurable ?P ?U")
proof (rule measurable_PiM_single)
  fix i A assume A: "A \<in> sets (M i)" "i \<in> I \<union> J"
  then have "{\<omega> \<in> space ?P. merge I J \<omega> i \<in> A} =
    (if i \<in> I then ((\<lambda>x. x i) \<circ> fst) -` A \<inter> space ?P else ((\<lambda>x. x i) \<circ> snd) -` A \<inter> space ?P)"
    by (auto simp: merge_def)
  also have "\<dots> \<in> sets ?P"
    using A
    by (auto intro!: measurable_sets[OF measurable_comp, OF _ measurable_component_singleton])
  finally show "{\<omega> \<in> space ?P. merge I J \<omega> i \<in> A} \<in> sets ?P" .
qed (auto simp: space_pair_measure space_PiM Pi_iff merge_def extensional_def)

lemma measurable_restrict:
  assumes X: "\<And>i. i \<in> I \<Longrightarrow> X i \<in> measurable N (M i)"
  shows "(\<lambda>x. \<lambda>i\<in>I. X i x) \<in> measurable N (Pi\<^isub>M I M)"
proof (rule measurable_PiM_single)
  fix A i assume A: "i \<in> I" "A \<in> sets (M i)"
  then have "{\<omega> \<in> space N. (\<lambda>i\<in>I. X i \<omega>) i \<in> A} = X i -` A \<inter> space N"
    by auto
  then show "{\<omega> \<in> space N. (\<lambda>i\<in>I. X i \<omega>) i \<in> A} \<in> sets N"
    using A X by (auto intro!: measurable_sets)
qed (insert X, auto dest: measurable_space)

locale product_sigma_finite =
  fixes M :: "'i \<Rightarrow> 'a measure"
  assumes sigma_finite_measures: "\<And>i. sigma_finite_measure (M i)"

sublocale product_sigma_finite \<subseteq> M: sigma_finite_measure "M i" for i
  by (rule sigma_finite_measures)

locale finite_product_sigma_finite = product_sigma_finite M for M :: "'i \<Rightarrow> 'a measure" +
  fixes I :: "'i set"
  assumes finite_index: "finite I"

lemma (in finite_product_sigma_finite) sigma_finite_pairs:
  "\<exists>F::'i \<Rightarrow> nat \<Rightarrow> 'a set.
    (\<forall>i\<in>I. range (F i) \<subseteq> sets (M i)) \<and>
    (\<forall>k. \<forall>i\<in>I. emeasure (M i) (F i k) \<noteq> \<infinity>) \<and> incseq (\<lambda>k. \<Pi>\<^isub>E i\<in>I. F i k) \<and>
    (\<Union>k. \<Pi>\<^isub>E i\<in>I. F i k) = space (PiM I M)"
proof -
  have "\<forall>i::'i. \<exists>F::nat \<Rightarrow> 'a set. range F \<subseteq> sets (M i) \<and> incseq F \<and> (\<Union>i. F i) = space (M i) \<and> (\<forall>k. emeasure (M i) (F k) \<noteq> \<infinity>)"
    using M.sigma_finite_incseq by metis
  from choice[OF this] guess F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set" ..
  then have F: "\<And>i. range (F i) \<subseteq> sets (M i)" "\<And>i. incseq (F i)" "\<And>i. (\<Union>j. F i j) = space (M i)" "\<And>i k. emeasure (M i) (F i k) \<noteq> \<infinity>"
    by auto
  let ?F = "\<lambda>k. \<Pi>\<^isub>E i\<in>I. F i k"
  note space_PiM[simp]
  show ?thesis
  proof (intro exI[of _ F] conjI allI incseq_SucI set_eqI iffI ballI)
    fix i show "range (F i) \<subseteq> sets (M i)" by fact
  next
    fix i k show "emeasure (M i) (F i k) \<noteq> \<infinity>" by fact
  next
    fix A assume "A \<in> (\<Union>i. ?F i)" then show "A \<in> space (PiM I M)"
      using `\<And>i. range (F i) \<subseteq> sets (M i)` sets_into_space
      by auto blast
  next
    fix f assume "f \<in> space (PiM I M)"
    with Pi_UN[OF finite_index, of "\<lambda>k i. F i k"] F
    show "f \<in> (\<Union>i. ?F i)" by (auto simp: incseq_def)
  next
    fix i show "?F i \<subseteq> ?F (Suc i)"
      using `\<And>i. incseq (F i)`[THEN incseq_SucD] by auto
  qed
qed

lemma
  shows space_PiM_empty: "space (Pi\<^isub>M {} M) = {\<lambda>k. undefined}"
    and sets_PiM_empty: "sets (Pi\<^isub>M {} M) = { {}, {\<lambda>k. undefined} }"
  by (simp_all add: space_PiM sets_PiM_single image_constant sigma_sets_empty_eq)

lemma emeasure_PiM_empty[simp]: "emeasure (PiM {} M) {\<lambda>_. undefined} = 1"
proof -
  let ?\<mu> = "\<lambda>A. if A = {} then 0 else (1::ereal)"
  have "emeasure (Pi\<^isub>M {} M) (prod_emb {} M {} (\<Pi>\<^isub>E i\<in>{}. {})) = 1"
  proof (subst emeasure_extend_measure_Pair[OF PiM_def])
    show "positive (PiM {} M) ?\<mu>"
      by (auto simp: positive_def)
    show "countably_additive (PiM {} M) ?\<mu>"
      by (rule countably_additiveI_finite)
         (auto simp: additive_def positive_def sets_PiM_empty space_PiM_empty intro!: )
  qed (auto simp: prod_emb_def)
  also have "(prod_emb {} M {} (\<Pi>\<^isub>E i\<in>{}. {})) = {\<lambda>_. undefined}"
    by (auto simp: prod_emb_def)
  finally show ?thesis
    by simp
qed

lemma PiM_empty: "PiM {} M = count_space {\<lambda>_. undefined}"
  by (rule measure_eqI) (auto simp add: sets_PiM_empty one_ereal_def)

lemma (in product_sigma_finite) emeasure_PiM:
  "finite I \<Longrightarrow> (\<And>i. i\<in>I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> emeasure (PiM I M) (Pi\<^isub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
proof (induct I arbitrary: A rule: finite_induct)
  case (insert i I)
  interpret finite_product_sigma_finite M I by default fact
  have "finite (insert i I)" using `finite I` by auto
  interpret I': finite_product_sigma_finite M "insert i I" by default fact
  let ?h = "(\<lambda>(f, y). f(i := y))"

  let ?P = "distr (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) (Pi\<^isub>M (insert i I) M) ?h"
  let ?\<mu> = "emeasure ?P"
  let ?I = "{j \<in> insert i I. emeasure (M j) (space (M j)) \<noteq> 1}"
  let ?f = "\<lambda>J E j. if j \<in> J then emeasure (M j) (E j) else emeasure (M j) (space (M j))"

  have "emeasure (Pi\<^isub>M (insert i I) M) (prod_emb (insert i I) M (insert i I) (Pi\<^isub>E (insert i I) A)) =
    (\<Prod>i\<in>insert i I. emeasure (M i) (A i))"
  proof (subst emeasure_extend_measure_Pair[OF PiM_def])
    fix J E assume "(J \<noteq> {} \<or> insert i I = {}) \<and> finite J \<and> J \<subseteq> insert i I \<and> E \<in> (\<Pi> j\<in>J. sets (M j))"
    then have J: "J \<noteq> {}" "finite J" "J \<subseteq> insert i I" and E: "\<forall>j\<in>J. E j \<in> sets (M j)" by auto
    let ?p = "prod_emb (insert i I) M J (Pi\<^isub>E J E)"
    let ?p' = "prod_emb I M (J - {i}) (\<Pi>\<^isub>E j\<in>J-{i}. E j)"
    have "?\<mu> ?p =
      emeasure (Pi\<^isub>M I M \<Otimes>\<^isub>M (M i)) (?h -` ?p \<inter> space (Pi\<^isub>M I M \<Otimes>\<^isub>M M i))"
      by (intro emeasure_distr measurable_add_dim sets_PiM_I) fact+
    also have "?h -` ?p \<inter> space (Pi\<^isub>M I M \<Otimes>\<^isub>M M i) = ?p' \<times> (if i \<in> J then E i else space (M i))"
      using J E[rule_format, THEN sets_into_space]
      by (force simp: space_pair_measure space_PiM Pi_iff prod_emb_iff split: split_if_asm)
    also have "emeasure (Pi\<^isub>M I M \<Otimes>\<^isub>M (M i)) (?p' \<times> (if i \<in> J then E i else space (M i))) =
      emeasure (Pi\<^isub>M I M) ?p' * emeasure (M i) (if i \<in> J then (E i) else space (M i))"
      using J E by (intro M.emeasure_pair_measure_Times sets_PiM_I) auto
    also have "?p' = (\<Pi>\<^isub>E j\<in>I. if j \<in> J-{i} then E j else space (M j))"
      using J E[rule_format, THEN sets_into_space]
      by (auto simp: prod_emb_iff Pi_iff split: split_if_asm) blast+
    also have "emeasure (Pi\<^isub>M I M) (\<Pi>\<^isub>E j\<in>I. if j \<in> J-{i} then E j else space (M j)) =
      (\<Prod> j\<in>I. if j \<in> J-{i} then emeasure (M j) (E j) else emeasure (M j) (space (M j)))"
      using E by (subst insert) (auto intro!: setprod_cong)
    also have "(\<Prod>j\<in>I. if j \<in> J - {i} then emeasure (M j) (E j) else emeasure (M j) (space (M j))) *
       emeasure (M i) (if i \<in> J then E i else space (M i)) = (\<Prod>j\<in>insert i I. ?f J E j)"
      using insert by (auto simp: mult_commute intro!: arg_cong2[where f="op *"] setprod_cong)
    also have "\<dots> = (\<Prod>j\<in>J \<union> ?I. ?f J E j)"
      using insert(1,2) J E by (intro setprod_mono_one_right) auto
    finally show "?\<mu> ?p = \<dots>" .

    show "prod_emb (insert i I) M J (Pi\<^isub>E J E) \<in> Pow (\<Pi>\<^isub>E i\<in>insert i I. space (M i))"
      using J E[rule_format, THEN sets_into_space] by (auto simp: prod_emb_iff)
  next
    show "positive (sets (Pi\<^isub>M (insert i I) M)) ?\<mu>" "countably_additive (sets (Pi\<^isub>M (insert i I) M)) ?\<mu>"
      using emeasure_positive[of ?P] emeasure_countably_additive[of ?P] by simp_all
  next
    show "(insert i I \<noteq> {} \<or> insert i I = {}) \<and> finite (insert i I) \<and>
      insert i I \<subseteq> insert i I \<and> A \<in> (\<Pi> j\<in>insert i I. sets (M j))"
      using insert by auto
  qed (auto intro!: setprod_cong)
  with insert show ?case
    by (subst (asm) prod_emb_PiE_same_index) (auto intro!: sets_into_space)
qed (simp add: emeasure_PiM_empty)

lemma (in product_sigma_finite) sigma_finite: 
  assumes "finite I"
  shows "sigma_finite_measure (PiM I M)"
proof -
  interpret finite_product_sigma_finite M I by default fact

  from sigma_finite_pairs guess F :: "'i \<Rightarrow> nat \<Rightarrow> 'a set" ..
  then have F: "\<And>j. j \<in> I \<Longrightarrow> range (F j) \<subseteq> sets (M j)"
    "incseq (\<lambda>k. \<Pi>\<^isub>E j \<in> I. F j k)"
    "(\<Union>k. \<Pi>\<^isub>E j \<in> I. F j k) = space (Pi\<^isub>M I M)"
    "\<And>k. \<And>j. j \<in> I \<Longrightarrow> emeasure (M j) (F j k) \<noteq> \<infinity>"
    by blast+
  let ?F = "\<lambda>k. \<Pi>\<^isub>E j \<in> I. F j k"

  show ?thesis
  proof (unfold_locales, intro exI[of _ ?F] conjI allI)
    show "range ?F \<subseteq> sets (Pi\<^isub>M I M)" using F(1) `finite I` by auto
  next
    from F(3) show "(\<Union>i. ?F i) = space (Pi\<^isub>M I M)" by simp
  next
    fix j
    from F `finite I` setprod_PInf[of I, OF emeasure_nonneg, of M]
    show "emeasure (\<Pi>\<^isub>M i\<in>I. M i) (?F j) \<noteq> \<infinity>"
      by (subst emeasure_PiM) auto
  qed
qed

sublocale finite_product_sigma_finite \<subseteq> sigma_finite_measure "Pi\<^isub>M I M"
  using sigma_finite[OF finite_index] .

lemma (in finite_product_sigma_finite) measure_times:
  "(\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)) \<Longrightarrow> emeasure (Pi\<^isub>M I M) (Pi\<^isub>E I A) = (\<Prod>i\<in>I. emeasure (M i) (A i))"
  using emeasure_PiM[OF finite_index] by auto

lemma (in product_sigma_finite) positive_integral_empty:
  assumes pos: "0 \<le> f (\<lambda>k. undefined)"
  shows "integral\<^isup>P (Pi\<^isub>M {} M) f = f (\<lambda>k. undefined)"
proof -
  interpret finite_product_sigma_finite M "{}" by default (fact finite.emptyI)
  have "\<And>A. emeasure (Pi\<^isub>M {} M) (Pi\<^isub>E {} A) = 1"
    using assms by (subst measure_times) auto
  then show ?thesis
    unfolding positive_integral_def simple_function_def simple_integral_def[abs_def]
  proof (simp add: space_PiM_empty sets_PiM_empty, intro antisym)
    show "f (\<lambda>k. undefined) \<le> (SUP f:{g. g \<le> max 0 \<circ> f}. f (\<lambda>k. undefined))"
      by (intro SUP_upper) (auto simp: le_fun_def split: split_max)
    show "(SUP f:{g. g \<le> max 0 \<circ> f}. f (\<lambda>k. undefined)) \<le> f (\<lambda>k. undefined)" using pos
      by (intro SUP_least) (auto simp: le_fun_def simp: max_def split: split_if_asm)
  qed
qed

lemma (in product_sigma_finite) distr_merge:
  assumes IJ[simp]: "I \<inter> J = {}" and fin: "finite I" "finite J"
  shows "distr (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) (Pi\<^isub>M (I \<union> J) M) (merge I J) = Pi\<^isub>M (I \<union> J) M"
   (is "?D = ?P")
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  have "finite (I \<union> J)" using fin by auto
  interpret IJ: finite_product_sigma_finite M "I \<union> J" by default fact
  interpret P: pair_sigma_finite "Pi\<^isub>M I M" "Pi\<^isub>M J M" by default
  let ?g = "merge I J"

  from IJ.sigma_finite_pairs obtain F where
    F: "\<And>i. i\<in> I \<union> J \<Longrightarrow> range (F i) \<subseteq> sets (M i)"
       "incseq (\<lambda>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k)"
       "(\<Union>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k) = space ?P"
       "\<And>k. \<forall>i\<in>I\<union>J. emeasure (M i) (F i k) \<noteq> \<infinity>"
    by auto
  let ?F = "\<lambda>k. \<Pi>\<^isub>E i\<in>I \<union> J. F i k"
  
  show ?thesis
  proof (rule measure_eqI_generator_eq[symmetric])
    show "Int_stable (prod_algebra (I \<union> J) M)"
      by (rule Int_stable_prod_algebra)
    show "prod_algebra (I \<union> J) M \<subseteq> Pow (\<Pi>\<^isub>E i \<in> I \<union> J. space (M i))"
      by (rule prod_algebra_sets_into_space)
    show "sets ?P = sigma_sets (\<Pi>\<^isub>E i\<in>I \<union> J. space (M i)) (prod_algebra (I \<union> J) M)"
      by (rule sets_PiM)
    then show "sets ?D = sigma_sets (\<Pi>\<^isub>E i\<in>I \<union> J. space (M i)) (prod_algebra (I \<union> J) M)"
      by simp

    show "range ?F \<subseteq> prod_algebra (I \<union> J) M" using F
      using fin by (auto simp: prod_algebra_eq_finite)
    show "(\<Union>i. \<Pi>\<^isub>E ia\<in>I \<union> J. F ia i) = (\<Pi>\<^isub>E i\<in>I \<union> J. space (M i))"
      using F(3) by (simp add: space_PiM)
  next
    fix k
    from F `finite I` setprod_PInf[of "I \<union> J", OF emeasure_nonneg, of M]
    show "emeasure ?P (?F k) \<noteq> \<infinity>" by (subst IJ.measure_times) auto
  next
    fix A assume A: "A \<in> prod_algebra (I \<union> J) M"
    with fin obtain F where A_eq: "A = (Pi\<^isub>E (I \<union> J) F)" and F: "\<forall>i\<in>I \<union> J. F i \<in> sets (M i)"
      by (auto simp add: prod_algebra_eq_finite)
    let ?B = "Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M"
    let ?X = "?g -` A \<inter> space ?B"
    have "Pi\<^isub>E I F \<subseteq> space (Pi\<^isub>M I M)" "Pi\<^isub>E J F \<subseteq> space (Pi\<^isub>M J M)"
      using F[rule_format, THEN sets_into_space] by (auto simp: space_PiM)
    then have X: "?X = (Pi\<^isub>E I F \<times> Pi\<^isub>E J F)"
      unfolding A_eq by (subst merge_vimage) (auto simp: space_pair_measure space_PiM)
    have "emeasure ?D A = emeasure ?B ?X"
      using A by (intro emeasure_distr measurable_merge) (auto simp: sets_PiM)
    also have "emeasure ?B ?X = (\<Prod>i\<in>I. emeasure (M i) (F i)) * (\<Prod>i\<in>J. emeasure (M i) (F i))"
      using `finite J` `finite I` F X
      by (simp add: J.emeasure_pair_measure_Times I.measure_times J.measure_times Pi_iff)
    also have "\<dots> = (\<Prod>i\<in>I \<union> J. emeasure (M i) (F i))"
      using `finite J` `finite I` `I \<inter> J = {}`  by (simp add: setprod_Un_one)
    also have "\<dots> = emeasure ?P (Pi\<^isub>E (I \<union> J) F)"
      using `finite J` `finite I` F unfolding A
      by (intro IJ.measure_times[symmetric]) auto
    finally show "emeasure ?P A = emeasure ?D A" using A_eq by simp
  qed
qed

lemma (in product_sigma_finite) product_positive_integral_fold:
  assumes IJ: "I \<inter> J = {}" "finite I" "finite J"
  and f: "f \<in> borel_measurable (Pi\<^isub>M (I \<union> J) M)"
  shows "integral\<^isup>P (Pi\<^isub>M (I \<union> J) M) f =
    (\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (merge I J (x, y)) \<partial>(Pi\<^isub>M J M)) \<partial>(Pi\<^isub>M I M))"
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  interpret P: pair_sigma_finite "Pi\<^isub>M I M" "Pi\<^isub>M J M" by default
  have P_borel: "(\<lambda>x. f (merge I J x)) \<in> borel_measurable (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M)"
    using measurable_comp[OF measurable_merge f] by (simp add: comp_def)
  show ?thesis
    apply (subst distr_merge[OF IJ, symmetric])
    apply (subst positive_integral_distr[OF measurable_merge f])
    apply (subst J.positive_integral_fst_measurable(2)[symmetric, OF P_borel])
    apply simp
    done
qed

lemma (in product_sigma_finite) distr_singleton:
  "distr (Pi\<^isub>M {i} M) (M i) (\<lambda>x. x i) = M i" (is "?D = _")
proof (intro measure_eqI[symmetric])
  interpret I: finite_product_sigma_finite M "{i}" by default simp
  fix A assume A: "A \<in> sets (M i)"
  moreover then have "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>M {i} M) = (\<Pi>\<^isub>E i\<in>{i}. A)"
    using sets_into_space by (auto simp: space_PiM)
  ultimately show "emeasure (M i) A = emeasure ?D A"
    using A I.measure_times[of "\<lambda>_. A"]
    by (simp add: emeasure_distr measurable_component_singleton)
qed simp

lemma (in product_sigma_finite) product_positive_integral_singleton:
  assumes f: "f \<in> borel_measurable (M i)"
  shows "integral\<^isup>P (Pi\<^isub>M {i} M) (\<lambda>x. f (x i)) = integral\<^isup>P (M i) f"
proof -
  interpret I: finite_product_sigma_finite M "{i}" by default simp
  from f show ?thesis
    apply (subst distr_singleton[symmetric])
    apply (subst positive_integral_distr[OF measurable_component_singleton])
    apply simp_all
    done
qed

lemma (in product_sigma_finite) product_positive_integral_insert:
  assumes I[simp]: "finite I" "i \<notin> I"
    and f: "f \<in> borel_measurable (Pi\<^isub>M (insert i I) M)"
  shows "integral\<^isup>P (Pi\<^isub>M (insert i I) M) f = (\<integral>\<^isup>+ x. (\<integral>\<^isup>+ y. f (x(i := y)) \<partial>(M i)) \<partial>(Pi\<^isub>M I M))"
proof -
  interpret I: finite_product_sigma_finite M I by default auto
  interpret i: finite_product_sigma_finite M "{i}" by default auto
  have IJ: "I \<inter> {i} = {}" and insert: "I \<union> {i} = insert i I"
    using f by auto
  show ?thesis
    unfolding product_positive_integral_fold[OF IJ, unfolded insert, OF I(1) i.finite_index f]
  proof (rule positive_integral_cong, subst product_positive_integral_singleton[symmetric])
    fix x assume x: "x \<in> space (Pi\<^isub>M I M)"
    let ?f = "\<lambda>y. f (x(i := y))"
    show "?f \<in> borel_measurable (M i)"
      using measurable_comp[OF measurable_component_update f, OF x `i \<notin> I`]
      unfolding comp_def .
    show "(\<integral>\<^isup>+ y. f (merge I {i} (x, y)) \<partial>Pi\<^isub>M {i} M) = (\<integral>\<^isup>+ y. f (x(i := y i)) \<partial>Pi\<^isub>M {i} M)"
      using x
      by (auto intro!: positive_integral_cong arg_cong[where f=f]
               simp add: space_PiM extensional_def)
  qed
qed

lemma (in product_sigma_finite) product_positive_integral_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "finite I" and borel: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable (M i)"
  and pos: "\<And>i x. i \<in> I \<Longrightarrow> 0 \<le> f i x"
  shows "(\<integral>\<^isup>+ x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^isub>M I M) = (\<Prod>i\<in>I. integral\<^isup>P (M i) (f i))"
using assms proof induct
  case (insert i I)
  note `finite I`[intro, simp]
  interpret I: finite_product_sigma_finite M I by default auto
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using insert by (auto intro!: setprod_cong)
  have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow> (\<lambda>x. (\<Prod>i\<in>J. f i (x i))) \<in> borel_measurable (Pi\<^isub>M J M)"
    using sets_into_space insert
    by (intro borel_measurable_ereal_setprod
              measurable_comp[OF measurable_component_singleton, unfolded comp_def])
       auto
  then show ?case
    apply (simp add: product_positive_integral_insert[OF insert(1,2) prod])
    apply (simp add: insert(2-) * pos borel setprod_ereal_pos positive_integral_multc)
    apply (subst positive_integral_cmult)
    apply (auto simp add: pos borel insert(2-) setprod_ereal_pos positive_integral_positive)
    done
qed (simp add: space_PiM)

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
  shows "integral\<^isup>L (Pi\<^isub>M (I \<union> J) M) f = (\<integral>x. (\<integral>y. f (merge I J (x, y)) \<partial>Pi\<^isub>M J M) \<partial>Pi\<^isub>M I M)"
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  have "finite (I \<union> J)" using fin by auto
  interpret IJ: finite_product_sigma_finite M "I \<union> J" by default fact
  interpret P: pair_sigma_finite "Pi\<^isub>M I M" "Pi\<^isub>M J M" by default
  let ?M = "merge I J"
  let ?f = "\<lambda>x. f (?M x)"
  from f have f_borel: "f \<in> borel_measurable (Pi\<^isub>M (I \<union> J) M)"
    by auto
  have P_borel: "(\<lambda>x. f (merge I J x)) \<in> borel_measurable (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M)"
    using measurable_comp[OF measurable_merge f_borel] by (simp add: comp_def)
  have f_int: "integrable (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) ?f"
    by (rule integrable_distr[OF measurable_merge]) (simp add: distr_merge[OF IJ fin] f)
  show ?thesis
    apply (subst distr_merge[symmetric, OF IJ fin])
    apply (subst integral_distr[OF measurable_merge f_borel])
    apply (subst P.integrable_fst_measurable(2)[symmetric, OF f_int])
    apply simp
    done
qed

lemma (in product_sigma_finite)
  assumes IJ: "I \<inter> J = {}" "finite I" "finite J" and A: "A \<in> sets (Pi\<^isub>M (I \<union> J) M)"
  shows emeasure_fold_integral:
    "emeasure (Pi\<^isub>M (I \<union> J) M) A = (\<integral>\<^isup>+x. emeasure (Pi\<^isub>M J M) ((\<lambda>y. merge I J (x, y)) -` A \<inter> space (Pi\<^isub>M J M)) \<partial>Pi\<^isub>M I M)" (is ?I)
    and emeasure_fold_measurable:
    "(\<lambda>x. emeasure (Pi\<^isub>M J M) ((\<lambda>y. merge I J (x, y)) -` A \<inter> space (Pi\<^isub>M J M))) \<in> borel_measurable (Pi\<^isub>M I M)" (is ?B)
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  interpret IJ: pair_sigma_finite "Pi\<^isub>M I M" "Pi\<^isub>M J M" ..
  have merge: "merge I J -` A \<inter> space (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M) \<in> sets (Pi\<^isub>M I M \<Otimes>\<^isub>M Pi\<^isub>M J M)"
    by (intro measurable_sets[OF _ A] measurable_merge assms)

  show ?I
    apply (subst distr_merge[symmetric, OF IJ])
    apply (subst emeasure_distr[OF measurable_merge A])
    apply (subst J.emeasure_pair_measure_alt[OF merge])
    apply (auto intro!: positive_integral_cong arg_cong2[where f=emeasure] simp: space_pair_measure)
    done

  show ?B
    using IJ.measurable_emeasure_Pair1[OF merge]
    by (simp add: vimage_compose[symmetric] comp_def space_pair_measure cong: measurable_cong)
qed

lemma (in product_sigma_finite) product_integral_insert:
  assumes I: "finite I" "i \<notin> I"
    and f: "integrable (Pi\<^isub>M (insert i I) M) f"
  shows "integral\<^isup>L (Pi\<^isub>M (insert i I) M) f = (\<integral>x. (\<integral>y. f (x(i:=y)) \<partial>M i) \<partial>Pi\<^isub>M I M)"
proof -
  have "integral\<^isup>L (Pi\<^isub>M (insert i I) M) f = integral\<^isup>L (Pi\<^isub>M (I \<union> {i}) M) f"
    by simp
  also have "\<dots> = (\<integral>x. (\<integral>y. f (merge I {i} (x,y)) \<partial>Pi\<^isub>M {i} M) \<partial>Pi\<^isub>M I M)"
    using f I by (intro product_integral_fold) auto
  also have "\<dots> = (\<integral>x. (\<integral>y. f (x(i := y)) \<partial>M i) \<partial>Pi\<^isub>M I M)"
  proof (rule integral_cong, subst product_integral_singleton[symmetric])
    fix x assume x: "x \<in> space (Pi\<^isub>M I M)"
    have f_borel: "f \<in> borel_measurable (Pi\<^isub>M (insert i I) M)"
      using f by auto
    show "(\<lambda>y. f (x(i := y))) \<in> borel_measurable (M i)"
      using measurable_comp[OF measurable_component_update f_borel, OF x `i \<notin> I`]
      unfolding comp_def .
    from x I show "(\<integral> y. f (merge I {i} (x,y)) \<partial>Pi\<^isub>M {i} M) = (\<integral> xa. f (x(i := xa i)) \<partial>Pi\<^isub>M {i} M)"
      by (auto intro!: integral_cong arg_cong[where f=f] simp: merge_def space_PiM extensional_def)
  qed
  finally show ?thesis .
qed

lemma (in product_sigma_finite) product_integrable_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes [simp]: "finite I" and integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (M i) (f i)"
  shows "integrable (Pi\<^isub>M I M) (\<lambda>x. (\<Prod>i\<in>I. f i (x i)))" (is "integrable _ ?f")
proof -
  interpret finite_product_sigma_finite M I by default fact
  have f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable (M i)"
    using integrable unfolding integrable_def by auto
  have borel: "?f \<in> borel_measurable (Pi\<^isub>M I M)"
    using measurable_comp[OF measurable_component_singleton[of _ I M] f] by (auto simp: comp_def)
  moreover have "integrable (Pi\<^isub>M I M) (\<lambda>x. \<bar>\<Prod>i\<in>I. f i (x i)\<bar>)"
  proof (unfold integrable_def, intro conjI)
    show "(\<lambda>x. abs (?f x)) \<in> borel_measurable (Pi\<^isub>M I M)"
      using borel by auto
    have "(\<integral>\<^isup>+x. ereal (abs (?f x)) \<partial>Pi\<^isub>M I M) = (\<integral>\<^isup>+x. (\<Prod>i\<in>I. ereal (abs (f i (x i)))) \<partial>Pi\<^isub>M I M)"
      by (simp add: setprod_ereal abs_setprod)
    also have "\<dots> = (\<Prod>i\<in>I. (\<integral>\<^isup>+x. ereal (abs (f i x)) \<partial>M i))"
      using f by (subst product_positive_integral_setprod) auto
    also have "\<dots> < \<infinity>"
      using integrable[THEN integrable_abs]
      by (simp add: setprod_PInf integrable_def positive_integral_positive)
    finally show "(\<integral>\<^isup>+x. ereal (abs (?f x)) \<partial>(Pi\<^isub>M I M)) \<noteq> \<infinity>" by auto
    have "(\<integral>\<^isup>+x. ereal (- abs (?f x)) \<partial>(Pi\<^isub>M I M)) = (\<integral>\<^isup>+x. 0 \<partial>(Pi\<^isub>M I M))"
      by (intro positive_integral_cong_pos) auto
    then show "(\<integral>\<^isup>+x. ereal (- abs (?f x)) \<partial>(Pi\<^isub>M I M)) \<noteq> \<infinity>" by simp
  qed
  ultimately show ?thesis
    by (rule integrable_abs_iff[THEN iffD1])
qed

lemma (in product_sigma_finite) product_integral_setprod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I" and integrable: "\<And>i. i \<in> I \<Longrightarrow> integrable (M i) (f i)"
  shows "(\<integral>x. (\<Prod>i\<in>I. f i (x i)) \<partial>Pi\<^isub>M I M) = (\<Prod>i\<in>I. integral\<^isup>L (M i) (f i))"
using assms proof induct
  case empty
  interpret finite_measure "Pi\<^isub>M {} M"
    by rule (simp add: space_PiM)
  show ?case by (simp add: space_PiM measure_def)
next
  case (insert i I)
  then have iI: "finite (insert i I)" by auto
  then have prod: "\<And>J. J \<subseteq> insert i I \<Longrightarrow>
    integrable (Pi\<^isub>M J M) (\<lambda>x. (\<Prod>i\<in>J. f i (x i)))"
    by (intro product_integrable_setprod insert(4)) (auto intro: finite_subset)
  interpret I: finite_product_sigma_finite M I by default fact
  have *: "\<And>x y. (\<Prod>j\<in>I. f j (if j = i then y else x j)) = (\<Prod>j\<in>I. f j (x j))"
    using `i \<notin> I` by (auto intro!: setprod_cong)
  show ?case
    unfolding product_integral_insert[OF insert(1,2) prod[OF subset_refl]]
    by (simp add: * insert integral_multc integral_cmult[OF prod] subset_insertI)
qed

lemma sets_Collect_single:
  "i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow> { x \<in> space (Pi\<^isub>M I M). x i \<in> A } \<in> sets (Pi\<^isub>M I M)"
  unfolding sets_PiM_single
  by (auto intro!: sigma_sets.Basic exI[of _ i] exI[of _ A]) (auto simp: space_PiM)

lemma sigma_prod_algebra_sigma_eq_infinite:
  fixes E :: "'i \<Rightarrow> 'a set set"
  assumes S_union: "\<And>i. i \<in> I \<Longrightarrow> (\<Union>j. S i j) = space (M i)"
    and S_in_E: "\<And>i. i \<in> I \<Longrightarrow> range (S i) \<subseteq> E i"
  assumes E_closed: "\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> Pow (space (M i))"
    and E_generates: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sigma_sets (space (M i)) (E i)"
  defines "P == {{f\<in>\<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A} | i A. i \<in> I \<and> A \<in> E i}"
  shows "sets (PiM I M) = sigma_sets (space (PiM I M)) P"
proof
  let ?P = "sigma (space (Pi\<^isub>M I M)) P"
  have P_closed: "P \<subseteq> Pow (space (Pi\<^isub>M I M))"
    using E_closed by (auto simp: space_PiM P_def Pi_iff subset_eq)
  then have space_P: "space ?P = (\<Pi>\<^isub>E i\<in>I. space (M i))"
    by (simp add: space_PiM)
  have "sets (PiM I M) =
      sigma_sets (space ?P) {{f \<in> \<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A} |i A. i \<in> I \<and> A \<in> sets (M i)}"
    using sets_PiM_single[of I M] by (simp add: space_P)
  also have "\<dots> \<subseteq> sets (sigma (space (PiM I M)) P)"
  proof (safe intro!: sigma_sets_subset)
    fix i A assume "i \<in> I" and A: "A \<in> sets (M i)"
    then have "(\<lambda>x. x i) \<in> measurable ?P (sigma (space (M i)) (E i))"
      apply (subst measurable_iff_measure_of)
      apply (simp_all add: P_closed)
      using E_closed
      apply (force simp: subset_eq space_PiM)
      apply (force simp: subset_eq space_PiM)
      apply (auto simp: P_def intro!: sigma_sets.Basic exI[of _ i])
      apply (rule_tac x=Aa in exI)
      apply (auto simp: space_PiM)
      done
    from measurable_sets[OF this, of A] A `i \<in> I` E_closed
    have "(\<lambda>x. x i) -` A \<inter> space ?P \<in> sets ?P"
      by (simp add: E_generates)
    also have "(\<lambda>x. x i) -` A \<inter> space ?P = {f \<in> \<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A}"
      using P_closed by (auto simp: space_PiM)
    finally show "\<dots> \<in> sets ?P" .
  qed
  finally show "sets (PiM I M) \<subseteq> sigma_sets (space (PiM I M)) P"
    by (simp add: P_closed)
  show "sigma_sets (space (PiM I M)) P \<subseteq> sets (PiM I M)"
    unfolding P_def space_PiM[symmetric]
    by (intro sigma_sets_subset) (auto simp: E_generates sets_Collect_single)
qed

lemma bchoice_iff: "(\<forall>a\<in>A. \<exists>b. P a b) \<longleftrightarrow> (\<exists>f. \<forall>a\<in>A. P a (f a))"
  by metis

lemma sigma_prod_algebra_sigma_eq:
  fixes E :: "'i \<Rightarrow> 'a set set" and S :: "'i \<Rightarrow> nat \<Rightarrow> 'a set"
  assumes "finite I"
  assumes S_union: "\<And>i. i \<in> I \<Longrightarrow> (\<Union>j. S i j) = space (M i)"
    and S_in_E: "\<And>i. i \<in> I \<Longrightarrow> range (S i) \<subseteq> E i"
  assumes E_closed: "\<And>i. i \<in> I \<Longrightarrow> E i \<subseteq> Pow (space (M i))"
    and E_generates: "\<And>i. i \<in> I \<Longrightarrow> sets (M i) = sigma_sets (space (M i)) (E i)"
  defines "P == { Pi\<^isub>E I F | F. \<forall>i\<in>I. F i \<in> E i }"
  shows "sets (PiM I M) = sigma_sets (space (PiM I M)) P"
proof
  let ?P = "sigma (space (Pi\<^isub>M I M)) P"
  from `finite I`[THEN ex_bij_betw_finite_nat] guess T ..
  then have T: "\<And>i. i \<in> I \<Longrightarrow> T i < card I" "\<And>i. i\<in>I \<Longrightarrow> the_inv_into I T (T i) = i"
    by (auto simp add: bij_betw_def set_eq_iff image_iff the_inv_into_f_f)
  have P_closed: "P \<subseteq> Pow (space (Pi\<^isub>M I M))"
    using E_closed by (auto simp: space_PiM P_def Pi_iff subset_eq)
  then have space_P: "space ?P = (\<Pi>\<^isub>E i\<in>I. space (M i))"
    by (simp add: space_PiM)
  have "sets (PiM I M) =
      sigma_sets (space ?P) {{f \<in> \<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A} |i A. i \<in> I \<and> A \<in> sets (M i)}"
    using sets_PiM_single[of I M] by (simp add: space_P)
  also have "\<dots> \<subseteq> sets (sigma (space (PiM I M)) P)"
  proof (safe intro!: sigma_sets_subset)
    fix i A assume "i \<in> I" and A: "A \<in> sets (M i)"
    have "(\<lambda>x. x i) \<in> measurable ?P (sigma (space (M i)) (E i))"
    proof (subst measurable_iff_measure_of)
      show "E i \<subseteq> Pow (space (M i))" using `i \<in> I` by fact
      from space_P `i \<in> I` show "(\<lambda>x. x i) \<in> space ?P \<rightarrow> space (M i)"
        by (auto simp: Pi_iff)
      show "\<forall>A\<in>E i. (\<lambda>x. x i) -` A \<inter> space ?P \<in> sets ?P"
      proof
        fix A assume A: "A \<in> E i"
        then have "(\<lambda>x. x i) -` A \<inter> space ?P = (\<Pi>\<^isub>E j\<in>I. if i = j then A else space (M j))"
          using E_closed `i \<in> I` by (auto simp: space_P Pi_iff subset_eq split: split_if_asm)
        also have "\<dots> = (\<Pi>\<^isub>E j\<in>I. \<Union>n. if i = j then A else S j n)"
          by (intro PiE_cong) (simp add: S_union)
        also have "\<dots> = (\<Union>xs\<in>{xs. length xs = card I}. \<Pi>\<^isub>E j\<in>I. if i = j then A else S j (xs ! T j))"
          using T
          apply (auto simp: Pi_iff bchoice_iff)
          apply (rule_tac x="map (\<lambda>n. f (the_inv_into I T n)) [0..<card I]" in exI)
          apply (auto simp: bij_betw_def)
          done
        also have "\<dots> \<in> sets ?P"
        proof (safe intro!: countable_UN)
          fix xs show "(\<Pi>\<^isub>E j\<in>I. if i = j then A else S j (xs ! T j)) \<in> sets ?P"
            using A S_in_E
            by (simp add: P_closed)
               (auto simp: P_def subset_eq intro!: exI[of _ "\<lambda>j. if i = j then A else S j (xs ! T j)"])
        qed
        finally show "(\<lambda>x. x i) -` A \<inter> space ?P \<in> sets ?P"
          using P_closed by simp
      qed
    qed
    from measurable_sets[OF this, of A] A `i \<in> I` E_closed
    have "(\<lambda>x. x i) -` A \<inter> space ?P \<in> sets ?P"
      by (simp add: E_generates)
    also have "(\<lambda>x. x i) -` A \<inter> space ?P = {f \<in> \<Pi>\<^isub>E i\<in>I. space (M i). f i \<in> A}"
      using P_closed by (auto simp: space_PiM)
    finally show "\<dots> \<in> sets ?P" .
  qed
  finally show "sets (PiM I M) \<subseteq> sigma_sets (space (PiM I M)) P"
    by (simp add: P_closed)
  show "sigma_sets (space (PiM I M)) P \<subseteq> sets (PiM I M)"
    using `finite I`
    by (auto intro!: sigma_sets_subset simp: E_generates P_def)
qed

end
