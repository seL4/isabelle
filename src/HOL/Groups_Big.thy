(*  Title:      HOL/Groups_Big.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

section \<open>Big sum and product over finite (non-empty) sets\<close>

theory Groups_Big
  imports Finite_Set Power
begin

subsection \<open>Generic monoid operation over a set\<close>

locale comm_monoid_set = comm_monoid
begin

interpretation comp_fun_commute f
  by standard (simp add: fun_eq_iff left_commute)

interpretation comp?: comp_fun_commute "f \<circ> g"
  by (fact comp_comp_fun_commute)

definition F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  where eq_fold: "F g A = Finite_Set.fold (f \<circ> g) \<^bold>1 A"

lemma infinite [simp]: "\<not> finite A \<Longrightarrow> F g A = \<^bold>1"
  by (simp add: eq_fold)

lemma empty [simp]: "F g {} = \<^bold>1"
  by (simp add: eq_fold)

lemma insert [simp]: "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> F g (insert x A) = g x \<^bold>* F g A"
  by (simp add: eq_fold)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F g A = g x \<^bold>* F g (A - {x})"
proof -
  from \<open>x \<in> A\<close> obtain B where B: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from \<open>finite A\<close> B have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove: "finite A \<Longrightarrow> F g (insert x A) = g x \<^bold>* F g (A - {x})"
  by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma neutral: "\<forall>x\<in>A. g x = \<^bold>1 \<Longrightarrow> F g A = \<^bold>1"
  by (induct A rule: infinite_finite_induct) simp_all

lemma neutral_const [simp]: "F (\<lambda>_. \<^bold>1) A = \<^bold>1"
  by (simp add: neutral)

lemma union_inter:
  assumes "finite A" and "finite B"
  shows "F g (A \<union> B) \<^bold>* F g (A \<inter> B) = F g A \<^bold>* F g B"
  \<comment> \<open>The reversed orientation looks more natural, but LOOPS as a simprule!\<close>
  using assms
proof (induct A)
  case empty
  then show ?case by simp
next
  case (insert x A)
  then show ?case
    by (auto simp: insert_absorb Int_insert_left commute [of _ "g x"] assoc left_commute)
qed

corollary union_inter_neutral:
  assumes "finite A" and "finite B"
    and "\<forall>x \<in> A \<inter> B. g x = \<^bold>1"
  shows "F g (A \<union> B) = F g A \<^bold>* F g B"
  using assms by (simp add: union_inter [symmetric] neutral)

corollary union_disjoint:
  assumes "finite A" and "finite B"
  assumes "A \<inter> B = {}"
  shows "F g (A \<union> B) = F g A \<^bold>* F g B"
  using assms by (simp add: union_inter_neutral)

lemma union_diff2:
  assumes "finite A" and "finite B"
  shows "F g (A \<union> B) = F g (A - B) \<^bold>* F g (B - A) \<^bold>* F g (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis
    by simp (subst union_disjoint, auto)+
qed

lemma subset_diff:
  assumes "B \<subseteq> A" and "finite A"
  shows "F g A = F g (A - B) \<^bold>* F g B"
proof -
  from assms have "finite (A - B)" by auto
  moreover from assms have "finite B" by (rule finite_subset)
  moreover from assms have "(A - B) \<inter> B = {}" by auto
  ultimately have "F g (A - B \<union> B) = F g (A - B) \<^bold>* F g B" by (rule union_disjoint)
  moreover from assms have "A \<union> B = A" by auto
  ultimately show ?thesis by simp
qed

lemma setdiff_irrelevant:
  assumes "finite A"
  shows "F g (A - {x. g x = z}) = F g A"
  using assms by (induct A) (simp_all add: insert_Diff_if)

lemma not_neutral_contains_not_neutral:
  assumes "F g A \<noteq> \<^bold>1"
  obtains a where "a \<in> A" and "g a \<noteq> \<^bold>1"
proof -
  from assms have "\<exists>a\<in>A. g a \<noteq> \<^bold>1"
  proof (induct A rule: infinite_finite_induct)
    case infinite
    then show ?case by simp
  next
    case empty
    then show ?case by simp
  next
    case (insert a A)
    then show ?case by fastforce
  qed
  with that show thesis by blast
qed

lemma reindex:
  assumes "inj_on h A"
  shows "F g (h ` A) = F (g \<circ> h) A"
proof (cases "finite A")
  case True
  with assms show ?thesis
    by (simp add: eq_fold fold_image comp_assoc)
next
  case False
  with assms have "\<not> finite (h ` A)" by (blast dest: finite_imageD)
  with False show ?thesis by simp
qed

lemma cong [fundef_cong]:
  assumes "A = B"
  assumes g_h: "\<And>x. x \<in> B \<Longrightarrow> g x = h x"
  shows "F g A = F h B"
  using g_h unfolding \<open>A = B\<close>
  by (induct B rule: infinite_finite_induct) auto

lemma strong_cong [cong]:
  assumes "A = B" "\<And>x. x \<in> B =simp=> g x = h x"
  shows "F (\<lambda>x. g x) A = F (\<lambda>x. h x) B"
  by (rule cong) (use assms in \<open>simp_all add: simp_implies_def\<close>)

lemma reindex_cong:
  assumes "inj_on l B"
  assumes "A = l ` B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x"
  shows "F g A = F h B"
  using assms by (simp add: reindex)

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "F g (UNION I A) = F (\<lambda>x. F g (A x)) I"
  apply (insert assms)
  apply (induct rule: finite_induct)
   apply simp
  apply atomize
  apply (subgoal_tac "\<forall>i\<in>Fa. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x \<inter> UNION Fa A = {}")
   prefer 2 apply blast
  apply (simp add: union_disjoint)
  done

lemma Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  shows "F g (\<Union>C) = (F \<circ> F) g C"
proof (cases "finite C")
  case True
  from UNION_disjoint [OF this assms] show ?thesis by simp
next
  case False
  then show ?thesis by (auto dest: finite_UnionD intro: infinite)
qed

lemma distrib: "F (\<lambda>x. g x \<^bold>* h x) A = F g A \<^bold>* F h A"
  by (induct A rule: infinite_finite_induct) (simp_all add: assoc commute left_commute)

lemma Sigma:
  "finite A \<Longrightarrow> \<forall>x\<in>A. finite (B x) \<Longrightarrow> F (\<lambda>x. F (g x) (B x)) A = F (case_prod g) (SIGMA x:A. B x)"
  apply (subst Sigma_def)
  apply (subst UNION_disjoint)
     apply assumption
    apply simp
   apply blast
  apply (rule cong)
   apply rule
  apply (simp add: fun_eq_iff)
  apply (subst UNION_disjoint)
     apply simp
    apply simp
   apply blast
  apply (simp add: comp_def)
  done

lemma related:
  assumes Re: "R \<^bold>1 \<^bold>1"
    and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 \<^bold>* y1) (x2 \<^bold>* y2)"
    and fin: "finite S"
    and R_h_g: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (F h S) (F g S)"
  using fin by (rule finite_subset_induct) (use assms in auto)

lemma mono_neutral_cong_left:
  assumes "finite T"
    and "S \<subseteq> T"
    and "\<forall>i \<in> T - S. h i = \<^bold>1"
    and "\<And>x. x \<in> S \<Longrightarrow> g x = h x"
  shows "F g S = F h T"
proof-
  have eq: "T = S \<union> (T - S)" using \<open>S \<subseteq> T\<close> by blast
  have d: "S \<inter> (T - S) = {}" using \<open>S \<subseteq> T\<close> by blast
  from \<open>finite T\<close> \<open>S \<subseteq> T\<close> have f: "finite S" "finite (T - S)"
    by (auto intro: finite_subset)
  show ?thesis using assms(4)
    by (simp add: union_disjoint [OF f d, unfolded eq [symmetric]] neutral [OF assms(3)])
qed

lemma mono_neutral_cong_right:
  "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> g x = h x) \<Longrightarrow>
    F g T = F h S"
  by (auto intro!: mono_neutral_cong_left [symmetric])

lemma mono_neutral_left: "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> F g S = F g T"
  by (blast intro: mono_neutral_cong_left)

lemma mono_neutral_right: "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> F g T = F g S"
  by (blast intro!: mono_neutral_left [symmetric])

lemma reindex_bij_betw: "bij_betw h S T \<Longrightarrow> F (\<lambda>x. g (h x)) S = F g T"
  by (auto simp: bij_betw_def reindex)

lemma reindex_bij_witness:
  assumes witness:
    "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
    "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows "F g S = F h T"
proof -
  have "bij_betw j S T"
    using bij_betw_byWitness[where A=S and f=j and f'=i and A'=T] witness by auto
  moreover have "F g S = F (\<lambda>x. h (j x)) S"
    by (intro cong) (auto simp: eq)
  ultimately show ?thesis
    by (simp add: reindex_bij_betw)
qed

lemma reindex_bij_betw_not_neutral:
  assumes fin: "finite S'" "finite T'"
  assumes bij: "bij_betw h (S - S') (T - T')"
  assumes nn:
    "\<And>a. a \<in> S' \<Longrightarrow> g (h a) = z"
    "\<And>b. b \<in> T' \<Longrightarrow> g b = z"
  shows "F (\<lambda>x. g (h x)) S = F g T"
proof -
  have [simp]: "finite S \<longleftrightarrow> finite T"
    using bij_betw_finite[OF bij] fin by auto
  show ?thesis
  proof (cases "finite S")
    case True
    with nn have "F (\<lambda>x. g (h x)) S = F (\<lambda>x. g (h x)) (S - S')"
      by (intro mono_neutral_cong_right) auto
    also have "\<dots> = F g (T - T')"
      using bij by (rule reindex_bij_betw)
    also have "\<dots> = F g T"
      using nn \<open>finite S\<close> by (intro mono_neutral_cong_left) auto
    finally show ?thesis .
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma reindex_nontrivial:
  assumes "finite A"
    and nz: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> h x = h y \<Longrightarrow> g (h x) = \<^bold>1"
  shows "F g (h ` A) = F (g \<circ> h) A"
proof (subst reindex_bij_betw_not_neutral [symmetric])
  show "bij_betw h (A - {x \<in> A. (g \<circ> h) x = \<^bold>1}) (h ` A - h ` {x \<in> A. (g \<circ> h) x = \<^bold>1})"
    using nz by (auto intro!: inj_onI simp: bij_betw_def)
qed (use \<open>finite A\<close> in auto)

lemma reindex_bij_witness_not_neutral:
  assumes fin: "finite S'" "finite T'"
  assumes witness:
    "\<And>a. a \<in> S - S' \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S - S' \<Longrightarrow> j a \<in> T - T'"
    "\<And>b. b \<in> T - T' \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T - T' \<Longrightarrow> i b \<in> S - S'"
  assumes nn:
    "\<And>a. a \<in> S' \<Longrightarrow> g a = z"
    "\<And>b. b \<in> T' \<Longrightarrow> h b = z"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows "F g S = F h T"
proof -
  have bij: "bij_betw j (S - (S' \<inter> S)) (T - (T' \<inter> T))"
    using witness by (intro bij_betw_byWitness[where f'=i]) auto
  have F_eq: "F g S = F (\<lambda>x. h (j x)) S"
    by (intro cong) (auto simp: eq)
  show ?thesis
    unfolding F_eq using fin nn eq
    by (intro reindex_bij_betw_not_neutral[OF _ _ bij]) auto
qed

lemma delta:
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k = a then b k else \<^bold>1) S = (if a \<in> S then b a else \<^bold>1)"
proof -
  let ?f = "(\<lambda>k. if k = a then b k else \<^bold>1)"
  show ?thesis
  proof (cases "a \<in> S")
    case False
    then have "\<forall>k\<in>S. ?f k = \<^bold>1" by simp
    with False show ?thesis by simp
  next
    case True
    let ?A = "S - {a}"
    let ?B = "{a}"
    from True have eq: "S = ?A \<union> ?B" by blast
    have dj: "?A \<inter> ?B = {}" by simp
    from fS have fAB: "finite ?A" "finite ?B" by auto
    have "F ?f S = F ?f ?A \<^bold>* F ?f ?B"
      using union_disjoint [OF fAB dj, of ?f, unfolded eq [symmetric]] by simp
    with True show ?thesis by simp
  qed
qed

lemma delta':
  assumes fin: "finite S"
  shows "F (\<lambda>k. if a = k then b k else \<^bold>1) S = (if a \<in> S then b a else \<^bold>1)"
  using delta [OF fin, of a b, symmetric] by (auto intro: cong)

lemma If_cases:
  fixes P :: "'b \<Rightarrow> bool" and g h :: "'b \<Rightarrow> 'a"
  assumes fin: "finite A"
  shows "F (\<lambda>x. if P x then h x else g x) A = F h (A \<inter> {x. P x}) \<^bold>* F g (A \<inter> - {x. P x})"
proof -
  have a: "A = A \<inter> {x. P x} \<union> A \<inter> -{x. P x}" "(A \<inter> {x. P x}) \<inter> (A \<inter> -{x. P x}) = {}"
    by blast+
  from fin have f: "finite (A \<inter> {x. P x})" "finite (A \<inter> -{x. P x})" by auto
  let ?g = "\<lambda>x. if P x then h x else g x"
  from union_disjoint [OF f a(2), of ?g] a(1) show ?thesis
    by (subst (1 2) cong) simp_all
qed

lemma cartesian_product: "F (\<lambda>x. F (g x) B) A = F (case_prod g) (A \<times> B)"
  apply (rule sym)
  apply (cases "finite A")
   apply (cases "finite B")
    apply (simp add: Sigma)
   apply (cases "A = {}")
    apply simp
   apply simp
   apply (auto intro: infinite dest: finite_cartesian_productD2)
  apply (cases "B = {}")
   apply (auto intro: infinite dest: finite_cartesian_productD1)
  done

lemma inter_restrict:
  assumes "finite A"
  shows "F g (A \<inter> B) = F (\<lambda>x. if x \<in> B then g x else \<^bold>1) A"
proof -
  let ?g = "\<lambda>x. if x \<in> A \<inter> B then g x else \<^bold>1"
  have "\<forall>i\<in>A - A \<inter> B. (if i \<in> A \<inter> B then g i else \<^bold>1) = \<^bold>1" by simp
  moreover have "A \<inter> B \<subseteq> A" by blast
  ultimately have "F ?g (A \<inter> B) = F ?g A"
    using \<open>finite A\<close> by (intro mono_neutral_left) auto
  then show ?thesis by simp
qed

lemma inter_filter:
  "finite A \<Longrightarrow> F g {x \<in> A. P x} = F (\<lambda>x. if P x then g x else \<^bold>1) A"
  by (simp add: inter_restrict [symmetric, of A "{x. P x}" g, simplified mem_Collect_eq] Int_def)

lemma Union_comp:
  assumes "\<forall>A \<in> B. finite A"
    and "\<And>A1 A2 x. A1 \<in> B \<Longrightarrow> A2 \<in> B \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> x \<in> A1 \<Longrightarrow> x \<in> A2 \<Longrightarrow> g x = \<^bold>1"
  shows "F g (\<Union>B) = (F \<circ> F) g B"
  using assms
proof (induct B rule: infinite_finite_induct)
  case (infinite A)
  then have "\<not> finite (\<Union>A)" by (blast dest: finite_UnionD)
  with infinite show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert A B)
  then have "finite A" "finite B" "finite (\<Union>B)" "A \<notin> B"
    and "\<forall>x\<in>A \<inter> \<Union>B. g x = \<^bold>1"
    and H: "F g (\<Union>B) = (F \<circ> F) g B" by auto
  then have "F g (A \<union> \<Union>B) = F g A \<^bold>* F g (\<Union>B)"
    by (simp add: union_inter_neutral)
  with \<open>finite B\<close> \<open>A \<notin> B\<close> show ?case
    by (simp add: H)
qed

lemma commute: "F (\<lambda>i. F (g i) B) A = F (\<lambda>j. F (\<lambda>i. g i j) A) B"
  unfolding cartesian_product
  by (rule reindex_bij_witness [where i = "\<lambda>(i, j). (j, i)" and j = "\<lambda>(i, j). (j, i)"]) auto

lemma commute_restrict:
  "finite A \<Longrightarrow> finite B \<Longrightarrow>
    F (\<lambda>x. F (g x) {y. y \<in> B \<and> R x y}) A = F (\<lambda>y. F (\<lambda>x. g x y) {x. x \<in> A \<and> R x y}) B"
  by (simp add: inter_filter) (rule commute)

lemma Plus:
  fixes A :: "'b set" and B :: "'c set"
  assumes fin: "finite A" "finite B"
  shows "F g (A <+> B) = F (g \<circ> Inl) A \<^bold>* F (g \<circ> Inr) B"
proof -
  have "A <+> B = Inl ` A \<union> Inr ` B" by auto
  moreover from fin have "finite (Inl ` A)" "finite (Inr ` B)" by auto
  moreover have "Inl ` A \<inter> Inr ` B = {}" by auto
  moreover have "inj_on Inl A" "inj_on Inr B" by (auto intro: inj_onI)
  ultimately show ?thesis
    using fin by (simp add: union_disjoint reindex)
qed

lemma same_carrier:
  assumes "finite C"
  assumes subset: "A \<subseteq> C" "B \<subseteq> C"
  assumes trivial: "\<And>a. a \<in> C - A \<Longrightarrow> g a = \<^bold>1" "\<And>b. b \<in> C - B \<Longrightarrow> h b = \<^bold>1"
  shows "F g A = F h B \<longleftrightarrow> F g C = F h C"
proof -
  have "finite A" and "finite B" and "finite (C - A)" and "finite (C - B)"
    using \<open>finite C\<close> subset by (auto elim: finite_subset)
  from subset have [simp]: "A - (C - A) = A" by auto
  from subset have [simp]: "B - (C - B) = B" by auto
  from subset have "C = A \<union> (C - A)" by auto
  then have "F g C = F g (A \<union> (C - A))" by simp
  also have "\<dots> = F g (A - (C - A)) \<^bold>* F g (C - A - A) \<^bold>* F g (A \<inter> (C - A))"
    using \<open>finite A\<close> \<open>finite (C - A)\<close> by (simp only: union_diff2)
  finally have *: "F g C = F g A" using trivial by simp
  from subset have "C = B \<union> (C - B)" by auto
  then have "F h C = F h (B \<union> (C - B))" by simp
  also have "\<dots> = F h (B - (C - B)) \<^bold>* F h (C - B - B) \<^bold>* F h (B \<inter> (C - B))"
    using \<open>finite B\<close> \<open>finite (C - B)\<close> by (simp only: union_diff2)
  finally have "F h C = F h B"
    using trivial by simp
  with * show ?thesis by simp
qed

lemma same_carrierI:
  assumes "finite C"
  assumes subset: "A \<subseteq> C" "B \<subseteq> C"
  assumes trivial: "\<And>a. a \<in> C - A \<Longrightarrow> g a = \<^bold>1" "\<And>b. b \<in> C - B \<Longrightarrow> h b = \<^bold>1"
  assumes "F g C = F h C"
  shows "F g A = F h B"
  using assms same_carrier [of C A B] by simp

end


subsection \<open>Generalized summation over a set\<close>

context comm_monoid_add
begin

sublocale setsum: comm_monoid_set plus 0
  defines setsum = setsum.F ..

abbreviation Setsum ("\<Sum>_" [1000] 999)
  where "\<Sum>A \<equiv> setsum (\<lambda>x. x) A"

end

text \<open>Now: lot's of fancy syntax. First, @{term "setsum (\<lambda>x. e) A"} is written \<open>\<Sum>x\<in>A. e\<close>.\<close>

syntax (ASCII)
  "_setsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::comm_monoid_add"  ("(3SUM _:_./ _)" [0, 51, 10] 10)
syntax
  "_setsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::comm_monoid_add"  ("(2\<Sum>_\<in>_./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>i\<in>A. b" \<rightleftharpoons> "CONST setsum (\<lambda>i. b) A"

text \<open>Instead of @{term"\<Sum>x\<in>{x. P}. e"} we introduce the shorter \<open>\<Sum>x|P. e\<close>.\<close>

syntax (ASCII)
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3SUM _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Sum>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>x|P. t" => "CONST setsum (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun setsum_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qsetsum"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | setsum_tr' _ = raise Match;
in [(@{const_syntax setsum}, K setsum_tr')] end
\<close>

(* TODO generalization candidates *)

lemma (in comm_monoid_add) setsum_image_gen:
  assumes fin: "finite S"
  shows "setsum g S = setsum (\<lambda>y. setsum g {x. x \<in> S \<and> f x = y}) (f ` S)"
proof -
  have "{y. y\<in> f`S \<and> f x = y} = {f x}" if "x \<in> S" for x
    using that by auto
  then have "setsum g S = setsum (\<lambda>x. setsum (\<lambda>y. g x) {y. y\<in> f`S \<and> f x = y}) S"
    by simp
  also have "\<dots> = setsum (\<lambda>y. setsum g {x. x \<in> S \<and> f x = y}) (f ` S)"
    by (rule setsum.commute_restrict [OF fin finite_imageI [OF fin]])
  finally show ?thesis .
qed


subsubsection \<open>Properties in more restricted classes of structures\<close>

lemma setsum_Un:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> setsum f (A \<union> B) = setsum f A + setsum f B - setsum f (A \<inter> B)"
  for f :: "'b \<Rightarrow> 'a::ab_group_add"
  by (subst setsum.union_inter [symmetric]) (auto simp add: algebra_simps)

lemma setsum_Un2:
  assumes "finite (A \<union> B)"
  shows "setsum f (A \<union> B) = setsum f (A - B) + setsum f (B - A) + setsum f (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis
    by simp (subst setsum.union_disjoint, auto)+
qed

lemma setsum_diff1:
  fixes f :: "'b \<Rightarrow> 'a::ab_group_add"
  assumes "finite A"
  shows "setsum f (A - {a}) = (if a \<in> A then setsum f A - f a else setsum f A)"
  using assms by induct (auto simp: insert_Diff_if)

lemma setsum_diff:
  fixes f :: "'b \<Rightarrow> 'a::ab_group_add"
  assumes "finite A" "B \<subseteq> A"
  shows "setsum f (A - B) = setsum f A - setsum f B"
proof -
  from assms(2,1) have "finite B" by (rule finite_subset)
  from this \<open>B \<subseteq> A\<close>
  show ?thesis
  proof induct
    case empty
    thus ?case by simp
  next
    case (insert x F)
    with \<open>finite A\<close> \<open>finite B\<close> show ?case
      by (simp add: Diff_insert[where a=x and B=F] setsum_diff1 insert_absorb)
  qed
qed

lemma (in ordered_comm_monoid_add) setsum_mono:
  "(\<And>i. i\<in>K \<Longrightarrow> f i \<le> g i) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
  by (induct K rule: infinite_finite_induct) (use add_mono in auto)

lemma (in strict_ordered_comm_monoid_add) setsum_strict_mono:
  assumes "finite A" "A \<noteq> {}"
    and "\<And>x. x \<in> A \<Longrightarrow> f x < g x"
  shows "setsum f A < setsum g A"
  using assms
proof (induct rule: finite_ne_induct)
  case singleton
  then show ?case by simp
next
  case insert
  then show ?case by (auto simp: add_strict_mono)
qed

lemma setsum_strict_mono_ex1:
  fixes f g :: "'i \<Rightarrow> 'a::ordered_cancel_comm_monoid_add"
  assumes "finite A"
    and "\<forall>x\<in>A. f x \<le> g x"
    and "\<exists>a\<in>A. f a < g a"
  shows "setsum f A < setsum g A"
proof-
  from assms(3) obtain a where a: "a \<in> A" "f a < g a" by blast
  have "setsum f A = setsum f ((A - {a}) \<union> {a})"
    by(simp add: insert_absorb[OF \<open>a \<in> A\<close>])
  also have "\<dots> = setsum f (A - {a}) + setsum f {a}"
    using \<open>finite A\<close> by(subst setsum.union_disjoint) auto
  also have "setsum f (A - {a}) \<le> setsum g (A - {a})"
    by (rule setsum_mono) (simp add: assms(2))
  also from a have "setsum f {a} < setsum g {a}" by simp
  also have "setsum g (A - {a}) + setsum g {a} = setsum g((A - {a}) \<union> {a})"
    using \<open>finite A\<close> by (subst setsum.union_disjoint[symmetric]) auto
  also have "\<dots> = setsum g A" by (simp add: insert_absorb[OF \<open>a \<in> A\<close>])
  finally show ?thesis
    by (auto simp add: add_right_mono add_strict_left_mono)
qed

lemma setsum_mono_inv:
  fixes f g :: "'i \<Rightarrow> 'a :: ordered_cancel_comm_monoid_add"
  assumes eq: "setsum f I = setsum g I"
  assumes le: "\<And>i. i \<in> I \<Longrightarrow> f i \<le> g i"
  assumes i: "i \<in> I"
  assumes I: "finite I"
  shows "f i = g i"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with le[OF i] have "f i < g i" by simp
  with i have "\<exists>i\<in>I. f i < g i" ..
  from setsum_strict_mono_ex1[OF I _ this] le have "setsum f I < setsum g I"
    by blast
  with eq show False by simp
qed

lemma setsum_negf: "(\<Sum>x\<in>A. - f x) = - (\<Sum>x\<in>A. f x)"
  for f :: "'b \<Rightarrow> 'a::ab_group_add"
  by (induct A rule: infinite_finite_induct) auto

lemma setsum_subtractf: "(\<Sum>x\<in>A. f x - g x) = (\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x)"
  for f g :: "'b \<Rightarrow>'a::ab_group_add"
  using setsum.distrib [of f "- g" A] by (simp add: setsum_negf)

lemma setsum_subtractf_nat:
  "(\<And>x. x \<in> A \<Longrightarrow> g x \<le> f x) \<Longrightarrow> (\<Sum>x\<in>A. f x - g x) = (\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x)"
  for f g :: "'a \<Rightarrow> nat"
  by (induct A rule: infinite_finite_induct) (auto simp: setsum_mono)

context ordered_comm_monoid_add
begin

lemma setsum_nonneg: "\<forall>x\<in>A. 0 \<le> f x \<Longrightarrow> 0 \<le> setsum f A"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have "0 + 0 \<le> f x + setsum f F" by (blast intro: add_mono)
  with insert show ?case by simp
qed

lemma setsum_nonpos: "\<forall>x\<in>A. f x \<le> 0 \<Longrightarrow> setsum f A \<le> 0"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have "f x + setsum f F \<le> 0 + 0" by (blast intro: add_mono)
  with insert show ?case by simp
qed

lemma setsum_nonneg_eq_0_iff:
  "finite A \<Longrightarrow> \<forall>x\<in>A. 0 \<le> f x \<Longrightarrow> setsum f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  by (induct set: finite) (simp_all add: add_nonneg_eq_0_iff setsum_nonneg)

lemma setsum_nonneg_0:
  "finite s \<Longrightarrow> (\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0) \<Longrightarrow> (\<Sum> i \<in> s. f i) = 0 \<Longrightarrow> i \<in> s \<Longrightarrow> f i = 0"
  by (simp add: setsum_nonneg_eq_0_iff)

lemma setsum_nonneg_leq_bound:
  assumes "finite s" "\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0" "(\<Sum>i \<in> s. f i) = B" "i \<in> s"
  shows "f i \<le> B"
proof -
  from assms have "f i \<le> f i + (\<Sum>i \<in> s - {i}. f i)"
    by (intro add_increasing2 setsum_nonneg) auto
  also have "\<dots> = B"
    using setsum.remove[of s i f] assms by simp
  finally show ?thesis by auto
qed

lemma setsum_mono2:
  assumes fin: "finite B"
    and sub: "A \<subseteq> B"
    and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 0 \<le> f b"
  shows "setsum f A \<le> setsum f B"
proof -
  have "setsum f A \<le> setsum f A + setsum f (B-A)"
    by(simp add: add_increasing2[OF setsum_nonneg] nn Ball_def)
  also from fin finite_subset[OF sub fin] have "\<dots> = setsum f (A \<union> (B-A))"
    by (simp add: setsum.union_disjoint del: Un_Diff_cancel)
  also from sub have "A \<union> (B-A) = B" by blast
  finally show ?thesis .
qed

lemma setsum_le_included:
  assumes "finite s" "finite t"
  and "\<forall>y\<in>t. 0 \<le> g y" "(\<forall>x\<in>s. \<exists>y\<in>t. i y = x \<and> f x \<le> g y)"
  shows "setsum f s \<le> setsum g t"
proof -
  have "setsum f s \<le> setsum (\<lambda>y. setsum g {x. x\<in>t \<and> i x = y}) s"
  proof (rule setsum_mono)
    fix y
    assume "y \<in> s"
    with assms obtain z where z: "z \<in> t" "y = i z" "f y \<le> g z" by auto
    with assms show "f y \<le> setsum g {x \<in> t. i x = y}" (is "?A y \<le> ?B y")
      using order_trans[of "?A (i z)" "setsum g {z}" "?B (i z)", intro]
      by (auto intro!: setsum_mono2)
  qed
  also have "\<dots> \<le> setsum (\<lambda>y. setsum g {x. x\<in>t \<and> i x = y}) (i ` t)"
    using assms(2-4) by (auto intro!: setsum_mono2 setsum_nonneg)
  also have "\<dots> \<le> setsum g t"
    using assms by (auto simp: setsum_image_gen[symmetric])
  finally show ?thesis .
qed

lemma setsum_mono3: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> \<forall>x\<in>B - A. 0 \<le> f x \<Longrightarrow> setsum f A \<le> setsum f B"
  by (rule setsum_mono2) auto

end

lemma (in canonically_ordered_monoid_add) setsum_eq_0_iff [simp]:
  "finite F \<Longrightarrow> (setsum f F = 0) = (\<forall>a\<in>F. f a = 0)"
  by (intro ballI setsum_nonneg_eq_0_iff zero_le)

lemma setsum_right_distrib: "r * setsum f A = setsum (\<lambda>n. r * f n) A"
  for f :: "'a \<Rightarrow> 'b::semiring_0"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (simp add: distrib_left)
qed

lemma setsum_left_distrib: "setsum f A * r = (\<Sum>n\<in>A. f n * r)"
  for r :: "'a::semiring_0"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (simp add: distrib_right)
qed

lemma setsum_divide_distrib: "setsum f A / r = (\<Sum>n\<in>A. f n / r)"
  for r :: "'a::field"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (simp add: add_divide_distrib)
qed

lemma setsum_abs[iff]: "\<bar>setsum f A\<bar> \<le> setsum (\<lambda>i. \<bar>f i\<bar>) A"
  for f :: "'a \<Rightarrow> 'b::ordered_ab_group_add_abs"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (auto intro: abs_triangle_ineq order_trans)
qed

lemma setsum_abs_ge_zero[iff]: "0 \<le> setsum (\<lambda>i. \<bar>f i\<bar>) A"
  for f :: "'a \<Rightarrow> 'b::ordered_ab_group_add_abs"
  by (simp add: setsum_nonneg)

lemma abs_setsum_abs[simp]: "\<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar> = (\<Sum>a\<in>A. \<bar>f a\<bar>)"
  for f :: "'a \<Rightarrow> 'b::ordered_ab_group_add_abs"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert a A)
  then have "\<bar>\<Sum>a\<in>insert a A. \<bar>f a\<bar>\<bar> = \<bar>\<bar>f a\<bar> + (\<Sum>a\<in>A. \<bar>f a\<bar>)\<bar>" by simp
  also from insert have "\<dots> = \<bar>\<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>\<bar>" by simp
  also have "\<dots> = \<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>" by (simp del: abs_of_nonneg)
  also from insert have "\<dots> = (\<Sum>a\<in>insert a A. \<bar>f a\<bar>)" by simp
  finally show ?case .
qed

lemma setsum_diff1_ring:
  fixes f :: "'b \<Rightarrow> 'a::ring"
  assumes "finite A" "a \<in> A"
  shows "setsum f (A - {a}) = setsum f A - (f a)"
  unfolding setsum.remove [OF assms] by auto

lemma setsum_product:
  fixes f :: "'a \<Rightarrow> 'b::semiring_0"
  shows "setsum f A * setsum g B = (\<Sum>i\<in>A. \<Sum>j\<in>B. f i * g j)"
  by (simp add: setsum_right_distrib setsum_left_distrib) (rule setsum.commute)

lemma setsum_mult_setsum_if_inj:
  fixes f :: "'a \<Rightarrow> 'b::semiring_0"
  shows "inj_on (\<lambda>(a, b). f a * g b) (A \<times> B) \<Longrightarrow>
    setsum f A * setsum g B = setsum id {f a * g b |a b. a \<in> A \<and> b \<in> B}"
  by(auto simp: setsum_product setsum.cartesian_product intro!: setsum.reindex_cong[symmetric])

lemma setsum_SucD: "setsum f A = Suc n \<Longrightarrow> \<exists>a\<in>A. 0 < f a"
  by (induct A rule: infinite_finite_induct) auto

lemma setsum_eq_Suc0_iff:
  "finite A \<Longrightarrow> setsum f A = Suc 0 \<longleftrightarrow> (\<exists>a\<in>A. f a = Suc 0 \<and> (\<forall>b\<in>A. a \<noteq> b \<longrightarrow> f b = 0))"
  by (induct A rule: finite_induct) (auto simp add: add_is_1)

lemmas setsum_eq_1_iff = setsum_eq_Suc0_iff[simplified One_nat_def[symmetric]]

lemma setsum_Un_nat:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> setsum f (A \<union> B) = setsum f A + setsum f B - setsum f (A \<inter> B)"
  for f :: "'a \<Rightarrow> nat"
  \<comment> \<open>For the natural numbers, we have subtraction.\<close>
  by (subst setsum.union_inter [symmetric]) (auto simp: algebra_simps)

lemma setsum_diff1_nat: "setsum f (A - {a}) = (if a \<in> A then setsum f A - f a else setsum f A)"
  for f :: "'a \<Rightarrow> nat"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case insert
  then show ?case
    apply (auto simp: insert_Diff_if)
    apply (drule mk_disjoint_insert)
    apply auto
    done
qed

lemma setsum_diff_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite B" and "B \<subseteq> A"
  shows "setsum f (A - B) = setsum f A - setsum f B"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case (insert x F)
  note IH = \<open>F \<subseteq> A \<Longrightarrow> setsum f (A - F) = setsum f A - setsum f F\<close>
  from \<open>x \<notin> F\<close> \<open>insert x F \<subseteq> A\<close> have "x \<in> A - F" by simp
  then have A: "setsum f ((A - F) - {x}) = setsum f (A - F) - f x"
    by (simp add: setsum_diff1_nat)
  from \<open>insert x F \<subseteq> A\<close> have "F \<subseteq> A" by simp
  with IH have "setsum f (A - F) = setsum f A - setsum f F" by simp
  with A have B: "setsum f ((A - F) - {x}) = setsum f A - setsum f F - f x"
    by simp
  from \<open>x \<notin> F\<close> have "A - insert x F = (A - F) - {x}" by auto
  with B have C: "setsum f (A - insert x F) = setsum f A - setsum f F - f x"
    by simp
  from \<open>finite F\<close> \<open>x \<notin> F\<close> have "setsum f (insert x F) = setsum f F + f x"
    by simp
  with C have "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)"
    by simp
  then show ?case by simp
qed

lemma setsum_comp_morphism:
  "h 0 = 0 \<Longrightarrow> (\<And>x y. h (x + y) = h x + h y) \<Longrightarrow> setsum (h \<circ> g) A = h (setsum g A)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in comm_semiring_1) dvd_setsum: "(\<And>a. a \<in> A \<Longrightarrow> d dvd f a) \<Longrightarrow> d dvd setsum f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in ordered_comm_monoid_add) setsum_pos:
  "finite I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> 0 < f i) \<Longrightarrow> 0 < setsum f I"
  by (induct I rule: finite_ne_induct) (auto intro: add_pos_pos)

lemma (in ordered_comm_monoid_add) setsum_pos2:
  assumes I: "finite I" "i \<in> I" "0 < f i" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "0 < setsum f I"
proof -
  have "0 < f i + setsum f (I - {i})"
    using assms by (intro add_pos_nonneg setsum_nonneg) auto
  also have "\<dots> = setsum f I"
    using assms by (simp add: setsum.remove)
  finally show ?thesis .
qed

lemma setsum_cong_Suc:
  assumes "0 \<notin> A" "\<And>x. Suc x \<in> A \<Longrightarrow> f (Suc x) = g (Suc x)"
  shows "setsum f A = setsum g A"
proof (rule setsum.cong)
  fix x
  assume "x \<in> A"
  with assms(1) show "f x = g x"
    by (cases x) (auto intro!: assms(2))
qed simp_all


subsubsection \<open>Cardinality as special case of @{const setsum}\<close>

lemma card_eq_setsum: "card A = setsum (\<lambda>x. 1) A"
proof -
  have "plus \<circ> (\<lambda>_. Suc 0) = (\<lambda>_. Suc)"
    by (simp add: fun_eq_iff)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) = Finite_Set.fold (\<lambda>_. Suc)"
    by (rule arg_cong)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) 0 A = Finite_Set.fold (\<lambda>_. Suc) 0 A"
    by (blast intro: fun_cong)
  then show ?thesis
    by (simp add: card.eq_fold setsum.eq_fold)
qed

lemma setsum_constant [simp]: "(\<Sum>x \<in> A. y) = of_nat (card A) * y"
  by (induct A rule: infinite_finite_induct) (auto simp: algebra_simps)

lemma setsum_Suc: "setsum (\<lambda>x. Suc(f x)) A = setsum f A + card A"
  using setsum.distrib[of f "\<lambda>_. 1" A] by simp

lemma setsum_bounded_above:
  fixes K :: "'a::{semiring_1,ordered_comm_monoid_add}"
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> K"
  shows "setsum f A \<le> of_nat (card A) * K"
proof (cases "finite A")
  case True
  then show ?thesis
    using le setsum_mono[where K=A and g = "\<lambda>x. K"] by simp
next
  case False
  then show ?thesis by simp
qed

lemma setsum_bounded_above_strict:
  fixes K :: "'a::{ordered_cancel_comm_monoid_add,semiring_1}"
  assumes "\<And>i. i\<in>A \<Longrightarrow> f i < K" "card A > 0"
  shows "setsum f A < of_nat (card A) * K"
  using assms setsum_strict_mono[where A=A and g = "\<lambda>x. K"]
  by (simp add: card_gt_0_iff)

lemma setsum_bounded_below:
  fixes K :: "'a::{semiring_1,ordered_comm_monoid_add}"
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> K \<le> f i"
  shows "of_nat (card A) * K \<le> setsum f A"
proof (cases "finite A")
  case True
  then show ?thesis
    using le setsum_mono[where K=A and f = "\<lambda>x. K"] by simp
next
  case False
  then show ?thesis by simp
qed

lemma card_UN_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "card (UNION I A) = (\<Sum>i\<in>I. card(A i))"
proof -
  have "(\<Sum>i\<in>I. card (A i)) = (\<Sum>i\<in>I. \<Sum>x\<in>A i. 1)"
    by simp
  with assms show ?thesis
    by (simp add: card_eq_setsum setsum.UNION_disjoint del: setsum_constant)
qed

lemma card_Union_disjoint:
  "finite C \<Longrightarrow> \<forall>A\<in>C. finite A \<Longrightarrow> \<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {} \<Longrightarrow>
    card (\<Union>C) = setsum card C"
  by (frule card_UN_disjoint [of C id]) simp_all

lemma setsum_multicount_gen:
  assumes "finite s" "finite t" "\<forall>j\<in>t. (card {i\<in>s. R i j} = k j)"
  shows "setsum (\<lambda>i. (card {j\<in>t. R i j})) s = setsum k t"
    (is "?l = ?r")
proof-
  have "?l = setsum (\<lambda>i. setsum (\<lambda>x.1) {j\<in>t. R i j}) s"
    by auto
  also have "\<dots> = ?r"
    unfolding setsum.commute_restrict [OF assms(1-2)]
    using assms(3) by auto
  finally show ?thesis .
qed

lemma setsum_multicount:
  assumes "finite S" "finite T" "\<forall>j\<in>T. (card {i\<in>S. R i j} = k)"
  shows "setsum (\<lambda>i. card {j\<in>T. R i j}) S = k * card T" (is "?l = ?r")
proof-
  have "?l = setsum (\<lambda>i. k) T"
    by (rule setsum_multicount_gen) (auto simp: assms)
  also have "\<dots> = ?r" by (simp add: mult.commute)
  finally show ?thesis by auto
qed


subsubsection \<open>Cardinality of products\<close>

lemma card_SigmaI [simp]:
  "finite A \<Longrightarrow> \<forall>a\<in>A. finite (B a) \<Longrightarrow> card (SIGMA x: A. B x) = (\<Sum>a\<in>A. card (B a))"
  by (simp add: card_eq_setsum setsum.Sigma del: setsum_constant)

(*
lemma SigmaI_insert: "y \<notin> A ==>
  (SIGMA x:(insert y A). B x) = (({y} \<times> (B y)) \<union> (SIGMA x: A. B x))"
  by auto
*)

lemma card_cartesian_product: "card (A \<times> B) = card A * card B"
  by (cases "finite A \<and> finite B")
    (auto simp add: card_eq_0_iff dest: finite_cartesian_productD1 finite_cartesian_productD2)

lemma card_cartesian_product_singleton:  "card ({x} \<times> A) = card A"
  by (simp add: card_cartesian_product)


subsection \<open>Generalized product over a set\<close>

context comm_monoid_mult
begin

sublocale setprod: comm_monoid_set times 1
  defines setprod = setprod.F ..

abbreviation Setprod ("\<Prod>_" [1000] 999)
  where "\<Prod>A \<equiv> setprod (\<lambda>x. x) A"

end

syntax (ASCII)
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(4PROD _:_./ _)" [0, 51, 10] 10)
syntax
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(2\<Prod>_\<in>_./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Prod>i\<in>A. b" == "CONST setprod (\<lambda>i. b) A"

text \<open>Instead of @{term"\<Prod>x\<in>{x. P}. e"} we introduce the shorter \<open>\<Prod>x|P. e\<close>.\<close>

syntax (ASCII)
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(4PROD _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Prod>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Prod>x|P. t" => "CONST setprod (\<lambda>x. t) {x. P}"

context comm_monoid_mult
begin

lemma setprod_dvd_setprod: "(\<And>a. a \<in> A \<Longrightarrow> f a dvd g a) \<Longrightarrow> setprod f A dvd setprod g A"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by (auto intro: dvdI)
next
  case empty
  then show ?case by (auto intro: dvdI)
next
  case (insert a A)
  then have "f a dvd g a" and "setprod f A dvd setprod g A"
    by simp_all
  then obtain r s where "g a = f a * r" and "setprod g A = setprod f A * s"
    by (auto elim!: dvdE)
  then have "g a * setprod g A = f a * setprod f A * (r * s)"
    by (simp add: ac_simps)
  with insert.hyps show ?case
    by (auto intro: dvdI)
qed

lemma setprod_dvd_setprod_subset: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> setprod f A dvd setprod f B"
  by (auto simp add: setprod.subset_diff ac_simps intro: dvdI)

end


subsubsection \<open>Properties in more restricted classes of structures\<close>

context comm_semiring_1
begin

lemma dvd_setprod_eqI [intro]:
  assumes "finite A" and "a \<in> A" and "b = f a"
  shows "b dvd setprod f A"
proof -
  from \<open>finite A\<close> have "setprod f (insert a (A - {a})) = f a * setprod f (A - {a})"
    by (intro setprod.insert) auto
  also from \<open>a \<in> A\<close> have "insert a (A - {a}) = A"
    by blast
  finally have "setprod f A = f a * setprod f (A - {a})" .
  with \<open>b = f a\<close> show ?thesis
    by simp
qed

lemma dvd_setprodI [intro]: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> f a dvd setprod f A"
  by auto

lemma setprod_zero:
  assumes "finite A" and "\<exists>a\<in>A. f a = 0"
  shows "setprod f A = 0"
  using assms
proof (induct A)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then have "f a = 0 \<or> (\<exists>a\<in>A. f a = 0)" by simp
  then have "f a * setprod f A = 0" by rule (simp_all add: insert)
  with insert show ?case by simp
qed

lemma setprod_dvd_setprod_subset2:
  assumes "finite B" and "A \<subseteq> B" and "\<And>a. a \<in> A \<Longrightarrow> f a dvd g a"
  shows "setprod f A dvd setprod g B"
proof -
  from assms have "setprod f A dvd setprod g A"
    by (auto intro: setprod_dvd_setprod)
  moreover from assms have "setprod g A dvd setprod g B"
    by (auto intro: setprod_dvd_setprod_subset)
  ultimately show ?thesis by (rule dvd_trans)
qed

end

lemma setprod_zero_iff [simp]:
  fixes f :: "'b \<Rightarrow> 'a::semidom"
  assumes "finite A"
  shows "setprod f A = 0 \<longleftrightarrow> (\<exists>a\<in>A. f a = 0)"
  using assms by (induct A) (auto simp: no_zero_divisors)

lemma (in semidom_divide) setprod_diff1:
  assumes "finite A" and "f a \<noteq> 0"
  shows "setprod f (A - {a}) = (if a \<in> A then setprod f A div f a else setprod f A)"
proof (cases "a \<notin> A")
  case True
  then show ?thesis by simp
next
  case False
  with assms show ?thesis
  proof induct
    case empty
    then show ?case by simp
  next
    case (insert b B)
    then show ?case
    proof (cases "a = b")
      case True
      with insert show ?thesis by simp
    next
      case False
      with insert have "a \<in> B" by simp
      define C where "C = B - {a}"
      with \<open>finite B\<close> \<open>a \<in> B\<close> have "B = insert a C" "finite C" "a \<notin> C"
        by auto
      with insert show ?thesis
        by (auto simp add: insert_commute ac_simps)
    qed
  qed
qed

lemma setsum_zero_power [simp]: "(\<Sum>i\<in>A. c i * 0^i) = (if finite A \<and> 0 \<in> A then c 0 else 0)"
  for c :: "nat \<Rightarrow> 'a::division_ring"
  by (induct A rule: infinite_finite_induct) auto

lemma setsum_zero_power' [simp]:
  "(\<Sum>i\<in>A. c i * 0^i / d i) = (if finite A \<and> 0 \<in> A then c 0 / d 0 else 0)"
  for c :: "nat \<Rightarrow> 'a::field"
  using setsum_zero_power [of "\<lambda>i. c i / d i" A] by auto

lemma (in field) setprod_inversef:
  "finite A \<Longrightarrow> setprod (inverse \<circ> f) A = inverse (setprod f A)"
  by (induct A rule: finite_induct) simp_all

lemma (in field) setprod_dividef: "finite A \<Longrightarrow> (\<Prod>x\<in>A. f x / g x) = setprod f A / setprod g A"
  using setprod_inversef [of A g] by (simp add: divide_inverse setprod.distrib)

lemma setprod_Un:
  fixes f :: "'b \<Rightarrow> 'a :: field"
  assumes "finite A" and "finite B"
    and "\<forall>x\<in>A \<inter> B. f x \<noteq> 0"
  shows "setprod f (A \<union> B) = setprod f A * setprod f B / setprod f (A \<inter> B)"
proof -
  from assms have "setprod f A * setprod f B = setprod f (A \<union> B) * setprod f (A \<inter> B)"
    by (simp add: setprod.union_inter [symmetric, of A B])
  with assms show ?thesis
    by simp
qed

lemma (in linordered_semidom) setprod_nonneg: "(\<forall>a\<in>A. 0 \<le> f a) \<Longrightarrow> 0 \<le> setprod f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in linordered_semidom) setprod_pos: "(\<forall>a\<in>A. 0 < f a) \<Longrightarrow> 0 < setprod f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in linordered_semidom) setprod_mono:
  "\<forall>i\<in>A. 0 \<le> f i \<and> f i \<le> g i \<Longrightarrow> setprod f A \<le> setprod g A"
  by (induct A rule: infinite_finite_induct) (auto intro!: setprod_nonneg mult_mono)

lemma (in linordered_semidom) setprod_mono_strict:
  assumes "finite A" "\<forall>i\<in>A. 0 \<le> f i \<and> f i < g i" "A \<noteq> {}"
  shows "setprod f A < setprod g A"
  using assms
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (force intro: mult_strict_mono' setprod_nonneg)
qed

lemma (in linordered_field) abs_setprod: "\<bar>setprod f A\<bar> = (\<Prod>x\<in>A. \<bar>f x\<bar>)"
  by (induct A rule: infinite_finite_induct) (simp_all add: abs_mult)

lemma setprod_eq_1_iff [simp]: "finite A \<Longrightarrow> setprod f A = 1 \<longleftrightarrow> (\<forall>a\<in>A. f a = 1)"
  for f :: "'a \<Rightarrow> nat"
  by (induct A rule: finite_induct) simp_all

lemma setprod_pos_nat_iff [simp]: "finite A \<Longrightarrow> setprod f A > 0 \<longleftrightarrow> (\<forall>a\<in>A. f a > 0)"
  for f :: "'a \<Rightarrow> nat"
  using setprod_zero_iff by (simp del: neq0_conv add: zero_less_iff_neq_zero)

lemma setprod_constant: "(\<Prod>x\<in> A. y) = y ^ card A"
  for y :: "'a::comm_monoid_mult"
  by (induct A rule: infinite_finite_induct) simp_all

lemma setprod_power_distrib: "setprod f A ^ n = setprod (\<lambda>x. (f x) ^ n) A"
  for f :: "'a \<Rightarrow> 'b::comm_semiring_1"
  by (induct A rule: infinite_finite_induct) (auto simp add: power_mult_distrib)

lemma power_setsum: "c ^ (\<Sum>a\<in>A. f a) = (\<Prod>a\<in>A. c ^ f a)"
  by (induct A rule: infinite_finite_induct) (simp_all add: power_add)

lemma setprod_gen_delta:
  fixes b :: "'b \<Rightarrow> 'a::comm_monoid_mult"
  assumes fin: "finite S"
  shows "setprod (\<lambda>k. if k = a then b k else c) S =
    (if a \<in> S then b a * c ^ (card S - 1) else c ^ card S)"
proof -
  let ?f = "(\<lambda>k. if k=a then b k else c)"
  show ?thesis
  proof (cases "a \<in> S")
    case False
    then have "\<forall> k\<in> S. ?f k = c" by simp
    with False show ?thesis by (simp add: setprod_constant)
  next
    case True
    let ?A = "S - {a}"
    let ?B = "{a}"
    from True have eq: "S = ?A \<union> ?B" by blast
    have disjoint: "?A \<inter> ?B = {}" by simp
    from fin have fin': "finite ?A" "finite ?B" by auto
    have f_A0: "setprod ?f ?A = setprod (\<lambda>i. c) ?A"
      by (rule setprod.cong) auto
    from fin True have card_A: "card ?A = card S - 1" by auto
    have f_A1: "setprod ?f ?A = c ^ card ?A"
      unfolding f_A0 by (rule setprod_constant)
    have "setprod ?f ?A * setprod ?f ?B = setprod ?f S"
      using setprod.union_disjoint[OF fin' disjoint, of ?f, unfolded eq[symmetric]]
      by simp
    with True card_A show ?thesis
      by (simp add: f_A1 field_simps cong add: setprod.cong cong del: if_weak_cong)
  qed
qed

end
