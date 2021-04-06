(*  Title:      HOL/Groups_Big.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

section \<open>Big sum and product over finite (non-empty) sets\<close>

theory Groups_Big
  imports Power
begin

subsection \<open>Generic monoid operation over a set\<close>

locale comm_monoid_set = comm_monoid
begin

subsubsection \<open>Standard sum or product indexed by a finite set\<close>

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

lemma insert_if: "finite A \<Longrightarrow> F g (insert x A) = (if x \<in> A then F g A else g x \<^bold>* F g A)"
  by (cases "x \<in> A") (simp_all add: insert_absorb)

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

lemma Int_Diff:
  assumes "finite A"
  shows "F g A = F g (A \<inter> B) \<^bold>* F g (A - B)"
  by (subst subset_diff [where B = "A - B"]) (auto simp:  Diff_Diff_Int assms)

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

lemma cong_simp [cong]:
  "\<lbrakk> A = B;  \<And>x. x \<in> B =simp=> g x = h x \<rbrakk> \<Longrightarrow> F (\<lambda>x. g x) A = F (\<lambda>x. h x) B"
by (rule cong) (simp_all add: simp_implies_def)

lemma reindex_cong:
  assumes "inj_on l B"
  assumes "A = l ` B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x"
  shows "F g A = F h B"
  using assms by (simp add: reindex)

lemma image_eq:
  assumes "inj_on g A"  
  shows "F (\<lambda>x. x) (g ` A) = F g A"
  using assms reindex_cong by fastforce

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "F g (\<Union>(A ` I)) = F (\<lambda>x. F g (A x)) I"
  using assms
proof (induction rule: finite_induct)
  case (insert i I)
  then have "\<forall>j\<in>I. j \<noteq> i"
    by blast
  with insert.prems have "A i \<inter> \<Union>(A ` I) = {}"
    by blast
  with insert show ?case
    by (simp add: union_disjoint)
qed auto

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
  assumes "finite A" "\<forall>x\<in>A. finite (B x)"
  shows "F (\<lambda>x. F (g x) (B x)) A = F (case_prod g) (SIGMA x:A. B x)"
  unfolding Sigma_def
proof (subst UNION_disjoint)
  show "F (\<lambda>x. F (g x) (B x)) A = F (\<lambda>x. F (\<lambda>(x, y). g x y) (\<Union>y\<in>B x. {(x, y)})) A"
  proof (rule cong [OF refl])
    show "F (g x) (B x) = F (\<lambda>(x, y). g x y) (\<Union>y\<in>B x. {(x, y)})"
      if "x \<in> A" for x
      using that assms by (simp add: UNION_disjoint)
  qed
qed (use assms in auto)

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

lemma mono_neutral_cong:
  assumes [simp]: "finite T" "finite S"
    and *: "\<And>i. i \<in> T - S \<Longrightarrow> h i = \<^bold>1" "\<And>i. i \<in> S - T \<Longrightarrow> g i = \<^bold>1"
    and gh: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x = h x"
 shows "F g S = F h T"
proof-
  have "F g S = F g (S \<inter> T)"
    by(rule mono_neutral_right)(auto intro: *)
  also have "\<dots> = F h (S \<inter> T)" using refl gh by(rule cong)
  also have "\<dots> = F h T"
    by(rule mono_neutral_left)(auto intro: *)
  finally show ?thesis .
qed

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

lemma delta_remove:
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k = a then b k else c k) S = (if a \<in> S then b a \<^bold>* F c (S-{a}) else F c (S-{a}))"
proof -
  let ?f = "(\<lambda>k. if k = a then b k else c k)"
  show ?thesis
  proof (cases "a \<in> S")
    case False
    then have "\<forall>k\<in>S. ?f k = c k" by simp
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
    with True show ?thesis
      using comm_monoid_set.remove comm_monoid_set_axioms fS by fastforce
  qed
qed

lemma delta [simp]:
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k = a then b k else \<^bold>1) S = (if a \<in> S then b a else \<^bold>1)"
  by (simp add: delta_remove [OF assms])

lemma delta' [simp]:
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
proof (cases "A = {} \<or> B = {}")
  case True
  then show ?thesis
    by auto
next
  case False
  then have "A \<noteq> {}" "B \<noteq> {}" by auto
  show ?thesis
  proof (cases "finite A \<and> finite B")
    case True
    then show ?thesis
      by (simp add: Sigma)
  next
    case False
    then consider "infinite A" | "infinite B" by auto
    then have "infinite (A \<times> B)"
      by cases (use \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> in \<open>auto dest: finite_cartesian_productD1 finite_cartesian_productD2\<close>)
    then show ?thesis
      using False by auto
  qed
qed

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

lemma swap: "F (\<lambda>i. F (g i) B) A = F (\<lambda>j. F (\<lambda>i. g i j) A) B"
  unfolding cartesian_product
  by (rule reindex_bij_witness [where i = "\<lambda>(i, j). (j, i)" and j = "\<lambda>(i, j). (j, i)"]) auto

lemma swap_restrict:
  "finite A \<Longrightarrow> finite B \<Longrightarrow>
    F (\<lambda>x. F (g x) {y. y \<in> B \<and> R x y}) A = F (\<lambda>y. F (\<lambda>x. g x y) {x. x \<in> A \<and> R x y}) B"
  by (simp add: inter_filter) (rule swap)

lemma image_gen:
  assumes fin: "finite S"
  shows "F h S = F (\<lambda>y. F h {x. x \<in> S \<and> g x = y}) (g ` S)"
proof -
  have "{y. y\<in> g`S \<and> g x = y} = {g x}" if "x \<in> S" for x
    using that by auto
  then have "F h S = F (\<lambda>x. F (\<lambda>y. h x) {y. y\<in> g`S \<and> g x = y}) S"
    by simp
  also have "\<dots> = F (\<lambda>y. F h {x. x \<in> S \<and> g x = y}) (g ` S)"
    by (rule swap_restrict [OF fin finite_imageI [OF fin]])
  finally show ?thesis .
qed

lemma group:
  assumes fS: "finite S" and fT: "finite T" and fST: "g ` S \<subseteq> T"
  shows "F (\<lambda>y. F h {x. x \<in> S \<and> g x = y}) T = F h S"
  unfolding image_gen[OF fS, of h g]
  by (auto intro: neutral mono_neutral_right[OF fT fST])

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

lemma eq_general:
  assumes B: "\<And>y. y \<in> B \<Longrightarrow> \<exists>!x. x \<in> A \<and> h x = y" and A: "\<And>x. x \<in> A \<Longrightarrow> h x \<in> B \<and> \<gamma>(h x) = \<phi> x"
  shows "F \<phi> A = F \<gamma> B"
proof -
  have eq: "B = h ` A"
    by (auto dest: assms)
  have h: "inj_on h A"
    using assms by (blast intro: inj_onI)
  have "F \<phi> A = F (\<gamma> \<circ> h) A"
    using A by auto
  also have "\<dots> = F \<gamma> B"
    by (simp add: eq reindex h)
  finally show ?thesis .
qed

lemma eq_general_inverses:
  assumes B: "\<And>y. y \<in> B \<Longrightarrow> k y \<in> A \<and> h(k y) = y" and A: "\<And>x. x \<in> A \<Longrightarrow> h x \<in> B \<and> k(h x) = x \<and> \<gamma>(h x) = \<phi> x"
  shows "F \<phi> A = F \<gamma> B"
  by (rule eq_general [where h=h]) (force intro: dest: A B)+

subsubsection \<open>HOL Light variant: sum/product indexed by the non-neutral subset\<close>
text \<open>NB only a subset of the properties above are proved\<close>

definition G :: "['b \<Rightarrow> 'a,'b set] \<Rightarrow> 'a"
  where "G p I \<equiv> if finite {x \<in> I. p x \<noteq> \<^bold>1} then F p {x \<in> I. p x \<noteq> \<^bold>1} else \<^bold>1"

lemma finite_Collect_op:
  shows "\<lbrakk>finite {i \<in> I. x i \<noteq> \<^bold>1}; finite {i \<in> I. y i \<noteq> \<^bold>1}\<rbrakk> \<Longrightarrow> finite {i \<in> I. x i \<^bold>* y i \<noteq> \<^bold>1}"
  apply (rule finite_subset [where B = "{i \<in> I. x i \<noteq> \<^bold>1} \<union> {i \<in> I. y i \<noteq> \<^bold>1}"]) 
  using left_neutral by force+

lemma empty' [simp]: "G p {} = \<^bold>1"
  by (auto simp: G_def)

lemma eq_sum [simp]: "finite I \<Longrightarrow> G p I = F p I"
  by (auto simp: G_def intro: mono_neutral_cong_left)

lemma insert' [simp]:
  assumes "finite {x \<in> I. p x \<noteq> \<^bold>1}"
  shows "G p (insert i I) = (if i \<in> I then G p I else p i \<^bold>* G p I)"
proof -
  have "{x. x = i \<and> p x \<noteq> \<^bold>1 \<or> x \<in> I \<and> p x \<noteq> \<^bold>1} = (if p i = \<^bold>1 then {x \<in> I. p x \<noteq> \<^bold>1} else insert i {x \<in> I. p x \<noteq> \<^bold>1})"
    by auto
  then show ?thesis
    using assms by (simp add: G_def conj_disj_distribR insert_absorb)
qed

lemma distrib_triv':
  assumes "finite I"
  shows "G (\<lambda>i. g i \<^bold>* h i) I = G g I \<^bold>* G h I"
  by (simp add: assms local.distrib)

lemma non_neutral': "G g {x \<in> I. g x \<noteq> \<^bold>1} = G g I"
  by (simp add: G_def)

lemma distrib':
  assumes "finite {x \<in> I. g x \<noteq> \<^bold>1}" "finite {x \<in> I. h x \<noteq> \<^bold>1}"
  shows "G (\<lambda>i. g i \<^bold>* h i) I = G g I \<^bold>* G h I"
proof -
  have "a \<^bold>* a \<noteq> a \<Longrightarrow> a \<noteq> \<^bold>1" for a
    by auto
  then have "G (\<lambda>i. g i \<^bold>* h i) I = G (\<lambda>i. g i \<^bold>* h i) ({i \<in> I. g i \<noteq> \<^bold>1} \<union> {i \<in> I. h i \<noteq> \<^bold>1})"
    using assms  by (force simp: G_def finite_Collect_op intro!: mono_neutral_cong)
  also have "\<dots> = G g I \<^bold>* G h I"
  proof -
    have "F g ({i \<in> I. g i \<noteq> \<^bold>1} \<union> {i \<in> I. h i \<noteq> \<^bold>1}) = G g I"
         "F h ({i \<in> I. g i \<noteq> \<^bold>1} \<union> {i \<in> I. h i \<noteq> \<^bold>1}) = G h I"
      by (auto simp: G_def assms intro: mono_neutral_right)
    then show ?thesis
      using assms by (simp add: distrib)
  qed
  finally show ?thesis .
qed

lemma cong':
  assumes "A = B"
  assumes g_h: "\<And>x. x \<in> B \<Longrightarrow> g x = h x"
  shows "G g A = G h B"
  using assms by (auto simp: G_def cong: conj_cong intro: cong)


lemma mono_neutral_cong_left':
  assumes "S \<subseteq> T"
    and "\<And>i. i \<in> T - S \<Longrightarrow> h i = \<^bold>1"
    and "\<And>x. x \<in> S \<Longrightarrow> g x = h x"
  shows "G g S = G h T"
proof -
  have *: "{x \<in> S. g x \<noteq> \<^bold>1} = {x \<in> T. h x \<noteq> \<^bold>1}"
    using assms by (metis DiffI subset_eq) 
  then have "finite {x \<in> S. g x \<noteq> \<^bold>1} = finite {x \<in> T. h x \<noteq> \<^bold>1}"
    by simp
  then show ?thesis
    using assms by (auto simp add: G_def * intro: cong)
qed

lemma mono_neutral_cong_right':
  "S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> g x = h x) \<Longrightarrow>
    G g T = G h S"
  by (auto intro!: mono_neutral_cong_left' [symmetric])

lemma mono_neutral_left': "S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> G g S = G g T"
  by (blast intro: mono_neutral_cong_left')

lemma mono_neutral_right': "S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> G g T = G g S"
  by (blast intro!: mono_neutral_left' [symmetric])

end


subsection \<open>Generalized summation over a set\<close>

context comm_monoid_add
begin

sublocale sum: comm_monoid_set plus 0
  defines sum = sum.F and sum' = sum.G ..

abbreviation Sum ("\<Sum>")
  where "\<Sum> \<equiv> sum (\<lambda>x. x)"

end

text \<open>Now: lots of fancy syntax. First, \<^term>\<open>sum (\<lambda>x. e) A\<close> is written \<open>\<Sum>x\<in>A. e\<close>.\<close>

syntax (ASCII)
  "_sum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::comm_monoid_add"  ("(3SUM (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_sum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::comm_monoid_add"  ("(2\<Sum>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>i\<in>A. b" \<rightleftharpoons> "CONST sum (\<lambda>i. b) A"

text \<open>Instead of \<^term>\<open>\<Sum>x\<in>{x. P}. e\<close> we introduce the shorter \<open>\<Sum>x|P. e\<close>.\<close>

syntax (ASCII)
  "_qsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3SUM _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Sum>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>x|P. t" => "CONST sum (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun sum_tr' [Abs (x, Tx, t), Const (\<^const_syntax>\<open>Collect\<close>, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const \<^syntax_const>\<open>_qsum\<close> $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | sum_tr' _ = raise Match;
in [(\<^const_syntax>\<open>sum\<close>, K sum_tr')] end
\<close>


subsubsection \<open>Properties in more restricted classes of structures\<close>

lemma sum_Un:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> sum f (A \<union> B) = sum f A + sum f B - sum f (A \<inter> B)"
  for f :: "'b \<Rightarrow> 'a::ab_group_add"
  by (subst sum.union_inter [symmetric]) (auto simp add: algebra_simps)

lemma sum_Un2:
  assumes "finite (A \<union> B)"
  shows "sum f (A \<union> B) = sum f (A - B) + sum f (B - A) + sum f (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis
    by simp (subst sum.union_disjoint, auto)+
qed

lemma sum_diff1:
  fixes f :: "'b \<Rightarrow> 'a::ab_group_add"
  assumes "finite A"
  shows "sum f (A - {a}) = (if a \<in> A then sum f A - f a else sum f A)"
  using assms by induct (auto simp: insert_Diff_if)

lemma sum_diff:
  fixes f :: "'b \<Rightarrow> 'a::ab_group_add"
  assumes "finite A" "B \<subseteq> A"
  shows "sum f (A - B) = sum f A - sum f B"
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
      by (simp add: Diff_insert[where a=x and B=F] sum_diff1 insert_absorb)
  qed
qed

lemma sum_diff1'_aux:
  fixes f :: "'a \<Rightarrow> 'b::ab_group_add"
  assumes "finite F" "{i \<in> I. f i \<noteq> 0} \<subseteq> F"
  shows "sum' f (I - {i}) = (if i \<in> I then sum' f I - f i else sum' f I)"
  using assms
proof induct
  case (insert x F)
  have 1: "finite {x \<in> I. f x \<noteq> 0} \<Longrightarrow> finite {x \<in> I. x \<noteq> i \<and> f x \<noteq> 0}"
    by (erule rev_finite_subset) auto
  have 2: "finite {x \<in> I. x \<noteq> i \<and> f x \<noteq> 0} \<Longrightarrow> finite {x \<in> I. f x \<noteq> 0}"
    apply (drule finite_insert [THEN iffD2])
    by (erule rev_finite_subset) auto
  have 3: "finite {i \<in> I. f i \<noteq> 0}"
    using finite_subset insert by blast
  show ?case
    using insert sum_diff1 [of "{i \<in> I. f i \<noteq> 0}" f i]
    by (auto simp: sum.G_def 1 2 3 set_diff_eq conj_ac)
qed (simp add: sum.G_def)

lemma sum_diff1':
  fixes f :: "'a \<Rightarrow> 'b::ab_group_add"
  assumes "finite {i \<in> I. f i \<noteq> 0}"
  shows "sum' f (I - {i}) = (if i \<in> I then sum' f I - f i else sum' f I)"
  by (rule sum_diff1'_aux [OF assms order_refl])

lemma (in ordered_comm_monoid_add) sum_mono:
  "(\<And>i. i\<in>K \<Longrightarrow> f i \<le> g i) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
  by (induct K rule: infinite_finite_induct) (use add_mono in auto)

lemma (in strict_ordered_comm_monoid_add) sum_strict_mono:
  assumes "finite A" "A \<noteq> {}"
    and "\<And>x. x \<in> A \<Longrightarrow> f x < g x"
  shows "sum f A < sum g A"
  using assms
proof (induct rule: finite_ne_induct)
  case singleton
  then show ?case by simp
next
  case insert
  then show ?case by (auto simp: add_strict_mono)
qed

lemma sum_strict_mono_ex1:
  fixes f g :: "'i \<Rightarrow> 'a::ordered_cancel_comm_monoid_add"
  assumes "finite A"
    and "\<forall>x\<in>A. f x \<le> g x"
    and "\<exists>a\<in>A. f a < g a"
  shows "sum f A < sum g A"
proof-
  from assms(3) obtain a where a: "a \<in> A" "f a < g a" by blast
  have "sum f A = sum f ((A - {a}) \<union> {a})"
    by(simp add: insert_absorb[OF \<open>a \<in> A\<close>])
  also have "\<dots> = sum f (A - {a}) + sum f {a}"
    using \<open>finite A\<close> by(subst sum.union_disjoint) auto
  also have "sum f (A - {a}) \<le> sum g (A - {a})"
    by (rule sum_mono) (simp add: assms(2))
  also from a have "sum f {a} < sum g {a}" by simp
  also have "sum g (A - {a}) + sum g {a} = sum g((A - {a}) \<union> {a})"
    using \<open>finite A\<close> by (subst sum.union_disjoint[symmetric]) auto
  also have "\<dots> = sum g A" by (simp add: insert_absorb[OF \<open>a \<in> A\<close>])
  finally show ?thesis
    by (auto simp add: add_right_mono add_strict_left_mono)
qed

lemma sum_mono_inv:
  fixes f g :: "'i \<Rightarrow> 'a :: ordered_cancel_comm_monoid_add"
  assumes eq: "sum f I = sum g I"
  assumes le: "\<And>i. i \<in> I \<Longrightarrow> f i \<le> g i"
  assumes i: "i \<in> I"
  assumes I: "finite I"
  shows "f i = g i"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with le[OF i] have "f i < g i" by simp
  with i have "\<exists>i\<in>I. f i < g i" ..
  from sum_strict_mono_ex1[OF I _ this] le have "sum f I < sum g I"
    by blast
  with eq show False by simp
qed

lemma member_le_sum:
  fixes f :: "_ \<Rightarrow> 'b::{semiring_1, ordered_comm_monoid_add}"
  assumes "i \<in> A"
    and le: "\<And>x. x \<in> A - {i} \<Longrightarrow> 0 \<le> f x"
    and "finite A"
  shows "f i \<le> sum f A"
proof -
  have "f i \<le> sum f (A \<inter> {i})"
    by (simp add: assms)
  also have "... = (\<Sum>x\<in>A. if x \<in> {i} then f x else 0)"
    using assms sum.inter_restrict by blast
  also have "... \<le> sum f A"
    apply (rule sum_mono)
    apply (auto simp: le)
    done
  finally show ?thesis .
qed

lemma sum_negf: "(\<Sum>x\<in>A. - f x) = - (\<Sum>x\<in>A. f x)"
  for f :: "'b \<Rightarrow> 'a::ab_group_add"
  by (induct A rule: infinite_finite_induct) auto

lemma sum_subtractf: "(\<Sum>x\<in>A. f x - g x) = (\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x)"
  for f g :: "'b \<Rightarrow>'a::ab_group_add"
  using sum.distrib [of f "- g" A] by (simp add: sum_negf)

lemma sum_subtractf_nat:
  "(\<And>x. x \<in> A \<Longrightarrow> g x \<le> f x) \<Longrightarrow> (\<Sum>x\<in>A. f x - g x) = (\<Sum>x\<in>A. f x) - (\<Sum>x\<in>A. g x)"
  for f g :: "'a \<Rightarrow> nat"
  by (induct A rule: infinite_finite_induct) (auto simp: sum_mono)

context ordered_comm_monoid_add
begin

lemma sum_nonneg: "(\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x) \<Longrightarrow> 0 \<le> sum f A"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have "0 + 0 \<le> f x + sum f F" by (blast intro: add_mono)
  with insert show ?case by simp
qed

lemma sum_nonpos: "(\<And>x. x \<in> A \<Longrightarrow> f x \<le> 0) \<Longrightarrow> sum f A \<le> 0"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have "f x + sum f F \<le> 0 + 0" by (blast intro: add_mono)
  with insert show ?case by simp
qed

lemma sum_nonneg_eq_0_iff:
  "finite A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x) \<Longrightarrow> sum f A = 0 \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  by (induct set: finite) (simp_all add: add_nonneg_eq_0_iff sum_nonneg)

lemma sum_nonneg_0:
  "finite s \<Longrightarrow> (\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0) \<Longrightarrow> (\<Sum> i \<in> s. f i) = 0 \<Longrightarrow> i \<in> s \<Longrightarrow> f i = 0"
  by (simp add: sum_nonneg_eq_0_iff)

lemma sum_nonneg_leq_bound:
  assumes "finite s" "\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0" "(\<Sum>i \<in> s. f i) = B" "i \<in> s"
  shows "f i \<le> B"
proof -
  from assms have "f i \<le> f i + (\<Sum>i \<in> s - {i}. f i)"
    by (intro add_increasing2 sum_nonneg) auto
  also have "\<dots> = B"
    using sum.remove[of s i f] assms by simp
  finally show ?thesis by auto
qed

lemma sum_mono2:
  assumes fin: "finite B"
    and sub: "A \<subseteq> B"
    and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 0 \<le> f b"
  shows "sum f A \<le> sum f B"
proof -
  have "sum f A \<le> sum f A + sum f (B-A)"
    by (auto intro: add_increasing2 [OF sum_nonneg] nn)
  also from fin finite_subset[OF sub fin] have "\<dots> = sum f (A \<union> (B-A))"
    by (simp add: sum.union_disjoint del: Un_Diff_cancel)
  also from sub have "A \<union> (B-A) = B" by blast
  finally show ?thesis .
qed

lemma sum_le_included:
  assumes "finite s" "finite t"
  and "\<forall>y\<in>t. 0 \<le> g y" "(\<forall>x\<in>s. \<exists>y\<in>t. i y = x \<and> f x \<le> g y)"
  shows "sum f s \<le> sum g t"
proof -
  have "sum f s \<le> sum (\<lambda>y. sum g {x. x\<in>t \<and> i x = y}) s"
  proof (rule sum_mono)
    fix y
    assume "y \<in> s"
    with assms obtain z where z: "z \<in> t" "y = i z" "f y \<le> g z" by auto
    with assms show "f y \<le> sum g {x \<in> t. i x = y}" (is "?A y \<le> ?B y")
      using order_trans[of "?A (i z)" "sum g {z}" "?B (i z)", intro]
      by (auto intro!: sum_mono2)
  qed
  also have "\<dots> \<le> sum (\<lambda>y. sum g {x. x\<in>t \<and> i x = y}) (i ` t)"
    using assms(2-4) by (auto intro!: sum_mono2 sum_nonneg)
  also have "\<dots> \<le> sum g t"
    using assms by (auto simp: sum.image_gen[symmetric])
  finally show ?thesis .
qed

end

lemma (in canonically_ordered_monoid_add) sum_eq_0_iff [simp]:
  "finite F \<Longrightarrow> (sum f F = 0) = (\<forall>a\<in>F. f a = 0)"
  by (intro ballI sum_nonneg_eq_0_iff zero_le)

context semiring_0
begin

lemma sum_distrib_left: "r * sum f A = (\<Sum>n\<in>A. r * f n)"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

lemma sum_distrib_right: "sum f A * r = (\<Sum>n\<in>A. f n * r)"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

end

lemma sum_divide_distrib: "sum f A / r = (\<Sum>n\<in>A. f n / r)"
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

lemma sum_abs[iff]: "\<bar>sum f A\<bar> \<le> sum (\<lambda>i. \<bar>f i\<bar>) A"
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

lemma sum_abs_ge_zero[iff]: "0 \<le> sum (\<lambda>i. \<bar>f i\<bar>) A"
  for f :: "'a \<Rightarrow> 'b::ordered_ab_group_add_abs"
  by (simp add: sum_nonneg)

lemma abs_sum_abs[simp]: "\<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar> = (\<Sum>a\<in>A. \<bar>f a\<bar>)"
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

lemma sum_product:
  fixes f :: "'a \<Rightarrow> 'b::semiring_0"
  shows "sum f A * sum g B = (\<Sum>i\<in>A. \<Sum>j\<in>B. f i * g j)"
  by (simp add: sum_distrib_left sum_distrib_right) (rule sum.swap)

lemma sum_mult_sum_if_inj:
  fixes f :: "'a \<Rightarrow> 'b::semiring_0"
  shows "inj_on (\<lambda>(a, b). f a * g b) (A \<times> B) \<Longrightarrow>
    sum f A * sum g B = sum id {f a * g b |a b. a \<in> A \<and> b \<in> B}"
  by(auto simp: sum_product sum.cartesian_product intro!: sum.reindex_cong[symmetric])

lemma sum_SucD: "sum f A = Suc n \<Longrightarrow> \<exists>a\<in>A. 0 < f a"
  by (induct A rule: infinite_finite_induct) auto

lemma sum_eq_Suc0_iff:
  "finite A \<Longrightarrow> sum f A = Suc 0 \<longleftrightarrow> (\<exists>a\<in>A. f a = Suc 0 \<and> (\<forall>b\<in>A. a \<noteq> b \<longrightarrow> f b = 0))"
  by (induct A rule: finite_induct) (auto simp add: add_is_1)

lemmas sum_eq_1_iff = sum_eq_Suc0_iff[simplified One_nat_def[symmetric]]

lemma sum_Un_nat:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> sum f (A \<union> B) = sum f A + sum f B - sum f (A \<inter> B)"
  for f :: "'a \<Rightarrow> nat"
  \<comment> \<open>For the natural numbers, we have subtraction.\<close>
  by (subst sum.union_inter [symmetric]) (auto simp: algebra_simps)

lemma sum_diff1_nat: "sum f (A - {a}) = (if a \<in> A then sum f A - f a else sum f A)"
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

lemma sum_diff_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite B" and "B \<subseteq> A"
  shows "sum f (A - B) = sum f A - sum f B"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case (insert x F)
  note IH = \<open>F \<subseteq> A \<Longrightarrow> sum f (A - F) = sum f A - sum f F\<close>
  from \<open>x \<notin> F\<close> \<open>insert x F \<subseteq> A\<close> have "x \<in> A - F" by simp
  then have A: "sum f ((A - F) - {x}) = sum f (A - F) - f x"
    by (simp add: sum_diff1_nat)
  from \<open>insert x F \<subseteq> A\<close> have "F \<subseteq> A" by simp
  with IH have "sum f (A - F) = sum f A - sum f F" by simp
  with A have B: "sum f ((A - F) - {x}) = sum f A - sum f F - f x"
    by simp
  from \<open>x \<notin> F\<close> have "A - insert x F = (A - F) - {x}" by auto
  with B have C: "sum f (A - insert x F) = sum f A - sum f F - f x"
    by simp
  from \<open>finite F\<close> \<open>x \<notin> F\<close> have "sum f (insert x F) = sum f F + f x"
    by simp
  with C have "sum f (A - insert x F) = sum f A - sum f (insert x F)"
    by simp
  then show ?case by simp
qed

lemma sum_comp_morphism:
  "h 0 = 0 \<Longrightarrow> (\<And>x y. h (x + y) = h x + h y) \<Longrightarrow> sum (h \<circ> g) A = h (sum g A)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in comm_semiring_1) dvd_sum: "(\<And>a. a \<in> A \<Longrightarrow> d dvd f a) \<Longrightarrow> d dvd sum f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma (in ordered_comm_monoid_add) sum_pos:
  "finite I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> 0 < f i) \<Longrightarrow> 0 < sum f I"
  by (induct I rule: finite_ne_induct) (auto intro: add_pos_pos)

lemma (in ordered_comm_monoid_add) sum_pos2:
  assumes I: "finite I" "i \<in> I" "0 < f i" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> f i"
  shows "0 < sum f I"
proof -
  have "0 < f i + sum f (I - {i})"
    using assms by (intro add_pos_nonneg sum_nonneg) auto
  also have "\<dots> = sum f I"
    using assms by (simp add: sum.remove)
  finally show ?thesis .
qed

lemma sum_strict_mono2:
  fixes f :: "'a \<Rightarrow> 'b::ordered_cancel_comm_monoid_add"
  assumes "finite B" "A \<subseteq> B" "b \<in> B-A" "f b > 0" and "\<And>x. x \<in> B \<Longrightarrow> f x \<ge> 0"
  shows "sum f A < sum f B"
proof -
  have "B - A \<noteq> {}"
    using assms(3) by blast
  have "sum f (B-A) > 0"
    by (rule sum_pos2) (use assms in auto)
  moreover have "sum f B = sum f (B-A) + sum f A"
    by (rule sum.subset_diff) (use assms in auto)
  ultimately show ?thesis
    using add_strict_increasing by auto
qed

lemma sum_cong_Suc:
  assumes "0 \<notin> A" "\<And>x. Suc x \<in> A \<Longrightarrow> f (Suc x) = g (Suc x)"
  shows "sum f A = sum g A"
proof (rule sum.cong)
  fix x
  assume "x \<in> A"
  with assms(1) show "f x = g x"
    by (cases x) (auto intro!: assms(2))
qed simp_all


subsubsection \<open>Cardinality as special case of \<^const>\<open>sum\<close>\<close>

lemma card_eq_sum: "card A = sum (\<lambda>x. 1) A"
proof -
  have "plus \<circ> (\<lambda>_. Suc 0) = (\<lambda>_. Suc)"
    by (simp add: fun_eq_iff)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) = Finite_Set.fold (\<lambda>_. Suc)"
    by (rule arg_cong)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) 0 A = Finite_Set.fold (\<lambda>_. Suc) 0 A"
    by (blast intro: fun_cong)
  then show ?thesis
    by (simp add: card.eq_fold sum.eq_fold)
qed

context semiring_1
begin

lemma sum_constant [simp]:
  "(\<Sum>x \<in> A. y) = of_nat (card A) * y"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

context
  fixes A
  assumes \<open>finite A\<close>
begin

lemma sum_of_bool_eq [simp]:
  \<open>(\<Sum>x \<in> A. of_bool (P x)) = of_nat (card (A \<inter> {x. P x}))\<close> if \<open>finite A\<close>
  using \<open>finite A\<close> by induction simp_all

lemma sum_mult_of_bool_eq [simp]:
  \<open>(\<Sum>x \<in> A. f x * of_bool (P x)) = (\<Sum>x \<in> (A \<inter> {x. P x}). f x)\<close>
  by (rule sum.mono_neutral_cong) (use \<open>finite A\<close> in auto)

lemma sum_of_bool_mult_eq [simp]:
  \<open>(\<Sum>x \<in> A. of_bool (P x) * f x) = (\<Sum>x \<in> (A \<inter> {x. P x}). f x)\<close>
  by (rule sum.mono_neutral_cong) (use \<open>finite A\<close> in auto)

end

end

lemma sum_Suc: "sum (\<lambda>x. Suc(f x)) A = sum f A + card A"
  using sum.distrib[of f "\<lambda>_. 1" A] by simp

lemma sum_bounded_above:
  fixes K :: "'a::{semiring_1,ordered_comm_monoid_add}"
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> K"
  shows "sum f A \<le> of_nat (card A) * K"
proof (cases "finite A")
  case True
  then show ?thesis
    using le sum_mono[where K=A and g = "\<lambda>x. K"] by simp
next
  case False
  then show ?thesis by simp
qed

lemma sum_bounded_above_divide:
  fixes K :: "'a::linordered_field"
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> K / of_nat (card A)" and fin: "finite A" "A \<noteq> {}"
  shows "sum f A \<le> K"
  using sum_bounded_above [of A f "K / of_nat (card A)", OF le] fin by simp

lemma sum_bounded_above_strict:
  fixes K :: "'a::{ordered_cancel_comm_monoid_add,semiring_1}"
  assumes "\<And>i. i\<in>A \<Longrightarrow> f i < K" "card A > 0"
  shows "sum f A < of_nat (card A) * K"
  using assms sum_strict_mono[where A=A and g = "\<lambda>x. K"]
  by (simp add: card_gt_0_iff)

lemma sum_bounded_below:
  fixes K :: "'a::{semiring_1,ordered_comm_monoid_add}"
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> K \<le> f i"
  shows "of_nat (card A) * K \<le> sum f A"
proof (cases "finite A")
  case True
  then show ?thesis
    using le sum_mono[where K=A and f = "\<lambda>x. K"] by simp
next
  case False
  then show ?thesis by simp
qed

lemma convex_sum_bound_le:
  fixes x :: "'a \<Rightarrow> 'b::linordered_idom"
  assumes 0: "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> x i" and 1: "sum x I = 1"
      and \<delta>: "\<And>i. i \<in> I \<Longrightarrow> \<bar>a i - b\<bar> \<le> \<delta>"
    shows "\<bar>(\<Sum>i\<in>I. a i * x i) - b\<bar> \<le> \<delta>"
proof -
  have [simp]: "(\<Sum>i\<in>I. c * x i) = c" for c
    by (simp flip: sum_distrib_left 1)
  then have "\<bar>(\<Sum>i\<in>I. a i * x i) - b\<bar> = \<bar>\<Sum>i\<in>I. (a i - b) * x i\<bar>"
    by (simp add: sum_subtractf left_diff_distrib)
  also have "\<dots> \<le> (\<Sum>i\<in>I. \<bar>(a i - b) * x i\<bar>)"
    using abs_abs abs_of_nonneg by blast
  also have "\<dots> \<le> (\<Sum>i\<in>I. \<bar>(a i - b)\<bar> * x i)"
    by (simp add: abs_mult 0)
  also have "\<dots> \<le> (\<Sum>i\<in>I. \<delta> * x i)"
    by (rule sum_mono) (use \<delta> "0" mult_right_mono in blast)
  also have "\<dots> = \<delta>"
    by simp
  finally show ?thesis .
qed

lemma card_UN_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "card (\<Union>(A ` I)) = (\<Sum>i\<in>I. card(A i))"
proof -
  have "(\<Sum>i\<in>I. card (A i)) = (\<Sum>i\<in>I. \<Sum>x\<in>A i. 1)"
    by simp
  with assms show ?thesis
    by (simp add: card_eq_sum sum.UNION_disjoint del: sum_constant)
qed

lemma card_Union_disjoint:
  assumes "pairwise disjnt C" and fin: "\<And>A. A \<in> C \<Longrightarrow> finite A"
  shows "card (\<Union>C) = sum card C"
proof (cases "finite C")
  case True
  then show ?thesis
    using card_UN_disjoint [OF True, of "\<lambda>x. x"] assms
    by (simp add: disjnt_def fin pairwise_def)
next
  case False
  then show ?thesis
    using assms card_eq_0_iff finite_UnionD by fastforce
qed

lemma card_Union_le_sum_card:
  fixes U :: "'a set set"
  assumes "\<forall>u \<in> U. finite u"
  shows "card (\<Union>U) \<le> sum card U"
proof (cases "finite U")
  case False
  then show "card (\<Union>U) \<le> sum card U"
    using card_eq_0_iff finite_UnionD by auto
next
  case True
  then show "card (\<Union>U) \<le> sum card U"
  proof (induct U rule: finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert x F)
    then have "card(\<Union>(insert x F)) \<le> card(x) + card (\<Union>F)" using card_Un_le by auto
    also have "... \<le> card(x) + sum card F" using insert.hyps by auto
    also have "... = sum card (insert x F)" using sum.insert_if and insert.hyps by auto
    finally show ?case .
  qed
qed

lemma card_UN_le:
  assumes "finite I"
  shows "card(\<Union>i\<in>I. A i) \<le> (\<Sum>i\<in>I. card(A i))"
  using assms
proof induction
  case (insert i I)
  then show ?case
    using card_Un_le nat_add_left_cancel_le by (force intro: order_trans) 
qed auto

lemma sum_multicount_gen:
  assumes "finite s" "finite t" "\<forall>j\<in>t. (card {i\<in>s. R i j} = k j)"
  shows "sum (\<lambda>i. (card {j\<in>t. R i j})) s = sum k t"
    (is "?l = ?r")
proof-
  have "?l = sum (\<lambda>i. sum (\<lambda>x.1) {j\<in>t. R i j}) s"
    by auto
  also have "\<dots> = ?r"
    unfolding sum.swap_restrict [OF assms(1-2)]
    using assms(3) by auto
  finally show ?thesis .
qed

lemma sum_multicount:
  assumes "finite S" "finite T" "\<forall>j\<in>T. (card {i\<in>S. R i j} = k)"
  shows "sum (\<lambda>i. card {j\<in>T. R i j}) S = k * card T" (is "?l = ?r")
proof-
  have "?l = sum (\<lambda>i. k) T"
    by (rule sum_multicount_gen) (auto simp: assms)
  also have "\<dots> = ?r" by (simp add: mult.commute)
  finally show ?thesis by auto
qed

lemma sum_card_image:
  assumes "finite A"
  assumes "pairwise (\<lambda>s t. disjnt (f s) (f t)) A"
  shows "sum card (f ` A) = sum (\<lambda>a. card (f a)) A"
using assms
proof (induct A)
  case (insert a A)
  show ?case
  proof cases
    assume "f a = {}"
    with insert show ?case
      by (subst sum.mono_neutral_right[where S="f ` A"]) (auto simp: pairwise_insert)
  next
    assume "f a \<noteq> {}"
    then have "sum card (insert (f a) (f ` A)) = card (f a) + sum card (f ` A)"
      using insert
      by (subst sum.insert) (auto simp: pairwise_insert)
    with insert show ?case by (simp add: pairwise_insert)
  qed
qed simp


subsubsection \<open>Cardinality of products\<close>

lemma card_SigmaI [simp]:
  "finite A \<Longrightarrow> \<forall>a\<in>A. finite (B a) \<Longrightarrow> card (SIGMA x: A. B x) = (\<Sum>a\<in>A. card (B a))"
  by (simp add: card_eq_sum sum.Sigma del: sum_constant)

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

sublocale prod: comm_monoid_set times 1
  defines prod = prod.F and prod' = prod.G ..

abbreviation Prod ("\<Prod>_" [1000] 999)
  where "\<Prod>A \<equiv> prod (\<lambda>x. x) A"

end

syntax (ASCII)
  "_prod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(4PROD (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_prod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(2\<Prod>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Prod>i\<in>A. b" == "CONST prod (\<lambda>i. b) A"

text \<open>Instead of \<^term>\<open>\<Prod>x\<in>{x. P}. e\<close> we introduce the shorter \<open>\<Prod>x|P. e\<close>.\<close>

syntax (ASCII)
  "_qprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(4PROD _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Prod>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Prod>x|P. t" => "CONST prod (\<lambda>x. t) {x. P}"

context comm_monoid_mult
begin

lemma prod_dvd_prod: "(\<And>a. a \<in> A \<Longrightarrow> f a dvd g a) \<Longrightarrow> prod f A dvd prod g A"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by (auto intro: dvdI)
next
  case empty
  then show ?case by (auto intro: dvdI)
next
  case (insert a A)
  then have "f a dvd g a" and "prod f A dvd prod g A"
    by simp_all
  then obtain r s where "g a = f a * r" and "prod g A = prod f A * s"
    by (auto elim!: dvdE)
  then have "g a * prod g A = f a * prod f A * (r * s)"
    by (simp add: ac_simps)
  with insert.hyps show ?case
    by (auto intro: dvdI)
qed

lemma prod_dvd_prod_subset: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> prod f A dvd prod f B"
  by (auto simp add: prod.subset_diff ac_simps intro: dvdI)

end


subsubsection \<open>Properties in more restricted classes of structures\<close>

context linordered_nonzero_semiring
begin

lemma prod_ge_1: "(\<And>x. x \<in> A \<Longrightarrow> 1 \<le> f x) \<Longrightarrow> 1 \<le> prod f A"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "1 * 1 \<le> f x * prod f F"
    by (rule mult_mono') (use insert in auto)
  with insert show ?case by simp
qed

lemma prod_le_1:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x \<and> f x \<le> 1"
  shows "prod f A \<le> 1"
    using assms
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case by (force simp: mult.commute intro: dest: mult_le_one)
qed

end

context comm_semiring_1
begin

lemma dvd_prod_eqI [intro]:
  assumes "finite A" and "a \<in> A" and "b = f a"
  shows "b dvd prod f A"
proof -
  from \<open>finite A\<close> have "prod f (insert a (A - {a})) = f a * prod f (A - {a})"
    by (intro prod.insert) auto
  also from \<open>a \<in> A\<close> have "insert a (A - {a}) = A"
    by blast
  finally have "prod f A = f a * prod f (A - {a})" .
  with \<open>b = f a\<close> show ?thesis
    by simp
qed

lemma dvd_prodI [intro]: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> f a dvd prod f A"
  by auto

lemma prod_zero:
  assumes "finite A" and "\<exists>a\<in>A. f a = 0"
  shows "prod f A = 0"
  using assms
proof (induct A)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then have "f a = 0 \<or> (\<exists>a\<in>A. f a = 0)" by simp
  then have "f a * prod f A = 0" by rule (simp_all add: insert)
  with insert show ?case by simp
qed

lemma prod_dvd_prod_subset2:
  assumes "finite B" and "A \<subseteq> B" and "\<And>a. a \<in> A \<Longrightarrow> f a dvd g a"
  shows "prod f A dvd prod g B"
proof -
  from assms have "prod f A dvd prod g A"
    by (auto intro: prod_dvd_prod)
  moreover from assms have "prod g A dvd prod g B"
    by (auto intro: prod_dvd_prod_subset)
  ultimately show ?thesis by (rule dvd_trans)
qed

end

lemma (in semidom) prod_zero_iff [simp]:
  fixes f :: "'b \<Rightarrow> 'a"
  assumes "finite A"
  shows "prod f A = 0 \<longleftrightarrow> (\<exists>a\<in>A. f a = 0)"
  using assms by (induct A) (auto simp: no_zero_divisors)

lemma (in semidom_divide) prod_diff1:
  assumes "finite A" and "f a \<noteq> 0"
  shows "prod f (A - {a}) = (if a \<in> A then prod f A div f a else prod f A)"
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

lemma sum_zero_power [simp]: "(\<Sum>i\<in>A. c i * 0^i) = (if finite A \<and> 0 \<in> A then c 0 else 0)"
  for c :: "nat \<Rightarrow> 'a::division_ring"
  by (induct A rule: infinite_finite_induct) auto

lemma sum_zero_power' [simp]:
  "(\<Sum>i\<in>A. c i * 0^i / d i) = (if finite A \<and> 0 \<in> A then c 0 / d 0 else 0)"
  for c :: "nat \<Rightarrow> 'a::field"
  using sum_zero_power [of "\<lambda>i. c i / d i" A] by auto

lemma (in field) prod_inversef: "prod (inverse \<circ> f) A = inverse (prod f A)"
 proof (cases "finite A")
   case True
   then show ?thesis
     by (induct A rule: finite_induct) simp_all
 next
   case False
   then show ?thesis
     by auto
 qed

lemma (in field) prod_dividef: "(\<Prod>x\<in>A. f x / g x) = prod f A / prod g A"
  using prod_inversef [of g A] by (simp add: divide_inverse prod.distrib)

lemma prod_Un:
  fixes f :: "'b \<Rightarrow> 'a :: field"
  assumes "finite A" and "finite B"
    and "\<forall>x\<in>A \<inter> B. f x \<noteq> 0"
  shows "prod f (A \<union> B) = prod f A * prod f B / prod f (A \<inter> B)"
proof -
  from assms have "prod f A * prod f B = prod f (A \<union> B) * prod f (A \<inter> B)"
    by (simp add: prod.union_inter [symmetric, of A B])
  with assms show ?thesis
    by simp
qed

context linordered_semidom
begin

lemma prod_nonneg: "(\<forall>a\<in>A. 0 \<le> f a) \<Longrightarrow> 0 \<le> prod f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma prod_pos: "(\<forall>a\<in>A. 0 < f a) \<Longrightarrow> 0 < prod f A"
  by (induct A rule: infinite_finite_induct) simp_all

lemma prod_mono:
  "(\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i \<and> f i \<le> g i) \<Longrightarrow> prod f A \<le> prod g A"
  by (induct A rule: infinite_finite_induct) (force intro!: prod_nonneg mult_mono)+

lemma prod_mono_strict:
  assumes "finite A" "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i \<and> f i < g i" "A \<noteq> {}"
  shows "prod f A < prod g A"
  using assms
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (force intro: mult_strict_mono' prod_nonneg)
qed

end

lemma prod_mono2:
  fixes f :: "'a \<Rightarrow> 'b :: linordered_idom"
  assumes fin: "finite B"
    and sub: "A \<subseteq> B"
    and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 1 \<le> f b"
    and A: "\<And>a. a \<in> A \<Longrightarrow> 0 \<le> f a"
  shows "prod f A \<le> prod f B"
proof -
  have "prod f A \<le> prod f A * prod f (B-A)"
    by (metis prod_ge_1 A mult_le_cancel_left1 nn not_less prod_nonneg)
  also from fin finite_subset[OF sub fin] have "\<dots> = prod f (A \<union> (B-A))"
    by (simp add: prod.union_disjoint del: Un_Diff_cancel)
  also from sub have "A \<union> (B-A) = B" by blast
  finally show ?thesis .
qed

lemma less_1_prod:
  fixes f :: "'a \<Rightarrow> 'b::linordered_idom"
  shows "finite I \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> 1 < f i) \<Longrightarrow> 1 < prod f I"
  by (induct I rule: finite_ne_induct) (auto intro: less_1_mult)

lemma less_1_prod2:
  fixes f :: "'a \<Rightarrow> 'b::linordered_idom"
  assumes I: "finite I" "i \<in> I" "1 < f i" "\<And>i. i \<in> I \<Longrightarrow> 1 \<le> f i"
  shows "1 < prod f I"
proof -
  have "1 < f i * prod f (I - {i})"
    using assms
    by (meson DiffD1 leI less_1_mult less_le_trans mult_le_cancel_left1 prod_ge_1)
  also have "\<dots> = prod f I"
    using assms by (simp add: prod.remove)
  finally show ?thesis .
qed

lemma (in linordered_field) abs_prod: "\<bar>prod f A\<bar> = (\<Prod>x\<in>A. \<bar>f x\<bar>)"
  by (induct A rule: infinite_finite_induct) (simp_all add: abs_mult)

lemma prod_eq_1_iff [simp]: "finite A \<Longrightarrow> prod f A = 1 \<longleftrightarrow> (\<forall>a\<in>A. f a = 1)"
  for f :: "'a \<Rightarrow> nat"
  by (induct A rule: finite_induct) simp_all

lemma prod_pos_nat_iff [simp]: "finite A \<Longrightarrow> prod f A > 0 \<longleftrightarrow> (\<forall>a\<in>A. f a > 0)"
  for f :: "'a \<Rightarrow> nat"
  using prod_zero_iff by (simp del: neq0_conv add: zero_less_iff_neq_zero)

lemma prod_constant [simp]: "(\<Prod>x\<in> A. y) = y ^ card A"
  for y :: "'a::comm_monoid_mult"
  by (induct A rule: infinite_finite_induct) simp_all

lemma prod_power_distrib: "prod f A ^ n = prod (\<lambda>x. (f x) ^ n) A"
  for f :: "'a \<Rightarrow> 'b::comm_semiring_1"
  by (induct A rule: infinite_finite_induct) (auto simp add: power_mult_distrib)

lemma power_sum: "c ^ (\<Sum>a\<in>A. f a) = (\<Prod>a\<in>A. c ^ f a)"
  by (induct A rule: infinite_finite_induct) (simp_all add: power_add)

lemma prod_gen_delta:
  fixes b :: "'b \<Rightarrow> 'a::comm_monoid_mult"
  assumes fin: "finite S"
  shows "prod (\<lambda>k. if k = a then b k else c) S =
    (if a \<in> S then b a * c ^ (card S - 1) else c ^ card S)"
proof -
  let ?f = "(\<lambda>k. if k=a then b k else c)"
  show ?thesis
  proof (cases "a \<in> S")
    case False
    then have "\<forall> k\<in> S. ?f k = c" by simp
    with False show ?thesis by (simp add: prod_constant)
  next
    case True
    let ?A = "S - {a}"
    let ?B = "{a}"
    from True have eq: "S = ?A \<union> ?B" by blast
    have disjoint: "?A \<inter> ?B = {}" by simp
    from fin have fin': "finite ?A" "finite ?B" by auto
    have f_A0: "prod ?f ?A = prod (\<lambda>i. c) ?A"
      by (rule prod.cong) auto
    from fin True have card_A: "card ?A = card S - 1" by auto
    have f_A1: "prod ?f ?A = c ^ card ?A"
      unfolding f_A0 by (rule prod_constant)
    have "prod ?f ?A * prod ?f ?B = prod ?f S"
      using prod.union_disjoint[OF fin' disjoint, of ?f, unfolded eq[symmetric]]
      by simp
    with True card_A show ?thesis
      by (simp add: f_A1 field_simps cong add: prod.cong cong del: if_weak_cong)
  qed
qed

lemma sum_image_le:
  fixes g :: "'a \<Rightarrow> 'b::ordered_comm_monoid_add"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> 0 \<le> g(f i)"
    shows "sum g (f ` I) \<le> sum (g \<circ> f) I"
  using assms
proof induction
  case empty
  then show ?case by auto
next
  case (insert x F)
  from insertI1 have "0 \<le> g (f x)" by (rule insert)
  hence 1: "sum g (f ` F) \<le> g (f x) + sum g (f ` F)" using add_increasing by blast
  have 2: "sum g (f ` F) \<le> sum (g \<circ> f) F" using insert by blast
  have "sum g (f ` insert x F) = sum g (insert (f x) (f ` F))" by simp
  also have "\<dots> \<le> g (f x) + sum g (f ` F)" by (simp add: 1 insert sum.insert_if)
  also from 2 have "\<dots> \<le> g (f x) + sum (g \<circ> f) F" by (rule add_left_mono)
  also from insert(1, 2) have "\<dots> = sum (g \<circ> f) (insert x F)" by (simp add: sum.insert_if)
  finally show ?case .
qed

end
