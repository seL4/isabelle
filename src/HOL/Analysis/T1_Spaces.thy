section\<open>T1 and Hausdorff spaces\<close>

theory T1_Spaces
imports Product_Topology 
begin

section\<open>T1 spaces with equivalences to many naturally "nice" properties. \<close>

definition t1_space where
 "t1_space X \<equiv> \<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x\<noteq>y \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> y \<notin> U)"

lemma t1_space_expansive:
   "\<lbrakk>topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk> \<Longrightarrow> t1_space X \<Longrightarrow> t1_space Y"
  by (metis t1_space_def)

lemma t1_space_alt:
   "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x\<noteq>y \<longrightarrow> (\<exists>U. closedin X U \<and> x \<in> U \<and> y \<notin> U))"
 by (metis DiffE DiffI closedin_def openin_closedin_eq t1_space_def)

lemma t1_space_empty: "topspace X = {} \<Longrightarrow> t1_space X"
  by (simp add: t1_space_def)

lemma t1_space_derived_set_of_singleton:
  "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. X derived_set_of {x} = {})"
  apply (simp add: t1_space_def derived_set_of_def, safe)
   apply (metis openin_topspace)
  by force

lemma t1_space_derived_set_of_finite:
   "t1_space X \<longleftrightarrow> (\<forall>S. finite S \<longrightarrow> X derived_set_of S = {})"
proof (intro iffI allI impI)
  fix S :: "'a set"
  assume "finite S"
  then have fin: "finite ((\<lambda>x. {x}) ` (topspace X \<inter> S))"
    by blast
  assume "t1_space X"
  then have "X derived_set_of (\<Union>x \<in> topspace X \<inter> S. {x}) = {}"
    unfolding derived_set_of_Union [OF fin]
    by (auto simp: t1_space_derived_set_of_singleton)
  then have "X derived_set_of (topspace X \<inter> S) = {}"
    by simp
  then show "X derived_set_of S = {}"
    by simp
qed (auto simp: t1_space_derived_set_of_singleton)

lemma t1_space_closedin_singleton:
   "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. closedin X {x})"
  apply (rule iffI)
  apply (simp add: closedin_contains_derived_set t1_space_derived_set_of_singleton)
  using t1_space_alt by auto

lemma closedin_t1_singleton:
   "\<lbrakk>t1_space X; a \<in> topspace X\<rbrakk> \<Longrightarrow> closedin X {a}"
  by (simp add: t1_space_closedin_singleton)

lemma t1_space_closedin_finite:
   "t1_space X \<longleftrightarrow> (\<forall>S. finite S \<and> S \<subseteq> topspace X \<longrightarrow> closedin X S)"
  apply (rule iffI)
  apply (simp add: closedin_contains_derived_set t1_space_derived_set_of_finite)
  by (simp add: t1_space_closedin_singleton)

lemma closure_of_singleton:
   "t1_space X \<Longrightarrow> X closure_of {a} = (if a \<in> topspace X then {a} else {})"
  by (simp add: closure_of_eq t1_space_closedin_singleton closure_of_eq_empty_gen)

lemma separated_in_singleton:
  assumes "t1_space X"
  shows "separatedin X {a} S \<longleftrightarrow> a \<in> topspace X \<and> S \<subseteq> topspace X \<and> (a \<notin> X closure_of S)"
        "separatedin X S {a} \<longleftrightarrow> a \<in> topspace X \<and> S \<subseteq> topspace X \<and> (a \<notin> X closure_of S)"
  unfolding separatedin_def
  using assms closure_of closure_of_singleton by fastforce+

lemma t1_space_openin_delete:
   "t1_space X \<longleftrightarrow> (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> openin X (U - {x}))"
  apply (rule iffI)
  apply (meson closedin_t1_singleton in_mono openin_diff openin_subset)
  by (simp add: closedin_def t1_space_closedin_singleton)

lemma t1_space_openin_delete_alt:
   "t1_space X \<longleftrightarrow> (\<forall>U x. openin X U \<longrightarrow> openin X (U - {x}))"
  by (metis Diff_empty Diff_insert0 t1_space_openin_delete)


lemma t1_space_singleton_Inter_open:
      "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<Inter>{U. openin X U \<and> x \<in> U} = {x})"  (is "?P=?Q")
  and t1_space_Inter_open_supersets:
     "t1_space X \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<longrightarrow> \<Inter>{U. openin X U \<and> S \<subseteq> U} = S)" (is "?P=?R")
proof -
  have "?R \<Longrightarrow> ?Q"
    apply clarify
    apply (drule_tac x="{x}" in spec, simp)
    done
  moreover have "?Q \<Longrightarrow> ?P"
    apply (clarsimp simp add: t1_space_def)
    apply (drule_tac x=x in bspec)
     apply (simp_all add: set_eq_iff)
    by (metis (no_types, lifting))
  moreover have "?P \<Longrightarrow> ?R"
  proof (clarsimp simp add: t1_space_closedin_singleton, rule subset_antisym)
    fix S
    assume S: "\<forall>x\<in>topspace X. closedin X {x}" "S \<subseteq> topspace X"
    then show "\<Inter> {U. openin X U \<and> S \<subseteq> U} \<subseteq> S"
      apply clarsimp
      by (metis Diff_insert_absorb Set.set_insert closedin_def openin_topspace subset_insert)
  qed force
  ultimately show "?P=?Q" "?P=?R"
    by auto
qed

lemma t1_space_derived_set_of_infinite_openin:
   "t1_space X \<longleftrightarrow>
        (\<forall>S. X derived_set_of S =
             {x \<in> topspace X. \<forall>U. x \<in> U \<and> openin X U \<longrightarrow> infinite(S \<inter> U)})"
         (is "_ = ?rhs")
proof
  assume "t1_space X"
  show ?rhs
  proof safe
    fix S x U
    assume "x \<in> X derived_set_of S" "x \<in> U" "openin X U" "finite (S \<inter> U)"
    with \<open>t1_space X\<close> show "False"
      apply (simp add: t1_space_derived_set_of_finite)
      by (metis IntI empty_iff empty_subsetI inf_commute openin_Int_derived_set_of_subset subset_antisym)
  next
    fix S x
    have eq: "(\<exists>y. (y \<noteq> x) \<and> y \<in> S \<and> y \<in> T) \<longleftrightarrow> ~((S \<inter> T) \<subseteq> {x})" for x S T
      by blast
    assume "x \<in> topspace X" "\<forall>U. x \<in> U \<and> openin X U \<longrightarrow> infinite (S \<inter> U)"
    then show "x \<in> X derived_set_of S"
      apply (clarsimp simp add: derived_set_of_def eq)
      by (meson finite.emptyI finite.insertI finite_subset)
  qed (auto simp: in_derived_set_of)
qed (auto simp: t1_space_derived_set_of_singleton)

lemma finite_t1_space_imp_discrete_topology:
   "\<lbrakk>topspace X = U; finite U; t1_space X\<rbrakk> \<Longrightarrow> X = discrete_topology U"
  by (metis discrete_topology_unique_derived_set t1_space_derived_set_of_finite)

lemma t1_space_subtopology: "t1_space X \<Longrightarrow> t1_space(subtopology X U)"
  by (simp add: derived_set_of_subtopology t1_space_derived_set_of_finite)

lemma closedin_derived_set_of_gen:
   "t1_space X \<Longrightarrow> closedin X (X derived_set_of S)"
  apply (clarsimp simp add: in_derived_set_of closedin_contains_derived_set derived_set_of_subset_topspace)
  by (metis DiffD2 insert_Diff insert_iff t1_space_openin_delete)

lemma derived_set_of_derived_set_subset_gen:
   "t1_space X \<Longrightarrow> X derived_set_of (X derived_set_of S) \<subseteq> X derived_set_of S"
  by (meson closedin_contains_derived_set closedin_derived_set_of_gen)

lemma subtopology_eq_discrete_topology_gen_finite:
   "\<lbrakk>t1_space X; finite S\<rbrakk> \<Longrightarrow> subtopology X S = discrete_topology(topspace X \<inter> S)"
  by (simp add: subtopology_eq_discrete_topology_gen t1_space_derived_set_of_finite)

lemma subtopology_eq_discrete_topology_finite:
   "\<lbrakk>t1_space X; S \<subseteq> topspace X; finite S\<rbrakk>
        \<Longrightarrow> subtopology X S = discrete_topology S"
  by (simp add: subtopology_eq_discrete_topology_eq t1_space_derived_set_of_finite)

lemma t1_space_closed_map_image:
   "\<lbrakk>closed_map X Y f; f ` (topspace X) = topspace Y; t1_space X\<rbrakk> \<Longrightarrow> t1_space Y"
  by (metis closed_map_def finite_subset_image t1_space_closedin_finite)

lemma homeomorphic_t1_space: "X homeomorphic_space Y \<Longrightarrow> (t1_space X \<longleftrightarrow> t1_space Y)"
  apply (clarsimp simp add: homeomorphic_space_def)
  by (meson homeomorphic_eq_everything_map homeomorphic_maps_map t1_space_closed_map_image)

proposition t1_space_product_topology:
   "t1_space (product_topology X I)
\<longleftrightarrow> topspace(product_topology X I) = {} \<or> (\<forall>i \<in> I. t1_space (X i))"
proof (cases "topspace(product_topology X I) = {}")
  case True
  then show ?thesis
    using True t1_space_empty by blast
next
  case False
  then obtain f where f: "f \<in> (\<Pi>\<^sub>E i\<in>I. topspace(X i))"
    by fastforce
  have "t1_space (product_topology X I) \<longleftrightarrow> (\<forall>i\<in>I. t1_space (X i))"
  proof (intro iffI ballI)
    show "t1_space (X i)" if "t1_space (product_topology X I)" and "i \<in> I" for i
    proof -
      have clo: "\<And>h. h \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i)) \<Longrightarrow> closedin (product_topology X I) {h}"
        using that by (simp add: t1_space_closedin_singleton)
      show ?thesis
        unfolding t1_space_closedin_singleton
      proof clarify
        show "closedin (X i) {xi}" if "xi \<in> topspace (X i)" for xi
          using clo [of "\<lambda>j \<in> I. if i=j then xi else f j"] f that \<open>i \<in> I\<close>
          by (fastforce simp add: closedin_product_topology_singleton)
      qed
    qed
  next
  next
    show "t1_space (product_topology X I)" if "\<forall>i\<in>I. t1_space (X i)"
      using that
      by (simp add: t1_space_closedin_singleton Ball_def PiE_iff closedin_product_topology_singleton)
  qed
  then show ?thesis
    using False by blast
qed

lemma t1_space_prod_topology:
   "t1_space(prod_topology X Y) \<longleftrightarrow> topspace(prod_topology X Y) = {} \<or> t1_space X \<and> t1_space Y"
proof (cases "topspace (prod_topology X Y) = {}")
  case True then show ?thesis
  by (auto simp: t1_space_empty)
next
  case False
  have eq: "{(x,y)} = {x} \<times> {y}" for x y
    by simp
  have "t1_space (prod_topology X Y) \<longleftrightarrow> (t1_space X \<and> t1_space Y)"
    using False
    by (force simp: t1_space_closedin_singleton closedin_prod_Times_iff eq simp del: insert_Times_insert)
  with False show ?thesis
    by simp
qed

subsection\<open>Hausdorff Spaces\<close>

definition Hausdorff_space
  where
 "Hausdorff_space X \<equiv>
        \<forall>x y. x \<in> topspace X \<and> y \<in> topspace X \<and> (x \<noteq> y)
              \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V)"

lemma Hausdorff_space_expansive:
   "\<lbrakk>Hausdorff_space X; topspace X = topspace Y; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk> \<Longrightarrow> Hausdorff_space Y"
  by (metis Hausdorff_space_def)

lemma Hausdorff_space_topspace_empty:
   "topspace X = {} \<Longrightarrow> Hausdorff_space X"
  by (simp add: Hausdorff_space_def)

lemma Hausdorff_imp_t1_space:
   "Hausdorff_space X \<Longrightarrow> t1_space X"
  by (metis Hausdorff_space_def disjnt_iff t1_space_def)

lemma closedin_derived_set_of:
   "Hausdorff_space X \<Longrightarrow> closedin X (X derived_set_of S)"
  by (simp add: Hausdorff_imp_t1_space closedin_derived_set_of_gen)

lemma t1_or_Hausdorff_space:
   "t1_space X \<or> Hausdorff_space X \<longleftrightarrow> t1_space X"
  using Hausdorff_imp_t1_space by blast

lemma Hausdorff_space_sing_Inter_opens:
   "\<lbrakk>Hausdorff_space X; a \<in> topspace X\<rbrakk> \<Longrightarrow> \<Inter>{u. openin X u \<and> a \<in> u} = {a}"
  using Hausdorff_imp_t1_space t1_space_singleton_Inter_open by force

lemma Hausdorff_space_subtopology:
  assumes "Hausdorff_space X" shows "Hausdorff_space(subtopology X S)"
proof -
  have *: "disjnt U V \<Longrightarrow> disjnt (S \<inter> U) (S \<inter> V)" for U V
    by (simp add: disjnt_iff)
  from assms show ?thesis
    apply (simp add: Hausdorff_space_def openin_subtopology_alt)
    apply (fast intro: * elim!: all_forward)
    done
qed

lemma Hausdorff_space_compact_separation:
  assumes X: "Hausdorff_space X" and S: "compactin X S" and T: "compactin X T" and "disjnt S T"
  obtains U V where "openin X U" "openin X V" "S \<subseteq> U" "T \<subseteq> V" "disjnt U V"
proof (cases "S = {}")
  case True
  then show thesis
    by (metis \<open>compactin X T\<close> compactin_subset_topspace disjnt_empty1 empty_subsetI openin_empty openin_topspace that)
next
  case False
  have "\<forall>x \<in> S. \<exists>U V. openin X U \<and> openin X V \<and> x \<in> U \<and> T \<subseteq> V \<and> disjnt U V"
  proof
    fix a
    assume "a \<in> S"
    then have "a \<notin> T"
      by (meson assms(4) disjnt_iff)
    have a: "a \<in> topspace X"
      using S \<open>a \<in> S\<close> compactin_subset_topspace by blast
    show "\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> T \<subseteq> V \<and> disjnt U V"
    proof (cases "T = {}")
      case True
      then show ?thesis
        using a disjnt_empty2 openin_empty by blast
    next
      case False
      have "\<forall>x \<in> topspace X - {a}. \<exists>U V. openin X U \<and> openin X V \<and> x \<in> U \<and> a \<in> V \<and> disjnt U V"
        using X a by (simp add: Hausdorff_space_def)
      then obtain U V where UV: "\<forall>x \<in> topspace X - {a}. openin X (U x) \<and> openin X (V x) \<and> x \<in> U x \<and> a \<in> V x \<and> disjnt (U x) (V x)"
        by metis
      with \<open>a \<notin> T\<close> compactin_subset_topspace [OF T]
      have Topen: "\<forall>W \<in> U ` T. openin X W" and Tsub: "T \<subseteq> \<Union> (U ` T)"
        by (auto simp: )
      then obtain \<F> where \<F>: "finite \<F>" "\<F> \<subseteq> U ` T" and "T \<subseteq> \<Union>\<F>"
        using T unfolding compactin_def by meson
      then obtain F where F: "finite F" "F \<subseteq> T" "\<F> = U ` F" and SUF: "T \<subseteq> \<Union>(U ` F)" and "a \<notin> F"
        using finite_subset_image [OF \<F>] \<open>a \<notin> T\<close> by (metis subsetD)
      have U: "\<And>x. \<lbrakk>x \<in> topspace X; x \<noteq> a\<rbrakk> \<Longrightarrow> openin X (U x)"
        and V: "\<And>x. \<lbrakk>x \<in> topspace X; x \<noteq> a\<rbrakk> \<Longrightarrow> openin X (V x)"
        and disj: "\<And>x. \<lbrakk>x \<in> topspace X; x \<noteq> a\<rbrakk> \<Longrightarrow> disjnt (U x) (V x)"
        using UV by blast+
      show ?thesis
      proof (intro exI conjI)
        have "F \<noteq> {}"
          using False SUF by blast
        with \<open>a \<notin> F\<close> show "openin X (\<Inter>(V ` F))"
          using F compactin_subset_topspace [OF T] by (force intro: V)
        show "openin X (\<Union>(U ` F))"
          using F Topen Tsub by (force intro: U)
        show "disjnt (\<Inter>(V ` F)) (\<Union>(U ` F))"
          using disj
          apply (auto simp: disjnt_def)
          using \<open>F \<subseteq> T\<close> \<open>a \<notin> F\<close> compactin_subset_topspace [OF T] by blast
        show "a \<in> (\<Inter>(V ` F))"
          using \<open>F \<subseteq> T\<close> T UV \<open>a \<notin> T\<close> compactin_subset_topspace by blast
      qed (auto simp: SUF)
    qed
  qed
  then obtain U V where UV: "\<forall>x \<in> S. openin X (U x) \<and> openin X (V x) \<and> x \<in> U x \<and> T \<subseteq> V x \<and> disjnt (U x) (V x)"
    by metis
  then have "S \<subseteq> \<Union> (U ` S)"
    by auto
  moreover have "\<forall>W \<in> U ` S. openin X W"
    using UV by blast
  ultimately obtain I where I: "S \<subseteq> \<Union> (U ` I)" "I \<subseteq> S" "finite I"
    by (metis S compactin_def finite_subset_image)
  show thesis
  proof
    show "openin X (\<Union>(U ` I))"
      using \<open>I \<subseteq> S\<close> UV by blast
    show "openin X (\<Inter> (V ` I))"
      using False UV \<open>I \<subseteq> S\<close> \<open>S \<subseteq> \<Union> (U ` I)\<close> \<open>finite I\<close> by blast
    show "disjnt (\<Union>(U ` I)) (\<Inter> (V ` I))"
      by simp (meson UV \<open>I \<subseteq> S\<close> disjnt_subset2 in_mono le_INF_iff order_refl)
  qed (use UV I in auto)
qed


lemma Hausdorff_space_compact_sets:
  "Hausdorff_space X \<longleftrightarrow>
    (\<forall>S T. compactin X S \<and> compactin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson Hausdorff_space_compact_separation)
next
  assume R [rule_format]: ?rhs
  show ?lhs
  proof (clarsimp simp add: Hausdorff_space_def)
    fix x y
    assume "x \<in> topspace X" "y \<in> topspace X" "x \<noteq> y"
    then show "\<exists>U. openin X U \<and> (\<exists>V. openin X V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V)"
      using R [of "{x}" "{y}"] by auto
  qed
qed

lemma compactin_imp_closedin:
  assumes X: "Hausdorff_space X" and S: "compactin X S" shows "closedin X S"
proof -
  have "S \<subseteq> topspace X"
    by (simp add: assms compactin_subset_topspace)
  moreover
  have "\<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> topspace X - S" if "x \<in> topspace X" "x \<notin> S" for x
    using Hausdorff_space_compact_separation [OF X _ S, of "{x}"] that
    apply (simp add: disjnt_def)
    by (metis Diff_mono Diff_triv openin_subset)
  ultimately show ?thesis
    using closedin_def openin_subopen by force
qed

lemma closedin_Hausdorff_singleton:
   "\<lbrakk>Hausdorff_space X; x \<in> topspace X\<rbrakk> \<Longrightarrow> closedin X {x}"
  by (simp add: Hausdorff_imp_t1_space closedin_t1_singleton)

lemma closedin_Hausdorff_sing_eq:
   "Hausdorff_space X \<Longrightarrow> closedin X {x} \<longleftrightarrow> x \<in> topspace X"
  by (meson closedin_Hausdorff_singleton closedin_subset insert_subset)

lemma Hausdorff_space_discrete_topology [simp]:
   "Hausdorff_space (discrete_topology U)"
  unfolding Hausdorff_space_def
  apply safe
  by (metis discrete_topology_unique_alt disjnt_empty2 disjnt_insert2 insert_iff mk_disjoint_insert topspace_discrete_topology)

lemma compactin_Int:
   "\<lbrakk>Hausdorff_space X; compactin X S; compactin X T\<rbrakk> \<Longrightarrow> compactin X (S \<inter> T)"
  by (simp add: closed_Int_compactin compactin_imp_closedin)

lemma finite_topspace_imp_discrete_topology:
   "\<lbrakk>topspace X = U; finite U; Hausdorff_space X\<rbrakk> \<Longrightarrow> X = discrete_topology U"
  using Hausdorff_imp_t1_space finite_t1_space_imp_discrete_topology by blast

lemma derived_set_of_finite:
   "\<lbrakk>Hausdorff_space X; finite S\<rbrakk> \<Longrightarrow> X derived_set_of S = {}"
  using Hausdorff_imp_t1_space t1_space_derived_set_of_finite by auto

lemma derived_set_of_singleton:
   "Hausdorff_space X \<Longrightarrow> X derived_set_of {x} = {}"
  by (simp add: derived_set_of_finite)

lemma closedin_Hausdorff_finite:
   "\<lbrakk>Hausdorff_space X; S \<subseteq> topspace X; finite S\<rbrakk> \<Longrightarrow> closedin X S"
  by (simp add: compactin_imp_closedin finite_imp_compactin_eq)

lemma open_in_Hausdorff_delete:
   "\<lbrakk>Hausdorff_space X; openin X S\<rbrakk> \<Longrightarrow> openin X (S - {x})"
  using Hausdorff_imp_t1_space t1_space_openin_delete_alt by auto

lemma closedin_Hausdorff_finite_eq:
   "\<lbrakk>Hausdorff_space X; finite S\<rbrakk> \<Longrightarrow> closedin X S \<longleftrightarrow> S \<subseteq> topspace X"
  by (meson closedin_Hausdorff_finite closedin_def)

lemma derived_set_of_infinite_openin:
   "Hausdorff_space X
        \<Longrightarrow> X derived_set_of S =
            {x \<in> topspace X. \<forall>U. x \<in> U \<and> openin X U \<longrightarrow> infinite(S \<inter> U)}"
  using Hausdorff_imp_t1_space t1_space_derived_set_of_infinite_openin by fastforce

lemma Hausdorff_space_discrete_compactin:
   "Hausdorff_space X
        \<Longrightarrow> S \<inter> X derived_set_of S = {} \<and> compactin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> finite S"
  using derived_set_of_finite discrete_compactin_eq_finite by fastforce

lemma Hausdorff_space_finite_topspace:
   "Hausdorff_space X \<Longrightarrow> X derived_set_of (topspace X) = {} \<and> compact_space X \<longleftrightarrow> finite(topspace X)"
  using derived_set_of_finite discrete_compact_space_eq_finite by auto

lemma derived_set_of_derived_set_subset:
   "Hausdorff_space X \<Longrightarrow> X derived_set_of (X derived_set_of S) \<subseteq> X derived_set_of S"
  by (simp add: Hausdorff_imp_t1_space derived_set_of_derived_set_subset_gen)


lemma Hausdorff_space_injective_preimage:
  assumes "Hausdorff_space Y" and cmf: "continuous_map X Y f" and "inj_on f (topspace X)"
  shows "Hausdorff_space X"
  unfolding Hausdorff_space_def
proof clarify
  fix x y
  assume x: "x \<in> topspace X" and y: "y \<in> topspace X" and "x \<noteq> y"
  then obtain U V where "openin Y U" "openin Y V" "f x \<in> U" "f y \<in> V" "disjnt U V"
    using assms unfolding Hausdorff_space_def continuous_map_def by (meson inj_onD)
  show "\<exists>U V. openin X U \<and> openin X V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
  proof (intro exI conjI)
    show "openin X {x \<in> topspace X. f x \<in> U}"
      using \<open>openin Y U\<close> cmf continuous_map by fastforce
    show "openin X {x \<in> topspace X. f x \<in> V}"
      using \<open>openin Y V\<close> cmf openin_continuous_map_preimage by blast
    show "disjnt {x \<in> topspace X. f x \<in> U} {x \<in> topspace X. f x \<in> V}"
      using \<open>disjnt U V\<close> by (auto simp add: disjnt_def)
  qed (use x \<open>f x \<in> U\<close> y \<open>f y \<in> V\<close> in auto)
qed

lemma homeomorphic_Hausdorff_space:
   "X homeomorphic_space Y \<Longrightarrow> Hausdorff_space X \<longleftrightarrow> Hausdorff_space Y"
  unfolding homeomorphic_space_def homeomorphic_maps_map
  by (auto simp: homeomorphic_eq_everything_map Hausdorff_space_injective_preimage)

lemma Hausdorff_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; Hausdorff_space X\<rbrakk> \<Longrightarrow> Hausdorff_space Y"
  unfolding retraction_map_def
  using Hausdorff_space_subtopology homeomorphic_Hausdorff_space retraction_maps_section_image2 by blast

lemma compact_Hausdorff_space_optimal:
  assumes eq: "topspace Y = topspace X" and XY: "\<And>U. openin X U \<Longrightarrow> openin Y U"
      and "Hausdorff_space X" "compact_space Y"
    shows "Y = X"
proof -
  have "\<And>U. closedin X U \<Longrightarrow> closedin Y U"
    using XY using topology_finer_closedin [OF eq]
    by metis
  have "openin Y S = openin X S" for S
    by (metis XY assms(3) assms(4) closedin_compact_space compactin_contractive compactin_imp_closedin eq openin_closedin_eq)
  then show ?thesis
    by (simp add: topology_eq)
qed

lemma continuous_map_imp_closed_graph:
  assumes f: "continuous_map X Y f" and Y: "Hausdorff_space Y"
  shows "closedin (prod_topology X Y) ((\<lambda>x. (x,f x)) ` topspace X)"
  unfolding closedin_def
proof
  show "(\<lambda>x. (x, f x)) ` topspace X \<subseteq> topspace (prod_topology X Y)"
    using continuous_map_def f by fastforce
  show "openin (prod_topology X Y) (topspace (prod_topology X Y) - (\<lambda>x. (x, f x)) ` topspace X)"
    unfolding openin_prod_topology_alt
  proof (intro allI impI)
    show "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> topspace (prod_topology X Y) - (\<lambda>x. (x, f x)) ` topspace X"
      if "(x,y) \<in> topspace (prod_topology X Y) - (\<lambda>x. (x, f x)) ` topspace X"
      for x y
    proof -
      have "x \<in> topspace X" "y \<in> topspace Y" "y \<noteq> f x"
        using that by auto
      moreover have "f x \<in> topspace Y"
        by (meson \<open>x \<in> topspace X\<close> continuous_map_def f)
      ultimately obtain U V where UV: "openin Y U" "openin Y V" "f x \<in> U" "y \<in> V" "disjnt U V"
        using Y Hausdorff_space_def by metis
      show ?thesis
      proof (intro exI conjI)
        show "openin X {x \<in> topspace X. f x \<in> U}"
          using \<open>openin Y U\<close> f openin_continuous_map_preimage by blast
        show "{x \<in> topspace X. f x \<in> U} \<times> V \<subseteq> topspace (prod_topology X Y) - (\<lambda>x. (x, f x)) ` topspace X"
          using UV by (auto simp: disjnt_iff dest: openin_subset)
      qed (use UV \<open>x \<in> topspace X\<close> in auto)
    qed
  qed
qed

lemma continuous_imp_closed_map:
   "\<lbrakk>continuous_map X Y f; compact_space X; Hausdorff_space Y\<rbrakk> \<Longrightarrow> closed_map X Y f"
  by (meson closed_map_def closedin_compact_space compactin_imp_closedin image_compactin)

lemma continuous_imp_quotient_map:
   "\<lbrakk>continuous_map X Y f; compact_space X; Hausdorff_space Y; f ` (topspace X) = topspace Y\<rbrakk>
        \<Longrightarrow> quotient_map X Y f"
  by (simp add: continuous_imp_closed_map continuous_closed_imp_quotient_map)

lemma continuous_imp_homeomorphic_map:
   "\<lbrakk>continuous_map X Y f; compact_space X; Hausdorff_space Y; 
     f ` (topspace X) = topspace Y; inj_on f (topspace X)\<rbrakk>
        \<Longrightarrow> homeomorphic_map X Y f"
  by (simp add: continuous_imp_closed_map bijective_closed_imp_homeomorphic_map)

lemma continuous_imp_embedding_map:
   "\<lbrakk>continuous_map X Y f; compact_space X; Hausdorff_space Y; inj_on f (topspace X)\<rbrakk>
        \<Longrightarrow> embedding_map X Y f"
  by (simp add: continuous_imp_closed_map injective_closed_imp_embedding_map)

lemma continuous_inverse_map:
  assumes "compact_space X" "Hausdorff_space Y"
    and cmf: "continuous_map X Y f" and gf: "\<And>x. x \<in> topspace X \<Longrightarrow> g(f x) = x"
    and Sf:  "S \<subseteq> f ` (topspace X)"
  shows "continuous_map (subtopology Y S) X g"
proof (rule continuous_map_from_subtopology_mono [OF _ \<open>S \<subseteq> f ` (topspace X)\<close>])
  show "continuous_map (subtopology Y (f ` (topspace X))) X g"
    unfolding continuous_map_closedin
  proof (intro conjI ballI allI impI)
    fix x
    assume "x \<in> topspace (subtopology Y (f ` topspace X))"
    then show "g x \<in> topspace X"
      by (auto simp: gf)
  next
    fix C
    assume C: "closedin X C"
    show "closedin (subtopology Y (f ` topspace X))
           {x \<in> topspace (subtopology Y (f ` topspace X)). g x \<in> C}"
    proof (rule compactin_imp_closedin)
      show "Hausdorff_space (subtopology Y (f ` topspace X))"
        using Hausdorff_space_subtopology [OF \<open>Hausdorff_space Y\<close>] by blast
      have "compactin Y (f ` C)"
        using C cmf image_compactin closedin_compact_space [OF \<open>compact_space X\<close>] by blast
      moreover have "{x \<in> topspace Y. x \<in> f ` topspace X \<and> g x \<in> C} = f ` C"
        using closedin_subset [OF C] cmf by (auto simp: gf continuous_map_def)
      ultimately have "compactin Y {x \<in> topspace Y. x \<in> f ` topspace X \<and> g x \<in> C}"
        by simp
      then show "compactin (subtopology Y (f ` topspace X))
              {x \<in> topspace (subtopology Y (f ` topspace X)). g x \<in> C}"
        by (auto simp add: compactin_subtopology)
    qed
  qed
qed

lemma closed_map_paired_continuous_map_right:
   "\<lbrakk>continuous_map X Y f; Hausdorff_space Y\<rbrakk> \<Longrightarrow> closed_map X (prod_topology X Y) (\<lambda>x. (x,f x))"
  by (simp add: continuous_map_imp_closed_graph embedding_map_graph embedding_imp_closed_map)

lemma closed_map_paired_continuous_map_left:
  assumes f: "continuous_map X Y f" and Y: "Hausdorff_space Y"
  shows "closed_map X (prod_topology Y X) (\<lambda>x. (f x,x))"
proof -
  have eq: "(\<lambda>x. (f x,x)) = (\<lambda>(a,b). (b,a)) \<circ> (\<lambda>x. (x,f x))"
    by auto
  show ?thesis
    unfolding eq
  proof (rule closed_map_compose)
    show "closed_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
      using Y closed_map_paired_continuous_map_right f by blast
    show "closed_map (prod_topology X Y) (prod_topology Y X) (\<lambda>(a, b). (b, a))"
      by (metis homeomorphic_map_swap homeomorphic_imp_closed_map)
  qed
qed

lemma proper_map_paired_continuous_map_right:
   "\<lbrakk>continuous_map X Y f; Hausdorff_space Y\<rbrakk>
        \<Longrightarrow> proper_map X (prod_topology X Y) (\<lambda>x. (x,f x))"
  using closed_injective_imp_proper_map closed_map_paired_continuous_map_right
  by (metis (mono_tags, lifting) Pair_inject inj_onI)

lemma proper_map_paired_continuous_map_left:
   "\<lbrakk>continuous_map X Y f; Hausdorff_space Y\<rbrakk>
        \<Longrightarrow> proper_map X (prod_topology Y X) (\<lambda>x. (f x,x))"
  using closed_injective_imp_proper_map closed_map_paired_continuous_map_left
  by (metis (mono_tags, lifting) Pair_inject inj_onI)

lemma Hausdorff_space_euclidean [simp]: "Hausdorff_space (euclidean :: 'a::metric_space topology)"
proof -
  have "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
    if "x \<noteq> y"
    for x y :: 'a
  proof (intro exI conjI)
    let ?r = "dist x y / 2"
    have [simp]: "?r > 0"
      by (simp add: that)
    show "open (ball x ?r)" "open (ball y ?r)" "x \<in> (ball x ?r)" "y \<in> (ball y ?r)"
      by (auto simp add: that)
    show "disjnt (ball x ?r) (ball y ?r)"
      unfolding disjnt_def by (simp add: disjoint_ballI)
  qed
  then show ?thesis
    by (simp add: Hausdorff_space_def)
qed

lemma Hausdorff_space_prod_topology:
  "Hausdorff_space(prod_topology X Y) \<longleftrightarrow> topspace(prod_topology X Y) = {} \<or> Hausdorff_space X \<and> Hausdorff_space Y"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (rule topological_property_of_prod_component) (auto simp: Hausdorff_space_subtopology homeomorphic_Hausdorff_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "(topspace X \<times> topspace Y) = {}")
    case False
    with R have ne: "topspace X \<noteq> {}" "topspace Y \<noteq> {}" and X: "Hausdorff_space X" and Y: "Hausdorff_space Y"
      by auto
    show ?thesis
      unfolding Hausdorff_space_def
    proof clarify
      fix x y x' y'
      assume xy: "(x, y) \<in> topspace (prod_topology X Y)"
        and xy': "(x',y') \<in> topspace (prod_topology X Y)"
        and *: "\<nexists>U V. openin (prod_topology X Y) U \<and> openin (prod_topology X Y) V
               \<and> (x, y) \<in> U \<and> (x', y') \<in> V \<and> disjnt U V"
      have False if "x \<noteq> x' \<or> y \<noteq> y'"
        using that
      proof
        assume "x \<noteq> x'"
        then obtain U V where "openin X U" "openin X V" "x \<in> U" "x' \<in> V" "disjnt U V"
          by (metis Hausdorff_space_def X mem_Sigma_iff topspace_prod_topology xy xy')
        let ?U = "U \<times> topspace Y"
        let ?V = "V \<times> topspace Y"
        have "openin (prod_topology X Y) ?U" "openin (prod_topology X Y) ?V"
          by (simp_all add: openin_prod_Times_iff \<open>openin X U\<close> \<open>openin X V\<close>)
        moreover have "disjnt ?U ?V"
          by (simp add: \<open>disjnt U V\<close>)
        ultimately show False
          using * \<open>x \<in> U\<close> \<open>x' \<in> V\<close> xy xy' by (metis SigmaD2 SigmaI topspace_prod_topology)
      next
        assume "y \<noteq> y'"
        then obtain U V where "openin Y U" "openin Y V" "y \<in> U" "y' \<in> V" "disjnt U V"
          by (metis Hausdorff_space_def Y mem_Sigma_iff topspace_prod_topology xy xy')
        let ?U = "topspace X \<times> U"
        let ?V = "topspace X \<times> V"
        have "openin (prod_topology X Y) ?U" "openin (prod_topology X Y) ?V"
          by (simp_all add: openin_prod_Times_iff \<open>openin Y U\<close> \<open>openin Y V\<close>)
        moreover have "disjnt ?U ?V"
          by (simp add: \<open>disjnt U V\<close>)
        ultimately show False
          using "*" \<open>y \<in> U\<close> \<open>y' \<in> V\<close> xy xy' by (metis SigmaD1 SigmaI topspace_prod_topology)
      qed
      then show "x = x' \<and> y = y'"
        by blast
    qed
  qed (simp add: Hausdorff_space_topspace_empty)
qed


lemma Hausdorff_space_product_topology:
   "Hausdorff_space (product_topology X I) \<longleftrightarrow> (\<Pi>\<^sub>E i\<in>I. topspace(X i)) = {} \<or> (\<forall>i \<in> I. Hausdorff_space (X i))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (rule topological_property_of_product_component)
     apply (blast dest: Hausdorff_space_subtopology homeomorphic_Hausdorff_space)+
    done
next
  assume R: ?rhs
  show ?lhs
  proof (cases "(\<Pi>\<^sub>E i\<in>I. topspace(X i)) = {}")
    case True
    then show ?thesis
      by (simp add: Hausdorff_space_topspace_empty)
  next
    case False
    have "\<exists>U V. openin (product_topology X I) U \<and> openin (product_topology X I) V \<and> f \<in> U \<and> g \<in> V \<and> disjnt U V"
      if f: "f \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))" and g: "g \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))" and "f \<noteq> g"
      for f g :: "'a \<Rightarrow> 'b"
    proof -
      obtain m where "f m \<noteq> g m"
        using \<open>f \<noteq> g\<close> by blast
      then have "m \<in> I"
        using f g by fastforce
      then have "Hausdorff_space (X m)" 
        using False that R by blast
      then obtain U V where U: "openin (X m) U" and V: "openin (X m) V" and "f m \<in> U" "g m \<in> V" "disjnt U V"
        by (metis Hausdorff_space_def PiE_mem \<open>f m \<noteq> g m\<close> \<open>m \<in> I\<close> f g)
      show ?thesis
      proof (intro exI conjI)
        let ?U = "(\<Pi>\<^sub>E i\<in>I. topspace(X i)) \<inter> {x. x m \<in> U}"
        let ?V = "(\<Pi>\<^sub>E i\<in>I. topspace(X i)) \<inter> {x. x m \<in> V}"
        show "openin (product_topology X I) ?U" "openin (product_topology X I) ?V"
          using \<open>m \<in> I\<close> U V
          by (force simp add: openin_product_topology intro: arbitrary_union_of_inc relative_to_inc finite_intersection_of_inc)+
        show "f \<in> ?U"
          using \<open>f m \<in> U\<close> f by blast
        show "g \<in> ?V"
          using \<open>g m \<in> V\<close> g by blast
        show "disjnt ?U ?V"
          using \<open>disjnt U V\<close> by (auto simp: PiE_def Pi_def disjnt_def)
        qed
    qed
    then show ?thesis
      by (simp add: Hausdorff_space_def)   
  qed
qed

end
