section \<open>Transfer from $\mathbb{R}^n$ to euclidean spaces\<close>

theory Euclidean_Space_Transfer
  imports Determinant_Linear_Function Lebesgue_Measure Path_Connected

begin

subsection \<open>General missing parametricity rules\<close>

context
  includes lifting_syntax
begin

lemma rel_set_flip: "rel_set (\<lambda>x y. r y x) = (\<lambda>A B. rel_set r B A)"
  by (simp add: rel_set_def conj_commute)

lemma rel_fun_flip:
  "rel_fun (\<lambda>y x. r1 x y) r2 = (\<lambda>y x. rel_fun r1 (\<lambda>y x. r2 x y) x y)"
by (auto simp: rel_fun_def fun_eq_iff)

lemma left_total_flip: "left_total (\<lambda>y x. r x y) \<longleftrightarrow> right_total r"
  unfolding left_total_def right_total_def by auto

lemma right_total_flip: "right_total (\<lambda>y x. r x y) \<longleftrightarrow> left_total r"
  unfolding left_total_def right_total_def by auto

lemma bi_total_flip: "bi_total (\<lambda>y x. r x y) \<longleftrightarrow> bi_total r"
proof -
  have "bi_total (\<lambda>y x. r x y) \<longleftrightarrow> left_total (\<lambda>y x. r x y) \<and> right_total (\<lambda>y x. r x y)"
    by (simp add: bi_total_alt_def)
  also have "\<dots> \<longleftrightarrow> right_total r \<and> left_total r"
    by (subst left_total_flip, subst (2) right_total_flip) (rule refl)
  also have "\<dots> \<longleftrightarrow> bi_total r"
    by (simp add: bi_total_alt_def conj_commute)
  finally show ?thesis .
qed

lemma rel_filter_flip_aux:
  assumes "rel_filter r F F'"
  shows   "rel_filter (\<lambda>y x. r x y) F' F"
proof -
  from assms obtain Z where Z: "\<forall>\<^sub>F (x, y) in Z. r x y"
    "F = map_filter_on {(x, y). r x y} fst Z" "F' = map_filter_on {(x, y). r x y} snd Z"
    by (auto simp: rel_filter.simps)
  define Z' where "Z' = filtermap (\<lambda>(x,y). (y,x)) Z"
  have "\<forall>\<^sub>F (x, y) in Z'. r y x"
    using Z(1) by (simp add: Z'_def eventually_filtermap case_prod_unfold)
  moreover have  "F = map_filter_on {(x, y). r y x} snd Z'" "F' = map_filter_on {(x, y). r y x} fst Z'"
    unfolding filter_eq_iff using Z
    by (auto simp: Z'_def eventually_filtermap case_prod_unfold
             eventually_conj_iff eventually_map_filter_on)
  ultimately show ?thesis unfolding rel_filter.simps
    by blast
qed 

lemma rel_filter_flip:
  "rel_filter (\<lambda>y x. r x y)  = (\<lambda>y x. rel_filter r x y)"
proof (intro ext)
  fix F F'
  show "rel_filter (\<lambda>y x. r x y) F F'  = rel_filter r F' F"
    using rel_filter_flip_aux[of r F' F] rel_filter_flip_aux[of "\<lambda>x y. r y x" F F']
    by auto
qed

lemma transfer_Sigma [transfer_rule]:
  "(rel_set r1 ===> (r1 ===> rel_set r2) ===> rel_set (rel_prod r1 r2)) Sigma Sigma"
  unfolding Sigma_def by transfer_prover

lemmas [transfer_rule] = inj_on_transfer

lemma transfer_disjoint_family_on [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r2" "bi_unique r1"
  shows "((r1 ===> rel_set r2) ===> rel_set r1 ===> (=)) disjoint_family_on disjoint_family_on"
  unfolding disjoint_family_on_def
  by transfer_prover

lemmas [transfer_rule] = Lifting_Set.filter_transfer

end


subsection \<open>Parametricity of measures\<close>

context
  includes lifting_syntax
begin

definition rel_measure_bij :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a measure \<Rightarrow> 'b measure \<Rightarrow> bool)" where
  "rel_measure_bij r M1 M2 \<longleftrightarrow>
     rel_set r (space M1) (space M2) \<and>
     rel_set (rel_set r) (sets M1) (sets M2) \<and>
     (rel_set r ===> (=)) (emeasure M1) (emeasure M2)"

lemma rel_measure_bij_flip:
  "rel_measure_bij (\<lambda>y x. r x y) = (\<lambda>y x. rel_measure_bij r x y)"
  by (auto simp: rel_measure_bij_def fun_eq_iff rel_set_flip[of r] rel_fun_flip[of "rel_set r"]
                 eq_commute rel_set_flip[of "rel_set r"])

lemma space_conv_UN_sets: "space M = (\<Union>X\<in>sets M. X)"
  using sets.sets_into_space by auto

lemma rel_measure_bijI:
  assumes [transfer_rule]: "rel_set (rel_set r) (sets M) (sets M')"
  assumes "(rel_fun (rel_set r) (=)) (emeasure M) (emeasure M')"
  shows   "rel_measure_bij r M M'"
proof -
  have "rel_set r (space M) (space M')"
    unfolding space_conv_UN_sets by transfer_prover
  with assms show ?thesis
    by (simp add: rel_measure_bij_def)
qed

(* TODO Move *)
lemma emeasure_completion_Un_set_null_set:
  assumes "X \<in> sets M" "Y \<in> null_sets M" "Z \<subseteq> Y"
  shows   "emeasure (completion M) (X \<union> Z) = emeasure M X"
proof -
  have "emeasure (completion M) (X \<union> Z) = emeasure M X + emeasure (completion M) (Z - X)"
    using assms null_sets_completion[of Y M Z] by (subst emeasure_Un) auto
  moreover have "Z - X \<in> null_sets (completion M)"
    using assms by (subst null_sets_completion_iff2) auto
  hence "emeasure (completion M) (Z - X) = 0"
    by auto
  ultimately show ?thesis by simp
qed

lemma sets_completion_eq:
  "sets (completion M) = ((\<lambda>(S,N). S \<union> N) ` (sets M \<times> (\<Union>N\<in>null_sets M. Pow N)))"
  unfolding sets_completion by auto

end


named_theorems transfer_measure_bij_rules

context
  includes lifting_syntax
begin

lemma transfer_sigma_sets_aux:
  assumes [transfer_rule]: "bi_unique r"
  assumes [transfer_rule]: "rel_set r \<Omega> \<Omega>'" "rel_set (rel_set r) \<Sigma> \<Sigma>'"
  assumes "X \<in> sigma_sets \<Omega> \<Sigma>"
  shows   "\<exists>X'\<in>sigma_sets \<Omega>' \<Sigma>'. rel_set r X X'"
  using assms(4)
proof induction
  case (Basic X)
  then obtain X' where "X' \<in> \<Sigma>'" "rel_set r X X'"
    using assms by (auto simp: rel_set_def)
  thus ?case
    by (intro bexI[of _ X'] sigma_sets.Basic)
next
  case Empty
  thus ?case
    by (intro bexI[of _ "{}"] sigma_sets.Empty) (auto simp: rel_set_def)
next
  case (Compl X)
  then obtain X' where X': "X' \<in> sigma_sets \<Omega>' \<Sigma>'" and [transfer_rule]: "rel_set r X X'"
    by auto
  from X' have "\<Omega>' - X' \<in> sigma_sets \<Omega>' \<Sigma>'"
    by (intro sigma_sets.Compl)
  moreover have "rel_set r (\<Omega> - X) (\<Omega>' - X')"
    by transfer_prover
  ultimately show ?case
    by blast
next
  case (Union F)
  hence "\<exists>F'. \<forall>i. F' i \<in> sigma_sets \<Omega>' \<Sigma>' \<and> rel_set r (F i) (F' i)"
    by metis
  then obtain F'
    where 1: "F' i \<in> sigma_sets \<Omega>' \<Sigma>'" and 2: "rel_set r (F i) (F' i)" for i
    by blast
  have [transfer_rule]: "((=) ===> rel_set r) F F'"
    using 2 by (auto simp: rel_fun_def)
  from 1 have "(\<Union>i. F' i) \<in> sigma_sets \<Omega>' \<Sigma>'"
    by (intro sigma_sets.Union)
  moreover have "rel_set r (\<Union>i. F i) (\<Union>i. F' i)"
    by transfer_prover
  ultimately show ?case
    by blast
qed

lemma transfer_sigma_sets [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_set r ===> rel_set (rel_set r) ===> rel_set (rel_set r)) sigma_sets sigma_sets"
  unfolding rel_fun_def
proof (safe, goal_cases)
  case (1 \<Omega> \<Omega>' \<Sigma> \<Sigma>')
  let ?r = "\<lambda>x y. r y x"
  note [simp] = rel_set_flip[of r] rel_set_flip[of "\<lambda>A B. rel_set r B A"]
  have 2: "bi_unique (\<lambda>x y. r y x)"
    using assms by (simp add: bi_unique_def)
  have 3: "rel_set ?r \<Omega>' \<Omega>" "rel_set (rel_set ?r) \<Sigma>' \<Sigma>"
    using 1 by simp_all
    
  from transfer_sigma_sets_aux[OF assms 1(1,2)] transfer_sigma_sets_aux[OF 2 3]
  show ?case by (subst rel_set_def) auto
qed

lemma transfer_countably_additive_aux:
  assumes [transfer_rule]: "bi_unique r"
  assumes M_M' [transfer_rule]: "rel_set (rel_set r) M M'"
  assumes f_f' [transfer_rule]: "(rel_set r ===> (=)) f f'"
  assumes "(\<forall>A. range A \<subseteq> M \<longrightarrow> disjoint_family A \<longrightarrow> \<Union> (range A) \<in> M \<longrightarrow> (\<Sum>i. f (A i)) = f (\<Union> (range A)))"
  assumes "range A' \<subseteq> M'" "disjoint_family A'" "\<Union> (range A') \<in> M'"
  shows   "(\<Sum>i. f' (A' i)) = f' (\<Union> (range A'))"
proof -
  have "\<exists>A\<in>M. rel_set r A (A' i)" for A i :: nat
  proof -
    have "A' i \<in> M'"
      using assms by auto
    with M_M' obtain A where "A \<in> M" "rel_set r A (A' i)"
      by (auto simp: rel_set_def)
    thus ?thesis by blast
  qed
  then obtain A where A: "rel_set r (A i) (A' i)" for i
    by metis
  hence [transfer_rule]: "((=) ===> rel_set r) A A'"
    by auto
  have "range A \<subseteq> M \<longleftrightarrow> range A' \<subseteq> M'" "disjoint_family A \<longleftrightarrow> disjoint_family A'"
       "(\<Union> (range A) \<in> M) \<longleftrightarrow> (\<Union> (range A') \<in> M')"
    by transfer_prover+
  with assms have "(\<Sum>i. f (A i)) = f (\<Union> (range A))"
    by auto
  also have "?this \<longleftrightarrow> (\<Sum>i. f' (A' i)) = f' (\<Union> (range A'))"
    by transfer_prover
  finally show ?thesis .
qed

lemma transfer_countably_additive [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_set (rel_set r) ===> (rel_set r ===> (=)) ===> (=)) countably_additive countably_additive"
proof (intro rel_funI conj_cong, goal_cases)
  case (1 M M' f f')
  have "bi_unique (\<lambda>x y. r y x)"
    using assms by (auto simp: bi_unique_def)
  note uniq = this assms
  show ?case
    using transfer_countably_additive_aux[OF uniq(1), of M' M f' f]
          transfer_countably_additive_aux[OF uniq(2), of M M' f f'] 1
    by (auto simp: rel_set_flip[of r] rel_set_flip[of "rel_set r"] rel_fun_flip[of "rel_set r"]
                   eq_commute countably_additive_def)
qed

lemma transfer_positive [transfer_rule]:
  "(rel_set (rel_set r) ===> (rel_set r ===> (=)) ===> (=)) positive positive"
  unfolding positive_def by transfer_prover

lemma transfer_algebra [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_set r ===> rel_set (rel_set r) ===> (=)) algebra algebra"
  unfolding algebra_iff_Un by transfer_prover

lemma transfer_sigma_algebra_aux:
  assumes [transfer_rule]: "bi_unique r" and M_M' [transfer_rule]: "rel_set (rel_set r) M M'"
  assumes "\<And>A. range A \<subseteq> M \<Longrightarrow> (\<Union>i::nat. A i) \<in> M"
  assumes "range A' \<subseteq> M'"
  shows   "(\<Union>i::nat. A' i) \<in> M'"
proof -
  have "\<exists>A\<in>M. rel_set r A (A' i)" for A i :: nat
  proof -
    have "A' i \<in> M'"
      using assms by auto
    with M_M' obtain A where "A \<in> M" "rel_set r A (A' i)"
      by (auto simp: rel_set_def)
    thus ?thesis by blast
  qed
  then obtain A where A: "rel_set r (A i) (A' i)" for i
    by metis
  hence [transfer_rule]: "((=) ===> rel_set r) A A'"
    by auto
  have "range A \<subseteq> M \<longleftrightarrow> range A' \<subseteq> M'"
    by transfer_prover
  with assms have "(\<Union>i::nat. A i) \<in> M"
    by simp
  also have "?this \<longleftrightarrow> (\<Union>i::nat. A' i) \<in> M'"
    by transfer_prover
  finally show ?thesis .
qed

lemma transfer_sigma_algebra [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_set r ===> rel_set (rel_set r) ===> (=)) sigma_algebra sigma_algebra"
  unfolding sigma_algebra_iff
proof (intro rel_funI conj_cong, goal_cases)
  case [transfer_rule]: (1 A A' M M')
  show ?case by transfer_prover
next
  case (2 A A' M M')
  have "bi_unique (\<lambda>x y. r y x)"
    using assms by (auto simp: bi_unique_def)
  note uniq = this assms
  show ?case
    using transfer_sigma_algebra_aux[OF uniq(1), of M' M]
          transfer_sigma_algebra_aux[OF uniq(2), of M M'] 2
    by (auto simp: rel_set_flip[of r] rel_set_flip[of "rel_set r"])
qed

lemma transfer_measure_space [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_set r ===> rel_set (rel_set r) ===> (rel_set r ===> (=)) ===> (=)) measure_space measure_space"
  unfolding measure_space_def by transfer_prover

lemma transfer_measure_of [transfer_rule]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_set r ===> rel_set (rel_set r) ===> (rel_set r ===> (=)) ===> rel_measure_bij r)
         measure_of measure_of"
proof (safe intro!: rel_funI, goal_cases)
  case [transfer_rule]: (1 \<Omega> \<Omega>' \<Sigma> \<Sigma>' \<mu> \<mu>')
  have [simp]: "measure_space \<Omega> \<Sigma> \<mu> = measure_space \<Omega>' \<Sigma>' \<mu>'"
    by transfer_prover
  let ?M1 = " (\<Omega>, if \<Sigma> \<subseteq> Pow \<Omega> then sigma_sets \<Omega> \<Sigma> else {{}, \<Omega>},
         \<lambda>a. if a \<in> sigma_sets \<Omega> \<Sigma> \<and> measure_space \<Omega> (sigma_sets \<Omega> \<Sigma>) \<mu> then \<mu> a else 0)"
  let ?M2 = "(\<Omega>', if \<Sigma>' \<subseteq> Pow \<Omega>' then sigma_sets \<Omega>' \<Sigma>' else {{}, \<Omega>'},
         \<lambda>a. if a \<in> sigma_sets \<Omega>' \<Sigma>' \<and> measure_space \<Omega>' (sigma_sets \<Omega>' \<Sigma>') \<mu>' then \<mu>' a else 0)"
  have "(rel_prod (rel_set r) (rel_prod (rel_set (rel_set r)) (rel_set r ===> (=)))) ?M1 ?M2"
    by transfer_prover

  have "rel_set r (space (measure_of \<Omega> \<Sigma> \<mu>)) (space (measure_of \<Omega>' \<Sigma>' \<mu>'))"
    by (subst (1 2) space_measure_of_conv) transfer_prover
  moreover have "rel_set (rel_set r) (sets (measure_of \<Omega> \<Sigma> \<mu>)) (sets (measure_of \<Omega>' \<Sigma>' \<mu>'))"
    by (subst (1 2) sets_measure_of_conv) transfer_prover
  moreover have "(rel_set r ===> (=)) (emeasure (measure_of \<Omega> \<Sigma> \<mu>)) (emeasure (measure_of \<Omega>' \<Sigma>' \<mu>'))"
    by (subst (1 2) emeasure_measure_of_conv) transfer_prover
  ultimately show ?case
    unfolding rel_measure_bij_def by blast
qed



lemma transfer_emeasure [transfer_rule, transfer_measure_bij_rules]:
  "(rel_measure_bij r ===> rel_set r ===> (=)) emeasure emeasure"
  by (auto simp: rel_measure_bij_def)

lemma transfer_measure [transfer_rule, transfer_measure_bij_rules]:
  "(rel_measure_bij r ===> rel_set r ===> (=)) measure measure"
  unfolding measure_def by transfer_prover

lemma transfer_space [transfer_rule, transfer_measure_bij_rules]:
  "(rel_measure_bij r ===> rel_set r) space space"
  by (auto simp: rel_measure_bij_def)

lemma transfer_sets [transfer_rule, transfer_measure_bij_rules]:
  "(rel_measure_bij r ===> rel_set (rel_set r)) sets sets"
  by (auto simp: rel_measure_bij_def)

lemma transfer_null_sets [transfer_rule, transfer_measure_bij_rules]:
  assumes [transfer_rule]: "bi_unique r"
  shows   "(rel_measure_bij r ===> rel_set (rel_set r)) null_sets null_sets"
  unfolding null_sets_def Set.filter_eq [symmetric] by transfer_prover

lemma transfer_fmeasurable [transfer_rule, transfer_measure_bij_rules]:
  assumes [transfer_rule]: "bi_unique r"
  shows "(rel_measure_bij r ===> rel_set (rel_set r)) fmeasurable fmeasurable"
  unfolding fmeasurable_def Set.filter_eq [symmetric] by transfer_prover

lemma transfer_emeasure_completion:
  assumes [transfer_rule]: "bi_unique r"
  assumes [transfer_rule]: "rel_measure_bij r M M'" "rel_set r X X'"
  defines "\<Sigma> \<equiv> ((\<lambda>(S,N). S \<union> N) ` (sets M \<times> (\<Union>N\<in>null_sets M. Pow N)))"
  shows "emeasure (completion M) X = emeasure (completion M') X'"
proof -
  define \<Sigma>' where "\<Sigma>' = ((\<lambda>(S,N). S \<union> N) ` (sets M' \<times> (\<Union>N\<in>null_sets M'. Pow N)))"
  have in_\<Sigma>_iff: "X \<in> \<Sigma> \<longleftrightarrow> X' \<in> \<Sigma>'"
    unfolding \<Sigma>_def \<Sigma>'_def by transfer_prover

  show ?thesis
  proof (cases "X \<in> \<Sigma>")
    case False
    have "\<not>X \<in> sets (completion M)"
      using False by (auto simp: sets_completion \<Sigma>_def)
    moreover have "\<not>X' \<in> sets (completion M')"
      using False unfolding in_\<Sigma>_iff by (auto simp: sets_completion \<Sigma>'_def)
    ultimately show ?thesis 
      by (simp add: emeasure_notin_sets)
  next
    case True
    hence "X' \<in> \<Sigma>'" using in_\<Sigma>_iff by simp
    have in_sets_iff: "X \<in> sets M \<longleftrightarrow> X' \<in> sets M'"
      by transfer_prover
    show ?thesis
    proof (cases "X \<in> sets M")
      case True
      have "emeasure M X = emeasure M' X'"
        by transfer_prover
      thus ?thesis using in_sets_iff using assms True
        by simp
    next
      case False
      from \<open>X \<in> \<Sigma>\<close> obtain S N Y where 1: "S \<in> sets M" "N \<in> null_sets M" "Y \<subseteq> N" "X = S \<union> Y"
        by (auto simp: \<Sigma>_def)
      let ?rs = "rel_set r"
      let ?SNYs1 = "(Set.filter (\<lambda>(S,N,Y). X = S \<union> Y) (sets M \<times> (SIGMA N:null_sets M. Pow N)))"
      let ?SNYs2 = "(Set.filter (\<lambda>(S,N,Y). X' = S \<union> Y) (sets M' \<times> (SIGMA N:null_sets M'. Pow N)))"
      have "(S, N, Y) \<in> ?SNYs1"
        using 1 by auto
      moreover  have "rel_set (rel_prod ?rs (rel_prod ?rs ?rs)) ?SNYs1 ?SNYs2"
        by transfer_prover
      ultimately obtain S' N' Y'
        where 2: "(S', N', Y') \<in> ?SNYs2"
          and 3: "rel_prod ?rs (rel_prod ?rs ?rs) (S, N, Y) (S', N', Y')"
        unfolding rel_set_def by fast
      from 3 have [transfer_rule]: "?rs S S'" "?rs N N'" "?rs Y Y'"
        by auto

      have "emeasure M S = emeasure M' S'"
        by transfer_prover
      thus ?thesis
        using 1 2 by (auto simp add: emeasure_completion_Un_set_null_set)
    qed
  qed
qed

lemma transfer_completion [transfer_rule, transfer_measure_bij_rules]:
  assumes [transfer_rule]: "bi_unique r"
  shows   "(rel_measure_bij r ===> rel_measure_bij r) completion completion"
proof (intro rel_funI rel_measure_bijI)
  fix M M'
  assume M_M' [transfer_rule]: "rel_measure_bij r M M'"
  show "rel_set (rel_set r) (sets (completion M)) (sets (completion M'))"
    unfolding sets_completion_eq by transfer_prover

  fix X X'
  assume X_X': "rel_set r X X'"
  show "emeasure (completion M) X = emeasure (completion M') X'"
    by (rule transfer_emeasure_completion[OF assms M_M' X_X'])
qed

lemmas [transfer_rule del] = transfer_measure_bij_rules

end (* context *)



subsection \<open>A type for the basis of a Euclidean space\<close>

typedef (overloaded) 'a :: euclidean_space basis = "Basis :: 'a set"
  using nonempty_Basis by blast

setup_lifting type_definition_basis

lemma cr_basis_altdef: "cr_basis b b' \<longleftrightarrow> b \<in> Basis \<and> b' = Abs_basis b"
  by (auto simp: cr_basis_def Rep_basis_inverse Abs_basis_inverse Rep_basis)

instance basis :: (euclidean_space) finite
proof
  have "(UNIV :: 'a basis set) \<subseteq> Abs_basis ` Basis"
  proof safe
    fix b :: "'a basis"
    have "Abs_basis (Rep_basis b) \<in> Abs_basis ` Basis"
      by (intro imageI) (auto simp: Rep_basis)
    also have "Abs_basis (Rep_basis b) = b"
      by (rule Rep_basis_inverse)
    finally show "b \<in> Abs_basis ` Basis" .
  qed
  moreover have "finite (Abs_basis ` Basis)"
    by auto
  ultimately show "finite (UNIV :: 'a basis set)"
    using finite_subset by blast
qed

definition eucl_to_vec' :: "'a :: euclidean_space \<Rightarrow> real ^ 'a basis" where
  "eucl_to_vec' x = vec_lambda (\<lambda>b. x \<bullet> Rep_basis b)"

definition eucl_to_vec :: "'a :: euclidean_space \<Rightarrow> real ^ 'a basis" where
  "eucl_to_vec x = vec_lambda (\<lambda>b. x \<bullet> Rep_basis b)"

definition eucl_of_vec :: "real ^ 'a :: euclidean_space basis \<Rightarrow> 'a" where
  "eucl_of_vec v = (\<Sum>b\<in>Basis. vec_nth v (Abs_basis b) *\<^sub>R b)"

lemma eucl_to_vec_of_vec [simp]: "eucl_to_vec (eucl_of_vec x) = x"
proof (subst vec_eq_iff, safe)
  fix b :: "'a basis"
  define b' where "b' = Rep_basis b"
  have b_eq: "b = Abs_basis b'" and b': "b' \<in> Basis"
    by (simp_all add: b'_def Rep_basis_inverse Rep_basis)
  from b' show "eucl_to_vec (eucl_of_vec x) $ b = x $ b"
    by (simp add: eucl_to_vec_def eucl_of_vec_def b_eq Abs_basis_inverse Rep_basis_inverse)
qed

lemma eucl_of_vec_to_vec [simp]: "eucl_of_vec (eucl_to_vec x) = x"
  using euclidean_representation[of x]
  by (simp add: eucl_to_vec_def eucl_of_vec_def Abs_basis_inverse)

lemma UNIV_basis_eq: "UNIV = Abs_basis ` Basis"
proof safe
  fix b :: "'a basis"
  have "Abs_basis (Rep_basis b) \<in> Abs_basis ` Basis"
    by (intro imageI) (auto simp: Rep_basis)
  also have "Abs_basis (Rep_basis b) = b"
    by (rule Rep_basis_inverse)
  finally show "b \<in> Abs_basis ` Basis" .
qed auto

lemma type_definition_eucl_to_vec: "type_definition eucl_to_vec eucl_of_vec UNIV"
  by (auto simp: type_definition_def)

lemma eucl_of_vec_eq_iff [simp]: "eucl_of_vec x = eucl_of_vec y \<longleftrightarrow> x = y"
proof
  assume "eucl_of_vec x = eucl_of_vec y"
  hence "eucl_to_vec (eucl_of_vec x) = eucl_to_vec (eucl_of_vec y)"
    by (simp only: )
  thus "x = y" by simp
qed auto

lemma eucl_to_vec_eq_iff [simp]: "eucl_to_vec x = eucl_to_vec y \<longleftrightarrow> x = y"
proof
  assume "eucl_to_vec x = eucl_to_vec y"
  hence "eucl_of_vec (eucl_to_vec x) = eucl_of_vec (eucl_to_vec y)"
    by (simp only: )
  thus "x = y" by simp
qed auto

lemma inj_Abs_basis: "inj_on Abs_basis Basis"
  by (auto intro!: inj_onI simp: Abs_basis_inject)

lemma Abs_basis_eq_iff_flip: "x \<in> Basis \<Longrightarrow> Abs_basis x = y \<longleftrightarrow> x = Rep_basis y"
  by (auto simp: Abs_basis_inverse Rep_basis_inverse)

lemma eucl_of_vec_axis [simp]: "eucl_of_vec (axis x a) = a *\<^sub>R Rep_basis x"
proof -
  have "eucl_of_vec (axis x a) = (\<Sum>b\<in>Basis. (if b = Rep_basis x then a else 0) *\<^sub>R b)"
    by (auto simp: eucl_of_vec_def axis_def Abs_basis_eq_iff_flip)
  also have "\<dots> = (\<Sum>b\<in>{Rep_basis x}. a *\<^sub>R b)"
    by (intro sum.mono_neutral_cong_right) (auto simp: Rep_basis)
  finally show ?thesis
    by simp
qed


text \<open>
  We define a completely arbitrary linear ordering on the basis elements.
\<close>
instantiation basis :: (euclidean_space) linorder
begin

definition less_eq_basis :: "'a basis \<Rightarrow> 'a basis \<Rightarrow> bool" where
  "less_eq_basis b1 b2 =
     (let f = (SOME f. bij_betw f UNIV {..<CARD('a basis)})
      in  f b1 \<le> f b2)"

definition less_basis :: "'a basis \<Rightarrow> 'a basis \<Rightarrow> bool" where
  "less_basis b1 b2 =
     (let f = (SOME f. bij_betw f UNIV {..<CARD('a basis)})
      in  f b1 < f b2)"

instance proof -
  define f' where "f' = (SOME f'. bij_betw f' (UNIV :: 'a basis set) {..<CARD('a basis)})"
  have f': "bij_betw f' UNIV {..<CARD('a basis)}"
  proof -
    obtain xs :: "'a basis list" where xs: "distinct xs" "set xs = UNIV"
      using finite_distinct_list[of "UNIV :: 'a basis set"] finite by blast
    have [simp]: "length xs = CARD('a basis)"
      using xs distinct_card[of xs] by simp
    
    define f where "f = nth xs"
    have "bij_betw f {..<CARD('a basis)} UNIV"
      unfolding bij_betw_def inj_on_def using xs
      by (auto simp: set_conv_nth f_def distinct_conv_nth)
    hence "\<exists>f'. bij_betw f' (UNIV :: 'a basis set) {..<CARD('a basis)}"
      using bij_betw_inv by blast
    from someI_ex[OF this] show ?thesis
      by (simp add: f'_def)
  qed
  have le_def: "b1 \<le> b2 \<longleftrightarrow> f' b1 \<le> f' b2"
   and less_def: "b1 < b2 \<longleftrightarrow> f' b1 < f' b2" for b1 b2
    by (simp_all add: f'_def less_eq_basis_def less_basis_def Let_def)

  show "OFCLASS('a basis, linorder_class)"
    using f' by intro_classes (auto simp: le_def less_def bij_betw_def inj_on_def)
qed

end

instance basis :: (euclidean_space) wellorder
proof (intro_classes, goal_cases)
  case (1 P a)
  have "wf ({(x :: 'a basis,y). x \<le> y} - Id)"
    by (rule partial_order_on_well_order_on[where A = UNIV])
       (auto simp: partial_order_on_def preorder_on_def antisym_def refl_on_def trans_def)
  also have "{(x :: 'a basis,y). x \<le> y} - Id = {(x,y). x < y}"
    by auto
  finally have "wfP ((<) :: 'a basis \<Rightarrow> _)" 
    unfolding wfp_def .
  from wfp_induct[OF this] show ?case using 1
    by blast
qed

lemma transfer_Rep_basis [transfer_rule]: "cr_basis (Rep_basis b) b"
  by (auto simp: cr_basis_def)
  
lemma bi_unique_cr_basis [transfer_rule]: "bi_unique cr_basis"
  by (auto simp: bi_unique_def cr_basis_def Rep_basis_inject)

lemma right_total_cr_basis [transfer_rule]: "right_total cr_basis"
  by (auto simp: right_total_def cr_basis_def)

lemma transfer_basis [transfer_rule]: "rel_set cr_basis Basis UNIV"
  unfolding rel_set_def cr_basis_def
proof safe
  show "\<exists>y\<in>UNIV. x = Rep_basis y" if "x \<in> Basis" for x :: 'a
    using Abs_basis_inverse[of x] that by (auto intro!: exI[of _ "Abs_basis x"])
qed (auto simp: Rep_basis)


subsection \<open>Transfer for Euclidean spaces\<close>

definition eucl_vec_rel :: "'a :: euclidean_space \<Rightarrow> real ^ 'a basis \<Rightarrow> bool" where
  "eucl_vec_rel a b \<longleftrightarrow> a = eucl_of_vec b"

lemma eucl_vec_rel_altdef: "eucl_vec_rel x y \<longleftrightarrow> y = eucl_to_vec x"
  by (auto simp: eucl_vec_rel_def)

definition eucl_linfun_rel where
  "eucl_linfun_rel R1 R2 f M = rel_fun R2 (rel_fun R1 (=)) (\<lambda>x y. f y \<bullet> x) (\<lambda>x y. M $ x $ y)"


lemma eucl_to_vec_nth [simp]: "eucl_to_vec x $ b = x \<bullet> Rep_basis b"
  by (simp add: eucl_to_vec_def)

lemma eucl_of_vec_inner_Basis [simp]: "b \<in> Basis \<Longrightarrow> eucl_of_vec x \<bullet> b = x $ Abs_basis b"
  by (simp add: eucl_of_vec_def)

lemma representation_Basis_eucl_of_vec:
  "representation Basis (eucl_of_vec y) = (\<lambda>b. if b \<in> Basis then y $ Abs_basis b else 0)"
proof (rule representation_eqI)
  show "(\<Sum>b | (if b \<in> Basis then y $ Abs_basis b else 0) \<noteq> 0.
            (if b \<in> Basis then y $ Abs_basis b else 0) *\<^sub>R b) = eucl_of_vec y"
    unfolding eucl_of_vec_def by (intro sum.mono_neutral_cong_left) auto
qed (auto simp: independent_Basis split: if_splits)

lemma inner_Basis_eucl_linfun_rel [transfer_rule]:
  assumes "eucl_linfun_rel R1 R2 f M" "R1 b1 b1'" "R2 b2 b2'"
  shows   "f b1 \<bullet> b2 = M $ b2' $ b1'"
  using assms unfolding eucl_linfun_rel_def by (auto simp: rel_fun_def)


named_theorems transfer_eucl_bij_rules

context
  includes lifting_syntax
begin

lemmas [transfer_rule] = transfer_measure_bij_rules

lemma transfer_eucl_to_vec [transfer_rule, transfer_eucl_bij_rules, intro]:
  "eucl_vec_rel x (eucl_to_vec x)"
  by (simp add: eucl_vec_rel_def)

lemma transfer_eucl_of_vec [transfer_rule, transfer_eucl_bij_rules, intro]:
  "eucl_vec_rel (eucl_of_vec x) x"
  by (simp add: eucl_vec_rel_def)

lemma bi_unique_eucl_vec_rel [transfer_rule]: "bi_unique eucl_vec_rel"
  by (auto simp: bi_unique_def eucl_vec_rel_def)

lemma bi_total_eucl_vec_rel [transfer_rule]: "bi_total eucl_vec_rel"
  by (auto simp: bi_total_def eucl_vec_rel_def intro: exI[of _ "eucl_to_vec x" for x] )

lemma rel_set_eucl_vec_eq: "rel_set eucl_vec_rel X Y \<longleftrightarrow> X = eucl_of_vec ` Y"
  by (auto simp: rel_set_def eucl_vec_rel_def)

lemma rel_set_eucl_vec_eq': "rel_set eucl_vec_rel X Y \<longleftrightarrow> Y = eucl_of_vec -` X"
  by (auto simp: rel_set_def eucl_vec_rel_def vimage_def intro!: exI[of _ "eucl_to_vec x" for x])

lemma transfer_eucl_vec_Basis [transfer_rule, transfer_eucl_bij_rules]: "rel_set eucl_vec_rel Basis Basis"
  unfolding rel_set_def
proof safe
  fix b :: 'a assume b: "b \<in> Basis"
  thus "\<exists>b'\<in>Basis. eucl_vec_rel b b'"
    by (auto simp: eucl_vec_rel_def Basis_vec_def Abs_basis_inverse intro!: exI[of _ "Abs_basis b"])
next
  fix b :: "real ^ 'a basis" assume b: "b \<in> Basis"
  have "(\<Sum>b\<in>Basis. (if b = Rep_basis b' then 1 else 0) *\<^sub>R b) = (\<Sum>b\<in>{Rep_basis b'}. b)"
    for b' :: "'a basis"
    by (intro sum.mono_neutral_cong_right) (auto simp: Rep_basis)
  thus "\<exists>b'\<in>Basis. eucl_vec_rel b' b"
    using b by (auto simp: eucl_vec_rel_def eucl_of_vec_def Basis_vec_def
                           axis_def Abs_basis_eq_iff_flip Rep_basis)
qed

lemma transfer_eucl_vec_rel_axis [transfer_rule, transfer_eucl_bij_rules]:
  "(cr_basis ===> (=) ===> eucl_vec_rel) (\<lambda>b x. x *\<^sub>R b) axis"
  by (auto simp: cr_basis_def rel_fun_def eucl_vec_rel_altdef
                 eucl_to_vec_def Rep_basis inner_Basis axis_def Rep_basis_inject)

lemma transfer_eucl_vec_rel_axis_1 [transfer_rule, transfer_eucl_bij_rules]:
  "(cr_basis ===> eucl_vec_rel) (\<lambda>b. b) (\<lambda>b. axis b 1)"
  by (auto simp: cr_basis_def rel_fun_def eucl_vec_rel_altdef
                 eucl_to_vec_def Rep_basis inner_Basis axis_def Rep_basis_inject)

lemma transfer_eucl_vec_0 [transfer_rule, transfer_eucl_bij_rules]: "eucl_vec_rel 0 0"
  and transfer_eucl_vec_plus [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> eucl_vec_rel) (+) (+)"
  and transfer_eucl_vec_diff [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> eucl_vec_rel) (-) (-)"
  and transfer_eucl_vec_uminus [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel) uminus uminus"
  and transfer_eucl_vec_scaleR [transfer_rule, transfer_eucl_bij_rules]: "((=) ===> eucl_vec_rel ===> eucl_vec_rel) (*\<^sub>R) (*\<^sub>R)"
  by (auto simp: eucl_vec_rel_def eucl_of_vec_def rel_fun_def sum.distrib algebra_simps 
                 sum_subtractf sum_negf scale_sum_right)

lemma transfer_eucl_vec_inner [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> (=)) (\<bullet>) (\<bullet>)"
proof -
  show "((eucl_vec_rel :: 'a \<Rightarrow> _) ===> eucl_vec_rel ===> (=)) (\<bullet>) (\<bullet>)"
    unfolding eucl_vec_rel_altdef
  proof (safe intro!: rel_funI)
    fix x y :: 'a
    have "eucl_to_vec x \<bullet> eucl_to_vec y = (\<Sum>i\<in>UNIV. x \<bullet> Rep_basis i * (y \<bullet> Rep_basis i))"
      by (auto simp: inner_vec_def algebra_simps eucl_to_vec_def)
    also have "\<dots> = (\<Sum>b\<in>Basis. (x \<bullet> b) * (y \<bullet> b))"
      unfolding UNIV_basis_eq using inj_Abs_basis
      by (subst sum.reindex) (auto simp: Abs_basis_inverse)
    also have "\<dots> = x \<bullet> y"
      by (rule euclidean_inner [symmetric])
    finally show "x \<bullet> y = eucl_to_vec x \<bullet> eucl_to_vec y" ..
  qed
qed

lemma transfer_eucl_vec_nth [transfer_rule, transfer_eucl_bij_rules]:
  "(eucl_vec_rel ===> cr_basis ===> (=)) (representation Basis) vec_nth"
  by (intro rel_funI)
     (auto simp: cr_basis_def Rep_basis eucl_vec_rel_def
                 representation_Basis_eucl_of_vec Rep_basis_inverse)

lemma transfer_eucl_vec_cbox [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> rel_set eucl_vec_rel) cbox cbox"
  unfolding cbox_def by transfer_prover

lemma transfer_eucl_vec_box [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> rel_set eucl_vec_rel) box box"
  unfolding box_def by transfer_prover

lemma transfer_eucl_vec_linepath [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> (=) ===> eucl_vec_rel) linepath linepath"
  unfolding linepath_def by transfer_prover

lemma transfer_eucl_vec_closed_segment [transfer_rule, transfer_eucl_bij_rules]:
  "(eucl_vec_rel ===> eucl_vec_rel ===> rel_set eucl_vec_rel) closed_segment closed_segment"
  unfolding closed_segment_def by transfer_prover

lemma transfer_eucl_vec_open_segment [transfer_rule, transfer_eucl_bij_rules]:
  "(eucl_vec_rel ===> eucl_vec_rel ===> rel_set eucl_vec_rel) open_segment open_segment"
  unfolding open_segment_def by transfer_prover

lemma transfer_eucl_vec_convex [transfer_rule, transfer_eucl_bij_rules]: "(rel_set eucl_vec_rel ===> (=)) convex convex"
  unfolding convex_def by transfer_prover

lemma transfer_eucl_linfun_rel_matrix [transfer_rule, transfer_eucl_bij_rules]:
  "((eucl_vec_rel ===> eucl_vec_rel) ===> eucl_linfun_rel cr_basis cr_basis) (\<lambda>f. f) matrix"
proof (intro rel_funI)
  fix f :: "'a \<Rightarrow> 'b" and g :: "(real, 'a basis) vec \<Rightarrow> (real, 'b basis) vec"
  assume fg [transfer_rule]: "(eucl_vec_rel ===> eucl_vec_rel) f g"
  show "eucl_linfun_rel cr_basis cr_basis f (matrix g)"
    unfolding eucl_linfun_rel_def cr_basis_def rel_fun_def
  proof safe
    fix b1 :: "'a basis" and b2 :: "'b basis"
    have "eucl_vec_rel (f (1 *\<^sub>R Rep_basis b1)) (g (axis b1 1))"
      by transfer_prover
    thus "f (Rep_basis b1) \<bullet> Rep_basis b2 = matrix g $ b2 $ b1"
      by (auto simp: eucl_vec_rel_def  Rep_basis_inverse Rep_basis matrix_def)
  qed
qed

lemma transfer_eucl_vec_det [transfer_rule, transfer_eucl_bij_rules]:
  assumes [transfer_rule]: "bi_unique R"
  assumes "rel_set R Basis UNIV"
  shows "(eucl_linfun_rel R R ===> (=)) eucl.det matrix_det"
proof (safe intro!: rel_funI, goal_cases)
  case [transfer_rule]: (1 f M)
  define P :: "('a \<Rightarrow> 'a) set" where "P = {p. p permutes Basis}"
  define P' :: "('b \<Rightarrow> 'b) set" where "P' = {p. p permutes UNIV}"

  from assms have uniq: "\<forall>x\<in>Basis. \<exists>!y. R x y"
    unfolding bi_unique_def by (auto simp: rel_set_def)
  then obtain right where right': "\<forall>x\<in>Basis. \<forall>y. right x = y \<longleftrightarrow> R x y"
    by metis
  hence right: "bij_betw right Basis UNIV"
    using uniq assms unfolding bij_betw_def inj_on_def bi_unique_def rel_set_def
    by blast
  define left where "left = inv_into Basis right"
  have [simp]: "right (left x) = x" for x
    using right by (simp add: left_def bij_betw_inv_into_right)
  have [simp]: "left (right x) = x" if "x \<in> Basis" for x
    using right that by (simp add: left_def bij_betw_inv_into_left)
  have left: "bij_betw left UNIV Basis"
    using right unfolding left_def by (simp add: bij_betw_inv_into)
  have [simp]: "left x \<in> Basis" for x
    using left by (auto simp: bij_betw_def)

  define g :: "('b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a)"
    where "g = (\<lambda>p x. if x \<in> Basis then left (p (right x)) else x)"
  define h :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)"
    where "h = (\<lambda>p x. right (p (left x)))"
  have g: "g p \<in> P" if "p \<in> P'" for p
  proof -
    interpret permutes_bij p UNIV Basis left right "g p"
      using that left
       by unfold_locales
          (auto intro!: bij_betw_byWitness[of _ Abs_basis] 
                simp: Rep_basis_inverse Abs_basis_inverse Rep_basis g_def P'_def)
     show "g p \<in> P" unfolding P_def
       using permutes_p' by simp
   qed
  have h: "h p \<in> P'" "evenperm (h p) \<longleftrightarrow> evenperm p" if "p \<in> P" for p
  proof -
    interpret permutes_bij_finite p Basis UNIV right left "h p"
      using that right
       by unfold_locales
          (auto intro!: bij_betw_byWitness[of _ Rep_basis] 
                simp: Rep_basis_inverse Abs_basis_inverse Rep_basis h_def P_def)
     show "h p \<in> P'" unfolding P'_def
       using permutes_p' by simp
     show "evenperm (h p) \<longleftrightarrow> evenperm p"
       using evenperm_p'_iff .
   qed

  have P_P': "bij_betw h P P'"
  proof (rule bij_betw_byWitness[of _ g])
    show "\<forall>p\<in>P. g (h p) = p"
      by (auto simp: P_def g_def h_def Abs_basis_inverse Rep_basis_inverse 
                     fun_eq_iff permutes_in_image permutes_not_in)
    show "\<forall>p\<in>P'. h (g p) = p"
      by (auto simp: P'_def g_def h_def Abs_basis_inverse Rep_basis_inverse Rep_basis
                     fun_eq_iff permutes_in_image permutes_not_in)
  qed (use g h in auto)

  have rel': "f y \<bullet> x = M $ x' $ y'" if "R x x'" "R y y'" for x y x' y'  
    using 1 that by (auto simp: rel_fun_def eucl_linfun_rel_def)

  have "(\<Sum>p\<in>P. real_of_int (sign (h p)) * (\<Prod>i\<in>UNIV. M $ i $ h p i)) =
        (\<Sum>p\<in>P'. real_of_int (sign p) * (\<Prod>i\<in>UNIV. M $ i $ p i))"
    by (rule sum.reindex_bij_betw[OF P_P'])
  also have "(\<Sum>p\<in>P. real_of_int (sign (h p)) * (\<Prod>i\<in>UNIV. M $ i $ h p i)) =
             (\<Sum>p\<in>P. real_of_int (sign p) * (\<Prod>b\<in>Basis. f (p b) \<bullet> b))"
  proof (rule sum.cong, goal_cases)
    case (2 p)
    have "(\<Prod>i\<in>UNIV. M $ i $ h p i) = (\<Prod>b\<in>Basis. M $ right b $ h p (right b))"
      by (subst prod.reindex_bij_betw[OF right]) auto
    also have "\<dots> = (\<Prod>b\<in>Basis. f (p b) \<bullet> b)"
      using 2 right' unfolding h_def P_def
      by (intro prod.cong)
         (auto simp: Abs_basis_inverse eucl_linfun_rel_def rel_fun_def 
                     cr_basis_altdef permutes_in_image intro!: rel' [symmetric])
    finally show ?case
      using h 2 by (simp add: sign_def)
  qed auto
  also have "\<dots> = eucl.det f"
    by (simp add: eucl_det_def P_def)
  also have "(\<Sum>p\<in>P'. real_of_int (sign p) * (\<Prod>i\<in>UNIV. M $ i $ p i)) = matrix_det M"
    by (simp add: P'_def Determinants.det_def)
  finally show ?case .
qed

lemma transfer_eucl_dist [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> eucl_vec_rel ===> (=)) dist dist"
  by (subst (1 2) euclidean_dist_l2[abs_def], subst (1 2) L2_set_def) transfer_prover

lemma transfer_eucl_norm [transfer_rule, transfer_eucl_bij_rules]: "(eucl_vec_rel ===> (=)) norm norm"
  unfolding norm_conv_dist[abs_def] by transfer_prover

lemma transfer_eucl_vec_bounded [transfer_rule, transfer_eucl_bij_rules]: "(rel_set eucl_vec_rel ===> (=)) bounded bounded"
  unfolding bounded_iff by transfer_prover

lemma transfer_eucl_vec_linear [transfer_rule, transfer_eucl_bij_rules]: "((eucl_vec_rel ===> eucl_vec_rel) ===> (=)) linear linear"
  unfolding linear_iff by transfer_prover

lemma transfer_eucl_vec_open [transfer_rule, transfer_eucl_bij_rules]: "(rel_set eucl_vec_rel ===> (=)) open open"
  unfolding open_dist by transfer_prover

lemma transfer_eucl_vec_closed [transfer_rule, transfer_eucl_bij_rules]: "(rel_set eucl_vec_rel ===> (=)) closed closed"
  unfolding closed_def by transfer_prover

lemma transfer_eucl_vec_compact [transfer_rule, transfer_eucl_bij_rules]: "(rel_set eucl_vec_rel ===> (=)) compact compact"
  unfolding compact_eq_bounded_closed by transfer_prover

lemma transfer_borel [transfer_rule, transfer_eucl_bij_rules]: "rel_measure_bij eucl_vec_rel borel borel"
  unfolding borel_def by transfer_prover

lemma measurable_eucl_of_vec [measurable]: "eucl_of_vec \<in> borel_measurable borel"
proof -
  let ?M1 = "borel :: 'a measure" and ?M2 = "borel :: (real ^ 'a basis) measure"
  have "(rel_set eucl_vec_rel ===> (=)) (\<lambda>X. X \<in> sets ?M1) (\<lambda>X. X \<in> sets ?M2)"
    by transfer_prover
  thus ?thesis
    unfolding rel_set_eucl_vec_eq' rel_fun_def measurable_def by simp
qed

lemma lborel_conv_eucl_of_vec: "lborel = distr lborel borel eucl_of_vec" (is "_ = ?M")
proof (rule measure_eqI_generator_eq)
  let ?E = "range (\<lambda>(a, b). box a b::'a set)"
  let ?A = "\<lambda>n::nat. box (- (real n *\<^sub>R One)) (real n *\<^sub>R One) :: 'a set"
  show "Int_stable ?E"
    by (auto simp: Int_stable_def box_Int_box)
  show "?E \<subseteq> Pow UNIV" "sets lborel = sigma_sets UNIV ?E" "sets ?M = sigma_sets UNIV ?E"
    by (simp_all add: borel_eq_box )
  show "range ?A \<subseteq> ?E" "(\<Union>i. ?A i) = UNIV"
    unfolding UN_box_eq_UNIV by auto
  show "emeasure lborel (?A i) \<noteq> \<infinity>" for i by auto
  show "emeasure lborel X = emeasure ?M X"
    if "X \<in> range (\<lambda>(a, b). box a b)" for X
    using that
  proof safe
    fix l u :: 'a
    have "emeasure ?M (box l u) = emeasure lborel (eucl_of_vec -` box l u)"
      by (subst emeasure_distr) simp_all
    also have "rel_set eucl_vec_rel (box l u) (box (eucl_to_vec l) (eucl_to_vec u))"
      by transfer_prover
    hence "eucl_of_vec -` box l u = box (eucl_to_vec l) (eucl_to_vec u)"
      by (simp add: rel_set_eucl_vec_eq')
    also have "emeasure lborel \<dots> = emeasure lborel (box l u)"
      by (rule sym, subst (1 2) emeasure_lborel_box_eq) transfer_prover
    finally show "emeasure lborel (box l u) =
                  emeasure (distr lborel borel eucl_of_vec) (box l u)" ..
  qed
qed

lemma transfer_lborel [transfer_rule, transfer_eucl_bij_rules]:
  "rel_measure_bij eucl_vec_rel lborel lborel"
  unfolding rel_measure_bij_def
proof safe
  let ?M1 = "lborel :: 'a measure" and ?M2 = "lborel :: (real ^ ('a basis)) measure"
  show "rel_set eucl_vec_rel (space lborel) (space lborel)"
       "rel_set (rel_set eucl_vec_rel) (sets lborel) (sets lborel)"
    unfolding space_lborel sets_lborel by transfer_prover+
  show "(rel_set eucl_vec_rel ===> (=)) (emeasure ?M1) (emeasure ?M2)"
  proof (safe intro!: rel_funI)
    fix X :: "'a set" and Y :: "(real ^ 'a basis) set"
    assume [transfer_rule]: "rel_set eucl_vec_rel X Y"
    show "emeasure lborel X = emeasure lborel Y"
    proof (cases "X \<in> sets borel")
      case True
      thus ?thesis using \<open>rel_set eucl_vec_rel X Y\<close> unfolding rel_set_eucl_vec_eq'
        by (subst lborel_conv_eucl_of_vec) (auto simp: emeasure_distr)
    next
      case False
      have "(X \<in> sets ?M1) \<longleftrightarrow> Y \<in> sets ?M2"
        unfolding sets_lborel by transfer_prover
      thus ?thesis using False by (simp add: emeasure_notin_sets)
    qed
  qed
qed

end

end
