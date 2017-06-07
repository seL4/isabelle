(*  Title:      HOL/Probability/Tree_Space.thy
    Author:     Johannes Hölzl, CMU *)

theory Tree_Space
  imports Analysis
begin

lemma countable_lfp:
  assumes step: "\<And>Y. countable Y \<Longrightarrow> countable (F Y)"
  and cont: "Order_Continuity.sup_continuous F"
  shows "countable (lfp F)"
by(subst sup_continuous_lfp[OF cont])(simp add: countable_funpow[OF step])

lemma countable_lfp_apply:
  assumes step: "\<And>Y x. (\<And>x. countable (Y x)) \<Longrightarrow> countable (F Y x)"
  and cont: "Order_Continuity.sup_continuous F"
  shows "countable (lfp F x)"
proof -
  { fix n
    have "\<And>x. countable ((F ^^ n) bot x)"
      by(induct n)(auto intro: step) }
  thus ?thesis using cont by(simp add: sup_continuous_lfp)
qed

datatype 'a tree = Leaf
  | Node (left: "'a tree") (val: 'a) (right: "'a tree")
  where
    "left Leaf = Leaf"
  | "right Leaf = Leaf"
  | "val Leaf = undefined"

inductive_set trees :: "'a set \<Rightarrow> 'a tree set" for S :: "'a set" where
  [intro!]: "Leaf \<in> trees S"
| "l \<in> trees S \<Longrightarrow> r \<in> trees S \<Longrightarrow> v \<in> S \<Longrightarrow> Node l v r \<in> trees S"

lemma Node_in_trees_iff[simp]: "Node l v r \<in> trees S \<longleftrightarrow> (l \<in> trees S \<and> v \<in> S \<and> r \<in> trees S)"
  by (subst trees.simps) auto

lemma trees_sub_lfp: "trees S \<subseteq> lfp (\<lambda>T. T \<union> {Leaf} \<union> (\<Union>l\<in>T. (\<Union>v\<in>S. (\<Union>r\<in>T. {Node l v r}))))"
proof
  have mono: "mono (\<lambda>T. T \<union> {Leaf} \<union> (\<Union>l\<in>T. (\<Union>v\<in>S. (\<Union>r\<in>T. {Node l v r}))))"
    by (auto simp: mono_def)
  fix t assume "t \<in> trees S" then show "t \<in> lfp (\<lambda>T. T \<union> {Leaf} \<union> (\<Union>l\<in>T. (\<Union>v\<in>S. (\<Union>r\<in>T. {Node l v r}))))"
  proof induction
    case 1 then show ?case
      by (subst lfp_unfold[OF mono]) auto
  next
    case 2 then show ?case
      by (subst lfp_unfold[OF mono]) auto
  qed
qed

lemma countable_trees: "countable A \<Longrightarrow> countable (trees A)"
  apply (rule countable_subset[OF trees_sub_lfp])
  apply (rule countable_lfp)
  subgoal by auto
  apply (intro sup_continuous_sup sup_continuous_const)
    subgoal by (simp add: sup_continuous_def)
    subgoal apply (auto simp add: sup_continuous_def)
      subgoal premises prems for M x c a y d
      using prems(3,5) prems(2)[THEN incseqD, of x "max x y"] prems(2)[THEN incseqD, of y "max x y"]
      by (intro exI[of _ "max x y"]) auto
    done
  done

lemma trees_UNIV[simp]: "trees UNIV = UNIV"
proof -
  have "t \<in> trees UNIV" for t :: "'a tree"
    by (induction t) (auto intro: trees.intros(2))
  then show ?thesis by auto
qed

instance tree :: (countable) countable
proof
  have "countable (UNIV :: 'a tree set)"
    by (subst trees_UNIV[symmetric]) (intro countable_trees[OF countableI_type])
  then show "\<exists>to_nat::'a tree \<Rightarrow> nat. inj to_nat"
    by (auto simp: countable_def)
qed

lemma map_in_trees[intro]: "(\<And>x. x \<in> set_tree t \<Longrightarrow> f x \<in> S) \<Longrightarrow> map_tree f t \<in> trees S"
  by (induction t) (auto intro: trees.intros(2))

primrec trees_cyl :: "'a set tree \<Rightarrow> 'a tree set" where
  "trees_cyl Leaf = {Leaf} "
| "trees_cyl (Node l v r) = (\<Union>l'\<in>trees_cyl l. (\<Union>v'\<in>v. (\<Union>r'\<in>trees_cyl r. {Node l' v' r'})))"

definition tree_sigma :: "'a measure \<Rightarrow> 'a tree measure"
where
  "tree_sigma M = sigma (trees (space M)) (trees_cyl ` trees (sets M))"

lemma Node_in_trees_cyl: "Node l' v' r' \<in> trees_cyl t \<longleftrightarrow>
  (\<exists>l v r. t = Node l v r \<and> l' \<in> trees_cyl l \<and> r' \<in> trees_cyl r \<and> v' \<in> v)"
  by (cases t) auto

lemma trees_cyl_sub_trees:
  assumes "t \<in> trees A" "A \<subseteq> Pow B" shows "trees_cyl t \<subseteq> trees B"
  using assms(1)
proof induction
  case (2 l v r) with \<open>A \<subseteq> Pow B\<close> show ?case
    by (auto intro!: trees.intros(2))
qed auto

lemma trees_cyl_sets_in_space: "trees_cyl ` trees (sets M) \<subseteq> Pow (trees (space M))"
  using trees_cyl_sub_trees[OF _ sets.space_closed, of _ M] by auto

lemma space_tree_sigma: "space (tree_sigma M) = trees (space M)"
  unfolding tree_sigma_def by (rule space_measure_of_conv)

lemma sets_tree_sigma_eq: "sets (tree_sigma M) = sigma_sets (trees (space M)) (trees_cyl ` trees (sets M))"
  unfolding tree_sigma_def by (rule sets_measure_of) (rule trees_cyl_sets_in_space)

lemma Leaf_in_tree_sigma[measurable]: "{Leaf} \<in> sets (tree_sigma M)"
  unfolding sets_tree_sigma_eq
  by (rule sigma_sets.Basic) (auto intro: trees.intros(2) image_eqI[where x=Leaf])

lemma trees_cyl_map_treeI: "t \<in> trees_cyl (map_tree (\<lambda>x. A) t)" if *: "t \<in> trees A"
  using * by induction auto

lemma trees_cyl_map_in_sets:
  "(\<And>x. x \<in> set_tree t \<Longrightarrow> f x \<in> sets M) \<Longrightarrow> trees_cyl (map_tree f t) \<in> sets (tree_sigma M)"
  by (subst sets_tree_sigma_eq) auto

lemma Node_in_tree_sigma:
  assumes L: "X \<in> sets (M \<Otimes>\<^sub>M (tree_sigma M \<Otimes>\<^sub>M tree_sigma M))"
  shows "{Node l v r | l v r. (v, l, r) \<in> X} \<in> sets (tree_sigma M)"
proof -
  let ?E = "\<lambda>s::unit tree. trees_cyl (map_tree (\<lambda>_. space M) s)"
  have 1: "countable (range ?E)"
    by (intro countable_image countableI_type)
  have 2: "trees_cyl ` trees (sets M) \<subseteq> Pow (space (tree_sigma M))"
    using trees_cyl_sets_in_space[of M] by (simp add: space_tree_sigma)
  have 3: "sets (tree_sigma M) = sigma_sets (space (tree_sigma M)) (trees_cyl ` trees (sets M))"
    unfolding sets_tree_sigma_eq by (simp add: space_tree_sigma)
  have 4: "(\<Union>s. ?E s) = space (tree_sigma M)"
  proof (safe; clarsimp simp: space_tree_sigma)
    fix t s assume "t \<in> trees_cyl (map_tree (\<lambda>_::unit. space M) s)"
    then show "t \<in> trees (space M)"
      by (induction s arbitrary: t) auto
  next
    fix t assume "t \<in> trees (space M)"
    then show "\<exists>t'. t \<in> ?E t'"
      by (intro exI[of _ "map_tree (\<lambda>_. ()) t"])
         (auto simp: tree.map_comp comp_def intro: trees_cyl_map_treeI)
  qed
  have 5: "range ?E \<subseteq> trees_cyl ` trees (sets M)" by auto
  let ?P = "{A \<times> B | A B. A \<in> trees_cyl ` trees (sets M) \<and> B \<in> trees_cyl ` trees (sets M)}"
  have P: "sets (tree_sigma M \<Otimes>\<^sub>M tree_sigma M) = sets (sigma (space (tree_sigma M) \<times> space (tree_sigma M)) ?P)"
    by (rule sets_pair_eq[OF 2 3 1 5 4 2 3 1 5 4])

  have "sets (M \<Otimes>\<^sub>M (tree_sigma M \<Otimes>\<^sub>M tree_sigma M)) =
    sets (sigma (space M \<times> space (tree_sigma M \<Otimes>\<^sub>M tree_sigma M)) {A \<times> BC | A BC. A \<in> sets M \<and> BC \<in> ?P})"
  proof (rule sets_pair_eq)
    show "sets M \<subseteq> Pow (space M)" "sets M = sigma_sets (space M) (sets M)"
      by (auto simp: sets.sigma_sets_eq sets.space_closed)
    show "countable {space M}" "{space M} \<subseteq> sets M" "\<Union>{space M} = space M"
      by auto
    show "?P \<subseteq> Pow (space (tree_sigma M \<Otimes>\<^sub>M tree_sigma M))"
      using trees_cyl_sets_in_space[of M]
      by (auto simp: space_pair_measure space_tree_sigma subset_eq)
    then show "sets (tree_sigma M \<Otimes>\<^sub>M tree_sigma M) =
      sigma_sets (space (tree_sigma M \<Otimes>\<^sub>M tree_sigma M)) ?P"
      by (subst P, subst sets_measure_of) (auto simp: space_tree_sigma space_pair_measure)
    show "countable ((\<lambda>(a, b). a \<times> b) ` (range ?E \<times> range ?E))"
      by (intro countable_image countable_SIGMA countableI_type)
    show "(\<lambda>(a, b). a \<times> b) ` (range ?E \<times> range ?E) \<subseteq> ?P"
      by auto
  qed (insert 4, auto simp: space_pair_measure space_tree_sigma set_eq_iff)
  also have "\<dots> = sigma_sets (space M \<times> trees (space M) \<times> trees (space M))
    {A \<times> trees_cyl B \<times> trees_cyl C | A B C. A \<in> sets M \<and> B \<in> trees (sets M) \<and> C \<in> trees (sets M) }"
    apply (subst sets_measure_of)
    subgoal
      using sets.space_closed[of M] trees_cyl_sets_in_space[of M]
      by (clarsimp simp: space_pair_measure space_tree_sigma) blast
    apply (rule arg_cong2[where f=sigma_sets])
    apply (auto simp: space_pair_measure space_tree_sigma)
      subgoal premises prems for A B C
      apply (rule exI conjI refl prems)+
      using trees_cyl_sets_in_space[of M] prems
      by auto
    done
  finally have "X \<in> sigma_sets (space M \<times> trees (space M) \<times> trees (space M))
    {A \<times> trees_cyl B \<times> trees_cyl C | A B C. A \<in> sets M \<and> B \<in> trees (sets M) \<and> C \<in> trees (sets M) }"
    using assms by auto
  then show ?thesis
  proof induction
    case (Basic A')
    then obtain A B C where "A' = A \<times> trees_cyl B \<times> trees_cyl C"
      and *: "A \<in> sets M" "B \<in> trees (sets M)" "C \<in> trees (sets M)"
      by auto
    then have "{Node l v r |l v r. (v, l, r) \<in> A'} = trees_cyl (Node B A C)"
      by auto
    then show ?case
      by (auto simp del: trees_cyl.simps simp: sets_tree_sigma_eq intro!: sigma_sets.Basic *)
  next
    case Empty show ?case by auto
  next
    case (Compl A)
    have "{Node l v r |l v r. (v, l, r) \<in> space M \<times> trees (space M) \<times> trees (space M) - A} =
      (space (tree_sigma M) - {Node l v r |l v r. (v, l, r) \<in> A}) - {Leaf}"
      apply (auto simp: space_tree_sigma)
      subgoal for t
        by (cases t) auto
      done
    also have "\<dots> \<in> sets (tree_sigma M)"
      by (intro sets.Diff Compl) auto
    finally show ?case .
  next
    case (Union I)
    have *: "{Node l v r |l v r. (v, l, r) \<in> UNION UNIV I} =
      (\<Union>i. {Node l v r |l v r. (v, l, r) \<in> I i})" by auto
    show ?case unfolding * using Union(2) by (intro sets.countable_UN) auto
  qed
qed

lemma measurable_left[measurable]: "left \<in> tree_sigma M \<rightarrow>\<^sub>M tree_sigma M"
proof (rule measurableI)
  show "t \<in> space (tree_sigma M) \<Longrightarrow> left t \<in> space (tree_sigma M)" for t
    by (cases t) (auto simp: space_tree_sigma)
  fix A assume A: "A \<in> sets (tree_sigma M)"
  from sets.sets_into_space[OF this]
  have *: "left -` A \<inter> space (tree_sigma M) =
    (if Leaf \<in> A then {Leaf} else {}) \<union>
    {Node a v r | a v r. (v, a, r) \<in> space M \<times> A \<times> space (tree_sigma M)}"
    by (auto simp: space_tree_sigma elim: trees.cases)
  show "left -` A \<inter> space (tree_sigma M) \<in> sets (tree_sigma M)"
    unfolding * using A by (intro sets.Un Node_in_tree_sigma pair_measureI) auto
qed

lemma measurable_right[measurable]: "right \<in> tree_sigma M \<rightarrow>\<^sub>M tree_sigma M"
proof (rule measurableI)
  show "t \<in> space (tree_sigma M) \<Longrightarrow> right t \<in> space (tree_sigma M)" for t
    by (cases t) (auto simp: space_tree_sigma)
  fix A assume A: "A \<in> sets (tree_sigma M)"
  from sets.sets_into_space[OF this]
  have *: "right -` A \<inter> space (tree_sigma M) =
    (if Leaf \<in> A then {Leaf} else {}) \<union>
    {Node l v a | l v a. (v, l, a) \<in> space M \<times> space (tree_sigma M) \<times> A}"
    by (auto simp: space_tree_sigma elim: trees.cases)
  show "right -` A \<inter> space (tree_sigma M) \<in> sets (tree_sigma M)"
    unfolding * using A by (intro sets.Un Node_in_tree_sigma pair_measureI) auto
qed

lemma measurable_val': "val \<in> restrict_space (tree_sigma M) (-{Leaf}) \<rightarrow>\<^sub>M M"
proof (rule measurableI)
  show "t \<in> space (restrict_space (tree_sigma M) (- {Leaf})) \<Longrightarrow> val t \<in> space M" for t
    by (cases t) (auto simp: space_restrict_space space_tree_sigma)
  fix A assume A: "A \<in> sets M"
  from sets.sets_into_space[OF this]
  have "val -` A \<inter> space (restrict_space (tree_sigma M) (- {Leaf})) =
    {Node l a r | l a r. (a, l, r) \<in> A \<times> space (tree_sigma M) \<times> space (tree_sigma M)}"
    by (auto simp: space_tree_sigma space_restrict_space elim: trees.cases)
  also have "\<dots> \<in> sets (tree_sigma M)"
    using A by (intro sets.Un Node_in_tree_sigma pair_measureI) auto
  finally show "val -` A \<inter> space (restrict_space (tree_sigma M) (- {Leaf})) \<in>
      sets (restrict_space (tree_sigma M) (- {Leaf}))"
    by (auto simp: sets_restrict_space_iff space_restrict_space)
qed

lemma measurable_restrict_mono:
  assumes f: "f \<in> restrict_space M A \<rightarrow>\<^sub>M N" and "B \<subseteq> A"
  shows "f \<in> restrict_space M B \<rightarrow>\<^sub>M N"
by (rule measurable_compose[OF measurable_restrict_space3 f])
   (insert \<open>B \<subseteq> A\<close>, auto)

(*
lemma measurable_val[measurable (raw)]:
  assumes "f \<in> X \<rightarrow>\<^sub>M tree_sigma M"
    and "\<And>x. x \<in> space X \<Longrightarrow> f x \<noteq> Leaf"
  shows "(\<lambda>\<omega>. val (f \<omega>)) \<in> X \<rightarrow>\<^sub>M M"
  sorry
*)

lemma measurable_rec_tree[measurable (raw)]:
  assumes t: "t \<in> B \<rightarrow>\<^sub>M tree_sigma M"
  assumes l: "l \<in> B \<rightarrow>\<^sub>M A"
  assumes n: "(\<lambda>(x, l, v, r, al, ar). n x l v r al ar) \<in>
    (B \<Otimes>\<^sub>M tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M \<Otimes>\<^sub>M A \<Otimes>\<^sub>M A) \<rightarrow>\<^sub>M A" (is "?N \<in> ?M \<rightarrow>\<^sub>M A")
  shows "(\<lambda>x. rec_tree (l x) (n x) (t x)) \<in> B \<rightarrow>\<^sub>M A"
proof (rule measurable_piecewise_restrict)
  let ?C = "\<lambda>t. \<lambda>s::unit tree. t -` trees_cyl (map_tree (\<lambda>_. space M) s)"
  show "countable (range (?C t))" by (intro countable_image countableI_type)
  show "space B \<subseteq> (\<Union>s. ?C t s)"
  proof (safe; clarsimp)
    fix x assume x: "x \<in> space B" have "t x \<in> trees (space M)"
      using t[THEN measurable_space, OF x] by (simp add: space_tree_sigma)
    then show "\<exists>xa::unit tree. t x \<in> trees_cyl (map_tree (\<lambda>_. space M) xa)"
      by (intro exI[of _ "map_tree (\<lambda>_. ()) (t x)"])
         (simp add: tree.map_comp comp_def trees_cyl_map_treeI)
  qed
  fix \<Omega> assume "\<Omega> \<in> range (?C t)"
  then obtain s :: "unit tree" where \<Omega>: "\<Omega> = ?C t s" by auto
  then show "\<Omega> \<inter> space B \<in> sets B"
    by (safe intro!: measurable_sets[OF t] trees_cyl_map_in_sets)
  show "(\<lambda>x. rec_tree (l x) (n x) (t x)) \<in> restrict_space B \<Omega> \<rightarrow>\<^sub>M A"
    unfolding \<Omega> using t
  proof (induction s arbitrary: t)
    case Leaf
    show ?case
    proof (rule measurable_cong[THEN iffD2])
      fix \<omega> assume "\<omega> \<in> space (restrict_space B (?C t Leaf))"
      then show "rec_tree (l \<omega>) (n \<omega>) (t \<omega>) = l \<omega>"
        by (auto simp: space_restrict_space)
    next
      show "l \<in> restrict_space B (?C t Leaf) \<rightarrow>\<^sub>M A"
        using l by (rule measurable_restrict_space1)
    qed
  next
    case (Node ls u rs)
    let ?F = "\<lambda>\<omega>. ?N (\<omega>, left (t \<omega>), val (t \<omega>), right (t \<omega>),
        rec_tree (l \<omega>) (n \<omega>) (left (t \<omega>)), rec_tree (l \<omega>) (n \<omega>) (right (t \<omega>)))"
    show ?case
    proof (rule measurable_cong[THEN iffD2])
      fix \<omega> assume "\<omega> \<in> space (restrict_space B (?C t (Node ls u rs)))"
      then show "rec_tree (l \<omega>) (n \<omega>) (t \<omega>) = ?F \<omega>"
        by (auto simp: space_restrict_space)
    next
      show "?F \<in> (restrict_space B (?C t (Node ls u rs))) \<rightarrow>\<^sub>M A"
        apply (intro measurable_compose[OF _ n] measurable_Pair[rotated])
        subgoal
          apply (rule measurable_restrict_mono[OF Node(2)])
          apply (rule measurable_compose[OF Node(3) measurable_right])
          by auto
        subgoal
          apply (rule measurable_restrict_mono[OF Node(1)])
          apply (rule measurable_compose[OF Node(3) measurable_left])
          by auto
        subgoal
          by (rule measurable_restrict_space1)
             (rule measurable_compose[OF Node(3) measurable_right])
        subgoal
          apply (rule measurable_compose[OF _ measurable_val'])
          apply (rule measurable_restrict_space3[OF Node(3)])
          by auto
        subgoal
          by (rule measurable_restrict_space1)
             (rule measurable_compose[OF Node(3) measurable_left])
        by (rule measurable_restrict_space1) auto
    qed
  qed
qed

end
