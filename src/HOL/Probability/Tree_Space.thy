(*  Title:      HOL/Probability/Tree_Space.thy
    Author:     Johannes Hölzl, CMU *)

theory Tree_Space
  imports "HOL-Analysis.Analysis" "HOL-Library.Tree"
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
proof (intro countable_subset[OF trees_sub_lfp] countable_lfp
         sup_continuous_sup sup_continuous_const sup_continuous_id)
  show "sup_continuous (\<lambda>T. (\<Union>l\<in>T. \<Union>v\<in>A. \<Union>r\<in>T. {\<langle>l, v, r\<rangle>}))"
    unfolding sup_continuous_def
  proof (intro allI impI equalityI subsetI, goal_cases)
    case (1 M t)
    then obtain i j :: nat and l x r  where "t = Node l x r" "x \<in> A" "l \<in> M i" "r \<in> M j"
      by auto
    hence "l \<in> M (max i j)" "r \<in> M (max i j)"
      using incseqD[OF \<open>incseq M\<close>, of i "max i j"] incseqD[OF \<open>incseq M\<close>, of j "max i j"] by auto
    with \<open>t = Node l x r\<close> and \<open>x \<in> A\<close> show ?case by auto
  qed auto
qed auto

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

lemma Leaf_in_space_tree_sigma [measurable, simp, intro]: "Leaf \<in> space (tree_sigma M)"
  by (auto simp: space_tree_sigma)

lemma Leaf_in_tree_sigma [measurable, simp, intro]: "{Leaf} \<in> sets (tree_sigma M)"
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
                    {A \<times> BC |A BC. A \<in> sets M \<and> BC \<in> {A \<times> B |A B.
                       A \<in> trees_cyl ` trees (sets M) \<and> B \<in> trees_cyl ` trees (sets M)}}"
    (is "_ = sigma_sets ?X ?Y") using sets.space_closed[of M] trees_cyl_sub_trees[of _ "sets M" "space M"]
    by (subst sets_measure_of) 
       (auto simp: space_pair_measure space_tree_sigma)
  also have "?Y = {A \<times> trees_cyl B \<times> trees_cyl C | A B C. A \<in> sets M \<and> 
                     B \<in> trees (sets M) \<and> C \<in> trees (sets M)}" by blast
  finally have "X \<in> sigma_sets (space M \<times> trees (space M) \<times> trees (space M))
    {A \<times> trees_cyl B \<times> trees_cyl C | A B C. A \<in> sets M \<and> B \<in> trees (sets M) \<and> C \<in> trees (sets M) }"
    using assms by blast
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
      by (auto simp: space_tree_sigma elim: trees.cases)
    also have "\<dots> \<in> sets (tree_sigma M)"
      by (intro sets.Diff Compl) auto
    finally show ?case .
  next
    case (Union I)
    have *: "{Node l v r |l v r. (v, l, r) \<in> \<Union>(I ` UNIV)} =
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

lemma measurable_value': "value \<in> restrict_space (tree_sigma M) (-{Leaf}) \<rightarrow>\<^sub>M M"
proof (rule measurableI)
  show "t \<in> space (restrict_space (tree_sigma M) (- {Leaf})) \<Longrightarrow> value t \<in> space M" for t
    by (cases t) (auto simp: space_restrict_space space_tree_sigma)
  fix A assume A: "A \<in> sets M"
  from sets.sets_into_space[OF this]
  have "value -` A \<inter> space (restrict_space (tree_sigma M) (- {Leaf})) =
    {Node l a r | l a r. (a, l, r) \<in> A \<times> space (tree_sigma M) \<times> space (tree_sigma M)}"
    by (auto simp: space_tree_sigma space_restrict_space elim: trees.cases)
  also have "\<dots> \<in> sets (tree_sigma M)"
    using A by (intro sets.Un Node_in_tree_sigma pair_measureI) auto
  finally show "value -` A \<inter> space (restrict_space (tree_sigma M) (- {Leaf})) \<in>
      sets (restrict_space (tree_sigma M) (- {Leaf}))"
    by (auto simp: sets_restrict_space_iff space_restrict_space)
qed

lemma measurable_restrict_mono:
  assumes f: "f \<in> restrict_space M A \<rightarrow>\<^sub>M N" and "B \<subseteq> A"
  shows "f \<in> restrict_space M B \<rightarrow>\<^sub>M N"
by (rule measurable_compose[OF measurable_restrict_space3 f])
   (insert \<open>B \<subseteq> A\<close>, auto)


lemma measurable_value[measurable (raw)]:
  assumes "f \<in> X \<rightarrow>\<^sub>M tree_sigma M"
    and "\<And>x. x \<in> space X \<Longrightarrow> f x \<noteq> Leaf"
  shows "(\<lambda>\<omega>. value (f \<omega>)) \<in> X \<rightarrow>\<^sub>M M"
proof -
  from assms have "f \<in> X \<rightarrow>\<^sub>M restrict_space (tree_sigma M) (- {Leaf})"
    by (intro measurable_restrict_space2) auto
  from this and measurable_value' show ?thesis by (rule measurable_compose)
qed


lemma measurable_Node [measurable]:
  "(\<lambda>(l,x,r). Node l x r) \<in> tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M \<rightarrow>\<^sub>M tree_sigma M"
proof (rule measurable_sigma_sets)
  show "sets (tree_sigma M) = sigma_sets (trees (space M)) (trees_cyl ` trees (sets M))"
    by (simp add: sets_tree_sigma_eq)
  show "trees_cyl ` trees (sets M) \<subseteq> Pow (trees (space M))"
    by (rule trees_cyl_sets_in_space)
  show "(\<lambda>(l, x, r). \<langle>l, x, r\<rangle>) \<in> space (tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M) \<rightarrow> trees (space M)"
    by (auto simp: space_pair_measure space_tree_sigma)
  fix A assume t: "A \<in> trees_cyl ` trees (sets M)"
  then obtain t where t: "t \<in> trees (sets M)" "A = trees_cyl t" by auto
  show "(\<lambda>(l, x, r). \<langle>l, x, r\<rangle>) -` A \<inter>
         space (tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M)
         \<in> sets (tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M)"
  proof (cases t)
    case Leaf
    have "(\<lambda>(l, x, r). \<langle>l, x, r\<rangle>) -` {Leaf :: 'a tree} = {}" by auto
    with Leaf show ?thesis using t by simp
  next
    case (Node l B r)
    hence "(\<lambda>(l, x, r). \<langle>l, x, r\<rangle>) -` A \<inter> space (tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M) = 
             trees_cyl l \<times> B \<times> trees_cyl r" 
      using t and Node and trees_cyl_sub_trees[of _ "sets M" "space M"]
      by (auto simp: space_pair_measure space_tree_sigma 
               dest: sets.sets_into_space[of _ M])
    thus ?thesis using t and Node
      by (auto intro!: pair_measureI simp: sets_tree_sigma_eq)
  qed    
qed

lemma measurable_Node' [measurable (raw)]:
  assumes [measurable]: "l \<in> B \<rightarrow>\<^sub>M tree_sigma A"
  assumes [measurable]: "x \<in> B \<rightarrow>\<^sub>M A"
  assumes [measurable]: "r \<in> B \<rightarrow>\<^sub>M tree_sigma A"
  shows   "(\<lambda>y. Node (l y) (x y) (r y)) \<in> B \<rightarrow>\<^sub>M tree_sigma A"
proof -
  have "(\<lambda>y. Node (l y) (x y) (r y)) = (\<lambda>(a,b,c). Node a b c) \<circ> (\<lambda>y. (l y, x y, r y))"
    by (simp add: o_def)
  also have "\<dots> \<in> B \<rightarrow>\<^sub>M tree_sigma A"
    by (intro measurable_comp[OF _ measurable_Node]) simp_all
  finally show ?thesis .
qed  

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
    let ?F = "\<lambda>\<omega>. ?N (\<omega>, left (t \<omega>), value (t \<omega>), right (t \<omega>),
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
          apply (rule measurable_compose[OF _ measurable_value'])
          apply (rule measurable_restrict_space3[OF Node(3)])
          by auto
        subgoal
          by (rule measurable_restrict_space1)
             (rule measurable_compose[OF Node(3) measurable_left])
        by (rule measurable_restrict_space1) auto
    qed
  qed
qed

lemma measurable_case_tree [measurable (raw)]:
  assumes "t \<in> B \<rightarrow>\<^sub>M tree_sigma M"
  assumes "l \<in> B \<rightarrow>\<^sub>M A"
  assumes "(\<lambda>(x, l, v, r). n x l v r)
             \<in> B \<Otimes>\<^sub>M tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M \<rightarrow>\<^sub>M A"
  shows   "(\<lambda>x. case_tree (l x) (n x) (t x)) \<in> B \<rightarrow>\<^sub>M (A :: 'a measure)"
proof -
  define n' where "n' = (\<lambda>x l v r (_::'a) (_::'a). n x l v r)"
  have "(\<lambda>x. case_tree (l x) (n x) (t x)) = (\<lambda>x. rec_tree (l x) (n' x) (t x))"
    (is "_ = (\<lambda>x. rec_tree _ (?n' x) _)") by (rule ext) (auto split: tree.splits simp: n'_def)
  also have "\<dots> \<in> B \<rightarrow>\<^sub>M A"
  proof (rule measurable_rec_tree)
    have "(\<lambda>(x, l, v, r, al, ar). n' x l v r al ar) = 
            (\<lambda>(x,l,v,r). n x l v r) \<circ> (\<lambda>(x,l,v,r,al,ar). (x,l,v,r))" 
      by (simp add: n'_def o_def case_prod_unfold)
    also have "\<dots> \<in> B \<Otimes>\<^sub>M tree_sigma M \<Otimes>\<^sub>M M \<Otimes>\<^sub>M tree_sigma M \<Otimes>\<^sub>M A \<Otimes>\<^sub>M A \<rightarrow>\<^sub>M A"
      using assms(3) by measurable
    finally show "(\<lambda>(x, l, v, r, al, ar). n' x l v r al ar) \<in> \<dots>" .
  qed (insert assms, simp_all)
  finally show ?thesis .
qed

hide_const (open) left
hide_const (open) right

end
