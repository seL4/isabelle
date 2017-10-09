(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary topology in Euclidean space.\<close>

theory Topology_Euclidean_Space
imports
  "HOL-Library.Indicator_Function"
  "HOL-Library.Countable_Set"
  "HOL-Library.FuncSet"
  Linear_Algebra
  Norm_Arith
begin

(* FIXME: move elsewhere *)

lemma Times_eq_image_sum:
  fixes S :: "'a :: comm_monoid_add set" and T :: "'b :: comm_monoid_add set"
  shows "S \<times> T = {u + v |u v. u \<in> (\<lambda>x. (x, 0)) ` S \<and> v \<in> Pair 0 ` T}"
  by force

lemma halfspace_Int_eq:
     "{x. a \<bullet> x \<le> b} \<inter> {x. b \<le> a \<bullet> x} = {x. a \<bullet> x = b}"
     "{x. b \<le> a \<bullet> x} \<inter> {x. a \<bullet> x \<le> b} = {x. a \<bullet> x = b}"
  by auto

definition (in monoid_add) support_on :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b set"
  where "support_on s f = {x\<in>s. f x \<noteq> 0}"

lemma in_support_on: "x \<in> support_on s f \<longleftrightarrow> x \<in> s \<and> f x \<noteq> 0"
  by (simp add: support_on_def)

lemma support_on_simps[simp]:
  "support_on {} f = {}"
  "support_on (insert x s) f =
    (if f x = 0 then support_on s f else insert x (support_on s f))"
  "support_on (s \<union> t) f = support_on s f \<union> support_on t f"
  "support_on (s \<inter> t) f = support_on s f \<inter> support_on t f"
  "support_on (s - t) f = support_on s f - support_on t f"
  "support_on (f ` s) g = f ` (support_on s (g \<circ> f))"
  unfolding support_on_def by auto

lemma support_on_cong:
  "(\<And>x. x \<in> s \<Longrightarrow> f x = 0 \<longleftrightarrow> g x = 0) \<Longrightarrow> support_on s f = support_on s g"
  by (auto simp: support_on_def)

lemma support_on_if: "a \<noteq> 0 \<Longrightarrow> support_on A (\<lambda>x. if P x then a else 0) = {x\<in>A. P x}"
  by (auto simp: support_on_def)

lemma support_on_if_subset: "support_on A (\<lambda>x. if P x then a else 0) \<subseteq> {x \<in> A. P x}"
  by (auto simp: support_on_def)

lemma finite_support[intro]: "finite s \<Longrightarrow> finite (support_on s f)"
  unfolding support_on_def by auto

(* TODO: is supp_sum really needed? TODO: Generalize to Finite_Set.fold *)
definition (in comm_monoid_add) supp_sum :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  where "supp_sum f s = (\<Sum>x\<in>support_on s f. f x)"

lemma supp_sum_empty[simp]: "supp_sum f {} = 0"
  unfolding supp_sum_def by auto

lemma supp_sum_insert[simp]:
  "finite (support_on s f) \<Longrightarrow>
    supp_sum f (insert x s) = (if x \<in> s then supp_sum f s else f x + supp_sum f s)"
  by (simp add: supp_sum_def in_support_on insert_absorb)

lemma supp_sum_divide_distrib: "supp_sum f A / (r::'a::field) = supp_sum (\<lambda>n. f n / r) A"
  by (cases "r = 0")
     (auto simp: supp_sum_def sum_divide_distrib intro!: sum.cong support_on_cong)

(*END OF SUPPORT, ETC.*)

lemma image_affinity_interval:
  fixes c :: "'a::ordered_real_vector"
  shows "((\<lambda>x. m *\<^sub>R x + c) ` {a..b}) = (if {a..b}={} then {}
            else if 0 <= m then {m *\<^sub>R a + c .. m  *\<^sub>R b + c}
            else {m *\<^sub>R b + c .. m *\<^sub>R a + c})"
  apply (case_tac "m=0", force)
  apply (auto simp: scaleR_left_mono)
  apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI, auto simp: pos_le_divideR_eq le_diff_eq scaleR_left_mono_neg)
  apply (metis diff_le_eq inverse_inverse_eq order.not_eq_order_implies_strict pos_le_divideR_eq positive_imp_inverse_positive)
  apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI, auto simp: not_le neg_le_divideR_eq diff_le_eq)
  using le_diff_eq scaleR_le_cancel_left_neg
  apply fastforce
  done

lemma countable_PiE:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> countable (F i)) \<Longrightarrow> countable (Pi\<^sub>E I F)"
  by (induct I arbitrary: F rule: finite_induct) (auto simp: PiE_insert_eq)

lemma open_sums:
  fixes T :: "('b::real_normed_vector) set"
  assumes "open S \<or> open T"
  shows "open (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  using assms
proof
  assume S: "open S"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with S obtain e where "e > 0" and e: "\<And>x'. dist x' x < e \<Longrightarrow> x' \<in> S"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>y \<in> T\<close> diff_add_cancel dist_add_cancel2)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>x \<in> S\<close> by blast
  qed
next
  assume T: "open T"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with T obtain e where "e > 0" and e: "\<And>x'. dist x' y < e \<Longrightarrow> x' \<in> T"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>x \<in> S\<close> add_diff_cancel_left' add_diff_eq diff_diff_add dist_norm)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>y \<in> T\<close> by blast
  qed
qed


subsection \<open>Topological Basis\<close>

context topological_space
begin

definition "topological_basis B \<longleftrightarrow>
  (\<forall>b\<in>B. open b) \<and> (\<forall>x. open x \<longrightarrow> (\<exists>B'. B' \<subseteq> B \<and> \<Union>B' = x))"

lemma topological_basis:
  "topological_basis B \<longleftrightarrow> (\<forall>x. open x \<longleftrightarrow> (\<exists>B'. B' \<subseteq> B \<and> \<Union>B' = x))"
  unfolding topological_basis_def
  apply safe
     apply fastforce
    apply fastforce
   apply (erule_tac x=x in allE, simp)
   apply (rule_tac x="{x}" in exI, auto)
  done

lemma topological_basis_iff:
  assumes "\<And>B'. B' \<in> B \<Longrightarrow> open B'"
  shows "topological_basis B \<longleftrightarrow> (\<forall>O'. open O' \<longrightarrow> (\<forall>x\<in>O'. \<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'))"
    (is "_ \<longleftrightarrow> ?rhs")
proof safe
  fix O' and x::'a
  assume H: "topological_basis B" "open O'" "x \<in> O'"
  then have "(\<exists>B'\<subseteq>B. \<Union>B' = O')" by (simp add: topological_basis_def)
  then obtain B' where "B' \<subseteq> B" "O' = \<Union>B'" by auto
  then show "\<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'" using H by auto
next
  assume H: ?rhs
  show "topological_basis B"
    using assms unfolding topological_basis_def
  proof safe
    fix O' :: "'a set"
    assume "open O'"
    with H obtain f where "\<forall>x\<in>O'. f x \<in> B \<and> x \<in> f x \<and> f x \<subseteq> O'"
      by (force intro: bchoice simp: Bex_def)
    then show "\<exists>B'\<subseteq>B. \<Union>B' = O'"
      by (auto intro: exI[where x="{f x |x. x \<in> O'}"])
  qed
qed

lemma topological_basisI:
  assumes "\<And>B'. B' \<in> B \<Longrightarrow> open B'"
    and "\<And>O' x. open O' \<Longrightarrow> x \<in> O' \<Longrightarrow> \<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'"
  shows "topological_basis B"
  using assms by (subst topological_basis_iff) auto

lemma topological_basisE:
  fixes O'
  assumes "topological_basis B"
    and "open O'"
    and "x \<in> O'"
  obtains B' where "B' \<in> B" "x \<in> B'" "B' \<subseteq> O'"
proof atomize_elim
  from assms have "\<And>B'. B'\<in>B \<Longrightarrow> open B'"
    by (simp add: topological_basis_def)
  with topological_basis_iff assms
  show  "\<exists>B'. B' \<in> B \<and> x \<in> B' \<and> B' \<subseteq> O'"
    using assms by (simp add: Bex_def)
qed

lemma topological_basis_open:
  assumes "topological_basis B"
    and "X \<in> B"
  shows "open X"
  using assms by (simp add: topological_basis_def)

lemma topological_basis_imp_subbasis:
  assumes B: "topological_basis B"
  shows "open = generate_topology B"
proof (intro ext iffI)
  fix S :: "'a set"
  assume "open S"
  with B obtain B' where "B' \<subseteq> B" "S = \<Union>B'"
    unfolding topological_basis_def by blast
  then show "generate_topology B S"
    by (auto intro: generate_topology.intros dest: topological_basis_open)
next
  fix S :: "'a set"
  assume "generate_topology B S"
  then show "open S"
    by induct (auto dest: topological_basis_open[OF B])
qed

lemma basis_dense:
  fixes B :: "'a set set"
    and f :: "'a set \<Rightarrow> 'a"
  assumes "topological_basis B"
    and choosefrom_basis: "\<And>B'. B' \<noteq> {} \<Longrightarrow> f B' \<in> B'"
  shows "\<forall>X. open X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>B' \<in> B. f B' \<in> X)"
proof (intro allI impI)
  fix X :: "'a set"
  assume "open X" and "X \<noteq> {}"
  from topological_basisE[OF \<open>topological_basis B\<close> \<open>open X\<close> choosefrom_basis[OF \<open>X \<noteq> {}\<close>]]
  obtain B' where "B' \<in> B" "f X \<in> B'" "B' \<subseteq> X" .
  then show "\<exists>B'\<in>B. f B' \<in> X"
    by (auto intro!: choosefrom_basis)
qed

end

lemma topological_basis_prod:
  assumes A: "topological_basis A"
    and B: "topological_basis B"
  shows "topological_basis ((\<lambda>(a, b). a \<times> b) ` (A \<times> B))"
  unfolding topological_basis_def
proof (safe, simp_all del: ex_simps add: subset_image_iff ex_simps(1)[symmetric])
  fix S :: "('a \<times> 'b) set"
  assume "open S"
  then show "\<exists>X\<subseteq>A \<times> B. (\<Union>(a,b)\<in>X. a \<times> b) = S"
  proof (safe intro!: exI[of _ "{x\<in>A \<times> B. fst x \<times> snd x \<subseteq> S}"])
    fix x y
    assume "(x, y) \<in> S"
    from open_prod_elim[OF \<open>open S\<close> this]
    obtain a b where a: "open a""x \<in> a" and b: "open b" "y \<in> b" and "a \<times> b \<subseteq> S"
      by (metis mem_Sigma_iff)
    moreover
    from A a obtain A0 where "A0 \<in> A" "x \<in> A0" "A0 \<subseteq> a"
      by (rule topological_basisE)
    moreover
    from B b obtain B0 where "B0 \<in> B" "y \<in> B0" "B0 \<subseteq> b"
      by (rule topological_basisE)
    ultimately show "(x, y) \<in> (\<Union>(a, b)\<in>{X \<in> A \<times> B. fst X \<times> snd X \<subseteq> S}. a \<times> b)"
      by (intro UN_I[of "(A0, B0)"]) auto
  qed auto
qed (metis A B topological_basis_open open_Times)


subsection \<open>Countable Basis\<close>

locale countable_basis =
  fixes B :: "'a::topological_space set set"
  assumes is_basis: "topological_basis B"
    and countable_basis: "countable B"
begin

lemma open_countable_basis_ex:
  assumes "open X"
  shows "\<exists>B' \<subseteq> B. X = \<Union>B'"
  using assms countable_basis is_basis
  unfolding topological_basis_def by blast

lemma open_countable_basisE:
  assumes "open X"
  obtains B' where "B' \<subseteq> B" "X = \<Union>B'"
  using assms open_countable_basis_ex
  by atomize_elim simp

lemma countable_dense_exists:
  "\<exists>D::'a set. countable D \<and> (\<forall>X. open X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>d \<in> D. d \<in> X))"
proof -
  let ?f = "(\<lambda>B'. SOME x. x \<in> B')"
  have "countable (?f ` B)" using countable_basis by simp
  with basis_dense[OF is_basis, of ?f] show ?thesis
    by (intro exI[where x="?f ` B"]) (metis (mono_tags) all_not_in_conv imageI someI)
qed

lemma countable_dense_setE:
  obtains D :: "'a set"
  where "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d \<in> D. d \<in> X"
  using countable_dense_exists by blast

end

lemma (in first_countable_topology) first_countable_basisE:
  obtains A where "countable A" "\<And>a. a \<in> A \<Longrightarrow> x \<in> a" "\<And>a. a \<in> A \<Longrightarrow> open a"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> (\<exists>a\<in>A. a \<subseteq> S)"
  using first_countable_basis[of x]
  apply atomize_elim
  apply (elim exE)
  apply (rule_tac x="range A" in exI, auto)
  done

lemma (in first_countable_topology) first_countable_basis_Int_stableE:
  obtains A where "countable A" "\<And>a. a \<in> A \<Longrightarrow> x \<in> a" "\<And>a. a \<in> A \<Longrightarrow> open a"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> (\<exists>a\<in>A. a \<subseteq> S)"
    "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<inter> b \<in> A"
proof atomize_elim
  obtain A' where A':
    "countable A'"
    "\<And>a. a \<in> A' \<Longrightarrow> x \<in> a"
    "\<And>a. a \<in> A' \<Longrightarrow> open a"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>a\<in>A'. a \<subseteq> S"
    by (rule first_countable_basisE) blast
  define A where [abs_def]:
    "A = (\<lambda>N. \<Inter>((\<lambda>n. from_nat_into A' n) ` N)) ` (Collect finite::nat set set)"
  then show "\<exists>A. countable A \<and> (\<forall>a. a \<in> A \<longrightarrow> x \<in> a) \<and> (\<forall>a. a \<in> A \<longrightarrow> open a) \<and>
        (\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> (\<exists>a\<in>A. a \<subseteq> S)) \<and> (\<forall>a b. a \<in> A \<longrightarrow> b \<in> A \<longrightarrow> a \<inter> b \<in> A)"
  proof (safe intro!: exI[where x=A])
    show "countable A"
      unfolding A_def by (intro countable_image countable_Collect_finite)
    fix a
    assume "a \<in> A"
    then show "x \<in> a" "open a"
      using A'(4)[OF open_UNIV] by (auto simp: A_def intro: A' from_nat_into)
  next
    let ?int = "\<lambda>N. \<Inter>(from_nat_into A' ` N)"
    fix a b
    assume "a \<in> A" "b \<in> A"
    then obtain N M where "a = ?int N" "b = ?int M" "finite (N \<union> M)"
      by (auto simp: A_def)
    then show "a \<inter> b \<in> A"
      by (auto simp: A_def intro!: image_eqI[where x="N \<union> M"])
  next
    fix S
    assume "open S" "x \<in> S"
    then obtain a where a: "a\<in>A'" "a \<subseteq> S" using A' by blast
    then show "\<exists>a\<in>A. a \<subseteq> S" using a A'
      by (intro bexI[where x=a]) (auto simp: A_def intro: image_eqI[where x="{to_nat_on A' a}"])
  qed
qed

lemma (in topological_space) first_countableI:
  assumes "countable A"
    and 1: "\<And>a. a \<in> A \<Longrightarrow> x \<in> a" "\<And>a. a \<in> A \<Longrightarrow> open a"
    and 2: "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>a\<in>A. a \<subseteq> S"
  shows "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
proof (safe intro!: exI[of _ "from_nat_into A"])
  fix i
  have "A \<noteq> {}" using 2[of UNIV] by auto
  show "x \<in> from_nat_into A i" "open (from_nat_into A i)"
    using range_from_nat_into_subset[OF \<open>A \<noteq> {}\<close>] 1 by auto
next
  fix S
  assume "open S" "x\<in>S" from 2[OF this]
  show "\<exists>i. from_nat_into A i \<subseteq> S"
    using subset_range_from_nat_into[OF \<open>countable A\<close>] by auto
qed

instance prod :: (first_countable_topology, first_countable_topology) first_countable_topology
proof
  fix x :: "'a \<times> 'b"
  obtain A where A:
      "countable A"
      "\<And>a. a \<in> A \<Longrightarrow> fst x \<in> a"
      "\<And>a. a \<in> A \<Longrightarrow> open a"
      "\<And>S. open S \<Longrightarrow> fst x \<in> S \<Longrightarrow> \<exists>a\<in>A. a \<subseteq> S"
    by (rule first_countable_basisE[of "fst x"]) blast
  obtain B where B:
      "countable B"
      "\<And>a. a \<in> B \<Longrightarrow> snd x \<in> a"
      "\<And>a. a \<in> B \<Longrightarrow> open a"
      "\<And>S. open S \<Longrightarrow> snd x \<in> S \<Longrightarrow> \<exists>a\<in>B. a \<subseteq> S"
    by (rule first_countable_basisE[of "snd x"]) blast
  show "\<exists>A::nat \<Rightarrow> ('a \<times> 'b) set.
    (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (rule first_countableI[of "(\<lambda>(a, b). a \<times> b) ` (A \<times> B)"], safe)
    fix a b
    assume x: "a \<in> A" "b \<in> B"
    with A(2, 3)[of a] B(2, 3)[of b] show "x \<in> a \<times> b" and "open (a \<times> b)"
      unfolding mem_Times_iff
      by (auto intro: open_Times)
  next
    fix S
    assume "open S" "x \<in> S"
    then obtain a' b' where a'b': "open a'" "open b'" "x \<in> a' \<times> b'" "a' \<times> b' \<subseteq> S"
      by (rule open_prod_elim)
    moreover
    from a'b' A(4)[of a'] B(4)[of b']
    obtain a b where "a \<in> A" "a \<subseteq> a'" "b \<in> B" "b \<subseteq> b'"
      by auto
    ultimately
    show "\<exists>a\<in>(\<lambda>(a, b). a \<times> b) ` (A \<times> B). a \<subseteq> S"
      by (auto intro!: bexI[of _ "a \<times> b"] bexI[of _ a] bexI[of _ b])
  qed (simp add: A B)
qed

class second_countable_topology = topological_space +
  assumes ex_countable_subbasis:
    "\<exists>B::'a::topological_space set set. countable B \<and> open = generate_topology B"
begin

lemma ex_countable_basis: "\<exists>B::'a set set. countable B \<and> topological_basis B"
proof -
  from ex_countable_subbasis obtain B where B: "countable B" "open = generate_topology B"
    by blast
  let ?B = "Inter ` {b. finite b \<and> b \<subseteq> B }"

  show ?thesis
  proof (intro exI conjI)
    show "countable ?B"
      by (intro countable_image countable_Collect_finite_subset B)
    {
      fix S
      assume "open S"
      then have "\<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. (\<Union>b\<in>B'. \<Inter>b) = S"
        unfolding B
      proof induct
        case UNIV
        show ?case by (intro exI[of _ "{{}}"]) simp
      next
        case (Int a b)
        then obtain x y where x: "a = UNION x Inter" "\<And>i. i \<in> x \<Longrightarrow> finite i \<and> i \<subseteq> B"
          and y: "b = UNION y Inter" "\<And>i. i \<in> y \<Longrightarrow> finite i \<and> i \<subseteq> B"
          by blast
        show ?case
          unfolding x y Int_UN_distrib2
          by (intro exI[of _ "{i \<union> j| i j.  i \<in> x \<and> j \<in> y}"]) (auto dest: x(2) y(2))
      next
        case (UN K)
        then have "\<forall>k\<in>K. \<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. UNION B' Inter = k" by auto
        then obtain k where
            "\<forall>ka\<in>K. k ka \<subseteq> {b. finite b \<and> b \<subseteq> B} \<and> UNION (k ka) Inter = ka"
          unfolding bchoice_iff ..
        then show "\<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. UNION B' Inter = \<Union>K"
          by (intro exI[of _ "UNION K k"]) auto
      next
        case (Basis S)
        then show ?case
          by (intro exI[of _ "{{S}}"]) auto
      qed
      then have "(\<exists>B'\<subseteq>Inter ` {b. finite b \<and> b \<subseteq> B}. \<Union>B' = S)"
        unfolding subset_image_iff by blast }
    then show "topological_basis ?B"
      unfolding topological_space_class.topological_basis_def
      by (safe intro!: topological_space_class.open_Inter)
         (simp_all add: B generate_topology.Basis subset_eq)
  qed
qed

end

sublocale second_countable_topology <
  countable_basis "SOME B. countable B \<and> topological_basis B"
  using someI_ex[OF ex_countable_basis]
  by unfold_locales safe

instance prod :: (second_countable_topology, second_countable_topology) second_countable_topology
proof
  obtain A :: "'a set set" where "countable A" "topological_basis A"
    using ex_countable_basis by auto
  moreover
  obtain B :: "'b set set" where "countable B" "topological_basis B"
    using ex_countable_basis by auto
  ultimately show "\<exists>B::('a \<times> 'b) set set. countable B \<and> open = generate_topology B"
    by (auto intro!: exI[of _ "(\<lambda>(a, b). a \<times> b) ` (A \<times> B)"] topological_basis_prod
      topological_basis_imp_subbasis)
qed

instance second_countable_topology \<subseteq> first_countable_topology
proof
  fix x :: 'a
  define B :: "'a set set" where "B = (SOME B. countable B \<and> topological_basis B)"
  then have B: "countable B" "topological_basis B"
    using countable_basis is_basis
    by (auto simp: countable_basis is_basis)
  then show "\<exists>A::nat \<Rightarrow> 'a set.
    (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
    by (intro first_countableI[of "{b\<in>B. x \<in> b}"])
       (fastforce simp: topological_space_class.topological_basis_def)+
qed

instance nat :: second_countable_topology
proof
  show "\<exists>B::nat set set. countable B \<and> open = generate_topology B"
    by (intro exI[of _ "range lessThan \<union> range greaterThan"]) (auto simp: open_nat_def)
qed

lemma countable_separating_set_linorder1:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x < b \<and> b \<le> y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  define B1 where "B1 = {(LEAST x. x \<in> U)| U. U \<in> A}"
  then have "countable B1" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  define B2 where "B2 = {(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  have "\<exists>b \<in> B1 \<union> B2. x < b \<and> b \<le> y" if "x < y" for x y
  proof (cases)
    assume "\<exists>z. x < z \<and> z < y"
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    moreover have "z \<in> U" using z U_def by simp
    ultimately obtain V where "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using \<open>z \<in> V\<close> by (metis someI2)
    then have "x < w \<and> w \<le> y" using \<open>w \<in> V\<close> \<open>V \<subseteq> U\<close> U_def by fastforce
    moreover have "w \<in> B1 \<union> B2" using w_def B2_def \<open>V \<in> A\<close> by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. x < z \<and> z < y)"
    then have *: "\<And>z. z > x \<Longrightarrow> z \<ge> y" by auto
    define U where "U = {x<..}"
    then have "open U" by simp
    moreover have "y \<in> U" using \<open>x < y\<close> U_def by simp
    ultimately obtain "V" where "V \<in> A" "y \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    have "U = {y..}" unfolding U_def using * \<open>x < y\<close> by auto
    then have "V \<subseteq> {y..}" using \<open>V \<subseteq> U\<close> by simp
    then have "(LEAST w. w \<in> V) = y" using \<open>y \<in> V\<close> by (meson Least_equality atLeast_iff subsetCE)
    then have "y \<in> B1 \<union> B2" using \<open>V \<in> A\<close> B1_def by auto
    moreover have "x < y \<and> y \<le> y" using \<open>x < y\<close> by simp
    ultimately show ?thesis by auto
  qed
  moreover have "countable (B1 \<union> B2)" using \<open>countable B1\<close> \<open>countable B2\<close> by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_linorder2:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x \<le> b \<and> b < y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  define B1 where "B1 = {(GREATEST x. x \<in> U) | U. U \<in> A}"
  then have "countable B1" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  define B2 where "B2 = {(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  have "\<exists>b \<in> B1 \<union> B2. x \<le> b \<and> b < y" if "x < y" for x y
  proof (cases)
    assume "\<exists>z. x < z \<and> z < y"
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    moreover have "z \<in> U" using z U_def by simp
    ultimately obtain "V" where "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using \<open>z \<in> V\<close> by (metis someI2)
    then have "x \<le> w \<and> w < y" using \<open>w \<in> V\<close> \<open>V \<subseteq> U\<close> U_def by fastforce
    moreover have "w \<in> B1 \<union> B2" using w_def B2_def \<open>V \<in> A\<close> by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. x < z \<and> z < y)"
    then have *: "\<And>z. z < y \<Longrightarrow> z \<le> x" using leI by blast
    define U where "U = {..<y}"
    then have "open U" by simp
    moreover have "x \<in> U" using \<open>x < y\<close> U_def by simp
    ultimately obtain "V" where "V \<in> A" "x \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    have "U = {..x}" unfolding U_def using * \<open>x < y\<close> by auto
    then have "V \<subseteq> {..x}" using \<open>V \<subseteq> U\<close> by simp
    then have "(GREATEST x. x \<in> V) = x" using \<open>x \<in> V\<close> by (meson Greatest_equality atMost_iff subsetCE)
    then have "x \<in> B1 \<union> B2" using \<open>V \<in> A\<close> B1_def by auto
    moreover have "x \<le> x \<and> x < y" using \<open>x < y\<close> by simp
    ultimately show ?thesis by auto
  qed
  moreover have "countable (B1 \<union> B2)" using \<open>countable B1\<close> \<open>countable B2\<close> by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_dense_linorder:
  shows "\<exists>B::('a::{linorder_topology, dense_linorder, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x < b \<and> b < y))"
proof -
  obtain B::"'a set" where B: "countable B" "\<And>x y. x < y \<Longrightarrow> (\<exists>b \<in> B. x < b \<and> b \<le> y)"
    using countable_separating_set_linorder1 by auto
  have "\<exists>b \<in> B. x < b \<and> b < y" if "x < y" for x y
  proof -
    obtain z where "x < z" "z < y" using \<open>x < y\<close> dense by blast
    then obtain b where "b \<in> B" "x < b \<and> b \<le> z" using B(2) by auto
    then have "x < b \<and> b < y" using \<open>z < y\<close> by auto
    then show ?thesis using \<open>b \<in> B\<close> by auto
  qed
  then show ?thesis using B(1) by auto
qed

subsection \<open>Polish spaces\<close>

text \<open>Textbooks define Polish spaces as completely metrizable.
  We assume the topology to be complete for a given metric.\<close>

class polish_space = complete_space + second_countable_topology

subsection \<open>General notion of a topology as a value\<close>

definition "istopology L \<longleftrightarrow>
  L {} \<and> (\<forall>S T. L S \<longrightarrow> L T \<longrightarrow> L (S \<inter> T)) \<and> (\<forall>K. Ball K L \<longrightarrow> L (\<Union>K))"

typedef 'a topology = "{L::('a set) \<Rightarrow> bool. istopology L}"
  morphisms "openin" "topology"
  unfolding istopology_def by blast

lemma istopology_openin[intro]: "istopology(openin U)"
  using openin[of U] by blast

lemma topology_inverse': "istopology U \<Longrightarrow> openin (topology U) = U"
  using topology_inverse[unfolded mem_Collect_eq] .

lemma topology_inverse_iff: "istopology U \<longleftrightarrow> openin (topology U) = U"
  using topology_inverse[of U] istopology_openin[of "topology U"] by auto

lemma topology_eq: "T1 = T2 \<longleftrightarrow> (\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S)"
proof
  assume "T1 = T2"
  then show "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S" by simp
next
  assume H: "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S"
  then have "openin T1 = openin T2" by (simp add: fun_eq_iff)
  then have "topology (openin T1) = topology (openin T2)" by simp
  then show "T1 = T2" unfolding openin_inverse .
qed

text\<open>Infer the "universe" from union of all sets in the topology.\<close>

definition "topspace T = \<Union>{S. openin T S}"

subsubsection \<open>Main properties of open sets\<close>

lemma openin_clauses:
  fixes U :: "'a topology"
  shows
    "openin U {}"
    "\<And>S T. openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S\<inter>T)"
    "\<And>K. (\<forall>S \<in> K. openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin[of U] unfolding istopology_def mem_Collect_eq by fast+

lemma openin_subset[intro]: "openin U S \<Longrightarrow> S \<subseteq> topspace U"
  unfolding topspace_def by blast

lemma openin_empty[simp]: "openin U {}"
  by (rule openin_clauses)

lemma openin_Int[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<inter> T)"
  by (rule openin_clauses)

lemma openin_Union[intro]: "(\<And>S. S \<in> K \<Longrightarrow> openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin_clauses by blast

lemma openin_Un[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<union> T)"
  using openin_Union[of "{S,T}" U] by auto

lemma openin_topspace[intro, simp]: "openin U (topspace U)"
  by (force simp: openin_Union topspace_def)

lemma openin_subopen: "openin U S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>T. openin U T \<and> x \<in> T \<and> T \<subseteq> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by auto
next
  assume H: ?rhs
  let ?t = "\<Union>{T. openin U T \<and> T \<subseteq> S}"
  have "openin U ?t" by (force simp: openin_Union)
  also have "?t = S" using H by auto
  finally show "openin U S" .
qed

lemma openin_INT [intro]:
  assumes "finite I"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T ((\<Inter>i \<in> I. U i) \<inter> topspace T)"
using assms by (induct, auto simp: inf_sup_aci(2) openin_Int)

lemma openin_INT2 [intro]:
  assumes "finite I" "I \<noteq> {}"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T (\<Inter>i \<in> I. U i)"
proof -
  have "(\<Inter>i \<in> I. U i) \<subseteq> topspace T"
    using \<open>I \<noteq> {}\<close> openin_subset[OF assms(3)] by auto
  then show ?thesis
    using openin_INT[of _ _ U, OF assms(1) assms(3)] by (simp add: inf.absorb2 inf_commute)
qed

lemma openin_Inter [intro]:
  assumes "finite \<F>" "\<F> \<noteq> {}" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (\<Inter>\<F>)"
  by (metis (full_types) assms openin_INT2 image_ident)


subsubsection \<open>Closed sets\<close>

definition "closedin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> openin U (topspace U - S)"

lemma closedin_subset: "closedin U S \<Longrightarrow> S \<subseteq> topspace U"
  by (metis closedin_def)

lemma closedin_empty[simp]: "closedin U {}"
  by (simp add: closedin_def)

lemma closedin_topspace[intro, simp]: "closedin U (topspace U)"
  by (simp add: closedin_def)

lemma closedin_Un[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<union> T)"
  by (auto simp: Diff_Un closedin_def)

lemma Diff_Inter[intro]: "A - \<Inter>S = \<Union>{A - s|s. s\<in>S}"
  by auto

lemma closedin_Union:
  assumes "finite S" "\<And>T. T \<in> S \<Longrightarrow> closedin U T"
    shows "closedin U (\<Union>S)"
  using assms by induction auto

lemma closedin_Inter[intro]:
  assumes Ke: "K \<noteq> {}"
    and Kc: "\<And>S. S \<in>K \<Longrightarrow> closedin U S"
  shows "closedin U (\<Inter>K)"
  using Ke Kc unfolding closedin_def Diff_Inter by auto

lemma closedin_INT[intro]:
  assumes "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> closedin U (B x)"
  shows "closedin U (\<Inter>x\<in>A. B x)"
  apply (rule closedin_Inter)
  using assms
  apply auto
  done

lemma closedin_Int[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<inter> T)"
  using closedin_Inter[of "{S,T}" U] by auto

lemma openin_closedin_eq: "openin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> closedin U (topspace U - S)"
  apply (auto simp: closedin_def Diff_Diff_Int inf_absorb2)
  apply (metis openin_subset subset_eq)
  done

lemma openin_closedin: "S \<subseteq> topspace U \<Longrightarrow> (openin U S \<longleftrightarrow> closedin U (topspace U - S))"
  by (simp add: openin_closedin_eq)

lemma openin_diff[intro]:
  assumes oS: "openin U S"
    and cT: "closedin U T"
  shows "openin U (S - T)"
proof -
  have "S - T = S \<inter> (topspace U - T)" using openin_subset[of U S]  oS cT
    by (auto simp: topspace_def openin_subset)
  then show ?thesis using oS cT
    by (auto simp: closedin_def)
qed

lemma closedin_diff[intro]:
  assumes oS: "closedin U S"
    and cT: "openin U T"
  shows "closedin U (S - T)"
proof -
  have "S - T = S \<inter> (topspace U - T)"
    using closedin_subset[of U S] oS cT by (auto simp: topspace_def)
  then show ?thesis
    using oS cT by (auto simp: openin_closedin_eq)
qed


subsubsection \<open>Subspace topology\<close>

definition "subtopology U V = topology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"

lemma istopology_subtopology: "istopology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"
  (is "istopology ?L")
proof -
  have "?L {}" by blast
  {
    fix A B
    assume A: "?L A" and B: "?L B"
    from A B obtain Sa and Sb where Sa: "openin U Sa" "A = Sa \<inter> V" and Sb: "openin U Sb" "B = Sb \<inter> V"
      by blast
    have "A \<inter> B = (Sa \<inter> Sb) \<inter> V" "openin U (Sa \<inter> Sb)"
      using Sa Sb by blast+
    then have "?L (A \<inter> B)" by blast
  }
  moreover
  {
    fix K
    assume K: "K \<subseteq> Collect ?L"
    have th0: "Collect ?L = (\<lambda>S. S \<inter> V) ` Collect (openin U)"
      by blast
    from K[unfolded th0 subset_image_iff]
    obtain Sk where Sk: "Sk \<subseteq> Collect (openin U)" "K = (\<lambda>S. S \<inter> V) ` Sk"
      by blast
    have "\<Union>K = (\<Union>Sk) \<inter> V"
      using Sk by auto
    moreover have "openin U (\<Union>Sk)"
      using Sk by (auto simp: subset_eq)
    ultimately have "?L (\<Union>K)" by blast
  }
  ultimately show ?thesis
    unfolding subset_eq mem_Collect_eq istopology_def by auto
qed

lemma openin_subtopology: "openin (subtopology U V) S \<longleftrightarrow> (\<exists>T. openin U T \<and> S = T \<inter> V)"
  unfolding subtopology_def topology_inverse'[OF istopology_subtopology]
  by auto

lemma topspace_subtopology: "topspace (subtopology U V) = topspace U \<inter> V"
  by (auto simp: topspace_def openin_subtopology)

lemma closedin_subtopology: "closedin (subtopology U V) S \<longleftrightarrow> (\<exists>T. closedin U T \<and> S = T \<inter> V)"
  unfolding closedin_def topspace_subtopology
  by (auto simp: openin_subtopology)

lemma openin_subtopology_refl: "openin (subtopology U V) V \<longleftrightarrow> V \<subseteq> topspace U"
  unfolding openin_subtopology
  by auto (metis IntD1 in_mono openin_subset)

lemma subtopology_superset:
  assumes UV: "topspace U \<subseteq> V"
  shows "subtopology U V = U"
proof -
  {
    fix S
    {
      fix T
      assume T: "openin U T" "S = T \<inter> V"
      from T openin_subset[OF T(1)] UV have eq: "S = T"
        by blast
      have "openin U S"
        unfolding eq using T by blast
    }
    moreover
    {
      assume S: "openin U S"
      then have "\<exists>T. openin U T \<and> S = T \<inter> V"
        using openin_subset[OF S] UV by auto
    }
    ultimately have "(\<exists>T. openin U T \<and> S = T \<inter> V) \<longleftrightarrow> openin U S"
      by blast
  }
  then show ?thesis
    unfolding topology_eq openin_subtopology by blast
qed

lemma subtopology_topspace[simp]: "subtopology U (topspace U) = U"
  by (simp add: subtopology_superset)

lemma subtopology_UNIV[simp]: "subtopology U UNIV = U"
  by (simp add: subtopology_superset)

lemma openin_subtopology_empty:
   "openin (subtopology U {}) S \<longleftrightarrow> S = {}"
by (metis Int_empty_right openin_empty openin_subtopology)

lemma closedin_subtopology_empty:
   "closedin (subtopology U {}) S \<longleftrightarrow> S = {}"
by (metis Int_empty_right closedin_empty closedin_subtopology)

lemma closedin_subtopology_refl [simp]:
   "closedin (subtopology U X) X \<longleftrightarrow> X \<subseteq> topspace U"
by (metis closedin_def closedin_topspace inf.absorb_iff2 le_inf_iff topspace_subtopology)

lemma openin_imp_subset:
   "openin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
by (metis Int_iff openin_subtopology subsetI)

lemma closedin_imp_subset:
   "closedin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
by (simp add: closedin_def topspace_subtopology)

lemma openin_subtopology_Un:
    "openin (subtopology U T) S \<and> openin (subtopology U u) S
     \<Longrightarrow> openin (subtopology U (T \<union> u)) S"
by (simp add: openin_subtopology) blast


subsubsection \<open>The standard Euclidean topology\<close>

definition euclidean :: "'a::topological_space topology"
  where "euclidean = topology open"

lemma open_openin: "open S \<longleftrightarrow> openin euclidean S"
  unfolding euclidean_def
  apply (rule cong[where x=S and y=S])
  apply (rule topology_inverse[symmetric])
  apply (auto simp: istopology_def)
  done

declare open_openin [symmetric, simp]

lemma topspace_euclidean [simp]: "topspace euclidean = UNIV"
  by (force simp: topspace_def)

lemma topspace_euclidean_subtopology[simp]: "topspace (subtopology euclidean S) = S"
  by (simp add: topspace_subtopology)

lemma closed_closedin: "closed S \<longleftrightarrow> closedin euclidean S"
  by (simp add: closed_def closedin_def Compl_eq_Diff_UNIV)

lemma open_subopen: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S)"
  using openI by auto

lemma openin_subtopology_self [simp]: "openin (subtopology euclidean S) S"
  by (metis openin_topspace topspace_euclidean_subtopology)

text \<open>Basic "localization" results are handy for connectedness.\<close>

lemma openin_open: "openin (subtopology euclidean U) S \<longleftrightarrow> (\<exists>T. open T \<and> (S = U \<inter> T))"
  by (auto simp: openin_subtopology)

lemma openin_Int_open:
   "\<lbrakk>openin (subtopology euclidean U) S; open T\<rbrakk>
        \<Longrightarrow> openin (subtopology euclidean U) (S \<inter> T)"
by (metis open_Int Int_assoc openin_open)

lemma openin_open_Int[intro]: "open S \<Longrightarrow> openin (subtopology euclidean U) (U \<inter> S)"
  by (auto simp: openin_open)

lemma open_openin_trans[trans]:
  "open S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> openin (subtopology euclidean S) T"
  by (metis Int_absorb1  openin_open_Int)

lemma open_subset: "S \<subseteq> T \<Longrightarrow> open S \<Longrightarrow> openin (subtopology euclidean T) S"
  by (auto simp: openin_open)

lemma closedin_closed: "closedin (subtopology euclidean U) S \<longleftrightarrow> (\<exists>T. closed T \<and> S = U \<inter> T)"
  by (simp add: closedin_subtopology closed_closedin Int_ac)

lemma closedin_closed_Int: "closed S \<Longrightarrow> closedin (subtopology euclidean U) (U \<inter> S)"
  by (metis closedin_closed)

lemma closed_subset: "S \<subseteq> T \<Longrightarrow> closed S \<Longrightarrow> closedin (subtopology euclidean T) S"
  by (auto simp: closedin_closed)

lemma closedin_closed_subset:
 "\<lbrakk>closedin (subtopology euclidean U) V; T \<subseteq> U; S = V \<inter> T\<rbrakk>
             \<Longrightarrow> closedin (subtopology euclidean T) S"
  by (metis (no_types, lifting) Int_assoc Int_commute closedin_closed inf.orderE)

lemma finite_imp_closedin:
  fixes S :: "'a::t1_space set"
  shows "\<lbrakk>finite S; S \<subseteq> T\<rbrakk> \<Longrightarrow> closedin (subtopology euclidean T) S"
    by (simp add: finite_imp_closed closed_subset)

lemma closedin_singleton [simp]:
  fixes a :: "'a::t1_space"
  shows "closedin (subtopology euclidean U) {a} \<longleftrightarrow> a \<in> U"
using closedin_subset  by (force intro: closed_subset)

lemma openin_euclidean_subtopology_iff:
  fixes S U :: "'a::metric_space set"
  shows "openin (subtopology euclidean U) S \<longleftrightarrow>
    S \<subseteq> U \<and> (\<forall>x\<in>S. \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x'\<in> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding openin_open open_dist by blast
next
  define T where "T = {x. \<exists>a\<in>S. \<exists>d>0. (\<forall>y\<in>U. dist y a < d \<longrightarrow> y \<in> S) \<and> dist x a < d}"
  have 1: "\<forall>x\<in>T. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> T"
    unfolding T_def
    apply clarsimp
    apply (rule_tac x="d - dist x a" in exI)
    apply (clarsimp simp add: less_diff_eq)
    by (metis dist_commute dist_triangle_lt)
  assume ?rhs then have 2: "S = U \<inter> T"
    unfolding T_def
    by auto (metis dist_self)
  from 1 2 show ?lhs
    unfolding openin_open open_dist by fast
qed

lemma connected_openin:
      "connected s \<longleftrightarrow>
       ~(\<exists>e1 e2. openin (subtopology euclidean s) e1 \<and>
                 openin (subtopology euclidean s) e2 \<and>
                 s \<subseteq> e1 \<union> e2 \<and> e1 \<inter> e2 = {} \<and> e1 \<noteq> {} \<and> e2 \<noteq> {})"
  apply (simp add: connected_def openin_open, safe)
  apply (simp_all, blast+)  (* SLOW *)
  done

lemma connected_openin_eq:
      "connected s \<longleftrightarrow>
       ~(\<exists>e1 e2. openin (subtopology euclidean s) e1 \<and>
                 openin (subtopology euclidean s) e2 \<and>
                 e1 \<union> e2 = s \<and> e1 \<inter> e2 = {} \<and>
                 e1 \<noteq> {} \<and> e2 \<noteq> {})"
  apply (simp add: connected_openin, safe, blast)
  by (metis Int_lower1 Un_subset_iff openin_open subset_antisym)

lemma connected_closedin:
      "connected s \<longleftrightarrow>
       ~(\<exists>e1 e2.
             closedin (subtopology euclidean s) e1 \<and>
             closedin (subtopology euclidean s) e2 \<and>
             s \<subseteq> e1 \<union> e2 \<and> e1 \<inter> e2 = {} \<and>
             e1 \<noteq> {} \<and> e2 \<noteq> {})"
proof -
  { fix A B x x'
    assume s_sub: "s \<subseteq> A \<union> B"
       and disj: "A \<inter> B \<inter> s = {}"
       and x: "x \<in> s" "x \<in> B" and x': "x' \<in> s" "x' \<in> A"
       and cl: "closed A" "closed B"
    assume "\<forall>e1. (\<forall>T. closed T \<longrightarrow> e1 \<noteq> s \<inter> T) \<or> (\<forall>e2. e1 \<inter> e2 = {} \<longrightarrow> s \<subseteq> e1 \<union> e2 \<longrightarrow> (\<forall>T. closed T \<longrightarrow> e2 \<noteq> s \<inter> T) \<or> e1 = {} \<or> e2 = {})"
    then have "\<And>C D. s \<inter> C = {} \<or> s \<inter> D = {} \<or> s \<inter> (C \<inter> (s \<inter> D)) \<noteq> {} \<or> \<not> s \<subseteq> s \<inter> (C \<union> D) \<or> \<not> closed C \<or> \<not> closed D"
      by (metis (no_types) Int_Un_distrib Int_assoc)
    moreover have "s \<inter> (A \<inter> B) = {}" "s \<inter> (A \<union> B) = s" "s \<inter> B \<noteq> {}"
      using disj s_sub x by blast+
    ultimately have "s \<inter> A = {}"
      using cl by (metis inf.left_commute inf_bot_right order_refl)
    then have False
      using x' by blast
  } note * = this
  show ?thesis
    apply (simp add: connected_closed closedin_closed)
    apply (safe; simp)
    apply blast
    apply (blast intro: *)
    done
qed

lemma connected_closedin_eq:
      "connected s \<longleftrightarrow>
           ~(\<exists>e1 e2.
                 closedin (subtopology euclidean s) e1 \<and>
                 closedin (subtopology euclidean s) e2 \<and>
                 e1 \<union> e2 = s \<and> e1 \<inter> e2 = {} \<and>
                 e1 \<noteq> {} \<and> e2 \<noteq> {})"
  apply (simp add: connected_closedin, safe, blast)
  by (metis Int_lower1 Un_subset_iff closedin_closed subset_antisym)

text \<open>These "transitivity" results are handy too\<close>

lemma openin_trans[trans]:
  "openin (subtopology euclidean T) S \<Longrightarrow> openin (subtopology euclidean U) T \<Longrightarrow>
    openin (subtopology euclidean U) S"
  unfolding open_openin openin_open by blast

lemma openin_open_trans: "openin (subtopology euclidean T) S \<Longrightarrow> open T \<Longrightarrow> open S"
  by (auto simp: openin_open intro: openin_trans)

lemma closedin_trans[trans]:
  "closedin (subtopology euclidean T) S \<Longrightarrow> closedin (subtopology euclidean U) T \<Longrightarrow>
    closedin (subtopology euclidean U) S"
  by (auto simp: closedin_closed closed_closedin closed_Inter Int_assoc)

lemma closedin_closed_trans: "closedin (subtopology euclidean T) S \<Longrightarrow> closed T \<Longrightarrow> closed S"
  by (auto simp: closedin_closed intro: closedin_trans)

lemma openin_subtopology_Int_subset:
   "\<lbrakk>openin (subtopology euclidean u) (u \<inter> S); v \<subseteq> u\<rbrakk> \<Longrightarrow> openin (subtopology euclidean v) (v \<inter> S)"
  by (auto simp: openin_subtopology)

lemma openin_open_eq: "open s \<Longrightarrow> (openin (subtopology euclidean s) t \<longleftrightarrow> open t \<and> t \<subseteq> s)"
  using open_subset openin_open_trans openin_subset by fastforce


subsection \<open>Open and closed balls\<close>

definition ball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "ball x e = {y. dist x y < e}"

definition cball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "cball x e = {y. dist x y \<le> e}"

definition sphere :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "sphere x e = {y. dist x y = e}"

lemma mem_ball [simp]: "y \<in> ball x e \<longleftrightarrow> dist x y < e"
  by (simp add: ball_def)

lemma mem_cball [simp]: "y \<in> cball x e \<longleftrightarrow> dist x y \<le> e"
  by (simp add: cball_def)

lemma mem_sphere [simp]: "y \<in> sphere x e \<longleftrightarrow> dist x y = e"
  by (simp add: sphere_def)

lemma ball_trivial [simp]: "ball x 0 = {}"
  by (simp add: ball_def)

lemma cball_trivial [simp]: "cball x 0 = {x}"
  by (simp add: cball_def)

lemma sphere_trivial [simp]: "sphere x 0 = {x}"
  by (simp add: sphere_def)

lemma mem_ball_0 [simp]: "x \<in> ball 0 e \<longleftrightarrow> norm x < e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma mem_cball_0 [simp]: "x \<in> cball 0 e \<longleftrightarrow> norm x \<le> e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma disjoint_ballI: "dist x y \<ge> r+s \<Longrightarrow> ball x r \<inter> ball y s = {}"
  using dist_triangle_less_add not_le by fastforce

lemma disjoint_cballI: "dist x y > r + s \<Longrightarrow> cball x r \<inter> cball y s = {}"
  by (metis add_mono disjoint_iff_not_equal dist_triangle2 dual_order.trans leD mem_cball)

lemma mem_sphere_0 [simp]: "x \<in> sphere 0 e \<longleftrightarrow> norm x = e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma sphere_empty [simp]: "r < 0 \<Longrightarrow> sphere a r = {}"
  for a :: "'a::metric_space"
  by auto

lemma centre_in_ball [simp]: "x \<in> ball x e \<longleftrightarrow> 0 < e"
  by simp

lemma centre_in_cball [simp]: "x \<in> cball x e \<longleftrightarrow> 0 \<le> e"
  by simp

lemma ball_subset_cball [simp, intro]: "ball x e \<subseteq> cball x e"
  by (simp add: subset_eq)

lemma sphere_cball [simp,intro]: "sphere z r \<subseteq> cball z r"
  by force

lemma cball_diff_sphere: "cball a r - sphere a r = ball a r"
  by auto

lemma subset_ball[intro]: "d \<le> e \<Longrightarrow> ball x d \<subseteq> ball x e"
  by (simp add: subset_eq)

lemma subset_cball[intro]: "d \<le> e \<Longrightarrow> cball x d \<subseteq> cball x e"
  by (simp add: subset_eq)

lemma ball_max_Un: "ball a (max r s) = ball a r \<union> ball a s"
  by (simp add: set_eq_iff) arith

lemma ball_min_Int: "ball a (min r s) = ball a r \<inter> ball a s"
  by (simp add: set_eq_iff)

lemma cball_max_Un: "cball a (max r s) = cball a r \<union> cball a s"
  by (simp add: set_eq_iff) arith

lemma cball_min_Int: "cball a (min r s) = cball a r \<inter> cball a s"
  by (simp add: set_eq_iff)

lemma cball_diff_eq_sphere: "cball a r - ball a r =  sphere a r"
  by (auto simp: cball_def ball_def dist_commute)

lemma image_add_ball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "op + b ` ball a r = ball (a+b) r"
apply (intro equalityI subsetI)
apply (force simp: dist_norm)
apply (rule_tac x="x-b" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma image_add_cball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "op + b ` cball a r = cball (a+b) r"
apply (intro equalityI subsetI)
apply (force simp: dist_norm)
apply (rule_tac x="x-b" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma open_ball [intro, simp]: "open (ball x e)"
proof -
  have "open (dist x -` {..<e})"
    by (intro open_vimage open_lessThan continuous_intros)
  also have "dist x -` {..<e} = ball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_ball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. ball x e \<subseteq> S)"
  by (simp add: open_dist subset_eq mem_ball Ball_def dist_commute)

lemma openI [intro?]: "(\<And>x. x\<in>S \<Longrightarrow> \<exists>e>0. ball x e \<subseteq> S) \<Longrightarrow> open S"
  by (auto simp: open_contains_ball)

lemma openE[elim?]:
  assumes "open S" "x\<in>S"
  obtains e where "e>0" "ball x e \<subseteq> S"
  using assms unfolding open_contains_ball by auto

lemma open_contains_ball_eq: "open S \<Longrightarrow> x\<in>S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  by (metis open_contains_ball subset_eq centre_in_ball)

lemma openin_contains_ball:
    "openin (subtopology euclidean t) s \<longleftrightarrow>
     s \<subseteq> t \<and> (\<forall>x \<in> s. \<exists>e. 0 < e \<and> ball x e \<inter> t \<subseteq> s)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: openin_open)
    apply (metis Int_commute Int_mono inf.cobounded2 open_contains_ball order_refl subsetCE)
    done
next
  assume ?rhs
  then show ?lhs
    apply (simp add: openin_euclidean_subtopology_iff)
    by (metis (no_types) Int_iff dist_commute inf.absorb_iff2 mem_ball)
qed

lemma openin_contains_cball:
   "openin (subtopology euclidean t) s \<longleftrightarrow>
        s \<subseteq> t \<and>
        (\<forall>x \<in> s. \<exists>e. 0 < e \<and> cball x e \<inter> t \<subseteq> s)"
apply (simp add: openin_contains_ball)
apply (rule iffI)
apply (auto dest!: bspec)
apply (rule_tac x="e/2" in exI, force+)
done

lemma ball_eq_empty[simp]: "ball x e = {} \<longleftrightarrow> e \<le> 0"
  unfolding mem_ball set_eq_iff
  apply (simp add: not_less)
  apply (metis zero_le_dist order_trans dist_self)
  done

lemma ball_empty: "e \<le> 0 \<Longrightarrow> ball x e = {}" by simp

lemma euclidean_dist_l2:
  fixes x y :: "'a :: euclidean_space"
  shows "dist x y = setL2 (\<lambda>i. dist (x \<bullet> i) (y \<bullet> i)) Basis"
  unfolding dist_norm norm_eq_sqrt_inner setL2_def
  by (subst euclidean_inner) (simp add: power2_eq_square inner_diff_left)

lemma eventually_nhds_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>x. x \<in> ball z d) (nhds z)"
  by (rule eventually_nhds_in_open) simp_all

lemma eventually_at_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>t. t \<in> ball z d \<and> t \<in> A) (at z within A)"
  unfolding eventually_at by (intro exI[of _ d]) (simp_all add: dist_commute)

lemma eventually_at_ball': "d > 0 \<Longrightarrow> eventually (\<lambda>t. t \<in> ball z d \<and> t \<noteq> z \<and> t \<in> A) (at z within A)"
  unfolding eventually_at by (intro exI[of _ d]) (simp_all add: dist_commute)


subsection \<open>Boxes\<close>

abbreviation One :: "'a::euclidean_space"
  where "One \<equiv> \<Sum>Basis"

lemma One_non_0: assumes "One = (0::'a::euclidean_space)" shows False
proof -
  have "dependent (Basis :: 'a set)"
    apply (simp add: dependent_finite)
    apply (rule_tac x="\<lambda>i. 1" in exI)
    using SOME_Basis apply (auto simp: assms)
    done
  with independent_Basis show False by force
qed

corollary One_neq_0[iff]: "One \<noteq> 0"
  by (metis One_non_0)

corollary Zero_neq_One[iff]: "0 \<noteq> One"
  by (metis One_non_0)

definition (in euclidean_space) eucl_less (infix "<e" 50)
  where "eucl_less a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < b \<bullet> i)"

definition box_eucl_less: "box a b = {x. a <e x \<and> x <e b}"
definition "cbox a b = {x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i}"

lemma box_def: "box a b = {x. \<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i}"
  and in_box_eucl_less: "x \<in> box a b \<longleftrightarrow> a <e x \<and> x <e b"
  and mem_box: "x \<in> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i)"
    "x \<in> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i)"
  by (auto simp: box_eucl_less eucl_less_def cbox_def)

lemma cbox_Pair_eq: "cbox (a, c) (b, d) = cbox a b \<times> cbox c d"
  by (force simp: cbox_def Basis_prod_def)

lemma cbox_Pair_iff [iff]: "(x, y) \<in> cbox (a, c) (b, d) \<longleftrightarrow> x \<in> cbox a b \<and> y \<in> cbox c d"
  by (force simp: cbox_Pair_eq)

lemma cbox_Complex_eq: "cbox (Complex a c) (Complex b d) = (\<lambda>(x,y). Complex x y) ` (cbox a b \<times> cbox c d)"
  apply (auto simp: cbox_def Basis_complex_def)
  apply (rule_tac x = "(Re x, Im x)" in image_eqI)
  using complex_eq by auto

lemma cbox_Pair_eq_0: "cbox (a, c) (b, d) = {} \<longleftrightarrow> cbox a b = {} \<or> cbox c d = {}"
  by (force simp: cbox_Pair_eq)

lemma swap_cbox_Pair [simp]: "prod.swap ` cbox (c, a) (d, b) = cbox (a,c) (b,d)"
  by auto

lemma mem_box_real[simp]:
  "(x::real) \<in> box a b \<longleftrightarrow> a < x \<and> x < b"
  "(x::real) \<in> cbox a b \<longleftrightarrow> a \<le> x \<and> x \<le> b"
  by (auto simp: mem_box)

lemma box_real[simp]:
  fixes a b:: real
  shows "box a b = {a <..< b}" "cbox a b = {a .. b}"
  by auto

lemma box_Int_box:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<inter> box c d =
    box (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box by auto

lemma rational_boxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> box a b \<and> box a b \<subseteq> ball x e"
proof -
  define e' where "e' = e / (2 * sqrt (real (DIM ('a))))"
  then have e: "e' > 0"
    using assms by (auto simp: DIM_positive)
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x \<bullet> i \<and> x \<bullet> i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i - e'" "x \<bullet> i"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain a where
    a: "\<forall>xa. a xa \<in> \<rat> \<and> a xa < x \<bullet> xa \<and> x \<bullet> xa - a xa < e'" ..
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x \<bullet> i < y \<and> y - x \<bullet> i < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i" "x \<bullet> i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain b where
    b: "\<forall>xa. b xa \<in> \<rat> \<and> x \<bullet> xa < b xa \<and> b xa - x \<bullet> xa < e'" ..
  let ?a = "\<Sum>i\<in>Basis. a i *\<^sub>R i" and ?b = "\<Sum>i\<in>Basis. b i *\<^sub>R i"
  show ?thesis
  proof (rule exI[of _ ?a], rule exI[of _ ?b], safe)
    fix y :: 'a
    assume *: "y \<in> box ?a ?b"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      unfolding setL2_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>(i::'a)\<in>Basis. e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule sum_strict_mono)
      fix i :: "'a"
      assume i: "i \<in> Basis"
      have "a i < y\<bullet>i \<and> y\<bullet>i < b i"
        using * i by (auto simp: box_def)
      moreover have "a i < x\<bullet>i" "x\<bullet>i - a i < e'"
        using a by auto
      moreover have "x\<bullet>i < b i" "b i - x\<bullet>i < e'"
        using b by auto
      ultimately have "\<bar>x\<bullet>i - y\<bullet>i\<bar> < 2 * e'"
        by auto
      then have "dist (x \<bullet> i) (y \<bullet> i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < (e/sqrt (real (DIM('a))))\<^sup>2"
        by (rule power_strict_mono) auto
      then show "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < e\<^sup>2 / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e"
      using \<open>0 < e\<close> by simp
    finally show "y \<in> ball x e"
      by (auto simp: ball_def)
  qed (insert a b, auto simp: box_def)
qed

lemma open_UNION_box:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f :: 'a \<Rightarrow> real \<times> real. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. box (a' f) (b' f))"
proof -
  have "x \<in> (\<Union>f\<in>I. box (a' f) (b' f))" if "x \<in> M" for x
  proof -
    obtain e where e: "e > 0" "ball x e \<subseteq> M"
      using openE[OF \<open>open M\<close> \<open>x \<in> M\<close>] by auto
    moreover obtain a b where ab:
      "x \<in> box a b"
      "\<forall>i \<in> Basis. a \<bullet> i \<in> \<rat>"
      "\<forall>i\<in>Basis. b \<bullet> i \<in> \<rat>"
      "box a b \<subseteq> ball x e"
      using rational_boxes[OF e(1)] by metis
    ultimately show ?thesis
       by (intro UN_I[of "\<lambda>i\<in>Basis. (a \<bullet> i, b \<bullet> i)"])
          (auto simp: euclidean_representation I_def a'_def b'_def)
  qed
  then show ?thesis by (auto simp: I_def)
qed

corollary open_countable_Union_open_box:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = box a b" "\<Union>\<D> = S"
proof -
  let ?a = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  let ?b = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  let ?I = "{f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. box (?a f) (?b f) \<subseteq> S}"
  let ?\<D> = "(\<lambda>f. box (?a f) (?b f)) ` ?I"
  show ?thesis
  proof
    have "countable ?I"
      by (simp add: countable_PiE countable_rat)
    then show "countable ?\<D>"
      by blast
    show "\<Union>?\<D> = S"
      using open_UNION_box [OF assms] by metis
  qed auto
qed

lemma rational_cboxes:
  fixes x :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<exists>a b. (\<forall>i\<in>Basis. a \<bullet> i \<in> \<rat> \<and> b \<bullet> i \<in> \<rat>) \<and> x \<in> cbox a b \<and> cbox a b \<subseteq> ball x e"
proof -
  define e' where "e' = e / (2 * sqrt (real (DIM ('a))))"
  then have e: "e' > 0"
    using assms by auto
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> y < x \<bullet> i \<and> x \<bullet> i - y < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i - e'" "x \<bullet> i"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain a where
    a: "\<forall>u. a u \<in> \<rat> \<and> a u < x \<bullet> u \<and> x \<bullet> u - a u < e'" ..
  have "\<forall>i. \<exists>y. y \<in> \<rat> \<and> x \<bullet> i < y \<and> y - x \<bullet> i < e'" (is "\<forall>i. ?th i")
  proof
    fix i
    from Rats_dense_in_real[of "x \<bullet> i" "x \<bullet> i + e'"] e
    show "?th i" by auto
  qed
  from choice[OF this] obtain b where
    b: "\<forall>u. b u \<in> \<rat> \<and> x \<bullet> u < b u \<and> b u - x \<bullet> u < e'" ..
  let ?a = "\<Sum>i\<in>Basis. a i *\<^sub>R i" and ?b = "\<Sum>i\<in>Basis. b i *\<^sub>R i"
  show ?thesis
  proof (rule exI[of _ ?a], rule exI[of _ ?b], safe)
    fix y :: 'a
    assume *: "y \<in> cbox ?a ?b"
    have "dist x y = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2)"
      unfolding setL2_def[symmetric] by (rule euclidean_dist_l2)
    also have "\<dots> < sqrt (\<Sum>(i::'a)\<in>Basis. e^2 / real (DIM('a)))"
    proof (rule real_sqrt_less_mono, rule sum_strict_mono)
      fix i :: "'a"
      assume i: "i \<in> Basis"
      have "a i \<le> y\<bullet>i \<and> y\<bullet>i \<le> b i"
        using * i by (auto simp: cbox_def)
      moreover have "a i < x\<bullet>i" "x\<bullet>i - a i < e'"
        using a by auto
      moreover have "x\<bullet>i < b i" "b i - x\<bullet>i < e'"
        using b by auto
      ultimately have "\<bar>x\<bullet>i - y\<bullet>i\<bar> < 2 * e'"
        by auto
      then have "dist (x \<bullet> i) (y \<bullet> i) < e/sqrt (real (DIM('a)))"
        unfolding e'_def by (auto simp: dist_real_def)
      then have "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < (e/sqrt (real (DIM('a))))\<^sup>2"
        by (rule power_strict_mono) auto
      then show "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 < e\<^sup>2 / real DIM('a)"
        by (simp add: power_divide)
    qed auto
    also have "\<dots> = e"
      using \<open>0 < e\<close> by simp
    finally show "y \<in> ball x e"
      by (auto simp: ball_def)
  next
    show "x \<in> cbox (\<Sum>i\<in>Basis. a i *\<^sub>R i) (\<Sum>i\<in>Basis. b i *\<^sub>R i)"
      using a b less_imp_le by (auto simp: cbox_def)
  qed (use a b cbox_def in auto)
qed

lemma open_UNION_cbox:
  fixes M :: "'a::euclidean_space set"
  assumes "open M"
  defines "a' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  defines "b' \<equiv> \<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  defines "I \<equiv> {f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (a' f) (b' f) \<subseteq> M}"
  shows "M = (\<Union>f\<in>I. cbox (a' f) (b' f))"
proof -
  have "x \<in> (\<Union>f\<in>I. cbox (a' f) (b' f))" if "x \<in> M" for x
  proof -
    obtain e where e: "e > 0" "ball x e \<subseteq> M"
      using openE[OF \<open>open M\<close> \<open>x \<in> M\<close>] by auto
    moreover obtain a b where ab: "x \<in> cbox a b" "\<forall>i \<in> Basis. a \<bullet> i \<in> \<rat>"
                                  "\<forall>i \<in> Basis. b \<bullet> i \<in> \<rat>" "cbox a b \<subseteq> ball x e"
      using rational_cboxes[OF e(1)] by metis
    ultimately show ?thesis
       by (intro UN_I[of "\<lambda>i\<in>Basis. (a \<bullet> i, b \<bullet> i)"])
          (auto simp: euclidean_representation I_def a'_def b'_def)
  qed
  then show ?thesis by (auto simp: I_def)
qed

corollary open_countable_Union_open_cbox:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S"
  obtains \<D> where "countable \<D>" "\<D> \<subseteq> Pow S" "\<And>X. X \<in> \<D> \<Longrightarrow> \<exists>a b. X = cbox a b" "\<Union>\<D> = S"
proof -
  let ?a = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. fst (f i) *\<^sub>R i)"
  let ?b = "\<lambda>f. (\<Sum>(i::'a)\<in>Basis. snd (f i) *\<^sub>R i)"
  let ?I = "{f\<in>Basis \<rightarrow>\<^sub>E \<rat> \<times> \<rat>. cbox (?a f) (?b f) \<subseteq> S}"
  let ?\<D> = "(\<lambda>f. cbox (?a f) (?b f)) ` ?I"
  show ?thesis
  proof
    have "countable ?I"
      by (simp add: countable_PiE countable_rat)
    then show "countable ?\<D>"
      by blast
    show "\<Union>?\<D> = S"
      using open_UNION_cbox [OF assms] by metis
  qed auto
qed

lemma box_eq_empty:
  fixes a :: "'a::euclidean_space"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i < a\<bullet>i))" (is ?th2)
proof -
  {
    fix i x
    assume i: "i\<in>Basis" and as:"b\<bullet>i \<le> a\<bullet>i" and x:"x\<in>box a b"
    then have "a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i"
      unfolding mem_box by (auto simp: box_def)
    then have "a\<bullet>i < b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as: "\<forall>i\<in>Basis. \<not> (b\<bullet>i \<le> a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "a\<bullet>i < b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i < ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i < b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "box a b \<noteq> {}"
      using mem_box(1)[of "?x" a b] by auto
  }
  ultimately show ?th1 by blast

  {
    fix i x
    assume i: "i \<in> Basis" and as:"b\<bullet>i < a\<bullet>i" and x:"x\<in>cbox a b"
    then have "a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
      unfolding mem_box by auto
    then have "a\<bullet>i \<le> b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as:"\<forall>i\<in>Basis. \<not> (b\<bullet>i < a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i:"i \<in> Basis"
      have "a\<bullet>i \<le> b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i \<le> ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i \<le> b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "cbox a b \<noteq> {}"
      using mem_box(2)[of "?x" a b] by auto
  }
  ultimately show ?th2 by blast
qed

lemma box_ne_empty:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i)"
  and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  unfolding box_eq_empty[of a b] by fastforce+

lemma
  fixes a :: "'a::euclidean_space"
  shows cbox_sing [simp]: "cbox a a = {a}"
    and box_sing [simp]: "box a a = {}"
  unfolding set_eq_iff mem_box eq_iff [symmetric]
  by (auto intro!: euclidean_eqI[where 'a='a])
     (metis all_not_in_conv nonempty_Basis)

lemma subset_box_imp:
  fixes a :: "'a::euclidean_space"
  shows "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> cbox a b"
     and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box
  by (best intro: order_trans less_le_trans le_less_trans less_imp_le)+

lemma box_subset_cbox:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<subseteq> cbox a b"
  unfolding subset_eq [unfolded Ball_def] mem_box
  by (fast intro: less_imp_le)

lemma subset_box:
  fixes a :: "'a::euclidean_space"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) \<longrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th4)
proof -
  show ?th1
    unfolding subset_eq and Ball_def and mem_box
    by (auto intro: order_trans)
  show ?th2
    unfolding subset_eq and Ball_def and mem_box
    by (auto intro: le_less_trans less_le_trans order_trans less_imp_le)
  {
    assume as: "box c d \<subseteq> cbox a b" "\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i"
    then have "box c d \<noteq> {}"
      unfolding box_eq_empty by auto
    fix i :: 'a
    assume i: "i \<in> Basis"
    (** TODO combine the following two parts as done in the HOL_light version. **)
    {
      let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((min (a\<bullet>j) (d\<bullet>j))+c\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume as2: "a\<bullet>i > c\<bullet>i"
      {
        fix j :: 'a
        assume j: "j \<in> Basis"
        then have "c \<bullet> j < ?x \<bullet> j \<and> ?x \<bullet> j < d \<bullet> j"
          apply (cases "j = i")
          using as(2)[THEN bspec[where x=j]] i
          apply (auto simp: as2)
          done
      }
      then have "?x\<in>box c d"
        using i unfolding mem_box by auto
      moreover
      have "?x \<notin> cbox a b"
        unfolding mem_box
        apply auto
        apply (rule_tac x=i in bexI)
        using as(2)[THEN bspec[where x=i]] and as2 i
        apply auto
        done
      ultimately have False using as by auto
    }
    then have "a\<bullet>i \<le> c\<bullet>i" by (rule ccontr) auto
    moreover
    {
      let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((max (b\<bullet>j) (c\<bullet>j))+d\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume as2: "b\<bullet>i < d\<bullet>i"
      {
        fix j :: 'a
        assume "j\<in>Basis"
        then have "d \<bullet> j > ?x \<bullet> j \<and> ?x \<bullet> j > c \<bullet> j"
          apply (cases "j = i")
          using as(2)[THEN bspec[where x=j]]
          apply (auto simp: as2)
          done
      }
      then have "?x\<in>box c d"
        unfolding mem_box by auto
      moreover
      have "?x\<notin>cbox a b"
        unfolding mem_box
        apply auto
        apply (rule_tac x=i in bexI)
        using as(2)[THEN bspec[where x=i]] and as2 using i
        apply auto
        done
      ultimately have False using as by auto
    }
    then have "b\<bullet>i \<ge> d\<bullet>i" by (rule ccontr) auto
    ultimately
    have "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i" by auto
  } note part1 = this
  show ?th3
    unfolding subset_eq and Ball_def and mem_box
    apply (rule, rule, rule, rule)
    apply (rule part1)
    unfolding subset_eq and Ball_def and mem_box
    prefer 4
    apply auto
    apply (erule_tac x=xa in allE, erule_tac x=xa in allE, fastforce)+
    done
  {
    assume as: "box c d \<subseteq> box a b" "\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i"
    fix i :: 'a
    assume i:"i\<in>Basis"
    from as(1) have "box c d \<subseteq> cbox a b"
      using box_subset_cbox[of a b] by auto
    then have "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
      using part1 and as(2) using i by auto
  } note * = this
  show ?th4
    unfolding subset_eq and Ball_def and mem_box
    apply (rule, rule, rule, rule)
    apply (rule *)
    unfolding subset_eq and Ball_def and mem_box
    prefer 4
    apply auto
    apply (erule_tac x=xa in allE, simp)+
    done
qed

lemma eq_cbox: "cbox a b = cbox c d \<longleftrightarrow> cbox a b = {} \<and> cbox c d = {} \<or> a = c \<and> b = d"
      (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "cbox a b \<subseteq> cbox c d" "cbox c d \<subseteq> cbox a b"
    by auto
  then show ?rhs
    by (force simp: subset_box box_eq_empty intro: antisym euclidean_eqI)
next
  assume ?rhs
  then show ?lhs
    by force
qed

lemma eq_cbox_box [simp]: "cbox a b = box c d \<longleftrightarrow> cbox a b = {} \<and> box c d = {}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "cbox a b \<subseteq> box c d" "box c d \<subseteq>cbox a b"
    by auto
  then show ?rhs
    apply (simp add: subset_box)
    using \<open>cbox a b = box c d\<close> box_ne_empty box_sing
    apply (fastforce simp add:)
    done
next
  assume ?rhs
  then show ?lhs
    by force
qed

lemma eq_box_cbox [simp]: "box a b = cbox c d \<longleftrightarrow> box a b = {} \<and> cbox c d = {}"
  by (metis eq_cbox_box)

lemma eq_box: "box a b = box c d \<longleftrightarrow> box a b = {} \<and> box c d = {} \<or> a = c \<and> b = d"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "box a b \<subseteq> box c d" "box c d \<subseteq> box a b"
    by auto
  then show ?rhs
    apply (simp add: subset_box)
    using box_ne_empty(2) \<open>box a b = box c d\<close>
    apply auto
     apply (meson euclidean_eqI less_eq_real_def not_less)+
    done
next
  assume ?rhs
  then show ?lhs
    by force
qed

lemma subset_box_complex:
   "cbox a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "cbox a b \<subseteq> box c d \<longleftrightarrow>
      (Re a \<le> Re b \<and> Im a \<le> Im b) \<longrightarrow> Re a > Re c \<and> Im a > Im c \<and> Re b < Re d \<and> Im b < Im d"
   "box a b \<subseteq> cbox c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
   "box a b \<subseteq> box c d \<longleftrightarrow>
      (Re a < Re b \<and> Im a < Im b) \<longrightarrow> Re a \<ge> Re c \<and> Im a \<ge> Im c \<and> Re b \<le> Re d \<and> Im b \<le> Im d"
  by (subst subset_box; force simp: Basis_complex_def)+

lemma Int_interval:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d =
    cbox (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box
  by auto

lemma disjoint_interval:
  fixes a::"'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i < c\<bullet>i \<or> d\<bullet>i < a\<bullet>i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th4)
proof -
  let ?z = "(\<Sum>i\<in>Basis. (((max (a\<bullet>i) (c\<bullet>i)) + (min (b\<bullet>i) (d\<bullet>i))) / 2) *\<^sub>R i)::'a"
  have **: "\<And>P Q. (\<And>i :: 'a. i \<in> Basis \<Longrightarrow> Q ?z i \<Longrightarrow> P i) \<Longrightarrow>
      (\<And>i x :: 'a. i \<in> Basis \<Longrightarrow> P i \<Longrightarrow> Q x i) \<Longrightarrow> (\<forall>x. \<exists>i\<in>Basis. Q x i) \<longleftrightarrow> (\<exists>i\<in>Basis. P i)"
    by blast
  note * = set_eq_iff Int_iff empty_iff mem_box ball_conj_distrib[symmetric] eq_False ball_simps(10)
  show ?th1 unfolding * by (intro **) auto
  show ?th2 unfolding * by (intro **) auto
  show ?th3 unfolding * by (intro **) auto
  show ?th4 unfolding * by (intro **) auto
qed

lemma UN_box_eq_UNIV: "(\<Union>i::nat. box (- (real i *\<^sub>R One)) (real i *\<^sub>R One)) = UNIV"
proof -
  have "\<bar>x \<bullet> b\<bar> < real_of_int (\<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil> + 1)"
    if [simp]: "b \<in> Basis" for x b :: 'a
  proof -
    have "\<bar>x \<bullet> b\<bar> \<le> real_of_int \<lceil>\<bar>x \<bullet> b\<bar>\<rceil>"
      by (rule le_of_int_ceiling)
    also have "\<dots> \<le> real_of_int \<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil>"
      by (auto intro!: ceiling_mono)
    also have "\<dots> < real_of_int (\<lceil>Max ((\<lambda>b. \<bar>x \<bullet> b\<bar>)`Basis)\<rceil> + 1)"
      by simp
    finally show ?thesis .
  qed
  then have "\<exists>n::nat. \<forall>b\<in>Basis. \<bar>x \<bullet> b\<bar> < real n" for x :: 'a
    by (metis order.strict_trans reals_Archimedean2)
  moreover have "\<And>x b::'a. \<And>n::nat.  \<bar>x \<bullet> b\<bar> < real n \<longleftrightarrow> - real n < x \<bullet> b \<and> x \<bullet> b < real n"
    by auto
  ultimately show ?thesis
    by (auto simp: box_def inner_sum_left inner_Basis sum.If_cases)
qed

text \<open>Intervals in general, including infinite and mixtures of open and closed.\<close>

definition "is_interval (s::('a::euclidean_space) set) \<longleftrightarrow>
  (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i\<in>Basis. ((a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i) \<or> (b\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> a\<bullet>i))) \<longrightarrow> x \<in> s)"

lemma is_interval_cbox [simp]: "is_interval (cbox a (b::'a::euclidean_space))" (is ?th1)
  and is_interval_box [simp]: "is_interval (box a b)" (is ?th2)
  unfolding is_interval_def mem_box Ball_def atLeastAtMost_iff
  by (meson order_trans le_less_trans less_le_trans less_trans)+

lemma is_interval_empty [iff]: "is_interval {}"
  unfolding is_interval_def  by simp

lemma is_interval_univ [iff]: "is_interval UNIV"
  unfolding is_interval_def  by simp

lemma mem_is_intervalI:
  assumes "is_interval s"
    and "a \<in> s" "b \<in> s"
    and "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i \<or> b \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i"
  shows "x \<in> s"
  by (rule assms(1)[simplified is_interval_def, rule_format, OF assms(2,3,4)])

lemma interval_subst:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
    and "x \<in> S" "y j \<in> S"
    and "j \<in> Basis"
  shows "(\<Sum>i\<in>Basis. (if i = j then y i \<bullet> i else x \<bullet> i) *\<^sub>R i) \<in> S"
  by (rule mem_is_intervalI[OF assms(1,2)]) (auto simp: assms)

lemma mem_box_componentwiseI:
  fixes S::"'a::euclidean_space set"
  assumes "is_interval S"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<in> ((\<lambda>x. x \<bullet> i) ` S)"
  shows "x \<in> S"
proof -
  from assms have "\<forall>i \<in> Basis. \<exists>s \<in> S. x \<bullet> i = s \<bullet> i"
    by auto
  with finite_Basis obtain s and bs::"'a list"
    where s: "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i = s i \<bullet> i" "\<And>i. i \<in> Basis \<Longrightarrow> s i \<in> S"
      and bs: "set bs = Basis" "distinct bs"
    by (metis finite_distinct_list)
  from nonempty_Basis s obtain j where j: "j \<in> Basis" "s j \<in> S"
    by blast
  define y where
    "y = rec_list (s j) (\<lambda>j _ Y. (\<Sum>i\<in>Basis. (if i = j then s i \<bullet> i else Y \<bullet> i) *\<^sub>R i))"
  have "x = (\<Sum>i\<in>Basis. (if i \<in> set bs then s i \<bullet> i else s j \<bullet> i) *\<^sub>R i)"
    using bs by (auto simp: s(1)[symmetric] euclidean_representation)
  also have [symmetric]: "y bs = \<dots>"
    using bs(2) bs(1)[THEN equalityD1]
    by (induct bs) (auto simp: y_def euclidean_representation intro!: euclidean_eqI[where 'a='a])
  also have "y bs \<in> S"
    using bs(1)[THEN equalityD1]
    apply (induct bs)
     apply (auto simp: y_def j)
    apply (rule interval_subst[OF assms(1)])
      apply (auto simp: s)
    done
  finally show ?thesis .
qed

lemma cbox01_nonempty [simp]: "cbox 0 One \<noteq> {}"
  by (simp add: box_ne_empty inner_Basis inner_sum_left sum_nonneg)

lemma box01_nonempty [simp]: "box 0 One \<noteq> {}"
  by (simp add: box_ne_empty inner_Basis inner_sum_left)

lemma empty_as_interval: "{} = cbox One (0::'a::euclidean_space)"
  using nonempty_Basis box01_nonempty box_eq_empty(1) box_ne_empty(1) by blast

lemma interval_subset_is_interval:
  assumes "is_interval S"
  shows "cbox a b \<subseteq> S \<longleftrightarrow> cbox a b = {} \<or> a \<in> S \<and> b \<in> S" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs  using box_ne_empty(1) mem_box(2) by fastforce
next
  assume ?rhs
  have "cbox a b \<subseteq> S" if "a \<in> S" "b \<in> S"
    using assms unfolding is_interval_def
    apply (clarsimp simp add: mem_box)
    using that by blast
  with \<open>?rhs\<close> show ?lhs
    by blast
qed


subsection \<open>Connectedness\<close>

lemma connected_local:
 "connected S \<longleftrightarrow>
  \<not> (\<exists>e1 e2.
      openin (subtopology euclidean S) e1 \<and>
      openin (subtopology euclidean S) e2 \<and>
      S \<subseteq> e1 \<union> e2 \<and>
      e1 \<inter> e2 = {} \<and>
      e1 \<noteq> {} \<and>
      e2 \<noteq> {})"
  unfolding connected_def openin_open
  by safe blast+

lemma exists_diff:
  fixes P :: "'a set \<Rightarrow> bool"
  shows "(\<exists>S. P (- S)) \<longleftrightarrow> (\<exists>S. P S)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have ?rhs if ?lhs
    using that by blast
  moreover have "P (- (- S))" if "P S" for S
  proof -
    have "S = - (- S)" by simp
    with that show ?thesis by metis
  qed
  ultimately show ?thesis by metis
qed

lemma connected_clopen: "connected S \<longleftrightarrow>
  (\<forall>T. openin (subtopology euclidean S) T \<and>
     closedin (subtopology euclidean S) T \<longrightarrow> T = {} \<or> T = S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "\<not> connected S \<longleftrightarrow>
    (\<exists>e1 e2. open e1 \<and> open (- e2) \<and> S \<subseteq> e1 \<union> (- e2) \<and> e1 \<inter> (- e2) \<inter> S = {} \<and> e1 \<inter> S \<noteq> {} \<and> (- e2) \<inter> S \<noteq> {})"
    unfolding connected_def openin_open closedin_closed
    by (metis double_complement)
  then have th0: "connected S \<longleftrightarrow>
    \<not> (\<exists>e2 e1. closed e2 \<and> open e1 \<and> S \<subseteq> e1 \<union> (- e2) \<and> e1 \<inter> (- e2) \<inter> S = {} \<and> e1 \<inter> S \<noteq> {} \<and> (- e2) \<inter> S \<noteq> {})"
    (is " _ \<longleftrightarrow> \<not> (\<exists>e2 e1. ?P e2 e1)")
    by (simp add: closed_def) metis
  have th1: "?rhs \<longleftrightarrow> \<not> (\<exists>t' t. closed t'\<and>t = S\<inter>t' \<and> t\<noteq>{} \<and> t\<noteq>S \<and> (\<exists>t'. open t' \<and> t = S \<inter> t'))"
    (is "_ \<longleftrightarrow> \<not> (\<exists>t' t. ?Q t' t)")
    unfolding connected_def openin_open closedin_closed by auto
  have "(\<exists>e1. ?P e2 e1) \<longleftrightarrow> (\<exists>t. ?Q e2 t)" for e2
  proof -
    have "?P e2 e1 \<longleftrightarrow> (\<exists>t. closed e2 \<and> t = S\<inter>e2 \<and> open e1 \<and> t = S\<inter>e1 \<and> t\<noteq>{} \<and> t \<noteq> S)" for e1
      by auto
    then show ?thesis
      by metis
  qed
  then have "\<forall>e2. (\<exists>e1. ?P e2 e1) \<longleftrightarrow> (\<exists>t. ?Q e2 t)"
    by blast
  then show ?thesis
    by (simp add: th0 th1)
qed


subsection \<open>Limit points\<close>

definition (in topological_space) islimpt:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infixr "islimpt" 60)
  where "x islimpt S \<longleftrightarrow> (\<forall>T. x\<in>T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x))"

lemma islimptI:
  assumes "\<And>T. x \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>y\<in>S. y \<in> T \<and> y \<noteq> x"
  shows "x islimpt S"
  using assms unfolding islimpt_def by auto

lemma islimptE:
  assumes "x islimpt S" and "x \<in> T" and "open T"
  obtains y where "y \<in> S" and "y \<in> T" and "y \<noteq> x"
  using assms unfolding islimpt_def by auto

lemma islimpt_iff_eventually: "x islimpt S \<longleftrightarrow> \<not> eventually (\<lambda>y. y \<notin> S) (at x)"
  unfolding islimpt_def eventually_at_topological by auto

lemma islimpt_subset: "x islimpt S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> x islimpt T"
  unfolding islimpt_def by fast

lemma islimpt_approachable:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e)"
  unfolding islimpt_iff_eventually eventually_at by fast

lemma islimpt_approachable_le: "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> S. x' \<noteq> x \<and> dist x' x \<le> e)"
  for x :: "'a::metric_space"
  unfolding islimpt_approachable
  using approachable_lt_le [where f="\<lambda>y. dist y x" and P="\<lambda>y. y \<notin> S \<or> y = x",
    THEN arg_cong [where f=Not]]
  by (simp add: Bex_def conj_commute conj_left_commute)

lemma islimpt_UNIV_iff: "x islimpt UNIV \<longleftrightarrow> \<not> open {x}"
  unfolding islimpt_def by (safe, fast, case_tac "T = {x}", fast, fast)

lemma islimpt_punctured: "x islimpt S = x islimpt (S-{x})"
  unfolding islimpt_def by blast

text \<open>A perfect space has no isolated points.\<close>

lemma islimpt_UNIV [simp, intro]: "x islimpt UNIV"
  for x :: "'a::perfect_space"
  unfolding islimpt_UNIV_iff by (rule not_open_singleton)

lemma perfect_choose_dist: "0 < r \<Longrightarrow> \<exists>a. a \<noteq> x \<and> dist a x < r"
  for x :: "'a::{perfect_space,metric_space}"
  using islimpt_UNIV [of x] by (simp add: islimpt_approachable)

lemma closed_limpt: "closed S \<longleftrightarrow> (\<forall>x. x islimpt S \<longrightarrow> x \<in> S)"
  unfolding closed_def
  apply (subst open_subopen)
  apply (simp add: islimpt_def subset_eq)
  apply (metis ComplE ComplI)
  done

lemma islimpt_EMPTY[simp]: "\<not> x islimpt {}"
  by (auto simp: islimpt_def)

lemma finite_set_avoid:
  fixes a :: "'a::metric_space"
  assumes fS: "finite S"
  shows "\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<longrightarrow> d \<le> dist a x"
proof (induct rule: finite_induct[OF fS])
  case 1
  then show ?case by (auto intro: zero_less_one)
next
  case (2 x F)
  from 2 obtain d where d: "d > 0" "\<forall>x\<in>F. x \<noteq> a \<longrightarrow> d \<le> dist a x"
    by blast
  show ?case
  proof (cases "x = a")
    case True
    with d show ?thesis by auto
  next
    case False
    let ?d = "min d (dist a x)"
    from False d(1) have dp: "?d > 0"
      by auto
    from d have d': "\<forall>x\<in>F. x \<noteq> a \<longrightarrow> ?d \<le> dist a x"
      by auto
    with dp False show ?thesis
      by (auto intro!: exI[where x="?d"])
  qed
qed

lemma islimpt_Un: "x islimpt (S \<union> T) \<longleftrightarrow> x islimpt S \<or> x islimpt T"
  by (simp add: islimpt_iff_eventually eventually_conj_iff)

lemma discrete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes e: "0 < e"
    and d: "\<forall>x \<in> S. \<forall>y \<in> S. dist y x < e \<longrightarrow> y = x"
  shows "closed S"
proof -
  have False if C: "\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e" for x
  proof -
    from e have e2: "e/2 > 0" by arith
    from C[rule_format, OF e2] obtain y where y: "y \<in> S" "y \<noteq> x" "dist y x < e/2"
      by blast
    let ?m = "min (e/2) (dist x y) "
    from e2 y(2) have mp: "?m > 0"
      by simp
    from C[rule_format, OF mp] obtain z where z: "z \<in> S" "z \<noteq> x" "dist z x < ?m"
      by blast
    from z y have "dist z y < e"
      by (intro dist_triangle_lt [where z=x]) simp
    from d[rule_format, OF y(1) z(1) this] y z show ?thesis
      by (auto simp: dist_commute)
  qed
  then show ?thesis
    by (metis islimpt_approachable closed_limpt [where 'a='a])
qed

lemma closed_of_nat_image: "closed (of_nat ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_nat)

lemma closed_of_int_image: "closed (of_int ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_int)

lemma closed_Nats [simp]: "closed (\<nat> :: 'a :: real_normed_algebra_1 set)"
  unfolding Nats_def by (rule closed_of_nat_image)

lemma closed_Ints [simp]: "closed (\<int> :: 'a :: real_normed_algebra_1 set)"
  unfolding Ints_def by (rule closed_of_int_image)

lemma closed_subset_Ints:
  fixes A :: "'a :: real_normed_algebra_1 set"
  assumes "A \<subseteq> \<int>"
  shows   "closed A"
proof (intro discrete_imp_closed[OF zero_less_one] ballI impI, goal_cases)
  case (1 x y)
  with assms have "x \<in> \<int>" and "y \<in> \<int>" by auto
  with \<open>dist y x < 1\<close> show "y = x"
    by (auto elim!: Ints_cases simp: dist_of_int)
qed


subsection \<open>Interior of a Set\<close>

definition "interior S = \<Union>{T. open T \<and> T \<subseteq> S}"

lemma interiorI [intro?]:
  assumes "open T" and "x \<in> T" and "T \<subseteq> S"
  shows "x \<in> interior S"
  using assms unfolding interior_def by fast

lemma interiorE [elim?]:
  assumes "x \<in> interior S"
  obtains T where "open T" and "x \<in> T" and "T \<subseteq> S"
  using assms unfolding interior_def by fast

lemma open_interior [simp, intro]: "open (interior S)"
  by (simp add: interior_def open_Union)

lemma interior_subset: "interior S \<subseteq> S"
  by (auto simp: interior_def)

lemma interior_maximal: "T \<subseteq> S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> interior S"
  by (auto simp: interior_def)

lemma interior_open: "open S \<Longrightarrow> interior S = S"
  by (intro equalityI interior_subset interior_maximal subset_refl)

lemma interior_eq: "interior S = S \<longleftrightarrow> open S"
  by (metis open_interior interior_open)

lemma open_subset_interior: "open S \<Longrightarrow> S \<subseteq> interior T \<longleftrightarrow> S \<subseteq> T"
  by (metis interior_maximal interior_subset subset_trans)

lemma interior_empty [simp]: "interior {} = {}"
  using open_empty by (rule interior_open)

lemma interior_UNIV [simp]: "interior UNIV = UNIV"
  using open_UNIV by (rule interior_open)

lemma interior_interior [simp]: "interior (interior S) = interior S"
  using open_interior by (rule interior_open)

lemma interior_mono: "S \<subseteq> T \<Longrightarrow> interior S \<subseteq> interior T"
  by (auto simp: interior_def)

lemma interior_unique:
  assumes "T \<subseteq> S" and "open T"
  assumes "\<And>T'. T' \<subseteq> S \<Longrightarrow> open T' \<Longrightarrow> T' \<subseteq> T"
  shows "interior S = T"
  by (intro equalityI assms interior_subset open_interior interior_maximal)

lemma interior_singleton [simp]: "interior {a} = {}"
  for a :: "'a::perfect_space"
  apply (rule interior_unique, simp_all)
  using not_open_singleton subset_singletonD
  apply fastforce
  done

lemma interior_Int [simp]: "interior (S \<inter> T) = interior S \<inter> interior T"
  by (intro equalityI Int_mono Int_greatest interior_mono Int_lower1
    Int_lower2 interior_maximal interior_subset open_Int open_interior)

lemma mem_interior: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  using open_contains_ball_eq [where S="interior S"]
  by (simp add: open_subset_interior)

lemma eventually_nhds_in_nhd: "x \<in> interior s \<Longrightarrow> eventually (\<lambda>y. y \<in> s) (nhds x)"
  using interior_subset[of s] by (subst eventually_nhds) blast

lemma interior_limit_point [intro]:
  fixes x :: "'a::perfect_space"
  assumes x: "x \<in> interior S"
  shows "x islimpt S"
  using x islimpt_UNIV [of x]
  unfolding interior_def islimpt_def
  apply (clarsimp, rename_tac T T')
  apply (drule_tac x="T \<inter> T'" in spec)
  apply (auto simp: open_Int)
  done

lemma interior_closed_Un_empty_interior:
  assumes cS: "closed S"
    and iT: "interior T = {}"
  shows "interior (S \<union> T) = interior S"
proof
  show "interior S \<subseteq> interior (S \<union> T)"
    by (rule interior_mono) (rule Un_upper1)
  show "interior (S \<union> T) \<subseteq> interior S"
  proof
    fix x
    assume "x \<in> interior (S \<union> T)"
    then obtain R where "open R" "x \<in> R" "R \<subseteq> S \<union> T" ..
    show "x \<in> interior S"
    proof (rule ccontr)
      assume "x \<notin> interior S"
      with \<open>x \<in> R\<close> \<open>open R\<close> obtain y where "y \<in> R - S"
        unfolding interior_def by fast
      from \<open>open R\<close> \<open>closed S\<close> have "open (R - S)"
        by (rule open_Diff)
      from \<open>R \<subseteq> S \<union> T\<close> have "R - S \<subseteq> T"
        by fast
      from \<open>y \<in> R - S\<close> \<open>open (R - S)\<close> \<open>R - S \<subseteq> T\<close> \<open>interior T = {}\<close> show False
        unfolding interior_def by fast
    qed
  qed
qed

lemma interior_Times: "interior (A \<times> B) = interior A \<times> interior B"
proof (rule interior_unique)
  show "interior A \<times> interior B \<subseteq> A \<times> B"
    by (intro Sigma_mono interior_subset)
  show "open (interior A \<times> interior B)"
    by (intro open_Times open_interior)
  fix T
  assume "T \<subseteq> A \<times> B" and "open T"
  then show "T \<subseteq> interior A \<times> interior B"
  proof safe
    fix x y
    assume "(x, y) \<in> T"
    then obtain C D where "open C" "open D" "C \<times> D \<subseteq> T" "x \<in> C" "y \<in> D"
      using \<open>open T\<close> unfolding open_prod_def by fast
    then have "open C" "open D" "C \<subseteq> A" "D \<subseteq> B" "x \<in> C" "y \<in> D"
      using \<open>T \<subseteq> A \<times> B\<close> by auto
    then show "x \<in> interior A" and "y \<in> interior B"
      by (auto intro: interiorI)
  qed
qed

lemma interior_Ici:
  fixes x :: "'a :: {dense_linorder,linorder_topology}"
  assumes "b < x"
  shows "interior {x ..} = {x <..}"
proof (rule interior_unique)
  fix T
  assume "T \<subseteq> {x ..}" "open T"
  moreover have "x \<notin> T"
  proof
    assume "x \<in> T"
    obtain y where "y < x" "{y <.. x} \<subseteq> T"
      using open_left[OF \<open>open T\<close> \<open>x \<in> T\<close> \<open>b < x\<close>] by auto
    with dense[OF \<open>y < x\<close>] obtain z where "z \<in> T" "z < x"
      by (auto simp: subset_eq Ball_def)
    with \<open>T \<subseteq> {x ..}\<close> show False by auto
  qed
  ultimately show "T \<subseteq> {x <..}"
    by (auto simp: subset_eq less_le)
qed auto

lemma interior_Iic:
  fixes x :: "'a ::{dense_linorder,linorder_topology}"
  assumes "x < b"
  shows "interior {.. x} = {..< x}"
proof (rule interior_unique)
  fix T
  assume "T \<subseteq> {.. x}" "open T"
  moreover have "x \<notin> T"
  proof
    assume "x \<in> T"
    obtain y where "x < y" "{x ..< y} \<subseteq> T"
      using open_right[OF \<open>open T\<close> \<open>x \<in> T\<close> \<open>x < b\<close>] by auto
    with dense[OF \<open>x < y\<close>] obtain z where "z \<in> T" "x < z"
      by (auto simp: subset_eq Ball_def less_le)
    with \<open>T \<subseteq> {.. x}\<close> show False by auto
  qed
  ultimately show "T \<subseteq> {..< x}"
    by (auto simp: subset_eq less_le)
qed auto


subsection \<open>Closure of a Set\<close>

definition "closure S = S \<union> {x | x. x islimpt S}"

lemma interior_closure: "interior S = - (closure (- S))"
  by (auto simp: interior_def closure_def islimpt_def)

lemma closure_interior: "closure S = - interior (- S)"
  by (simp add: interior_closure)

lemma closed_closure[simp, intro]: "closed (closure S)"
  by (simp add: closure_interior closed_Compl)

lemma closure_subset: "S \<subseteq> closure S"
  by (simp add: closure_def)

lemma closure_hull: "closure S = closed hull S"
  by (auto simp: hull_def closure_interior interior_def)

lemma closure_eq: "closure S = S \<longleftrightarrow> closed S"
  unfolding closure_hull using closed_Inter by (rule hull_eq)

lemma closure_closed [simp]: "closed S \<Longrightarrow> closure S = S"
  by (simp only: closure_eq)

lemma closure_closure [simp]: "closure (closure S) = closure S"
  unfolding closure_hull by (rule hull_hull)

lemma closure_mono: "S \<subseteq> T \<Longrightarrow> closure S \<subseteq> closure T"
  unfolding closure_hull by (rule hull_mono)

lemma closure_minimal: "S \<subseteq> T \<Longrightarrow> closed T \<Longrightarrow> closure S \<subseteq> T"
  unfolding closure_hull by (rule hull_minimal)

lemma closure_unique:
  assumes "S \<subseteq> T"
    and "closed T"
    and "\<And>T'. S \<subseteq> T' \<Longrightarrow> closed T' \<Longrightarrow> T \<subseteq> T'"
  shows "closure S = T"
  using assms unfolding closure_hull by (rule hull_unique)

lemma closure_empty [simp]: "closure {} = {}"
  using closed_empty by (rule closure_closed)

lemma closure_UNIV [simp]: "closure UNIV = UNIV"
  using closed_UNIV by (rule closure_closed)

lemma closure_Un [simp]: "closure (S \<union> T) = closure S \<union> closure T"
  by (simp add: closure_interior)

lemma closure_eq_empty [iff]: "closure S = {} \<longleftrightarrow> S = {}"
  using closure_empty closure_subset[of S] by blast

lemma closure_subset_eq: "closure S \<subseteq> S \<longleftrightarrow> closed S"
  using closure_eq[of S] closure_subset[of S] by simp

lemma open_Int_closure_eq_empty: "open S \<Longrightarrow> (S \<inter> closure T) = {} \<longleftrightarrow> S \<inter> T = {}"
  using open_subset_interior[of S "- T"]
  using interior_subset[of "- T"]
  by (auto simp: closure_interior)

lemma open_Int_closure_subset: "open S \<Longrightarrow> S \<inter> closure T \<subseteq> closure (S \<inter> T)"
proof
  fix x
  assume *: "open S" "x \<in> S \<inter> closure T"
  have "x islimpt (S \<inter> T)" if **: "x islimpt T"
  proof (rule islimptI)
    fix A
    assume "x \<in> A" "open A"
    with * have "x \<in> A \<inter> S" "open (A \<inter> S)"
      by (simp_all add: open_Int)
    with ** obtain y where "y \<in> T" "y \<in> A \<inter> S" "y \<noteq> x"
      by (rule islimptE)
    then have "y \<in> S \<inter> T" "y \<in> A \<and> y \<noteq> x"
      by simp_all
    then show "\<exists>y\<in>(S \<inter> T). y \<in> A \<and> y \<noteq> x" ..
  qed
  with * show "x \<in> closure (S \<inter> T)"
    unfolding closure_def by blast
qed

lemma closure_complement: "closure (- S) = - interior S"
  by (simp add: closure_interior)

lemma interior_complement: "interior (- S) = - closure S"
  by (simp add: closure_interior)

lemma interior_diff: "interior(S - T) = interior S - closure T"
  by (simp add: Diff_eq interior_complement)

lemma closure_Times: "closure (A \<times> B) = closure A \<times> closure B"
proof (rule closure_unique)
  show "A \<times> B \<subseteq> closure A \<times> closure B"
    by (intro Sigma_mono closure_subset)
  show "closed (closure A \<times> closure B)"
    by (intro closed_Times closed_closure)
  fix T
  assume "A \<times> B \<subseteq> T" and "closed T"
  then show "closure A \<times> closure B \<subseteq> T"
    apply (simp add: closed_def open_prod_def, clarify)
    apply (rule ccontr)
    apply (drule_tac x="(a, b)" in bspec, simp, clarify, rename_tac C D)
    apply (simp add: closure_interior interior_def)
    apply (drule_tac x=C in spec)
    apply (drule_tac x=D in spec, auto)
    done
qed

lemma closure_openin_Int_closure:
  assumes ope: "openin (subtopology euclidean U) S" and "T \<subseteq> U"
  shows "closure(S \<inter> closure T) = closure(S \<inter> T)"
proof
  obtain V where "open V" and S: "S = U \<inter> V"
    using ope using openin_open by metis
  show "closure (S \<inter> closure T) \<subseteq> closure (S \<inter> T)"
    proof (clarsimp simp: S)
      fix x
      assume  "x \<in> closure (U \<inter> V \<inter> closure T)"
      then have "V \<inter> closure T \<subseteq> A \<Longrightarrow> x \<in> closure A" for A
          by (metis closure_mono subsetD inf.coboundedI2 inf_assoc)
      then have "x \<in> closure (T \<inter> V)"
         by (metis \<open>open V\<close> closure_closure inf_commute open_Int_closure_subset)
      then show "x \<in> closure (U \<inter> V \<inter> T)"
        by (metis \<open>T \<subseteq> U\<close> inf.absorb_iff2 inf_assoc inf_commute)
    qed
next
  show "closure (S \<inter> T) \<subseteq> closure (S \<inter> closure T)"
    by (meson Int_mono closure_mono closure_subset order_refl)
qed

lemma islimpt_in_closure: "(x islimpt S) = (x:closure(S-{x}))"
  unfolding closure_def using islimpt_punctured by blast

lemma connected_imp_connected_closure: "connected S \<Longrightarrow> connected (closure S)"
  by (rule connectedI) (meson closure_subset open_Int open_Int_closure_eq_empty subset_trans connectedD)

lemma limpt_of_limpts: "x islimpt {y. y islimpt S} \<Longrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  apply (clarsimp simp add: islimpt_approachable)
  apply (drule_tac x="e/2" in spec)
  apply (auto simp: simp del: less_divide_eq_numeral1)
  apply (drule_tac x="dist x' x" in spec)
  apply (auto simp: zero_less_dist_iff simp del: less_divide_eq_numeral1)
  apply (erule rev_bexI)
  apply (metis dist_commute dist_triangle_half_r less_trans less_irrefl)
  done

lemma closed_limpts:  "closed {x::'a::metric_space. x islimpt S}"
  using closed_limpt limpt_of_limpts by blast

lemma limpt_of_closure: "x islimpt closure S \<longleftrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  by (auto simp: closure_def islimpt_Un dest: limpt_of_limpts)

lemma closedin_limpt:
  "closedin (subtopology euclidean T) S \<longleftrightarrow> S \<subseteq> T \<and> (\<forall>x. x islimpt S \<and> x \<in> T \<longrightarrow> x \<in> S)"
  apply (simp add: closedin_closed, safe)
   apply (simp add: closed_limpt islimpt_subset)
  apply (rule_tac x="closure S" in exI, simp)
  apply (force simp: closure_def)
  done

lemma closedin_closed_eq: "closed S \<Longrightarrow> closedin (subtopology euclidean S) T \<longleftrightarrow> closed T \<and> T \<subseteq> S"
  by (meson closedin_limpt closed_subset closedin_closed_trans)

lemma connected_closed_set:
   "closed S
    \<Longrightarrow> connected S \<longleftrightarrow> (\<nexists>A B. closed A \<and> closed B \<and> A \<noteq> {} \<and> B \<noteq> {} \<and> A \<union> B = S \<and> A \<inter> B = {})"
  unfolding connected_closedin_eq closedin_closed_eq connected_closedin_eq by blast

lemma closedin_subset_trans:
  "closedin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    closedin (subtopology euclidean T) S"
  by (meson closedin_limpt subset_iff)

lemma openin_subset_trans:
  "openin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    openin (subtopology euclidean T) S"
  by (auto simp: openin_open)

lemma openin_Times:
  "openin (subtopology euclidean S) S' \<Longrightarrow> openin (subtopology euclidean T) T' \<Longrightarrow>
    openin (subtopology euclidean (S \<times> T)) (S' \<times> T')"
  unfolding openin_open using open_Times by blast

lemma Times_in_interior_subtopology:
  fixes U :: "('a::metric_space \<times> 'b::metric_space) set"
  assumes "(x, y) \<in> U" "openin (subtopology euclidean (S \<times> T)) U"
  obtains V W where "openin (subtopology euclidean S) V" "x \<in> V"
                    "openin (subtopology euclidean T) W" "y \<in> W" "(V \<times> W) \<subseteq> U"
proof -
  from assms obtain e where "e > 0" and "U \<subseteq> S \<times> T"
    and e: "\<And>x' y'. \<lbrakk>x'\<in>S; y'\<in>T; dist (x', y') (x, y) < e\<rbrakk> \<Longrightarrow> (x', y') \<in> U"
    by (force simp: openin_euclidean_subtopology_iff)
  with assms have "x \<in> S" "y \<in> T"
    by auto
  show ?thesis
  proof
    show "openin (subtopology euclidean S) (ball x (e/2) \<inter> S)"
      by (simp add: Int_commute openin_open_Int)
    show "x \<in> ball x (e / 2) \<inter> S"
      by (simp add: \<open>0 < e\<close> \<open>x \<in> S\<close>)
    show "openin (subtopology euclidean T) (ball y (e/2) \<inter> T)"
      by (simp add: Int_commute openin_open_Int)
    show "y \<in> ball y (e / 2) \<inter> T"
      by (simp add: \<open>0 < e\<close> \<open>y \<in> T\<close>)
    show "(ball x (e / 2) \<inter> S) \<times> (ball y (e / 2) \<inter> T) \<subseteq> U"
      by clarify (simp add: e dist_Pair_Pair \<open>0 < e\<close> dist_commute sqrt_sum_squares_half_less)
  qed
qed

lemma openin_Times_eq:
  fixes S :: "'a::metric_space set" and T :: "'b::metric_space set"
  shows
    "openin (subtopology euclidean (S \<times> T)) (S' \<times> T') \<longleftrightarrow>
      S' = {} \<or> T' = {} \<or> openin (subtopology euclidean S) S' \<and> openin (subtopology euclidean T) T'"
    (is "?lhs = ?rhs")
proof (cases "S' = {} \<or> T' = {}")
  case True
  then show ?thesis by auto
next
  case False
  then obtain x y where "x \<in> S'" "y \<in> T'"
    by blast
  show ?thesis
  proof
    assume ?lhs
    have "openin (subtopology euclidean S) S'"
      apply (subst openin_subopen, clarify)
      apply (rule Times_in_interior_subtopology [OF _ \<open>?lhs\<close>])
      using \<open>y \<in> T'\<close>
       apply auto
      done
    moreover have "openin (subtopology euclidean T) T'"
      apply (subst openin_subopen, clarify)
      apply (rule Times_in_interior_subtopology [OF _ \<open>?lhs\<close>])
      using \<open>x \<in> S'\<close>
       apply auto
      done
    ultimately show ?rhs
      by simp
  next
    assume ?rhs
    with False show ?lhs
      by (simp add: openin_Times)
  qed
qed

lemma closedin_Times:
  "closedin (subtopology euclidean S) S' \<Longrightarrow> closedin (subtopology euclidean T) T' \<Longrightarrow>
    closedin (subtopology euclidean (S \<times> T)) (S' \<times> T')"
  unfolding closedin_closed using closed_Times by blast

lemma bdd_below_closure:
  fixes A :: "real set"
  assumes "bdd_below A"
  shows "bdd_below (closure A)"
proof -
  from assms obtain m where "\<And>x. x \<in> A \<Longrightarrow> m \<le> x"
    by (auto simp: bdd_below_def)
  then have "A \<subseteq> {m..}" by auto
  then have "closure A \<subseteq> {m..}"
    using closed_real_atLeast by (rule closure_minimal)
  then show ?thesis
    by (auto simp: bdd_below_def)
qed


subsection \<open>Connected components, considered as a connectedness relation or a set\<close>

definition "connected_component s x y \<equiv> \<exists>t. connected t \<and> t \<subseteq> s \<and> x \<in> t \<and> y \<in> t"

abbreviation "connected_component_set s x \<equiv> Collect (connected_component s x)"

lemma connected_componentI:
  "connected t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> x \<in> t \<Longrightarrow> y \<in> t \<Longrightarrow> connected_component s x y"
  by (auto simp: connected_component_def)

lemma connected_component_in: "connected_component s x y \<Longrightarrow> x \<in> s \<and> y \<in> s"
  by (auto simp: connected_component_def)

lemma connected_component_refl: "x \<in> s \<Longrightarrow> connected_component s x x"
  by (auto simp: connected_component_def) (use connected_sing in blast)

lemma connected_component_refl_eq [simp]: "connected_component s x x \<longleftrightarrow> x \<in> s"
  by (auto simp: connected_component_refl) (auto simp: connected_component_def)

lemma connected_component_sym: "connected_component s x y \<Longrightarrow> connected_component s y x"
  by (auto simp: connected_component_def)

lemma connected_component_trans:
  "connected_component s x y \<Longrightarrow> connected_component s y z \<Longrightarrow> connected_component s x z"
  unfolding connected_component_def
  by (metis Int_iff Un_iff Un_subset_iff equals0D connected_Un)

lemma connected_component_of_subset:
  "connected_component s x y \<Longrightarrow> s \<subseteq> t \<Longrightarrow> connected_component t x y"
  by (auto simp: connected_component_def)

lemma connected_component_Union: "connected_component_set s x = \<Union>{t. connected t \<and> x \<in> t \<and> t \<subseteq> s}"
  by (auto simp: connected_component_def)

lemma connected_connected_component [iff]: "connected (connected_component_set s x)"
  by (auto simp: connected_component_Union intro: connected_Union)

lemma connected_iff_eq_connected_component_set:
  "connected s \<longleftrightarrow> (\<forall>x \<in> s. connected_component_set s x = s)"
proof (cases "s = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain x where "x \<in> s" by auto
  show ?thesis
  proof
    assume "connected s"
    then show "\<forall>x \<in> s. connected_component_set s x = s"
      by (force simp: connected_component_def)
  next
    assume "\<forall>x \<in> s. connected_component_set s x = s"
    then show "connected s"
      by (metis \<open>x \<in> s\<close> connected_connected_component)
  qed
qed

lemma connected_component_subset: "connected_component_set s x \<subseteq> s"
  using connected_component_in by blast

lemma connected_component_eq_self: "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> connected_component_set s x = s"
  by (simp add: connected_iff_eq_connected_component_set)

lemma connected_iff_connected_component:
  "connected s \<longleftrightarrow> (\<forall>x \<in> s. \<forall>y \<in> s. connected_component s x y)"
  using connected_component_in by (auto simp: connected_iff_eq_connected_component_set)

lemma connected_component_maximal:
  "x \<in> t \<Longrightarrow> connected t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> t \<subseteq> (connected_component_set s x)"
  using connected_component_eq_self connected_component_of_subset by blast

lemma connected_component_mono:
  "s \<subseteq> t \<Longrightarrow> connected_component_set s x \<subseteq> connected_component_set t x"
  by (simp add: Collect_mono connected_component_of_subset)

lemma connected_component_eq_empty [simp]: "connected_component_set s x = {} \<longleftrightarrow> x \<notin> s"
  using connected_component_refl by (fastforce simp: connected_component_in)

lemma connected_component_set_empty [simp]: "connected_component_set {} x = {}"
  using connected_component_eq_empty by blast

lemma connected_component_eq:
  "y \<in> connected_component_set s x \<Longrightarrow> (connected_component_set s y = connected_component_set s x)"
  by (metis (no_types, lifting)
      Collect_cong connected_component_sym connected_component_trans mem_Collect_eq)

lemma closed_connected_component:
  assumes s: "closed s"
  shows "closed (connected_component_set s x)"
proof (cases "x \<in> s")
  case False
  then show ?thesis
    by (metis connected_component_eq_empty closed_empty)
next
  case True
  show ?thesis
    unfolding closure_eq [symmetric]
  proof
    show "closure (connected_component_set s x) \<subseteq> connected_component_set s x"
      apply (rule connected_component_maximal)
        apply (simp add: closure_def True)
       apply (simp add: connected_imp_connected_closure)
      apply (simp add: s closure_minimal connected_component_subset)
      done
  next
    show "connected_component_set s x \<subseteq> closure (connected_component_set s x)"
      by (simp add: closure_subset)
  qed
qed

lemma connected_component_disjoint:
  "connected_component_set s a \<inter> connected_component_set s b = {} \<longleftrightarrow>
    a \<notin> connected_component_set s b"
  apply (auto simp: connected_component_eq)
  using connected_component_eq connected_component_sym
  apply blast
  done

lemma connected_component_nonoverlap:
  "connected_component_set s a \<inter> connected_component_set s b = {} \<longleftrightarrow>
    a \<notin> s \<or> b \<notin> s \<or> connected_component_set s a \<noteq> connected_component_set s b"
  apply (auto simp: connected_component_in)
  using connected_component_refl_eq
    apply blast
   apply (metis connected_component_eq mem_Collect_eq)
  apply (metis connected_component_eq mem_Collect_eq)
  done

lemma connected_component_overlap:
  "connected_component_set s a \<inter> connected_component_set s b \<noteq> {} \<longleftrightarrow>
    a \<in> s \<and> b \<in> s \<and> connected_component_set s a = connected_component_set s b"
  by (auto simp: connected_component_nonoverlap)

lemma connected_component_sym_eq: "connected_component s x y \<longleftrightarrow> connected_component s y x"
  using connected_component_sym by blast

lemma connected_component_eq_eq:
  "connected_component_set s x = connected_component_set s y \<longleftrightarrow>
    x \<notin> s \<and> y \<notin> s \<or> x \<in> s \<and> y \<in> s \<and> connected_component s x y"
  apply (cases "y \<in> s", simp)
   apply (metis connected_component_eq connected_component_eq_empty connected_component_refl_eq mem_Collect_eq)
  apply (cases "x \<in> s", simp)
   apply (metis connected_component_eq_empty)
  using connected_component_eq_empty
  apply blast
  done

lemma connected_iff_connected_component_eq:
  "connected s \<longleftrightarrow> (\<forall>x \<in> s. \<forall>y \<in> s. connected_component_set s x = connected_component_set s y)"
  by (simp add: connected_component_eq_eq connected_iff_connected_component)

lemma connected_component_idemp:
  "connected_component_set (connected_component_set s x) x = connected_component_set s x"
  apply (rule subset_antisym)
   apply (simp add: connected_component_subset)
  apply (metis connected_component_eq_empty connected_component_maximal
      connected_component_refl_eq connected_connected_component mem_Collect_eq set_eq_subset)
  done

lemma connected_component_unique:
  "\<lbrakk>x \<in> c; c \<subseteq> s; connected c;
    \<And>c'. x \<in> c' \<and> c' \<subseteq> s \<and> connected c'
              \<Longrightarrow> c' \<subseteq> c\<rbrakk>
        \<Longrightarrow> connected_component_set s x = c"
apply (rule subset_antisym)
apply (meson connected_component_maximal connected_component_subset connected_connected_component contra_subsetD)
by (simp add: connected_component_maximal)

lemma joinable_connected_component_eq:
  "\<lbrakk>connected t; t \<subseteq> s;
    connected_component_set s x \<inter> t \<noteq> {};
    connected_component_set s y \<inter> t \<noteq> {}\<rbrakk>
    \<Longrightarrow> connected_component_set s x = connected_component_set s y"
apply (simp add: ex_in_conv [symmetric])
apply (rule connected_component_eq)
by (metis (no_types, hide_lams) connected_component_eq_eq connected_component_in connected_component_maximal subsetD mem_Collect_eq)


lemma Union_connected_component: "\<Union>(connected_component_set s ` s) = s"
  apply (rule subset_antisym)
  apply (simp add: SUP_least connected_component_subset)
  using connected_component_refl_eq
  by force


lemma complement_connected_component_unions:
    "s - connected_component_set s x =
     \<Union>(connected_component_set s ` s - {connected_component_set s x})"
  apply (subst Union_connected_component [symmetric], auto)
  apply (metis connected_component_eq_eq connected_component_in)
  by (metis connected_component_eq mem_Collect_eq)

lemma connected_component_intermediate_subset:
        "\<lbrakk>connected_component_set u a \<subseteq> t; t \<subseteq> u\<rbrakk>
        \<Longrightarrow> connected_component_set t a = connected_component_set u a"
  apply (case_tac "a \<in> u")
  apply (simp add: connected_component_maximal connected_component_mono subset_antisym)
  using connected_component_eq_empty by blast

proposition connected_Times:
  assumes S: "connected S" and T: "connected T"
  shows "connected (S \<times> T)"
proof (clarsimp simp add: connected_iff_connected_component)
  fix x y x' y'
  assume xy: "x \<in> S" "y \<in> T" "x' \<in> S" "y' \<in> T"
  with xy obtain U V where U: "connected U" "U \<subseteq> S" "x \<in> U" "x' \<in> U"
                       and V: "connected V" "V \<subseteq> T" "y \<in> V" "y' \<in> V"
    using S T \<open>x \<in> S\<close> \<open>x' \<in> S\<close> by blast+
  show "connected_component (S \<times> T) (x, y) (x', y')"
    unfolding connected_component_def
  proof (intro exI conjI)
    show "connected ((\<lambda>x. (x, y)) ` U \<union> Pair x' ` V)"
    proof (rule connected_Un)
      have "continuous_on U (\<lambda>x. (x, y))"
        by (intro continuous_intros)
      then show "connected ((\<lambda>x. (x, y)) ` U)"
        by (rule connected_continuous_image) (rule \<open>connected U\<close>)
      have "continuous_on V (Pair x')"
        by (intro continuous_intros)
      then show "connected (Pair x' ` V)"
        by (rule connected_continuous_image) (rule \<open>connected V\<close>)
    qed (use U V in auto)
  qed (use U V in auto)
qed

corollary connected_Times_eq [simp]:
   "connected (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> connected S \<and> connected T"  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof (cases "S = {} \<or> T = {}")
    case True
    then show ?thesis by auto
  next
    case False
    have "connected (fst ` (S \<times> T))" "connected (snd ` (S \<times> T))"
      using continuous_on_fst continuous_on_snd continuous_on_id
      by (blast intro: connected_continuous_image [OF _ L])+
    with False show ?thesis
      by auto
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp: connected_Times)
qed


subsection \<open>The set of connected components of a set\<close>

definition components:: "'a::topological_space set \<Rightarrow> 'a set set"
  where "components s \<equiv> connected_component_set s ` s"

lemma components_iff: "s \<in> components u \<longleftrightarrow> (\<exists>x. x \<in> u \<and> s = connected_component_set u x)"
  by (auto simp: components_def)

lemma componentsI: "x \<in> u \<Longrightarrow> connected_component_set u x \<in> components u"
  by (auto simp: components_def)

lemma componentsE:
  assumes "s \<in> components u"
  obtains x where "x \<in> u" "s = connected_component_set u x"
  using assms by (auto simp: components_def)

lemma Union_components [simp]: "\<Union>(components u) = u"
  apply (rule subset_antisym)
  using Union_connected_component components_def apply fastforce
  apply (metis Union_connected_component components_def set_eq_subset)
  done

lemma pairwise_disjoint_components: "pairwise (\<lambda>X Y. X \<inter> Y = {}) (components u)"
  apply (simp add: pairwise_def)
  apply (auto simp: components_iff)
  apply (metis connected_component_eq_eq connected_component_in)+
  done

lemma in_components_nonempty: "c \<in> components s \<Longrightarrow> c \<noteq> {}"
    by (metis components_iff connected_component_eq_empty)

lemma in_components_subset: "c \<in> components s \<Longrightarrow> c \<subseteq> s"
  using Union_components by blast

lemma in_components_connected: "c \<in> components s \<Longrightarrow> connected c"
  by (metis components_iff connected_connected_component)

lemma in_components_maximal:
  "c \<in> components s \<longleftrightarrow>
    c \<noteq> {} \<and> c \<subseteq> s \<and> connected c \<and> (\<forall>d. d \<noteq> {} \<and> c \<subseteq> d \<and> d \<subseteq> s \<and> connected d \<longrightarrow> d = c)"
  apply (rule iffI)
   apply (simp add: in_components_nonempty in_components_connected)
   apply (metis (full_types) components_iff connected_component_eq_self connected_component_intermediate_subset connected_component_refl in_components_subset mem_Collect_eq rev_subsetD)
  apply (metis bot.extremum_uniqueI components_iff connected_component_eq_empty connected_component_maximal connected_component_subset connected_connected_component subset_emptyI)
  done

lemma joinable_components_eq:
  "connected t \<and> t \<subseteq> s \<and> c1 \<in> components s \<and> c2 \<in> components s \<and> c1 \<inter> t \<noteq> {} \<and> c2 \<inter> t \<noteq> {} \<Longrightarrow> c1 = c2"
  by (metis (full_types) components_iff joinable_connected_component_eq)

lemma closed_components: "\<lbrakk>closed s; c \<in> components s\<rbrakk> \<Longrightarrow> closed c"
  by (metis closed_connected_component components_iff)

lemma components_nonoverlap:
    "\<lbrakk>c \<in> components s; c' \<in> components s\<rbrakk> \<Longrightarrow> (c \<inter> c' = {}) \<longleftrightarrow> (c \<noteq> c')"
  apply (auto simp: in_components_nonempty components_iff)
    using connected_component_refl apply blast
   apply (metis connected_component_eq_eq connected_component_in)
  by (metis connected_component_eq mem_Collect_eq)

lemma components_eq: "\<lbrakk>c \<in> components s; c' \<in> components s\<rbrakk> \<Longrightarrow> (c = c' \<longleftrightarrow> c \<inter> c' \<noteq> {})"
  by (metis components_nonoverlap)

lemma components_eq_empty [simp]: "components s = {} \<longleftrightarrow> s = {}"
  by (simp add: components_def)

lemma components_empty [simp]: "components {} = {}"
  by simp

lemma connected_eq_connected_components_eq: "connected s \<longleftrightarrow> (\<forall>c \<in> components s. \<forall>c' \<in> components s. c = c')"
  by (metis (no_types, hide_lams) components_iff connected_component_eq_eq connected_iff_connected_component)

lemma components_eq_sing_iff: "components s = {s} \<longleftrightarrow> connected s \<and> s \<noteq> {}"
  apply (rule iffI)
  using in_components_connected apply fastforce
  apply safe
  using Union_components apply fastforce
   apply (metis components_iff connected_component_eq_self)
  using in_components_maximal
  apply auto
  done

lemma components_eq_sing_exists: "(\<exists>a. components s = {a}) \<longleftrightarrow> connected s \<and> s \<noteq> {}"
  apply (rule iffI)
  using connected_eq_connected_components_eq apply fastforce
  apply (metis components_eq_sing_iff)
  done

lemma connected_eq_components_subset_sing: "connected s \<longleftrightarrow> components s \<subseteq> {s}"
  by (metis Union_components components_empty components_eq_sing_iff connected_empty insert_subset order_refl subset_singletonD)

lemma connected_eq_components_subset_sing_exists: "connected s \<longleftrightarrow> (\<exists>a. components s \<subseteq> {a})"
  by (metis components_eq_sing_exists connected_eq_components_subset_sing empty_iff subset_iff subset_singletonD)

lemma in_components_self: "s \<in> components s \<longleftrightarrow> connected s \<and> s \<noteq> {}"
  by (metis components_empty components_eq_sing_iff empty_iff in_components_connected insertI1)

lemma components_maximal: "\<lbrakk>c \<in> components s; connected t; t \<subseteq> s; c \<inter> t \<noteq> {}\<rbrakk> \<Longrightarrow> t \<subseteq> c"
  apply (simp add: components_def ex_in_conv [symmetric], clarify)
  by (meson connected_component_def connected_component_trans)

lemma exists_component_superset: "\<lbrakk>t \<subseteq> s; s \<noteq> {}; connected t\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> components s \<and> t \<subseteq> c"
  apply (cases "t = {}", force)
  apply (metis components_def ex_in_conv connected_component_maximal contra_subsetD image_eqI)
  done

lemma components_intermediate_subset: "\<lbrakk>s \<in> components u; s \<subseteq> t; t \<subseteq> u\<rbrakk> \<Longrightarrow> s \<in> components t"
  apply (auto simp: components_iff)
  apply (metis connected_component_eq_empty connected_component_intermediate_subset)
  done

lemma in_components_unions_complement: "c \<in> components s \<Longrightarrow> s - c = \<Union>(components s - {c})"
  by (metis complement_connected_component_unions components_def components_iff)

lemma connected_intermediate_closure:
  assumes cs: "connected s" and st: "s \<subseteq> t" and ts: "t \<subseteq> closure s"
  shows "connected t"
proof (rule connectedI)
  fix A B
  assume A: "open A" and B: "open B" and Alap: "A \<inter> t \<noteq> {}" and Blap: "B \<inter> t \<noteq> {}"
    and disj: "A \<inter> B \<inter> t = {}" and cover: "t \<subseteq> A \<union> B"
  have disjs: "A \<inter> B \<inter> s = {}"
    using disj st by auto
  have "A \<inter> closure s \<noteq> {}"
    using Alap Int_absorb1 ts by blast
  then have Alaps: "A \<inter> s \<noteq> {}"
    by (simp add: A open_Int_closure_eq_empty)
  have "B \<inter> closure s \<noteq> {}"
    using Blap Int_absorb1 ts by blast
  then have Blaps: "B \<inter> s \<noteq> {}"
    by (simp add: B open_Int_closure_eq_empty)
  then show False
    using cs [unfolded connected_def] A B disjs Alaps Blaps cover st
    by blast
qed

lemma closedin_connected_component: "closedin (subtopology euclidean s) (connected_component_set s x)"
proof (cases "connected_component_set s x = {}")
  case True
  then show ?thesis
    by (metis closedin_empty)
next
  case False
  then obtain y where y: "connected_component s x y"
    by blast
  have *: "connected_component_set s x \<subseteq> s \<inter> closure (connected_component_set s x)"
    by (auto simp: closure_def connected_component_in)
  have "connected_component s x y \<Longrightarrow> s \<inter> closure (connected_component_set s x) \<subseteq> connected_component_set s x"
    apply (rule connected_component_maximal, simp)
    using closure_subset connected_component_in apply fastforce
    using * connected_intermediate_closure apply blast+
    done
  with y * show ?thesis
    by (auto simp: Topology_Euclidean_Space.closedin_closed)
qed


subsection \<open>Frontier (also known as boundary)\<close>

definition "frontier S = closure S - interior S"

lemma frontier_closed [iff]: "closed (frontier S)"
  by (simp add: frontier_def closed_Diff)

lemma frontier_closures: "frontier S = closure S \<inter> closure (- S)"
  by (auto simp: frontier_def interior_closure)

lemma frontier_straddle:
  fixes a :: "'a::metric_space"
  shows "a \<in> frontier S \<longleftrightarrow> (\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e))"
  unfolding frontier_def closure_interior
  by (auto simp: mem_interior subset_eq ball_def)

lemma frontier_subset_closed: "closed S \<Longrightarrow> frontier S \<subseteq> S"
  by (metis frontier_def closure_closed Diff_subset)

lemma frontier_empty [simp]: "frontier {} = {}"
  by (simp add: frontier_def)

lemma frontier_subset_eq: "frontier S \<subseteq> S \<longleftrightarrow> closed S"
proof -
  {
    assume "frontier S \<subseteq> S"
    then have "closure S \<subseteq> S"
      using interior_subset unfolding frontier_def by auto
    then have "closed S"
      using closure_subset_eq by auto
  }
  then show ?thesis using frontier_subset_closed[of S] ..
qed

lemma frontier_complement [simp]: "frontier (- S) = frontier S"
  by (auto simp: frontier_def closure_complement interior_complement)

lemma frontier_disjoint_eq: "frontier S \<inter> S = {} \<longleftrightarrow> open S"
  using frontier_complement frontier_subset_eq[of "- S"]
  unfolding open_closed by auto

lemma frontier_UNIV [simp]: "frontier UNIV = {}"
  using frontier_complement frontier_empty by fastforce

lemma frontier_interiors: "frontier s = - interior(s) - interior(-s)"
  by (simp add: Int_commute frontier_def interior_closure)

lemma frontier_interior_subset: "frontier(interior S) \<subseteq> frontier S"
  by (simp add: Diff_mono frontier_interiors interior_mono interior_subset)

lemma connected_Int_frontier:
     "\<lbrakk>connected s; s \<inter> t \<noteq> {}; s - t \<noteq> {}\<rbrakk> \<Longrightarrow> (s \<inter> frontier t \<noteq> {})"
  apply (simp add: frontier_interiors connected_openin, safe)
  apply (drule_tac x="s \<inter> interior t" in spec, safe)
   apply (drule_tac [2] x="s \<inter> interior (-t)" in spec)
   apply (auto simp: disjoint_eq_subset_Compl dest: interior_subset [THEN subsetD])
  done

lemma closure_Un_frontier: "closure S = S \<union> frontier S"
proof -
  have "S \<union> interior S = S"
    using interior_subset by auto
  then show ?thesis
    using closure_subset by (auto simp: frontier_def)
qed


subsection \<open>Filters and the ``eventually true'' quantifier\<close>

definition indirection :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'a filter"  (infixr "indirection" 70)
  where "a indirection v = at a within {b. \<exists>c\<ge>0. b - a = scaleR c v}"

text \<open>Identify Trivial limits, where we can't approach arbitrarily closely.\<close>

lemma trivial_limit_within: "trivial_limit (at a within S) \<longleftrightarrow> \<not> a islimpt S"
proof
  assume "trivial_limit (at a within S)"
  then show "\<not> a islimpt S"
    unfolding trivial_limit_def
    unfolding eventually_at_topological
    unfolding islimpt_def
    apply (clarsimp simp add: set_eq_iff)
    apply (rename_tac T, rule_tac x=T in exI)
    apply (clarsimp, drule_tac x=y in bspec, simp_all)
    done
next
  assume "\<not> a islimpt S"
  then show "trivial_limit (at a within S)"
    unfolding trivial_limit_def eventually_at_topological islimpt_def
    by metis
qed

lemma trivial_limit_at_iff: "trivial_limit (at a) \<longleftrightarrow> \<not> a islimpt UNIV"
  using trivial_limit_within [of a UNIV] by simp

lemma trivial_limit_at: "\<not> trivial_limit (at a)"
  for a :: "'a::perfect_space"
  by (rule at_neq_bot)

lemma trivial_limit_at_infinity:
  "\<not> trivial_limit (at_infinity :: ('a::{real_normed_vector,perfect_space}) filter)"
  unfolding trivial_limit_def eventually_at_infinity
  apply clarsimp
  apply (subgoal_tac "\<exists>x::'a. x \<noteq> 0", clarify)
   apply (rule_tac x="scaleR (b / norm x) x" in exI, simp)
  apply (cut_tac islimpt_UNIV [of "0::'a", unfolded islimpt_def])
  apply (drule_tac x=UNIV in spec, simp)
  done

lemma not_trivial_limit_within: "\<not> trivial_limit (at x within S) = (x \<in> closure (S - {x}))"
  using islimpt_in_closure by (metis trivial_limit_within)

lemma at_within_eq_bot_iff: "at c within A = bot \<longleftrightarrow> c \<notin> closure (A - {c})"
  using not_trivial_limit_within[of c A] by blast

text \<open>Some property holds "sufficiently close" to the limit point.\<close>

lemma trivial_limit_eventually: "trivial_limit net \<Longrightarrow> eventually P net"
  by simp

lemma trivial_limit_eq: "trivial_limit net \<longleftrightarrow> (\<forall>P. eventually P net)"
  by (simp add: filter_eq_iff)


subsection \<open>Limits\<close>

lemma Lim: "(f \<longlongrightarrow> l) net \<longleftrightarrow> trivial_limit net \<or> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"
  by (auto simp: tendsto_iff trivial_limit_eq)

text \<open>Show that they yield usual definitions in the various cases.\<close>

lemma Lim_within_le: "(f \<longlongrightarrow> l)(at a within S) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a \<le> d \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_le)

lemma Lim_within: "(f \<longlongrightarrow> l) (at a within S) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x \<in> S. 0 < dist x a \<and> dist x a  < d \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

corollary Lim_withinI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x \<in> S. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) (at a within S)"
  apply (simp add: Lim_within, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

lemma Lim_at: "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

lemma Lim_at_infinity: "(f \<longlongrightarrow> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x. norm x \<ge> b \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_infinity)

corollary Lim_at_infinityI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>B. \<forall>x. norm x \<ge> B \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) at_infinity"
  apply (simp add: Lim_at_infinity, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

lemma Lim_eventually: "eventually (\<lambda>x. f x = l) net \<Longrightarrow> (f \<longlongrightarrow> l) net"
  by (rule topological_tendstoI) (auto elim: eventually_mono)

lemma Lim_transform_within_set:
  fixes a :: "'a::metric_space" and l :: "'b::metric_space"
  shows "\<lbrakk>(f \<longlongrightarrow> l) (at a within S); eventually (\<lambda>x. x \<in> S \<longleftrightarrow> x \<in> T) (at a)\<rbrakk>
         \<Longrightarrow> (f \<longlongrightarrow> l) (at a within T)"
apply (clarsimp simp: eventually_at Lim_within)
apply (drule_tac x=e in spec, clarify)
apply (rename_tac k)
apply (rule_tac x="min d k" in exI, simp)
done

lemma Lim_transform_within_set_eq:
  fixes a l :: "'a::real_normed_vector"
  shows "eventually (\<lambda>x. x \<in> s \<longleftrightarrow> x \<in> t) (at a)
         \<Longrightarrow> ((f \<longlongrightarrow> l) (at a within s) \<longleftrightarrow> (f \<longlongrightarrow> l) (at a within t))"
  by (force intro: Lim_transform_within_set elim: eventually_mono)

lemma Lim_transform_within_openin:
  fixes a :: "'a::metric_space"
  assumes f: "(f \<longlongrightarrow> l) (at a within T)"
    and "openin (subtopology euclidean T) S" "a \<in> S"
    and eq: "\<And>x. \<lbrakk>x \<in> S; x \<noteq> a\<rbrakk> \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) (at a within T)"
proof -
  obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball a \<epsilon> \<inter> T \<subseteq> S"
    using assms by (force simp: openin_contains_ball)
  then have "a \<in> ball a \<epsilon>"
    by simp
  show ?thesis
    by (rule Lim_transform_within [OF f \<open>0 < \<epsilon>\<close> eq]) (use \<epsilon> in \<open>auto simp: dist_commute subset_iff\<close>)
qed

lemma continuous_transform_within_openin:
  fixes a :: "'a::metric_space"
  assumes "continuous (at a within T) f"
    and "openin (subtopology euclidean T) S" "a \<in> S"
    and eq: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "continuous (at a within T) g"
  using assms by (simp add: Lim_transform_within_openin continuous_within)

text \<open>The expected monotonicity property.\<close>

lemma Lim_Un:
  assumes "(f \<longlongrightarrow> l) (at x within S)" "(f \<longlongrightarrow> l) (at x within T)"
  shows "(f \<longlongrightarrow> l) (at x within (S \<union> T))"
  using assms unfolding at_within_union by (rule filterlim_sup)

lemma Lim_Un_univ:
  "(f \<longlongrightarrow> l) (at x within S) \<Longrightarrow> (f \<longlongrightarrow> l) (at x within T) \<Longrightarrow>
    S \<union> T = UNIV \<Longrightarrow> (f \<longlongrightarrow> l) (at x)"
  by (metis Lim_Un)

text \<open>Interrelations between restricted and unrestricted limits.\<close>

lemma Lim_at_imp_Lim_at_within: "(f \<longlongrightarrow> l) (at x) \<Longrightarrow> (f \<longlongrightarrow> l) (at x within S)"
  by (metis order_refl filterlim_mono subset_UNIV at_le)

lemma eventually_within_interior:
  assumes "x \<in> interior S"
  shows "eventually P (at x within S) \<longleftrightarrow> eventually P (at x)"
  (is "?lhs = ?rhs")
proof
  from assms obtain T where T: "open T" "x \<in> T" "T \<subseteq> S" ..
  {
    assume ?lhs
    then obtain A where "open A" and "x \<in> A" and "\<forall>y\<in>A. y \<noteq> x \<longrightarrow> y \<in> S \<longrightarrow> P y"
      by (auto simp: eventually_at_topological)
    with T have "open (A \<inter> T)" and "x \<in> A \<inter> T" and "\<forall>y \<in> A \<inter> T. y \<noteq> x \<longrightarrow> P y"
      by auto
    then show ?rhs
      by (auto simp: eventually_at_topological)
  next
    assume ?rhs
    then show ?lhs
      by (auto elim: eventually_mono simp: eventually_at_filter)
  }
qed

lemma at_within_interior: "x \<in> interior S \<Longrightarrow> at x within S = at x"
  unfolding filter_eq_iff by (intro allI eventually_within_interior)

lemma Lim_within_LIMSEQ:
  fixes a :: "'a::first_countable_topology"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a \<and> S n \<in> T) \<and> S \<longlonglongrightarrow> a \<longrightarrow> (\<lambda>n. X (S n)) \<longlonglongrightarrow> L"
  shows "(X \<longlongrightarrow> L) (at a within T)"
  using assms unfolding tendsto_def [where l=L]
  by (simp add: sequentially_imp_eventually_within)

lemma Lim_right_bound:
  fixes f :: "'a :: {linorder_topology, conditionally_complete_linorder, no_top} \<Rightarrow>
    'b::{linorder_topology, conditionally_complete_linorder}"
  assumes mono: "\<And>a b. a \<in> I \<Longrightarrow> b \<in> I \<Longrightarrow> x < a \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> f b"
    and bnd: "\<And>a. a \<in> I \<Longrightarrow> x < a \<Longrightarrow> K \<le> f a"
  shows "(f \<longlongrightarrow> Inf (f ` ({x<..} \<inter> I))) (at x within ({x<..} \<inter> I))"
proof (cases "{x<..} \<inter> I = {}")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule order_tendstoI)
    fix a
    assume a: "a < Inf (f ` ({x<..} \<inter> I))"
    {
      fix y
      assume "y \<in> {x<..} \<inter> I"
      with False bnd have "Inf (f ` ({x<..} \<inter> I)) \<le> f y"
        by (auto intro!: cInf_lower bdd_belowI2)
      with a have "a < f y"
        by (blast intro: less_le_trans)
    }
    then show "eventually (\<lambda>x. a < f x) (at x within ({x<..} \<inter> I))"
      by (auto simp: eventually_at_filter intro: exI[of _ 1] zero_less_one)
  next
    fix a
    assume "Inf (f ` ({x<..} \<inter> I)) < a"
    from cInf_lessD[OF _ this] False obtain y where y: "x < y" "y \<in> I" "f y < a"
      by auto
    then have "eventually (\<lambda>x. x \<in> I \<longrightarrow> f x < a) (at_right x)"
      unfolding eventually_at_right[OF \<open>x < y\<close>] by (metis less_imp_le le_less_trans mono)
    then show "eventually (\<lambda>x. f x < a) (at x within ({x<..} \<inter> I))"
      unfolding eventually_at_filter by eventually_elim simp
  qed
qed

text \<open>Another limit point characterization.\<close>

lemma limpt_sequential_inj:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow>
         (\<exists>f. (\<forall>n::nat. f n \<in> S - {x}) \<and> inj f \<and> (f \<longlongrightarrow> x) sequentially)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e"
    by (force simp: islimpt_approachable)
  then obtain y where y: "\<And>e. e>0 \<Longrightarrow> y e \<in> S \<and> y e \<noteq> x \<and> dist (y e) x < e"
    by metis
  define f where "f \<equiv> rec_nat (y 1) (\<lambda>n fn. y (min (inverse(2 ^ (Suc n))) (dist fn x)))"
  have [simp]: "f 0 = y 1"
               "f(Suc n) = y (min (inverse(2 ^ (Suc n))) (dist (f n) x))" for n
    by (simp_all add: f_def)
  have f: "f n \<in> S \<and> (f n \<noteq> x) \<and> dist (f n) x < inverse(2 ^ n)" for n
  proof (induction n)
    case 0 show ?case
      by (simp add: y)
  next
    case (Suc n) then show ?case
      apply (auto simp: y)
      by (metis half_gt_zero_iff inverse_positive_iff_positive less_divide_eq_numeral1(1) min_less_iff_conj y zero_less_dist_iff zero_less_numeral zero_less_power)
  qed
  show ?rhs
  proof (rule_tac x=f in exI, intro conjI allI)
    show "\<And>n. f n \<in> S - {x}"
      using f by blast
    have "dist (f n) x < dist (f m) x" if "m < n" for m n
    using that
    proof (induction n)
      case 0 then show ?case by simp
    next
      case (Suc n)
      then consider "m < n" | "m = n" using less_Suc_eq by blast
      then show ?case
      proof cases
        assume "m < n"
        have "dist (f(Suc n)) x = dist (y (min (inverse(2 ^ (Suc n))) (dist (f n) x))) x"
          by simp
        also have "... < dist (f n) x"
          by (metis dist_pos_lt f min.strict_order_iff min_less_iff_conj y)
        also have "... < dist (f m) x"
          using Suc.IH \<open>m < n\<close> by blast
        finally show ?thesis .
      next
        assume "m = n" then show ?case
          by simp (metis dist_pos_lt f half_gt_zero_iff inverse_positive_iff_positive min_less_iff_conj y zero_less_numeral zero_less_power)
      qed
    qed
    then show "inj f"
      by (metis less_irrefl linorder_injI)
    show "f \<longlonglongrightarrow> x"
      apply (rule tendstoI)
      apply (rule_tac c="nat (ceiling(1/e))" in eventually_sequentiallyI)
      apply (rule less_trans [OF f [THEN conjunct2, THEN conjunct2]])
      apply (simp add: field_simps)
      by (meson le_less_trans mult_less_cancel_left not_le of_nat_less_two_power)
  qed
next
  assume ?rhs
  then show ?lhs
    by (fastforce simp add: islimpt_approachable lim_sequentially)
qed

(*could prove directly from islimpt_sequential_inj, but only for metric spaces*)
lemma islimpt_sequential:
  fixes x :: "'a::first_countable_topology"
  shows "x islimpt S \<longleftrightarrow> (\<exists>f. (\<forall>n::nat. f n \<in> S - {x}) \<and> (f \<longlongrightarrow> x) sequentially)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  from countable_basis_at_decseq[of x] obtain A where A:
      "\<And>i. open (A i)"
      "\<And>i. x \<in> A i"
      "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast
  define f where "f n = (SOME y. y \<in> S \<and> y \<in> A n \<and> x \<noteq> y)" for n
  {
    fix n
    from \<open>?lhs\<close> have "\<exists>y. y \<in> S \<and> y \<in> A n \<and> x \<noteq> y"
      unfolding islimpt_def using A(1,2)[of n] by auto
    then have "f n \<in> S \<and> f n \<in> A n \<and> x \<noteq> f n"
      unfolding f_def by (rule someI_ex)
    then have "f n \<in> S" "f n \<in> A n" "x \<noteq> f n" by auto
  }
  then have "\<forall>n. f n \<in> S - {x}" by auto
  moreover have "(\<lambda>n. f n) \<longlonglongrightarrow> x"
  proof (rule topological_tendstoI)
    fix S
    assume "open S" "x \<in> S"
    from A(3)[OF this] \<open>\<And>n. f n \<in> A n\<close>
    show "eventually (\<lambda>x. f x \<in> S) sequentially"
      by (auto elim!: eventually_mono)
  qed
  ultimately show ?rhs by fast
next
  assume ?rhs
  then obtain f :: "nat \<Rightarrow> 'a" where f: "\<And>n. f n \<in> S - {x}" and lim: "f \<longlonglongrightarrow> x"
    by auto
  show ?lhs
    unfolding islimpt_def
  proof safe
    fix T
    assume "open T" "x \<in> T"
    from lim[THEN topological_tendstoD, OF this] f
    show "\<exists>y\<in>S. y \<in> T \<and> y \<noteq> x"
      unfolding eventually_sequentially by auto
  qed
qed

lemma Lim_null:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f \<longlongrightarrow> l) net \<longleftrightarrow> ((\<lambda>x. f(x) - l) \<longlongrightarrow> 0) net"
  by (simp add: Lim dist_norm)

lemma Lim_null_comparison:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "eventually (\<lambda>x. norm (f x) \<le> g x) net" "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(2)
proof (rule metric_tendsto_imp_tendsto)
  show "eventually (\<lambda>x. dist (f x) 0 \<le> dist (g x) 0) net"
    using assms(1) by (rule eventually_mono) (simp add: dist_norm)
qed

lemma Lim_transform_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
    and g :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) net"
    and "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(1) tendsto_norm_zero [OF assms(2)]
  by (rule Lim_null_comparison)

lemma lim_null_mult_right_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "eventually (\<lambda>x. norm(g x) \<le> B) F"
    shows "((\<lambda>z. f z * g z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. norm (f x) * B) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_left_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (f x) * norm (g x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_left_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_mult_left_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes g: "eventually (\<lambda>x. norm(g x) \<le> B) F" and f: "(f \<longlongrightarrow> 0) F"
    shows "((\<lambda>z. g z * f z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. B * norm (f x)) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_right_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (g x) * norm (f x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_right_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_scaleR_bounded:
  assumes f: "(f \<longlongrightarrow> 0) net" and gB: "eventually (\<lambda>a. f a = 0 \<or> norm(g a) \<le> B) net"
    shows "((\<lambda>n. f n *\<^sub>R g n) \<longlongrightarrow> 0) net"
proof
  fix \<epsilon>::real
  assume "0 < \<epsilon>"
  then have B: "0 < \<epsilon> / (abs B + 1)" by simp
  have *: "\<bar>f x\<bar> * norm (g x) < \<epsilon>" if f: "\<bar>f x\<bar> * (\<bar>B\<bar> + 1) < \<epsilon>" and g: "norm (g x) \<le> B" for x
  proof -
    have "\<bar>f x\<bar> * norm (g x) \<le> \<bar>f x\<bar> * B"
      by (simp add: mult_left_mono g)
    also have "... \<le> \<bar>f x\<bar> * (\<bar>B\<bar> + 1)"
      by (simp add: mult_left_mono)
    also have "... < \<epsilon>"
      by (rule f)
    finally show ?thesis .
  qed
  show "\<forall>\<^sub>F x in net. dist (f x *\<^sub>R g x) 0 < \<epsilon>"
    apply (rule eventually_mono [OF eventually_conj [OF tendstoD [OF f B] gB] ])
    apply (auto simp: \<open>0 < \<epsilon>\<close> divide_simps * split: if_split_asm)
    done
qed

text\<open>Deducing things about the limit from the elements.\<close>

lemma Lim_in_closed_set:
  assumes "closed S"
    and "eventually (\<lambda>x. f(x) \<in> S) net"
    and "\<not> trivial_limit net" "(f \<longlongrightarrow> l) net"
  shows "l \<in> S"
proof (rule ccontr)
  assume "l \<notin> S"
  with \<open>closed S\<close> have "open (- S)" "l \<in> - S"
    by (simp_all add: open_Compl)
  with assms(4) have "eventually (\<lambda>x. f x \<in> - S) net"
    by (rule topological_tendstoD)
  with assms(2) have "eventually (\<lambda>x. False) net"
    by (rule eventually_elim2) simp
  with assms(3) show "False"
    by (simp add: eventually_False)
qed

text\<open>Need to prove closed(cball(x,e)) before deducing this as a corollary.\<close>

lemma Lim_dist_ubound:
  assumes "\<not>(trivial_limit net)"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. dist a (f x) \<le> e) net"
  shows "dist a l \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)

lemma Lim_norm_ubound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not>(trivial_limit net)" "(f \<longlongrightarrow> l) net" "eventually (\<lambda>x. norm(f x) \<le> e) net"
  shows "norm(l) \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)

lemma Lim_norm_lbound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not> trivial_limit net"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. e \<le> norm (f x)) net"
  shows "e \<le> norm l"
  using assms by (fast intro: tendsto_le tendsto_intros)

text\<open>Limit under bilinear function\<close>

lemma Lim_bilinear:
  assumes "(f \<longlongrightarrow> l) net"
    and "(g \<longlongrightarrow> m) net"
    and "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) \<longlongrightarrow> (h l m)) net"
  using \<open>bounded_bilinear h\<close> \<open>(f \<longlongrightarrow> l) net\<close> \<open>(g \<longlongrightarrow> m) net\<close>
  by (rule bounded_bilinear.tendsto)

text\<open>These are special for limits out of the same vector space.\<close>

lemma Lim_within_id: "(id \<longlongrightarrow> a) (at a within s)"
  unfolding id_def by (rule tendsto_ident_at)

lemma Lim_at_id: "(id \<longlongrightarrow> a) (at a)"
  unfolding id_def by (rule tendsto_ident_at)

lemma Lim_at_zero:
  fixes a :: "'a::real_normed_vector"
    and l :: "'b::topological_space"
  shows "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow> ((\<lambda>x. f(a + x)) \<longlongrightarrow> l) (at 0)"
  using LIM_offset_zero LIM_offset_zero_cancel ..

text\<open>It's also sometimes useful to extract the limit point from the filter.\<close>

abbreviation netlimit :: "'a::t2_space filter \<Rightarrow> 'a"
  where "netlimit F \<equiv> Lim F (\<lambda>x. x)"

lemma netlimit_within: "\<not> trivial_limit (at a within S) \<Longrightarrow> netlimit (at a within S) = a"
  by (rule tendsto_Lim) (auto intro: tendsto_intros)

lemma netlimit_at:
  fixes a :: "'a::{perfect_space,t2_space}"
  shows "netlimit (at a) = a"
  using netlimit_within [of a UNIV] by simp

lemma lim_within_interior:
  "x \<in> interior S \<Longrightarrow> (f \<longlongrightarrow> l) (at x within S) \<longleftrightarrow> (f \<longlongrightarrow> l) (at x)"
  by (metis at_within_interior)

lemma netlimit_within_interior:
  fixes x :: "'a::{t2_space,perfect_space}"
  assumes "x \<in> interior S"
  shows "netlimit (at x within S) = x"
  using assms by (metis at_within_interior netlimit_at)

lemma netlimit_at_vector:
  fixes a :: "'a::real_normed_vector"
  shows "netlimit (at a) = a"
proof (cases "\<exists>x. x \<noteq> a")
  case True then obtain x where x: "x \<noteq> a" ..
  have "\<not> trivial_limit (at a)"
    unfolding trivial_limit_def eventually_at dist_norm
    apply clarsimp
    apply (rule_tac x="a + scaleR (d / 2) (sgn (x - a))" in exI)
    apply (simp add: norm_sgn sgn_zero_iff x)
    done
  then show ?thesis
    by (rule netlimit_within [of a UNIV])
qed simp


text\<open>Useful lemmas on closure and set of possible sequential limits.\<close>

lemma closure_sequential:
  fixes l :: "'a::first_countable_topology"
  shows "l \<in> closure S \<longleftrightarrow> (\<exists>x. (\<forall>n. x n \<in> S) \<and> (x \<longlongrightarrow> l) sequentially)"
  (is "?lhs = ?rhs")
proof
  assume "?lhs"
  moreover
  {
    assume "l \<in> S"
    then have "?rhs" using tendsto_const[of l sequentially] by auto
  }
  moreover
  {
    assume "l islimpt S"
    then have "?rhs" unfolding islimpt_sequential by auto
  }
  ultimately show "?rhs"
    unfolding closure_def by auto
next
  assume "?rhs"
  then show "?lhs" unfolding closure_def islimpt_sequential by auto
qed

lemma closed_sequential_limits:
  fixes S :: "'a::first_countable_topology set"
  shows "closed S \<longleftrightarrow> (\<forall>x l. (\<forall>n. x n \<in> S) \<and> (x \<longlongrightarrow> l) sequentially \<longrightarrow> l \<in> S)"
by (metis closure_sequential closure_subset_eq subset_iff)

lemma closure_approachable:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e)"
  apply (auto simp: closure_def islimpt_approachable)
  apply (metis dist_self)
  done

lemma closure_approachable_le:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x \<le> e)"
  unfolding closure_approachable
  using dense by force

lemma closed_approachable:
  fixes S :: "'a::metric_space set"
  shows "closed S \<Longrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e) \<longleftrightarrow> x \<in> S"
  by (metis closure_closed closure_approachable)

lemma closure_contains_Inf:
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_below S"
  shows "Inf S \<in> closure S"
proof -
  have *: "\<forall>x\<in>S. Inf S \<le> x"
    using cInf_lower[of _ S] assms by metis
  {
    fix e :: real
    assume "e > 0"
    then have "Inf S < Inf S + e" by simp
    with assms obtain x where "x \<in> S" "x < Inf S + e"
      by (subst (asm) cInf_less_iff) auto
    with * have "\<exists>x\<in>S. dist x (Inf S) < e"
      by (intro bexI[of _ x]) (auto simp: dist_real_def)
  }
  then show ?thesis unfolding closure_approachable by auto
qed

lemma closure_Int_ballI:
  fixes S :: "'a :: metric_space set"
  assumes "\<And>U. \<lbrakk>openin (subtopology euclidean S) U; U \<noteq> {}\<rbrakk> \<Longrightarrow> T \<inter> U \<noteq> {}"
 shows "S \<subseteq> closure T"
proof (clarsimp simp: closure_approachable dist_commute)
  fix x and e::real
  assume "x \<in> S" "0 < e"
  with assms [of "S \<inter> ball x e"] show "\<exists>y\<in>T. dist x y < e"
    by force
qed

lemma closed_contains_Inf:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> closed S \<Longrightarrow> Inf S \<in> S"
  by (metis closure_contains_Inf closure_closed)

lemma closed_subset_contains_Inf:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<in> C"
  by (metis closure_contains_Inf closure_minimal subset_eq)

lemma atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real
  shows "A \<noteq> {} \<Longrightarrow> a \<le> b \<Longrightarrow> A \<subseteq> {a..b} \<Longrightarrow> Inf A \<in> {a..b}"
  by (rule closed_subset_contains_Inf)
     (auto intro: closed_real_atLeastAtMost intro!: bdd_belowI[of A a])

lemma not_trivial_limit_within_ball:
  "\<not> trivial_limit (at x within S) \<longleftrightarrow> (\<forall>e>0. S \<inter> ball x e - {x} \<noteq> {})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    {
      fix e :: real
      assume "e > 0"
      then obtain y where "y \<in> S - {x}" and "dist y x < e"
        using \<open>?lhs\<close> not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"]
        by auto
      then have "y \<in> S \<inter> ball x e - {x}"
        unfolding ball_def by (simp add: dist_commute)
      then have "S \<inter> ball x e - {x} \<noteq> {}" by blast
    }
    then show ?thesis by auto
  qed
  show ?lhs if ?rhs
  proof -
    {
      fix e :: real
      assume "e > 0"
      then obtain y where "y \<in> S \<inter> ball x e - {x}"
        using \<open>?rhs\<close> by blast
      then have "y \<in> S - {x}" and "dist y x < e"
        unfolding ball_def by (simp_all add: dist_commute)
      then have "\<exists>y \<in> S - {x}. dist y x < e"
        by auto
    }
    then show ?thesis
      using not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"]
      by auto
  qed
qed


subsection \<open>Infimum Distance\<close>

definition "infdist x A = (if A = {} then 0 else INF a:A. dist x a)"

lemma bdd_below_infdist[intro, simp]: "bdd_below (dist x`A)"
  by (auto intro!: zero_le_dist)

lemma infdist_notempty: "A \<noteq> {} \<Longrightarrow> infdist x A = (INF a:A. dist x a)"
  by (simp add: infdist_def)

lemma infdist_nonneg: "0 \<le> infdist x A"
  by (auto simp: infdist_def intro: cINF_greatest)

lemma infdist_le: "a \<in> A \<Longrightarrow> infdist x A \<le> dist x a"
  by (auto intro: cINF_lower simp add: infdist_def)

lemma infdist_le2: "a \<in> A \<Longrightarrow> dist x a \<le> d \<Longrightarrow> infdist x A \<le> d"
  by (auto intro!: cINF_lower2 simp add: infdist_def)

lemma infdist_zero[simp]: "a \<in> A \<Longrightarrow> infdist a A = 0"
  by (auto intro!: antisym infdist_nonneg infdist_le2)

lemma infdist_triangle: "infdist x A \<le> infdist y A + dist x y"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: infdist_def)
next
  case False
  then obtain a where "a \<in> A" by auto
  have "infdist x A \<le> Inf {dist x y + dist y a |a. a \<in> A}"
  proof (rule cInf_greatest)
    from \<open>A \<noteq> {}\<close> show "{dist x y + dist y a |a. a \<in> A} \<noteq> {}"
      by simp
    fix d
    assume "d \<in> {dist x y + dist y a |a. a \<in> A}"
    then obtain a where d: "d = dist x y + dist y a" "a \<in> A"
      by auto
    show "infdist x A \<le> d"
      unfolding infdist_notempty[OF \<open>A \<noteq> {}\<close>]
    proof (rule cINF_lower2)
      show "a \<in> A" by fact
      show "dist x a \<le> d"
        unfolding d by (rule dist_triangle)
    qed simp
  qed
  also have "\<dots> = dist x y + infdist y A"
  proof (rule cInf_eq, safe)
    fix a
    assume "a \<in> A"
    then show "dist x y + infdist y A \<le> dist x y + dist y a"
      by (auto intro: infdist_le)
  next
    fix i
    assume inf: "\<And>d. d \<in> {dist x y + dist y a |a. a \<in> A} \<Longrightarrow> i \<le> d"
    then have "i - dist x y \<le> infdist y A"
      unfolding infdist_notempty[OF \<open>A \<noteq> {}\<close>] using \<open>a \<in> A\<close>
      by (intro cINF_greatest) (auto simp: field_simps)
    then show "i \<le> dist x y + infdist y A"
      by simp
  qed
  finally show ?thesis by simp
qed

lemma in_closure_iff_infdist_zero:
  assumes "A \<noteq> {}"
  shows "x \<in> closure A \<longleftrightarrow> infdist x A = 0"
proof
  assume "x \<in> closure A"
  show "infdist x A = 0"
  proof (rule ccontr)
    assume "infdist x A \<noteq> 0"
    with infdist_nonneg[of x A] have "infdist x A > 0"
      by auto
    then have "ball x (infdist x A) \<inter> closure A = {}"
      apply auto
      apply (metis \<open>x \<in> closure A\<close> closure_approachable dist_commute infdist_le not_less)
      done
    then have "x \<notin> closure A"
      by (metis \<open>0 < infdist x A\<close> centre_in_ball disjoint_iff_not_equal)
    then show False using \<open>x \<in> closure A\<close> by simp
  qed
next
  assume x: "infdist x A = 0"
  then obtain a where "a \<in> A"
    by atomize_elim (metis all_not_in_conv assms)
  show "x \<in> closure A"
    unfolding closure_approachable
    apply safe
  proof (rule ccontr)
    fix e :: real
    assume "e > 0"
    assume "\<not> (\<exists>y\<in>A. dist y x < e)"
    then have "infdist x A \<ge> e" using \<open>a \<in> A\<close>
      unfolding infdist_def
      by (force simp: dist_commute intro: cINF_greatest)
    with x \<open>e > 0\<close> show False by auto
  qed
qed

lemma in_closed_iff_infdist_zero:
  assumes "closed A" "A \<noteq> {}"
  shows "x \<in> A \<longleftrightarrow> infdist x A = 0"
proof -
  have "x \<in> closure A \<longleftrightarrow> infdist x A = 0"
    by (rule in_closure_iff_infdist_zero) fact
  with assms show ?thesis by simp
qed

lemma tendsto_infdist [tendsto_intros]:
  assumes f: "(f \<longlongrightarrow> l) F"
  shows "((\<lambda>x. infdist (f x) A) \<longlongrightarrow> infdist l A) F"
proof (rule tendstoI)
  fix e ::real
  assume "e > 0"
  from tendstoD[OF f this]
  show "eventually (\<lambda>x. dist (infdist (f x) A) (infdist l A) < e) F"
  proof (eventually_elim)
    fix x
    from infdist_triangle[of l A "f x"] infdist_triangle[of "f x" A l]
    have "dist (infdist (f x) A) (infdist l A) \<le> dist (f x) l"
      by (simp add: dist_commute dist_real_def)
    also assume "dist (f x) l < e"
    finally show "dist (infdist (f x) A) (infdist l A) < e" .
  qed
qed

text\<open>Some other lemmas about sequences.\<close>

lemma sequentially_offset: (* TODO: move to Topological_Spaces.thy *)
  assumes "eventually (\<lambda>i. P i) sequentially"
  shows "eventually (\<lambda>i. P (i + k)) sequentially"
  using assms by (rule eventually_sequentially_seg [THEN iffD2])

lemma seq_offset_neg: (* TODO: move to Topological_Spaces.thy *)
  "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> ((\<lambda>i. f(i - k)) \<longlongrightarrow> l) sequentially"
  apply (erule filterlim_compose)
  apply (simp add: filterlim_def le_sequentially eventually_filtermap eventually_sequentially, arith)
  done

lemma seq_harmonic: "((\<lambda>n. inverse (real n)) \<longlongrightarrow> 0) sequentially"
  using LIMSEQ_inverse_real_of_nat by (rule LIMSEQ_imp_Suc) (* TODO: move to Limits.thy *)

subsection \<open>More properties of closed balls\<close>

lemma closed_cball [iff]: "closed (cball x e)"
proof -
  have "closed (dist x -` {..e})"
    by (intro closed_vimage closed_atMost continuous_intros)
  also have "dist x -` {..e} = cball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_cball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0.  cball x e \<subseteq> S)"
proof -
  {
    fix x and e::real
    assume "x\<in>S" "e>0" "ball x e \<subseteq> S"
    then have "\<exists>d>0. cball x d \<subseteq> S" unfolding subset_eq by (rule_tac x="e/2" in exI, auto)
  }
  moreover
  {
    fix x and e::real
    assume "x\<in>S" "e>0" "cball x e \<subseteq> S"
    then have "\<exists>d>0. ball x d \<subseteq> S"
      unfolding subset_eq
      apply (rule_tac x="e/2" in exI, auto)
      done
  }
  ultimately show ?thesis
    unfolding open_contains_ball by auto
qed

lemma open_contains_cball_eq: "open S \<Longrightarrow> (\<forall>x. x \<in> S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S))"
  by (metis open_contains_cball subset_eq order_less_imp_le centre_in_cball)

lemma mem_interior_cball: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S)"
  apply (simp add: interior_def, safe)
  apply (force simp: open_contains_cball)
  apply (rule_tac x="ball x e" in exI)
  apply (simp add: subset_trans [OF ball_subset_cball])
  done

lemma islimpt_ball:
  fixes x y :: "'a::{real_normed_vector,perfect_space}"
  shows "y islimpt ball x e \<longleftrightarrow> 0 < e \<and> y \<in> cball x e"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof
    {
      assume "e \<le> 0"
      then have *: "ball x e = {}"
        using ball_eq_empty[of x e] by auto
      have False using \<open>?lhs\<close>
        unfolding * using islimpt_EMPTY[of y] by auto
    }
    then show "e > 0" by (metis not_less)
    show "y \<in> cball x e"
      using closed_cball[of x e] islimpt_subset[of y "ball x e" "cball x e"]
        ball_subset_cball[of x e] \<open>?lhs\<close>
      unfolding closed_limpt by auto
  qed
  show ?lhs if ?rhs
  proof -
    from that have "e > 0" by auto
    {
      fix d :: real
      assume "d > 0"
      have "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
      proof (cases "d \<le> dist x y")
        case True
        then show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
        proof (cases "x = y")
          case True
          then have False
            using \<open>d \<le> dist x y\<close> \<open>d>0\<close> by auto
          then show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            by auto
        next
          case False
          have "dist x (y - (d / (2 * dist y x)) *\<^sub>R (y - x)) =
            norm (x - y + (d / (2 * norm (y - x))) *\<^sub>R (y - x))"
            unfolding mem_cball mem_ball dist_norm diff_diff_eq2 diff_add_eq[symmetric]
            by auto
          also have "\<dots> = \<bar>- 1 + d / (2 * norm (x - y))\<bar> * norm (x - y)"
            using scaleR_left_distrib[of "- 1" "d / (2 * norm (y - x))", symmetric, of "y - x"]
            unfolding scaleR_minus_left scaleR_one
            by (auto simp: norm_minus_commute)
          also have "\<dots> = \<bar>- norm (x - y) + d / 2\<bar>"
            unfolding abs_mult_pos[of "norm (x - y)", OF norm_ge_zero[of "x - y"]]
            unfolding distrib_right using \<open>x\<noteq>y\<close>  by auto
          also have "\<dots> \<le> e - d/2" using \<open>d \<le> dist x y\<close> and \<open>d>0\<close> and \<open>?rhs\<close>
            by (auto simp: dist_norm)
          finally have "y - (d / (2 * dist y x)) *\<^sub>R (y - x) \<in> ball x e" using \<open>d>0\<close>
            by auto
          moreover
          have "(d / (2*dist y x)) *\<^sub>R (y - x) \<noteq> 0"
            using \<open>x\<noteq>y\<close>[unfolded dist_nz] \<open>d>0\<close> unfolding scaleR_eq_0_iff
            by (auto simp: dist_commute)
          moreover
          have "dist (y - (d / (2 * dist y x)) *\<^sub>R (y - x)) y < d"
            unfolding dist_norm
            apply simp
            unfolding norm_minus_cancel
            using \<open>d > 0\<close> \<open>x\<noteq>y\<close>[unfolded dist_nz] dist_commute[of x y]
            unfolding dist_norm
            apply auto
            done
          ultimately show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            apply (rule_tac x = "y - (d / (2*dist y x)) *\<^sub>R (y - x)" in bexI)
            apply auto
            done
        qed
      next
        case False
        then have "d > dist x y" by auto
        show "\<exists>x' \<in> ball x e. x' \<noteq> y \<and> dist x' y < d"
        proof (cases "x = y")
          case True
          obtain z where **: "z \<noteq> y" "dist z y < min e d"
            using perfect_choose_dist[of "min e d" y]
            using \<open>d > 0\<close> \<open>e>0\<close> by auto
          show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            unfolding \<open>x = y\<close>
            using \<open>z \<noteq> y\<close> **
            apply (rule_tac x=z in bexI)
            apply (auto simp: dist_commute)
            done
        next
          case False
          then show "\<exists>x'\<in>ball x e. x' \<noteq> y \<and> dist x' y < d"
            using \<open>d>0\<close> \<open>d > dist x y\<close> \<open>?rhs\<close>
            apply (rule_tac x=x in bexI, auto)
            done
        qed
      qed
    }
    then show ?thesis
      unfolding mem_cball islimpt_approachable mem_ball by auto
  qed
qed

lemma closure_ball_lemma:
  fixes x y :: "'a::real_normed_vector"
  assumes "x \<noteq> y"
  shows "y islimpt ball x (dist x y)"
proof (rule islimptI)
  fix T
  assume "y \<in> T" "open T"
  then obtain r where "0 < r" "\<forall>z. dist z y < r \<longrightarrow> z \<in> T"
    unfolding open_dist by fast
  (* choose point between x and y, within distance r of y. *)
  define k where "k = min 1 (r / (2 * dist x y))"
  define z where "z = y + scaleR k (x - y)"
  have z_def2: "z = x + scaleR (1 - k) (y - x)"
    unfolding z_def by (simp add: algebra_simps)
  have "dist z y < r"
    unfolding z_def k_def using \<open>0 < r\<close>
    by (simp add: dist_norm min_def)
  then have "z \<in> T"
    using \<open>\<forall>z. dist z y < r \<longrightarrow> z \<in> T\<close> by simp
  have "dist x z < dist x y"
    unfolding z_def2 dist_norm
    apply (simp add: norm_minus_commute)
    apply (simp only: dist_norm [symmetric])
    apply (subgoal_tac "\<bar>1 - k\<bar> * dist x y < 1 * dist x y", simp)
    apply (rule mult_strict_right_mono)
    apply (simp add: k_def \<open>0 < r\<close> \<open>x \<noteq> y\<close>)
    apply (simp add: \<open>x \<noteq> y\<close>)
    done
  then have "z \<in> ball x (dist x y)"
    by simp
  have "z \<noteq> y"
    unfolding z_def k_def using \<open>x \<noteq> y\<close> \<open>0 < r\<close>
    by (simp add: min_def)
  show "\<exists>z\<in>ball x (dist x y). z \<in> T \<and> z \<noteq> y"
    using \<open>z \<in> ball x (dist x y)\<close> \<open>z \<in> T\<close> \<open>z \<noteq> y\<close>
    by fast
qed

lemma closure_ball [simp]:
  fixes x :: "'a::real_normed_vector"
  shows "0 < e \<Longrightarrow> closure (ball x e) = cball x e"
  apply (rule equalityI)
  apply (rule closure_minimal)
  apply (rule ball_subset_cball)
  apply (rule closed_cball)
  apply (rule subsetI, rename_tac y)
  apply (simp add: le_less [where 'a=real])
  apply (erule disjE)
  apply (rule subsetD [OF closure_subset], simp)
  apply (simp add: closure_def, clarify)
  apply (rule closure_ball_lemma)
  apply (simp add: zero_less_dist_iff)
  done

(* In a trivial vector space, this fails for e = 0. *)
lemma interior_cball [simp]:
  fixes x :: "'a::{real_normed_vector, perfect_space}"
  shows "interior (cball x e) = ball x e"
proof (cases "e \<ge> 0")
  case False note cs = this
  from cs have null: "ball x e = {}"
    using ball_empty[of e x] by auto
  moreover
  {
    fix y
    assume "y \<in> cball x e"
    then have False
      by (metis ball_eq_empty null cs dist_eq_0_iff dist_le_zero_iff empty_subsetI mem_cball subset_antisym subset_ball)
  }
  then have "cball x e = {}" by auto
  then have "interior (cball x e) = {}"
    using interior_empty by auto
  ultimately show ?thesis by blast
next
  case True note cs = this
  have "ball x e \<subseteq> cball x e"
    using ball_subset_cball by auto
  moreover
  {
    fix S y
    assume as: "S \<subseteq> cball x e" "open S" "y\<in>S"
    then obtain d where "d>0" and d: "\<forall>x'. dist x' y < d \<longrightarrow> x' \<in> S"
      unfolding open_dist by blast
    then obtain xa where xa_y: "xa \<noteq> y" and xa: "dist xa y < d"
      using perfect_choose_dist [of d] by auto
    have "xa \<in> S"
      using d[THEN spec[where x = xa]]
      using xa by (auto simp: dist_commute)
    then have xa_cball: "xa \<in> cball x e"
      using as(1) by auto
    then have "y \<in> ball x e"
    proof (cases "x = y")
      case True
      then have "e > 0" using cs order.order_iff_strict xa_cball xa_y by fastforce
      then show "y \<in> ball x e"
        using \<open>x = y \<close> by simp
    next
      case False
      have "dist (y + (d / 2 / dist y x) *\<^sub>R (y - x)) y < d"
        unfolding dist_norm
        using \<open>d>0\<close> norm_ge_zero[of "y - x"] \<open>x \<noteq> y\<close> by auto
      then have *: "y + (d / 2 / dist y x) *\<^sub>R (y - x) \<in> cball x e"
        using d as(1)[unfolded subset_eq] by blast
      have "y - x \<noteq> 0" using \<open>x \<noteq> y\<close> by auto
      hence **:"d / (2 * norm (y - x)) > 0"
        unfolding zero_less_norm_iff[symmetric] using \<open>d>0\<close> by auto
      have "dist (y + (d / 2 / dist y x) *\<^sub>R (y - x)) x =
        norm (y + (d / (2 * norm (y - x))) *\<^sub>R y - (d / (2 * norm (y - x))) *\<^sub>R x - x)"
        by (auto simp: dist_norm algebra_simps)
      also have "\<dots> = norm ((1 + d / (2 * norm (y - x))) *\<^sub>R (y - x))"
        by (auto simp: algebra_simps)
      also have "\<dots> = \<bar>1 + d / (2 * norm (y - x))\<bar> * norm (y - x)"
        using ** by auto
      also have "\<dots> = (dist y x) + d/2"
        using ** by (auto simp: distrib_right dist_norm)
      finally have "e \<ge> dist x y +d/2"
        using *[unfolded mem_cball] by (auto simp: dist_commute)
      then show "y \<in> ball x e"
        unfolding mem_ball using \<open>d>0\<close> by auto
    qed
  }
  then have "\<forall>S \<subseteq> cball x e. open S \<longrightarrow> S \<subseteq> ball x e"
    by auto
  ultimately show ?thesis
    using interior_unique[of "ball x e" "cball x e"]
    using open_ball[of x e]
    by auto
qed

lemma interior_ball [simp]: "interior (ball x e) = ball x e"
  by (simp add: interior_open)

lemma frontier_ball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "0 < e \<Longrightarrow> frontier (ball a e) = sphere a e"
  by (force simp: frontier_def)

lemma frontier_cball [simp]:
  fixes a :: "'a::{real_normed_vector, perfect_space}"
  shows "frontier (cball a e) = sphere a e"
  by (force simp: frontier_def)

lemma cball_eq_empty [simp]: "cball x e = {} \<longleftrightarrow> e < 0"
  apply (simp add: set_eq_iff not_le)
  apply (metis zero_le_dist dist_self order_less_le_trans)
  done

lemma cball_empty [simp]: "e < 0 \<Longrightarrow> cball x e = {}"
  by (simp add: cball_eq_empty)

lemma cball_eq_sing:
  fixes x :: "'a::{metric_space,perfect_space}"
  shows "cball x e = {x} \<longleftrightarrow> e = 0"
proof (rule linorder_cases)
  assume e: "0 < e"
  obtain a where "a \<noteq> x" "dist a x < e"
    using perfect_choose_dist [OF e] by auto
  then have "a \<noteq> x" "dist x a \<le> e"
    by (auto simp: dist_commute)
  with e show ?thesis by (auto simp: set_eq_iff)
qed auto

lemma cball_sing:
  fixes x :: "'a::metric_space"
  shows "e = 0 \<Longrightarrow> cball x e = {x}"
  by (auto simp: set_eq_iff)

lemma ball_divide_subset: "d \<ge> 1 \<Longrightarrow> ball x (e/d) \<subseteq> ball x e"
  apply (cases "e \<le> 0")
  apply (simp add: ball_empty divide_simps)
  apply (rule subset_ball)
  apply (simp add: divide_simps)
  done

lemma ball_divide_subset_numeral: "ball x (e / numeral w) \<subseteq> ball x e"
  using ball_divide_subset one_le_numeral by blast

lemma cball_divide_subset: "d \<ge> 1 \<Longrightarrow> cball x (e/d) \<subseteq> cball x e"
  apply (cases "e < 0")
  apply (simp add: divide_simps)
  apply (rule subset_cball)
  apply (metis div_by_1 frac_le not_le order_refl zero_less_one)
  done

lemma cball_divide_subset_numeral: "cball x (e / numeral w) \<subseteq> cball x e"
  using cball_divide_subset one_le_numeral by blast


subsection \<open>Boundedness\<close>

  (* FIXME: This has to be unified with BSEQ!! *)
definition (in metric_space) bounded :: "'a set \<Rightarrow> bool"
  where "bounded S \<longleftrightarrow> (\<exists>x e. \<forall>y\<in>S. dist x y \<le> e)"

lemma bounded_subset_cball: "bounded S \<longleftrightarrow> (\<exists>e x. S \<subseteq> cball x e \<and> 0 \<le> e)"
  unfolding bounded_def subset_eq  by auto (meson order_trans zero_le_dist)

lemma bounded_any_center: "bounded S \<longleftrightarrow> (\<exists>e. \<forall>y\<in>S. dist a y \<le> e)"
  unfolding bounded_def
  by auto (metis add.commute add_le_cancel_right dist_commute dist_triangle_le)

lemma bounded_iff: "bounded S \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. norm x \<le> a)"
  unfolding bounded_any_center [where a=0]
  by (simp add: dist_norm)

lemma bdd_above_norm: "bdd_above (norm ` X) \<longleftrightarrow> bounded X"
  by (simp add: bounded_iff bdd_above_def)

lemma bounded_norm_comp: "bounded ((\<lambda>x. norm (f x)) ` S) = bounded (f ` S)"
  by (simp add: bounded_iff)

lemma boundedI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
  shows "bounded S"
  using assms bounded_iff by blast

lemma bounded_empty [simp]: "bounded {}"
  by (simp add: bounded_def)

lemma bounded_subset: "bounded T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> bounded S"
  by (metis bounded_def subset_eq)

lemma bounded_interior[intro]: "bounded S \<Longrightarrow> bounded(interior S)"
  by (metis bounded_subset interior_subset)

lemma bounded_closure[intro]:
  assumes "bounded S"
  shows "bounded (closure S)"
proof -
  from assms obtain x and a where a: "\<forall>y\<in>S. dist x y \<le> a"
    unfolding bounded_def by auto
  {
    fix y
    assume "y \<in> closure S"
    then obtain f where f: "\<forall>n. f n \<in> S"  "(f \<longlongrightarrow> y) sequentially"
      unfolding closure_sequential by auto
    have "\<forall>n. f n \<in> S \<longrightarrow> dist x (f n) \<le> a" using a by simp
    then have "eventually (\<lambda>n. dist x (f n) \<le> a) sequentially"
      by (simp add: f(1))
    have "dist x y \<le> a"
      apply (rule Lim_dist_ubound [of sequentially f])
      apply (rule trivial_limit_sequentially)
      apply (rule f(2))
      apply fact
      done
  }
  then show ?thesis
    unfolding bounded_def by auto
qed

lemma bounded_closure_image: "bounded (f ` closure S) \<Longrightarrow> bounded (f ` S)"
  by (simp add: bounded_subset closure_subset image_mono)

lemma bounded_cball[simp,intro]: "bounded (cball x e)"
  apply (simp add: bounded_def)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=e in exI, auto)
  done

lemma bounded_ball[simp,intro]: "bounded (ball x e)"
  by (metis ball_subset_cball bounded_cball bounded_subset)

lemma bounded_Un[simp]: "bounded (S \<union> T) \<longleftrightarrow> bounded S \<and> bounded T"
  by (auto simp: bounded_def) (metis Un_iff bounded_any_center le_max_iff_disj)

lemma bounded_Union[intro]: "finite F \<Longrightarrow> \<forall>S\<in>F. bounded S \<Longrightarrow> bounded (\<Union>F)"
  by (induct rule: finite_induct[of F]) auto

lemma bounded_UN [intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. bounded (B x) \<Longrightarrow> bounded (\<Union>x\<in>A. B x)"
  by (induct set: finite) auto

lemma bounded_insert [simp]: "bounded (insert x S) \<longleftrightarrow> bounded S"
proof -
  have "\<forall>y\<in>{x}. dist x y \<le> 0"
    by simp
  then have "bounded {x}"
    unfolding bounded_def by fast
  then show ?thesis
    by (metis insert_is_Un bounded_Un)
qed

lemma bounded_subset_ballI: "S \<subseteq> ball x r \<Longrightarrow> bounded S"
  by (meson bounded_ball bounded_subset)

lemma bounded_subset_ballD:
  assumes "bounded S" shows "\<exists>r. 0 < r \<and> S \<subseteq> ball x r"
proof -
  obtain e::real and y where "S \<subseteq> cball y e"  "0 \<le> e"
    using assms by (auto simp: bounded_subset_cball)
  then show ?thesis
    apply (rule_tac x="dist x y + e + 1" in exI)
    apply (simp add: add.commute add_pos_nonneg)
    apply (erule subset_trans)
    apply (clarsimp simp add: cball_def)
    by (metis add_le_cancel_right add_strict_increasing dist_commute dist_triangle_le zero_less_one)
qed

lemma finite_imp_bounded [intro]: "finite S \<Longrightarrow> bounded S"
  by (induct set: finite) simp_all

lemma bounded_pos: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x \<le> b)"
  apply (simp add: bounded_iff)
  apply (subgoal_tac "\<And>x (y::real). 0 < 1 + \<bar>y\<bar> \<and> (x \<le> y \<longrightarrow> x \<le> 1 + \<bar>y\<bar>)")
  apply metis
  apply arith
  done

lemma bounded_pos_less: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x < b)"
  apply (simp add: bounded_pos)
  apply (safe; rule_tac x="b+1" in exI; force)
  done

lemma Bseq_eq_bounded:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "Bseq f \<longleftrightarrow> bounded (range f)"
  unfolding Bseq_def bounded_pos by auto

lemma bounded_Int[intro]: "bounded S \<or> bounded T \<Longrightarrow> bounded (S \<inter> T)"
  by (metis Int_lower1 Int_lower2 bounded_subset)

lemma bounded_diff[intro]: "bounded S \<Longrightarrow> bounded (S - T)"
  by (metis Diff_subset bounded_subset)

lemma not_bounded_UNIV[simp]:
  "\<not> bounded (UNIV :: 'a::{real_normed_vector, perfect_space} set)"
proof (auto simp: bounded_pos not_le)
  obtain x :: 'a where "x \<noteq> 0"
    using perfect_choose_dist [OF zero_less_one] by fast
  fix b :: real
  assume b: "b >0"
  have b1: "b +1 \<ge> 0"
    using b by simp
  with \<open>x \<noteq> 0\<close> have "b < norm (scaleR (b + 1) (sgn x))"
    by (simp add: norm_sgn)
  then show "\<exists>x::'a. b < norm x" ..
qed

corollary cobounded_imp_unbounded:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded (- S) \<Longrightarrow> ~ (bounded S)"
  using bounded_Un [of S "-S"]  by (simp add: sup_compl_top)

lemma bounded_dist_comp:
  assumes "bounded (f ` S)" "bounded (g ` S)"
  shows "bounded ((\<lambda>x. dist (f x) (g x)) ` S)"
proof -
  from assms obtain M1 M2 where *: "dist (f x) undefined \<le> M1" "dist undefined (g x) \<le> M2" if "x \<in> S" for x
    by (auto simp: bounded_any_center[of _ undefined] dist_commute)
  have "dist (f x) (g x) \<le> M1 + M2" if "x \<in> S" for x
    using *[OF that]
    by (rule order_trans[OF dist_triangle add_mono])
  then show ?thesis
    by (auto intro!: boundedI)
qed

lemma bounded_linear_image:
  assumes "bounded S"
    and "bounded_linear f"
  shows "bounded (f ` S)"
proof -
  from assms(1) obtain b where b: "b > 0" "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  from assms(2) obtain B where B: "B > 0" "\<forall>x. norm (f x) \<le> B * norm x"
    using bounded_linear.pos_bounded by (auto simp: ac_simps)
  {
    fix x
    assume "x \<in> S"
    then have "norm x \<le> b"
      using b by auto
    then have "norm (f x) \<le> B * b"
      using B(2)
      apply (erule_tac x=x in allE)
      apply (metis B(1) B(2) order_trans mult_le_cancel_left_pos)
      done
  }
  then show ?thesis
    unfolding bounded_pos
    apply (rule_tac x="b*B" in exI)
    using b B by (auto simp: mult.commute)
qed

lemma bounded_scaling:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. c *\<^sub>R x) ` S)"
  apply (rule bounded_linear_image, assumption)
  apply (rule bounded_linear_scaleR_right)
  done

lemma bounded_scaleR_comp:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  shows "bounded ((\<lambda>x. r *\<^sub>R f x) ` S)"
  using bounded_scaling[of "f ` S" r] assms
  by (auto simp: image_image)

lemma bounded_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S"
  shows "bounded ((\<lambda>x. a + x) ` S)"
proof -
  from assms obtain b where b: "b > 0" "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  {
    fix x
    assume "x \<in> S"
    then have "norm (a + x) \<le> b + norm a"
      using norm_triangle_ineq[of a x] b by auto
  }
  then show ?thesis
    unfolding bounded_pos
    using norm_ge_zero[of a] b(1) and add_strict_increasing[of b 0 "norm a"]
    by (auto intro!: exI[of _ "b + norm a"])
qed

lemma bounded_translation_minus:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. x - a) ` S)"
using bounded_translation [of S "-a"] by simp

lemma bounded_uminus [simp]:
  fixes X :: "'a::real_normed_vector set"
  shows "bounded (uminus ` X) \<longleftrightarrow> bounded X"
by (auto simp: bounded_def dist_norm; rule_tac x="-x" in exI; force simp: add.commute norm_minus_commute)

lemma uminus_bounded_comp [simp]:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "bounded ((\<lambda>x. - f x) ` S) \<longleftrightarrow> bounded (f ` S)"
  using bounded_uminus[of "f ` S"]
  by (auto simp: image_image)

lemma bounded_plus_comp:
  fixes f g::"'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  assumes "bounded (g ` S)"
  shows "bounded ((\<lambda>x. f x + g x) ` S)"
proof -
  {
    fix B C
    assume "\<And>x. x\<in>S \<Longrightarrow> norm (f x) \<le> B" "\<And>x. x\<in>S \<Longrightarrow> norm (g x) \<le> C"
    then have "\<And>x. x \<in> S \<Longrightarrow> norm (f x + g x) \<le> B + C"
      by (auto intro!: norm_triangle_le add_mono)
  } then show ?thesis
    using assms by (fastforce simp: bounded_iff)
qed

lemma bounded_minus_comp:
  "bounded (f ` S) \<Longrightarrow> bounded (g ` S) \<Longrightarrow> bounded ((\<lambda>x. f x - g x) ` S)"
  for f g::"'a \<Rightarrow> 'b::real_normed_vector"
  using bounded_plus_comp[of "f" S "\<lambda>x. - g x"]
  by auto


subsection\<open>Some theorems on sups and infs using the notion "bounded".\<close>

lemma bounded_real: "bounded (S::real set) \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. \<bar>x\<bar> \<le> a)"
  by (simp add: bounded_iff)

lemma bounded_imp_bdd_above: "bounded S \<Longrightarrow> bdd_above (S :: real set)"
  by (auto simp: bounded_def bdd_above_def dist_real_def)
     (metis abs_le_D1 abs_minus_commute diff_le_eq)

lemma bounded_imp_bdd_below: "bounded S \<Longrightarrow> bdd_below (S :: real set)"
  by (auto simp: bounded_def bdd_below_def dist_real_def)
     (metis abs_le_D1 add.commute diff_le_eq)

lemma bounded_inner_imp_bdd_above:
  assumes "bounded s"
    shows "bdd_above ((\<lambda>x. x \<bullet> a) ` s)"
by (simp add: assms bounded_imp_bdd_above bounded_linear_image bounded_linear_inner_left)

lemma bounded_inner_imp_bdd_below:
  assumes "bounded s"
    shows "bdd_below ((\<lambda>x. x \<bullet> a) ` s)"
by (simp add: assms bounded_imp_bdd_below bounded_linear_image bounded_linear_inner_left)

lemma bounded_has_Sup:
  fixes S :: "real set"
  assumes "bounded S"
    and "S \<noteq> {}"
  shows "\<forall>x\<in>S. x \<le> Sup S"
    and "\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> Sup S \<le> b"
proof
  show "\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> Sup S \<le> b"
    using assms by (metis cSup_least)
qed (metis cSup_upper assms(1) bounded_imp_bdd_above)

lemma Sup_insert:
  fixes S :: "real set"
  shows "bounded S \<Longrightarrow> Sup (insert x S) = (if S = {} then x else max x (Sup S))"
  by (auto simp: bounded_imp_bdd_above sup_max cSup_insert_If)

lemma Sup_insert_finite:
  fixes S :: "'a::conditionally_complete_linorder set"
  shows "finite S \<Longrightarrow> Sup (insert x S) = (if S = {} then x else max x (Sup S))"
by (simp add: cSup_insert sup_max)

lemma bounded_has_Inf:
  fixes S :: "real set"
  assumes "bounded S"
    and "S \<noteq> {}"
  shows "\<forall>x\<in>S. x \<ge> Inf S"
    and "\<forall>b. (\<forall>x\<in>S. x \<ge> b) \<longrightarrow> Inf S \<ge> b"
proof
  show "\<forall>b. (\<forall>x\<in>S. x \<ge> b) \<longrightarrow> Inf S \<ge> b"
    using assms by (metis cInf_greatest)
qed (metis cInf_lower assms(1) bounded_imp_bdd_below)

lemma Inf_insert:
  fixes S :: "real set"
  shows "bounded S \<Longrightarrow> Inf (insert x S) = (if S = {} then x else min x (Inf S))"
  by (auto simp: bounded_imp_bdd_below inf_min cInf_insert_If)

lemma Inf_insert_finite:
  fixes S :: "'a::conditionally_complete_linorder set"
  shows "finite S \<Longrightarrow> Inf (insert x S) = (if S = {} then x else min x (Inf S))"
by (simp add: cInf_eq_Min)

lemma finite_imp_less_Inf:
  fixes a :: "'a::conditionally_complete_linorder"
  shows "\<lbrakk>finite X; x \<in> X; \<And>x. x\<in>X \<Longrightarrow> a < x\<rbrakk> \<Longrightarrow> a < Inf X"
  by (induction X rule: finite_induct) (simp_all add: cInf_eq_Min Inf_insert_finite)

lemma finite_less_Inf_iff:
  fixes a :: "'a :: conditionally_complete_linorder"
  shows "\<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> a < Inf X \<longleftrightarrow> (\<forall>x \<in> X. a < x)"
  by (auto simp: cInf_eq_Min)

lemma finite_imp_Sup_less:
  fixes a :: "'a::conditionally_complete_linorder"
  shows "\<lbrakk>finite X; x \<in> X; \<And>x. x\<in>X \<Longrightarrow> a > x\<rbrakk> \<Longrightarrow> a > Sup X"
  by (induction X rule: finite_induct) (simp_all add: cSup_eq_Max Sup_insert_finite)

lemma finite_Sup_less_iff:
  fixes a :: "'a :: conditionally_complete_linorder"
  shows "\<lbrakk>finite X; X \<noteq> {}\<rbrakk> \<Longrightarrow> a > Sup X \<longleftrightarrow> (\<forall>x \<in> X. a > x)"
  by (auto simp: cSup_eq_Max)

subsection \<open>Compactness\<close>

subsubsection \<open>Bolzano-Weierstrass property\<close>

lemma heine_borel_imp_bolzano_weierstrass:
  assumes "compact s"
    and "infinite t"
    and "t \<subseteq> s"
  shows "\<exists>x \<in> s. x islimpt t"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> s. x islimpt t)"
  then obtain f where f: "\<forall>x\<in>s. x \<in> f x \<and> open (f x) \<and> (\<forall>y\<in>t. y \<in> f x \<longrightarrow> y = x)"
    unfolding islimpt_def
    using bchoice[of s "\<lambda> x T. x \<in> T \<and> open T \<and> (\<forall>y\<in>t. y \<in> T \<longrightarrow> y = x)"]
    by auto
  obtain g where g: "g \<subseteq> {t. \<exists>x. x \<in> s \<and> t = f x}" "finite g" "s \<subseteq> \<Union>g"
    using assms(1)[unfolded compact_eq_heine_borel, THEN spec[where x="{t. \<exists>x. x\<in>s \<and> t = f x}"]]
    using f by auto
  from g(1,3) have g':"\<forall>x\<in>g. \<exists>xa \<in> s. x = f xa"
    by auto
  {
    fix x y
    assume "x \<in> t" "y \<in> t" "f x = f y"
    then have "x \<in> f x"  "y \<in> f x \<longrightarrow> y = x"
      using f[THEN bspec[where x=x]] and \<open>t \<subseteq> s\<close> by auto
    then have "x = y"
      using \<open>f x = f y\<close> and f[THEN bspec[where x=y]] and \<open>y \<in> t\<close> and \<open>t \<subseteq> s\<close>
      by auto
  }
  then have "inj_on f t"
    unfolding inj_on_def by simp
  then have "infinite (f ` t)"
    using assms(2) using finite_imageD by auto
  moreover
  {
    fix x
    assume "x \<in> t" "f x \<notin> g"
    from g(3) assms(3) \<open>x \<in> t\<close> obtain h where "h \<in> g" and "x \<in> h"
      by auto
    then obtain y where "y \<in> s" "h = f y"
      using g'[THEN bspec[where x=h]] by auto
    then have "y = x"
      using f[THEN bspec[where x=y]] and \<open>x\<in>t\<close> and \<open>x\<in>h\<close>[unfolded \<open>h = f y\<close>]
      by auto
    then have False
      using \<open>f x \<notin> g\<close> \<open>h \<in> g\<close> unfolding \<open>h = f y\<close>
      by auto
  }
  then have "f ` t \<subseteq> g" by auto
  ultimately show False
    using g(2) using finite_subset by auto
qed

lemma acc_point_range_imp_convergent_subsequence:
  fixes l :: "'a :: first_countable_topology"
  assumes l: "\<forall>U. l\<in>U \<longrightarrow> open U \<longrightarrow> infinite (U \<inter> range f)"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
proof -
  from countable_basis_at_decseq[of l]
  obtain A where A:
      "\<And>i. open (A i)"
      "\<And>i. l \<in> A i"
      "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast
  define s where "s n i = (SOME j. i < j \<and> f j \<in> A (Suc n))" for n i
  {
    fix n i
    have "infinite (A (Suc n) \<inter> range f - f`{.. i})"
      using l A by auto
    then have "\<exists>x. x \<in> A (Suc n) \<inter> range f - f`{.. i}"
      unfolding ex_in_conv by (intro notI) simp
    then have "\<exists>j. f j \<in> A (Suc n) \<and> j \<notin> {.. i}"
      by auto
    then have "\<exists>a. i < a \<and> f a \<in> A (Suc n)"
      by (auto simp: not_le)
    then have "i < s n i" "f (s n i) \<in> A (Suc n)"
      unfolding s_def by (auto intro: someI2_ex)
  }
  note s = this
  define r where "r = rec_nat (s 0 0) s"
  have "strict_mono r"
    by (auto simp: r_def s strict_mono_Suc_iff)
  moreover
  have "(\<lambda>n. f (r n)) \<longlonglongrightarrow> l"
  proof (rule topological_tendstoI)
    fix S
    assume "open S" "l \<in> S"
    with A(3) have "eventually (\<lambda>i. A i \<subseteq> S) sequentially"
      by auto
    moreover
    {
      fix i
      assume "Suc 0 \<le> i"
      then have "f (r i) \<in> A i"
        by (cases i) (simp_all add: r_def s)
    }
    then have "eventually (\<lambda>i. f (r i) \<in> A i) sequentially"
      by (auto simp: eventually_sequentially)
    ultimately show "eventually (\<lambda>i. f (r i) \<in> S) sequentially"
      by eventually_elim auto
  qed
  ultimately show "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by (auto simp: convergent_def comp_def)
qed

lemma sequence_infinite_lemma:
  fixes f :: "nat \<Rightarrow> 'a::t1_space"
  assumes "\<forall>n. f n \<noteq> l"
    and "(f \<longlongrightarrow> l) sequentially"
  shows "infinite (range f)"
proof
  assume "finite (range f)"
  then have "closed (range f)"
    by (rule finite_imp_closed)
  then have "open (- range f)"
    by (rule open_Compl)
  from assms(1) have "l \<in> - range f"
    by auto
  from assms(2) have "eventually (\<lambda>n. f n \<in> - range f) sequentially"
    using \<open>open (- range f)\<close> \<open>l \<in> - range f\<close>
    by (rule topological_tendstoD)
  then show False
    unfolding eventually_sequentially
    by auto
qed

lemma closure_insert:
  fixes x :: "'a::t1_space"
  shows "closure (insert x s) = insert x (closure s)"
  apply (rule closure_unique)
  apply (rule insert_mono [OF closure_subset])
  apply (rule closed_insert [OF closed_closure])
  apply (simp add: closure_minimal)
  done

lemma islimpt_insert:
  fixes x :: "'a::t1_space"
  shows "x islimpt (insert a s) \<longleftrightarrow> x islimpt s"
proof
  assume *: "x islimpt (insert a s)"
  show "x islimpt s"
  proof (rule islimptI)
    fix t
    assume t: "x \<in> t" "open t"
    show "\<exists>y\<in>s. y \<in> t \<and> y \<noteq> x"
    proof (cases "x = a")
      case True
      obtain y where "y \<in> insert a s" "y \<in> t" "y \<noteq> x"
        using * t by (rule islimptE)
      with \<open>x = a\<close> show ?thesis by auto
    next
      case False
      with t have t': "x \<in> t - {a}" "open (t - {a})"
        by (simp_all add: open_Diff)
      obtain y where "y \<in> insert a s" "y \<in> t - {a}" "y \<noteq> x"
        using * t' by (rule islimptE)
      then show ?thesis by auto
    qed
  qed
next
  assume "x islimpt s"
  then show "x islimpt (insert a s)"
    by (rule islimpt_subset) auto
qed

lemma islimpt_finite:
  fixes x :: "'a::t1_space"
  shows "finite s \<Longrightarrow> \<not> x islimpt s"
  by (induct set: finite) (simp_all add: islimpt_insert)

lemma islimpt_Un_finite:
  fixes x :: "'a::t1_space"
  shows "finite s \<Longrightarrow> x islimpt (s \<union> t) \<longleftrightarrow> x islimpt t"
  by (simp add: islimpt_Un islimpt_finite)

lemma islimpt_eq_acc_point:
  fixes l :: "'a :: t1_space"
  shows "l islimpt S \<longleftrightarrow> (\<forall>U. l\<in>U \<longrightarrow> open U \<longrightarrow> infinite (U \<inter> S))"
proof (safe intro!: islimptI)
  fix U
  assume "l islimpt S" "l \<in> U" "open U" "finite (U \<inter> S)"
  then have "l islimpt S" "l \<in> (U - (U \<inter> S - {l}))" "open (U - (U \<inter> S - {l}))"
    by (auto intro: finite_imp_closed)
  then show False
    by (rule islimptE) auto
next
  fix T
  assume *: "\<forall>U. l\<in>U \<longrightarrow> open U \<longrightarrow> infinite (U \<inter> S)" "l \<in> T" "open T"
  then have "infinite (T \<inter> S - {l})"
    by auto
  then have "\<exists>x. x \<in> (T \<inter> S - {l})"
    unfolding ex_in_conv by (intro notI) simp
  then show "\<exists>y\<in>S. y \<in> T \<and> y \<noteq> l"
    by auto
qed

corollary infinite_openin:
  fixes S :: "'a :: t1_space set"
  shows "\<lbrakk>openin (subtopology euclidean U) S; x \<in> S; x islimpt U\<rbrakk> \<Longrightarrow> infinite S"
  by (clarsimp simp add: openin_open islimpt_eq_acc_point inf_commute)

lemma islimpt_range_imp_convergent_subsequence:
  fixes l :: "'a :: {t1_space, first_countable_topology}"
  assumes l: "l islimpt (range f)"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
  using l unfolding islimpt_eq_acc_point
  by (rule acc_point_range_imp_convergent_subsequence)

lemma islimpt_eq_infinite_ball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> ball x e))"
  apply (simp add: islimpt_eq_acc_point, safe)
   apply (metis Int_commute open_ball centre_in_ball)
  by (metis open_contains_ball Int_mono finite_subset inf_commute subset_refl)

lemma islimpt_eq_infinite_cball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> cball x e))"
  apply (simp add: islimpt_eq_infinite_ball, safe)
   apply (meson Int_mono ball_subset_cball finite_subset order_refl)
  by (metis open_ball centre_in_ball finite_Int inf.absorb_iff2 inf_assoc open_contains_cball_eq)

lemma sequence_unique_limpt:
  fixes f :: "nat \<Rightarrow> 'a::t2_space"
  assumes "(f \<longlongrightarrow> l) sequentially"
    and "l' islimpt (range f)"
  shows "l' = l"
proof (rule ccontr)
  assume "l' \<noteq> l"
  obtain s t where "open s" "open t" "l' \<in> s" "l \<in> t" "s \<inter> t = {}"
    using hausdorff [OF \<open>l' \<noteq> l\<close>] by auto
  have "eventually (\<lambda>n. f n \<in> t) sequentially"
    using assms(1) \<open>open t\<close> \<open>l \<in> t\<close> by (rule topological_tendstoD)
  then obtain N where "\<forall>n\<ge>N. f n \<in> t"
    unfolding eventually_sequentially by auto

  have "UNIV = {..<N} \<union> {N..}"
    by auto
  then have "l' islimpt (f ` ({..<N} \<union> {N..}))"
    using assms(2) by simp
  then have "l' islimpt (f ` {..<N} \<union> f ` {N..})"
    by (simp add: image_Un)
  then have "l' islimpt (f ` {N..})"
    by (simp add: islimpt_Un_finite)
  then obtain y where "y \<in> f ` {N..}" "y \<in> s" "y \<noteq> l'"
    using \<open>l' \<in> s\<close> \<open>open s\<close> by (rule islimptE)
  then obtain n where "N \<le> n" "f n \<in> s" "f n \<noteq> l'"
    by auto
  with \<open>\<forall>n\<ge>N. f n \<in> t\<close> have "f n \<in> s \<inter> t"
    by simp
  with \<open>s \<inter> t = {}\<close> show False
    by simp
qed

lemma bolzano_weierstrass_imp_closed:
  fixes s :: "'a::{first_countable_topology,t2_space} set"
  assumes "\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t)"
  shows "closed s"
proof -
  {
    fix x l
    assume as: "\<forall>n::nat. x n \<in> s" "(x \<longlongrightarrow> l) sequentially"
    then have "l \<in> s"
    proof (cases "\<forall>n. x n \<noteq> l")
      case False
      then show "l\<in>s" using as(1) by auto
    next
      case True note cas = this
      with as(2) have "infinite (range x)"
        using sequence_infinite_lemma[of x l] by auto
      then obtain l' where "l'\<in>s" "l' islimpt (range x)"
        using assms[THEN spec[where x="range x"]] as(1) by auto
      then show "l\<in>s" using sequence_unique_limpt[of x l l']
        using as cas by auto
    qed
  }
  then show ?thesis
    unfolding closed_sequential_limits by fast
qed

lemma compact_imp_bounded:
  assumes "compact U"
  shows "bounded U"
proof -
  have "compact U" "\<forall>x\<in>U. open (ball x 1)" "U \<subseteq> (\<Union>x\<in>U. ball x 1)"
    using assms by auto
  then obtain D where D: "D \<subseteq> U" "finite D" "U \<subseteq> (\<Union>x\<in>D. ball x 1)"
    by (metis compactE_image)
  from \<open>finite D\<close> have "bounded (\<Union>x\<in>D. ball x 1)"
    by (simp add: bounded_UN)
  then show "bounded U" using \<open>U \<subseteq> (\<Union>x\<in>D. ball x 1)\<close>
    by (rule bounded_subset)
qed

text\<open>In particular, some common special cases.\<close>

lemma compact_Un [intro]:
  assumes "compact s"
    and "compact t"
  shows " compact (s \<union> t)"
proof (rule compactI)
  fix f
  assume *: "Ball f open" "s \<union> t \<subseteq> \<Union>f"
  from * \<open>compact s\<close> obtain s' where "s' \<subseteq> f \<and> finite s' \<and> s \<subseteq> \<Union>s'"
    unfolding compact_eq_heine_borel by (auto elim!: allE[of _ f])
  moreover
  from * \<open>compact t\<close> obtain t' where "t' \<subseteq> f \<and> finite t' \<and> t \<subseteq> \<Union>t'"
    unfolding compact_eq_heine_borel by (auto elim!: allE[of _ f])
  ultimately show "\<exists>f'\<subseteq>f. finite f' \<and> s \<union> t \<subseteq> \<Union>f'"
    by (auto intro!: exI[of _ "s' \<union> t'"])
qed

lemma compact_Union [intro]: "finite S \<Longrightarrow> (\<And>T. T \<in> S \<Longrightarrow> compact T) \<Longrightarrow> compact (\<Union>S)"
  by (induct set: finite) auto

lemma compact_UN [intro]:
  "finite A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> compact (B x)) \<Longrightarrow> compact (\<Union>x\<in>A. B x)"
  by (rule compact_Union) auto

lemma closed_Int_compact [intro]:
  assumes "closed s"
    and "compact t"
  shows "compact (s \<inter> t)"
  using compact_Int_closed [of t s] assms
  by (simp add: Int_commute)

lemma compact_Int [intro]:
  fixes s t :: "'a :: t2_space set"
  assumes "compact s"
    and "compact t"
  shows "compact (s \<inter> t)"
  using assms by (intro compact_Int_closed compact_imp_closed)

lemma compact_sing [simp]: "compact {a}"
  unfolding compact_eq_heine_borel by auto

lemma compact_insert [simp]:
  assumes "compact s"
  shows "compact (insert x s)"
proof -
  have "compact ({x} \<union> s)"
    using compact_sing assms by (rule compact_Un)
  then show ?thesis by simp
qed

lemma finite_imp_compact: "finite s \<Longrightarrow> compact s"
  by (induct set: finite) simp_all

lemma open_delete:
  fixes s :: "'a::t1_space set"
  shows "open s \<Longrightarrow> open (s - {x})"
  by (simp add: open_Diff)

lemma openin_delete:
  fixes a :: "'a :: t1_space"
  shows "openin (subtopology euclidean u) s
         \<Longrightarrow> openin (subtopology euclidean u) (s - {a})"
by (metis Int_Diff open_delete openin_open)


text\<open>Compactness expressed with filters\<close>

lemma closure_iff_nhds_not_empty:
  "x \<in> closure X \<longleftrightarrow> (\<forall>A. \<forall>S\<subseteq>A. open S \<longrightarrow> x \<in> S \<longrightarrow> X \<inter> A \<noteq> {})"
proof safe
  assume x: "x \<in> closure X"
  fix S A
  assume "open S" "x \<in> S" "X \<inter> A = {}" "S \<subseteq> A"
  then have "x \<notin> closure (-S)"
    by (auto simp: closure_complement subset_eq[symmetric] intro: interiorI)
  with x have "x \<in> closure X - closure (-S)"
    by auto
  also have "\<dots> \<subseteq> closure (X \<inter> S)"
    using \<open>open S\<close> open_Int_closure_subset[of S X] by (simp add: closed_Compl ac_simps)
  finally have "X \<inter> S \<noteq> {}" by auto
  then show False using \<open>X \<inter> A = {}\<close> \<open>S \<subseteq> A\<close> by auto
next
  assume "\<forall>A S. S \<subseteq> A \<longrightarrow> open S \<longrightarrow> x \<in> S \<longrightarrow> X \<inter> A \<noteq> {}"
  from this[THEN spec, of "- X", THEN spec, of "- closure X"]
  show "x \<in> closure X"
    by (simp add: closure_subset open_Compl)
qed

corollary closure_Int_ball_not_empty:
  assumes "S \<subseteq> closure T" "x \<in> S" "r > 0"
  shows "T \<inter> ball x r \<noteq> {}"
  using assms centre_in_ball closure_iff_nhds_not_empty by blast

lemma compact_filter:
  "compact U \<longleftrightarrow> (\<forall>F. F \<noteq> bot \<longrightarrow> eventually (\<lambda>x. x \<in> U) F \<longrightarrow> (\<exists>x\<in>U. inf (nhds x) F \<noteq> bot))"
proof (intro allI iffI impI compact_fip[THEN iffD2] notI)
  fix F
  assume "compact U"
  assume F: "F \<noteq> bot" "eventually (\<lambda>x. x \<in> U) F"
  then have "U \<noteq> {}"
    by (auto simp: eventually_False)

  define Z where "Z = closure ` {A. eventually (\<lambda>x. x \<in> A) F}"
  then have "\<forall>z\<in>Z. closed z"
    by auto
  moreover
  have ev_Z: "\<And>z. z \<in> Z \<Longrightarrow> eventually (\<lambda>x. x \<in> z) F"
    unfolding Z_def by (auto elim: eventually_mono intro: set_mp[OF closure_subset])
  have "(\<forall>B \<subseteq> Z. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {})"
  proof (intro allI impI)
    fix B assume "finite B" "B \<subseteq> Z"
    with \<open>finite B\<close> ev_Z F(2) have "eventually (\<lambda>x. x \<in> U \<inter> (\<Inter>B)) F"
      by (auto simp: eventually_ball_finite_distrib eventually_conj_iff)
    with F show "U \<inter> \<Inter>B \<noteq> {}"
      by (intro notI) (simp add: eventually_False)
  qed
  ultimately have "U \<inter> \<Inter>Z \<noteq> {}"
    using \<open>compact U\<close> unfolding compact_fip by blast
  then obtain x where "x \<in> U" and x: "\<And>z. z \<in> Z \<Longrightarrow> x \<in> z"
    by auto

  have "\<And>P. eventually P (inf (nhds x) F) \<Longrightarrow> P \<noteq> bot"
    unfolding eventually_inf eventually_nhds
  proof safe
    fix P Q R S
    assume "eventually R F" "open S" "x \<in> S"
    with open_Int_closure_eq_empty[of S "{x. R x}"] x[of "closure {x. R x}"]
    have "S \<inter> {x. R x} \<noteq> {}" by (auto simp: Z_def)
    moreover assume "Ball S Q" "\<forall>x. Q x \<and> R x \<longrightarrow> bot x"
    ultimately show False by (auto simp: set_eq_iff)
  qed
  with \<open>x \<in> U\<close> show "\<exists>x\<in>U. inf (nhds x) F \<noteq> bot"
    by (metis eventually_bot)
next
  fix A
  assume A: "\<forall>a\<in>A. closed a" "\<forall>B\<subseteq>A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}" "U \<inter> \<Inter>A = {}"
  define F where "F = (INF a:insert U A. principal a)"
  have "F \<noteq> bot"
    unfolding F_def
  proof (rule INF_filter_not_bot)
    fix X
    assume X: "X \<subseteq> insert U A" "finite X"
    with A(2)[THEN spec, of "X - {U}"] have "U \<inter> \<Inter>(X - {U}) \<noteq> {}"
      by auto
    with X show "(INF a:X. principal a) \<noteq> bot"
      by (auto simp: INF_principal_finite principal_eq_bot_iff)
  qed
  moreover
  have "F \<le> principal U"
    unfolding F_def by auto
  then have "eventually (\<lambda>x. x \<in> U) F"
    by (auto simp: le_filter_def eventually_principal)
  moreover
  assume "\<forall>F. F \<noteq> bot \<longrightarrow> eventually (\<lambda>x. x \<in> U) F \<longrightarrow> (\<exists>x\<in>U. inf (nhds x) F \<noteq> bot)"
  ultimately obtain x where "x \<in> U" and x: "inf (nhds x) F \<noteq> bot"
    by auto

  { fix V assume "V \<in> A"
    then have "F \<le> principal V"
      unfolding F_def by (intro INF_lower2[of V]) auto
    then have V: "eventually (\<lambda>x. x \<in> V) F"
      by (auto simp: le_filter_def eventually_principal)
    have "x \<in> closure V"
      unfolding closure_iff_nhds_not_empty
    proof (intro impI allI)
      fix S A
      assume "open S" "x \<in> S" "S \<subseteq> A"
      then have "eventually (\<lambda>x. x \<in> A) (nhds x)"
        by (auto simp: eventually_nhds)
      with V have "eventually (\<lambda>x. x \<in> V \<inter> A) (inf (nhds x) F)"
        by (auto simp: eventually_inf)
      with x show "V \<inter> A \<noteq> {}"
        by (auto simp del: Int_iff simp add: trivial_limit_def)
    qed
    then have "x \<in> V"
      using \<open>V \<in> A\<close> A(1) by simp
  }
  with \<open>x\<in>U\<close> have "x \<in> U \<inter> \<Inter>A" by auto
  with \<open>U \<inter> \<Inter>A = {}\<close> show False by auto
qed

definition "countably_compact U \<longleftrightarrow>
    (\<forall>A. countable A \<longrightarrow> (\<forall>a\<in>A. open a) \<longrightarrow> U \<subseteq> \<Union>A \<longrightarrow> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T))"

lemma countably_compactE:
  assumes "countably_compact s" and "\<forall>t\<in>C. open t" and "s \<subseteq> \<Union>C" "countable C"
  obtains C' where "C' \<subseteq> C" and "finite C'" and "s \<subseteq> \<Union>C'"
  using assms unfolding countably_compact_def by metis

lemma countably_compactI:
  assumes "\<And>C. \<forall>t\<in>C. open t \<Longrightarrow> s \<subseteq> \<Union>C \<Longrightarrow> countable C \<Longrightarrow> (\<exists>C'\<subseteq>C. finite C' \<and> s \<subseteq> \<Union>C')"
  shows "countably_compact s"
  using assms unfolding countably_compact_def by metis

lemma compact_imp_countably_compact: "compact U \<Longrightarrow> countably_compact U"
  by (auto simp: compact_eq_heine_borel countably_compact_def)

lemma countably_compact_imp_compact:
  assumes "countably_compact U"
    and ccover: "countable B" "\<forall>b\<in>B. open b"
    and basis: "\<And>T x. open T \<Longrightarrow> x \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>b\<in>B. x \<in> b \<and> b \<inter> U \<subseteq> T"
  shows "compact U"
  using \<open>countably_compact U\<close>
  unfolding compact_eq_heine_borel countably_compact_def
proof safe
  fix A
  assume A: "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A"
  assume *: "\<forall>A. countable A \<longrightarrow> (\<forall>a\<in>A. open a) \<longrightarrow> U \<subseteq> \<Union>A \<longrightarrow> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T)"
  moreover define C where "C = {b\<in>B. \<exists>a\<in>A. b \<inter> U \<subseteq> a}"
  ultimately have "countable C" "\<forall>a\<in>C. open a"
    unfolding C_def using ccover by auto
  moreover
  have "\<Union>A \<inter> U \<subseteq> \<Union>C"
  proof safe
    fix x a
    assume "x \<in> U" "x \<in> a" "a \<in> A"
    with basis[of a x] A obtain b where "b \<in> B" "x \<in> b" "b \<inter> U \<subseteq> a"
      by blast
    with \<open>a \<in> A\<close> show "x \<in> \<Union>C"
      unfolding C_def by auto
  qed
  then have "U \<subseteq> \<Union>C" using \<open>U \<subseteq> \<Union>A\<close> by auto
  ultimately obtain T where T: "T\<subseteq>C" "finite T" "U \<subseteq> \<Union>T"
    using * by metis
  then have "\<forall>t\<in>T. \<exists>a\<in>A. t \<inter> U \<subseteq> a"
    by (auto simp: C_def)
  then obtain f where "\<forall>t\<in>T. f t \<in> A \<and> t \<inter> U \<subseteq> f t"
    unfolding bchoice_iff Bex_def ..
  with T show "\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T"
    unfolding C_def by (intro exI[of _ "f`T"]) fastforce
qed

lemma countably_compact_imp_compact_second_countable:
  "countably_compact U \<Longrightarrow> compact (U :: 'a :: second_countable_topology set)"
proof (rule countably_compact_imp_compact)
  fix T and x :: 'a
  assume "open T" "x \<in> T"
  from topological_basisE[OF is_basis this] obtain b where
    "b \<in> (SOME B. countable B \<and> topological_basis B)" "x \<in> b" "b \<subseteq> T" .
  then show "\<exists>b\<in>SOME B. countable B \<and> topological_basis B. x \<in> b \<and> b \<inter> U \<subseteq> T"
    by blast
qed (insert countable_basis topological_basis_open[OF is_basis], auto)

lemma countably_compact_eq_compact:
  "countably_compact U \<longleftrightarrow> compact (U :: 'a :: second_countable_topology set)"
  using countably_compact_imp_compact_second_countable compact_imp_countably_compact by blast

subsubsection\<open>Sequential compactness\<close>

definition seq_compact :: "'a::topological_space set \<Rightarrow> bool"
  where "seq_compact S \<longleftrightarrow>
    (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially))"

lemma seq_compactI:
  assumes "\<And>f. \<forall>n. f n \<in> S \<Longrightarrow> \<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
  shows "seq_compact S"
  unfolding seq_compact_def using assms by fast

lemma seq_compactE:
  assumes "seq_compact S" "\<forall>n. f n \<in> S"
  obtains l r where "l \<in> S" "strict_mono (r :: nat \<Rightarrow> nat)" "((f \<circ> r) \<longlongrightarrow> l) sequentially"
  using assms unfolding seq_compact_def by fast

lemma closed_sequentially: (* TODO: move upwards *)
  assumes "closed s" and "\<forall>n. f n \<in> s" and "f \<longlonglongrightarrow> l"
  shows "l \<in> s"
proof (rule ccontr)
  assume "l \<notin> s"
  with \<open>closed s\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "eventually (\<lambda>n. f n \<in> - s) sequentially"
    by (fast intro: topological_tendstoD)
  with \<open>\<forall>n. f n \<in> s\<close> show "False"
    by simp
qed

lemma seq_compact_Int_closed:
  assumes "seq_compact s" and "closed t"
  shows "seq_compact (s \<inter> t)"
proof (rule seq_compactI)
  fix f assume "\<forall>n::nat. f n \<in> s \<inter> t"
  hence "\<forall>n. f n \<in> s" and "\<forall>n. f n \<in> t"
    by simp_all
  from \<open>seq_compact s\<close> and \<open>\<forall>n. f n \<in> s\<close>
  obtain l r where "l \<in> s" and r: "strict_mono r" and l: "(f \<circ> r) \<longlonglongrightarrow> l"
    by (rule seq_compactE)
  from \<open>\<forall>n. f n \<in> t\<close> have "\<forall>n. (f \<circ> r) n \<in> t"
    by simp
  from \<open>closed t\<close> and this and l have "l \<in> t"
    by (rule closed_sequentially)
  with \<open>l \<in> s\<close> and r and l show "\<exists>l\<in>s \<inter> t. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by fast
qed

lemma seq_compact_closed_subset:
  assumes "closed s" and "s \<subseteq> t" and "seq_compact t"
  shows "seq_compact s"
  using assms seq_compact_Int_closed [of t s] by (simp add: Int_absorb1)

lemma seq_compact_imp_countably_compact:
  fixes U :: "'a :: first_countable_topology set"
  assumes "seq_compact U"
  shows "countably_compact U"
proof (safe intro!: countably_compactI)
  fix A
  assume A: "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A" "countable A"
  have subseq: "\<And>X. range X \<subseteq> U \<Longrightarrow> \<exists>r x. x \<in> U \<and> strict_mono (r :: nat \<Rightarrow> nat) \<and> (X \<circ> r) \<longlonglongrightarrow> x"
    using \<open>seq_compact U\<close> by (fastforce simp: seq_compact_def subset_eq)
  show "\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T"
  proof cases
    assume "finite A"
    with A show ?thesis by auto
  next
    assume "infinite A"
    then have "A \<noteq> {}" by auto
    show ?thesis
    proof (rule ccontr)
      assume "\<not> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T)"
      then have "\<forall>T. \<exists>x. T \<subseteq> A \<and> finite T \<longrightarrow> (x \<in> U - \<Union>T)"
        by auto
      then obtain X' where T: "\<And>T. T \<subseteq> A \<Longrightarrow> finite T \<Longrightarrow> X' T \<in> U - \<Union>T"
        by metis
      define X where "X n = X' (from_nat_into A ` {.. n})" for n
      have X: "\<And>n. X n \<in> U - (\<Union>i\<le>n. from_nat_into A i)"
        using \<open>A \<noteq> {}\<close> unfolding X_def by (intro T) (auto intro: from_nat_into)
      then have "range X \<subseteq> U"
        by auto
      with subseq[of X] obtain r x where "x \<in> U" and r: "strict_mono r" "(X \<circ> r) \<longlonglongrightarrow> x"
        by auto
      from \<open>x\<in>U\<close> \<open>U \<subseteq> \<Union>A\<close> from_nat_into_surj[OF \<open>countable A\<close>]
      obtain n where "x \<in> from_nat_into A n" by auto
      with r(2) A(1) from_nat_into[OF \<open>A \<noteq> {}\<close>, of n]
      have "eventually (\<lambda>i. X (r i) \<in> from_nat_into A n) sequentially"
        unfolding tendsto_def by (auto simp: comp_def)
      then obtain N where "\<And>i. N \<le> i \<Longrightarrow> X (r i) \<in> from_nat_into A n"
        by (auto simp: eventually_sequentially)
      moreover from X have "\<And>i. n \<le> r i \<Longrightarrow> X (r i) \<notin> from_nat_into A n"
        by auto
      moreover from \<open>strict_mono r\<close>[THEN seq_suble, of "max n N"] have "\<exists>i. n \<le> r i \<and> N \<le> i"
        by (auto intro!: exI[of _ "max n N"])
      ultimately show False
        by auto
    qed
  qed
qed

lemma compact_imp_seq_compact:
  fixes U :: "'a :: first_countable_topology set"
  assumes "compact U"
  shows "seq_compact U"
  unfolding seq_compact_def
proof safe
  fix X :: "nat \<Rightarrow> 'a"
  assume "\<forall>n. X n \<in> U"
  then have "eventually (\<lambda>x. x \<in> U) (filtermap X sequentially)"
    by (auto simp: eventually_filtermap)
  moreover
  have "filtermap X sequentially \<noteq> bot"
    by (simp add: trivial_limit_def eventually_filtermap)
  ultimately
  obtain x where "x \<in> U" and x: "inf (nhds x) (filtermap X sequentially) \<noteq> bot" (is "?F \<noteq> _")
    using \<open>compact U\<close> by (auto simp: compact_filter)

  from countable_basis_at_decseq[of x]
  obtain A where A:
      "\<And>i. open (A i)"
      "\<And>i. x \<in> A i"
      "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast
  define s where "s n i = (SOME j. i < j \<and> X j \<in> A (Suc n))" for n i
  {
    fix n i
    have "\<exists>a. i < a \<and> X a \<in> A (Suc n)"
    proof (rule ccontr)
      assume "\<not> (\<exists>a>i. X a \<in> A (Suc n))"
      then have "\<And>a. Suc i \<le> a \<Longrightarrow> X a \<notin> A (Suc n)"
        by auto
      then have "eventually (\<lambda>x. x \<notin> A (Suc n)) (filtermap X sequentially)"
        by (auto simp: eventually_filtermap eventually_sequentially)
      moreover have "eventually (\<lambda>x. x \<in> A (Suc n)) (nhds x)"
        using A(1,2)[of "Suc n"] by (auto simp: eventually_nhds)
      ultimately have "eventually (\<lambda>x. False) ?F"
        by (auto simp: eventually_inf)
      with x show False
        by (simp add: eventually_False)
    qed
    then have "i < s n i" "X (s n i) \<in> A (Suc n)"
      unfolding s_def by (auto intro: someI2_ex)
  }
  note s = this
  define r where "r = rec_nat (s 0 0) s"
  have "strict_mono r"
    by (auto simp: r_def s strict_mono_Suc_iff)
  moreover
  have "(\<lambda>n. X (r n)) \<longlonglongrightarrow> x"
  proof (rule topological_tendstoI)
    fix S
    assume "open S" "x \<in> S"
    with A(3) have "eventually (\<lambda>i. A i \<subseteq> S) sequentially"
      by auto
    moreover
    {
      fix i
      assume "Suc 0 \<le> i"
      then have "X (r i) \<in> A i"
        by (cases i) (simp_all add: r_def s)
    }
    then have "eventually (\<lambda>i. X (r i) \<in> A i) sequentially"
      by (auto simp: eventually_sequentially)
    ultimately show "eventually (\<lambda>i. X (r i) \<in> S) sequentially"
      by eventually_elim auto
  qed
  ultimately show "\<exists>x \<in> U. \<exists>r. strict_mono r \<and> (X \<circ> r) \<longlonglongrightarrow> x"
    using \<open>x \<in> U\<close> by (auto simp: convergent_def comp_def)
qed

lemma countably_compact_imp_acc_point:
  assumes "countably_compact s"
    and "countable t"
    and "infinite t"
    and "t \<subseteq> s"
  shows "\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t)"
proof (rule ccontr)
  define C where "C = (\<lambda>F. interior (F \<union> (- t))) ` {F. finite F \<and> F \<subseteq> t }"
  note \<open>countably_compact s\<close>
  moreover have "\<forall>t\<in>C. open t"
    by (auto simp: C_def)
  moreover
  assume "\<not> (\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t))"
  then have s: "\<And>x. x \<in> s \<Longrightarrow> \<exists>U. x\<in>U \<and> open U \<and> finite (U \<inter> t)" by metis
  have "s \<subseteq> \<Union>C"
    using \<open>t \<subseteq> s\<close>
    unfolding C_def
    apply (safe dest!: s)
    apply (rule_tac a="U \<inter> t" in UN_I)
    apply (auto intro!: interiorI simp add: finite_subset)
    done
  moreover
  from \<open>countable t\<close> have "countable C"
    unfolding C_def by (auto intro: countable_Collect_finite_subset)
  ultimately
  obtain D where "D \<subseteq> C" "finite D" "s \<subseteq> \<Union>D"
    by (rule countably_compactE)
  then obtain E where E: "E \<subseteq> {F. finite F \<and> F \<subseteq> t }" "finite E"
    and s: "s \<subseteq> (\<Union>F\<in>E. interior (F \<union> (- t)))"
    by (metis (lifting) finite_subset_image C_def)
  from s \<open>t \<subseteq> s\<close> have "t \<subseteq> \<Union>E"
    using interior_subset by blast
  moreover have "finite (\<Union>E)"
    using E by auto
  ultimately show False using \<open>infinite t\<close>
    by (auto simp: finite_subset)
qed

lemma countable_acc_point_imp_seq_compact:
  fixes s :: "'a::first_countable_topology set"
  assumes "\<forall>t. infinite t \<and> countable t \<and> t \<subseteq> s \<longrightarrow>
    (\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t))"
  shows "seq_compact s"
proof -
  {
    fix f :: "nat \<Rightarrow> 'a"
    assume f: "\<forall>n. f n \<in> s"
    have "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    proof (cases "finite (range f)")
      case True
      obtain l where "infinite {n. f n = f l}"
        using pigeonhole_infinite[OF _ True] by auto
      then obtain r :: "nat \<Rightarrow> nat" where "strict_mono  r" and fr: "\<forall>n. f (r n) = f l"
        using infinite_enumerate by blast
      then have "strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> f l"
        by (simp add: fr o_def)
      with f show "\<exists>l\<in>s. \<exists>r. strict_mono  r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
        by auto
    next
      case False
      with f assms have "\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> range f)"
        by auto
      then obtain l where "l \<in> s" "\<forall>U. l\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> range f)" ..
      from this(2) have "\<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
        using acc_point_range_imp_convergent_subsequence[of l f] by auto
      with \<open>l \<in> s\<close> show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially" ..
    qed
  }
  then show ?thesis
    unfolding seq_compact_def by auto
qed

lemma seq_compact_eq_countably_compact:
  fixes U :: "'a :: first_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> countably_compact U"
  using
    countable_acc_point_imp_seq_compact
    countably_compact_imp_acc_point
    seq_compact_imp_countably_compact
  by metis

lemma seq_compact_eq_acc_point:
  fixes s :: "'a :: first_countable_topology set"
  shows "seq_compact s \<longleftrightarrow>
    (\<forall>t. infinite t \<and> countable t \<and> t \<subseteq> s --> (\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t)))"
  using
    countable_acc_point_imp_seq_compact[of s]
    countably_compact_imp_acc_point[of s]
    seq_compact_imp_countably_compact[of s]
  by metis

lemma seq_compact_eq_compact:
  fixes U :: "'a :: second_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> compact U"
  using seq_compact_eq_countably_compact countably_compact_eq_compact by blast

lemma bolzano_weierstrass_imp_seq_compact:
  fixes s :: "'a::{t1_space, first_countable_topology} set"
  shows "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t) \<Longrightarrow> seq_compact s"
  by (rule countable_acc_point_imp_seq_compact) (metis islimpt_eq_acc_point)


subsubsection\<open>Totally bounded\<close>

lemma cauchy_def: "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m n. m \<ge> N \<and> n \<ge> N \<longrightarrow> dist (s m) (s n) < e)"
  unfolding Cauchy_def by metis

lemma seq_compact_imp_totally_bounded:
  assumes "seq_compact s"
  shows "\<forall>e>0. \<exists>k. finite k \<and> k \<subseteq> s \<and> s \<subseteq> (\<Union>x\<in>k. ball x e)"
proof -
  { fix e::real assume "e > 0" assume *: "\<And>k. finite k \<Longrightarrow> k \<subseteq> s \<Longrightarrow> \<not> s \<subseteq> (\<Union>x\<in>k. ball x e)"
    let ?Q = "\<lambda>x n r. r \<in> s \<and> (\<forall>m < (n::nat). \<not> (dist (x m) r < e))"
    have "\<exists>x. \<forall>n::nat. ?Q x n (x n)"
    proof (rule dependent_wellorder_choice)
      fix n x assume "\<And>y. y < n \<Longrightarrow> ?Q x y (x y)"
      then have "\<not> s \<subseteq> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        using *[of "x ` {0 ..< n}"] by (auto simp: subset_eq)
      then obtain z where z:"z\<in>s" "z \<notin> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        unfolding subset_eq by auto
      show "\<exists>r. ?Q x n r"
        using z by auto
    qed simp
    then obtain x where "\<forall>n::nat. x n \<in> s" and x:"\<And>n m. m < n \<Longrightarrow> \<not> (dist (x m) (x n) < e)"
      by blast
    then obtain l r where "l \<in> s" and r:"strict_mono  r" and "((x \<circ> r) \<longlongrightarrow> l) sequentially"
      using assms by (metis seq_compact_def)
    from this(3) have "Cauchy (x \<circ> r)"
      using LIMSEQ_imp_Cauchy by auto
    then obtain N::nat where "\<And>m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> dist ((x \<circ> r) m) ((x \<circ> r) n) < e"
      unfolding cauchy_def using \<open>e > 0\<close> by blast
    then have False
      using x[of "r N" "r (N+1)"] r by (auto simp: strict_mono_def) }
  then show ?thesis
    by metis
qed

subsubsection\<open>Heine-Borel theorem\<close>

lemma seq_compact_imp_heine_borel:
  fixes s :: "'a :: metric_space set"
  assumes "seq_compact s"
  shows "compact s"
proof -
  from seq_compact_imp_totally_bounded[OF \<open>seq_compact s\<close>]
  obtain f where f: "\<forall>e>0. finite (f e) \<and> f e \<subseteq> s \<and> s \<subseteq> (\<Union>x\<in>f e. ball x e)"
    unfolding choice_iff' ..
  define K where "K = (\<lambda>(x, r). ball x r) ` ((\<Union>e \<in> \<rat> \<inter> {0 <..}. f e) \<times> \<rat>)"
  have "countably_compact s"
    using \<open>seq_compact s\<close> by (rule seq_compact_imp_countably_compact)
  then show "compact s"
  proof (rule countably_compact_imp_compact)
    show "countable K"
      unfolding K_def using f
      by (auto intro: countable_finite countable_subset countable_rat
               intro!: countable_image countable_SIGMA countable_UN)
    show "\<forall>b\<in>K. open b" by (auto simp: K_def)
  next
    fix T x
    assume T: "open T" "x \<in> T" and x: "x \<in> s"
    from openE[OF T] obtain e where "0 < e" "ball x e \<subseteq> T"
      by auto
    then have "0 < e / 2" "ball x (e / 2) \<subseteq> T"
      by auto
    from Rats_dense_in_real[OF \<open>0 < e / 2\<close>] obtain r where "r \<in> \<rat>" "0 < r" "r < e / 2"
      by auto
    from f[rule_format, of r] \<open>0 < r\<close> \<open>x \<in> s\<close> obtain k where "k \<in> f r" "x \<in> ball k r"
      by auto
    from \<open>r \<in> \<rat>\<close> \<open>0 < r\<close> \<open>k \<in> f r\<close> have "ball k r \<in> K"
      by (auto simp: K_def)
    then show "\<exists>b\<in>K. x \<in> b \<and> b \<inter> s \<subseteq> T"
    proof (rule bexI[rotated], safe)
      fix y
      assume "y \<in> ball k r"
      with \<open>r < e / 2\<close> \<open>x \<in> ball k r\<close> have "dist x y < e"
        by (intro dist_triangle_half_r [of k _ e]) (auto simp: dist_commute)
      with \<open>ball x e \<subseteq> T\<close> show "y \<in> T"
        by auto
    next
      show "x \<in> ball k r" by fact
    qed
  qed
qed

lemma compact_eq_seq_compact_metric:
  "compact (s :: 'a::metric_space set) \<longleftrightarrow> seq_compact s"
  using compact_imp_seq_compact seq_compact_imp_heine_borel by blast

lemma compact_def: \<comment>\<open>this is the definition of compactness in HOL Light\<close>
  "compact (S :: 'a::metric_space set) \<longleftrightarrow>
   (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l))"
  unfolding compact_eq_seq_compact_metric seq_compact_def by auto

subsubsection \<open>Complete the chain of compactness variants\<close>

lemma compact_eq_bolzano_weierstrass:
  fixes s :: "'a::metric_space set"
  shows "compact s \<longleftrightarrow> (\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using heine_borel_imp_bolzano_weierstrass[of s] by auto
next
  assume ?rhs
  then show ?lhs
    unfolding compact_eq_seq_compact_metric by (rule bolzano_weierstrass_imp_seq_compact)
qed

lemma bolzano_weierstrass_imp_bounded:
  "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t) \<Longrightarrow> bounded s"
  using compact_imp_bounded unfolding compact_eq_bolzano_weierstrass .


subsection \<open>Metric spaces with the Heine-Borel property\<close>

text \<open>
  A metric space (or topological vector space) is said to have the
  Heine-Borel property if every closed and bounded subset is compact.
\<close>

class heine_borel = metric_space +
  assumes bounded_imp_convergent_subsequence:
    "bounded (range f) \<Longrightarrow> \<exists>l r. strict_mono (r::nat\<Rightarrow>nat) \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"

lemma bounded_closed_imp_seq_compact:
  fixes s::"'a::heine_borel set"
  assumes "bounded s"
    and "closed s"
  shows "seq_compact s"
proof (unfold seq_compact_def, clarify)
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> s"
  with \<open>bounded s\<close> have "bounded (range f)"
    by (auto intro: bounded_subset)
  obtain l r where r: "strict_mono (r :: nat \<Rightarrow> nat)" and l: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using bounded_imp_convergent_subsequence [OF \<open>bounded (range f)\<close>] by auto
  from f have fr: "\<forall>n. (f \<circ> r) n \<in> s"
    by simp
  have "l \<in> s" using \<open>closed s\<close> fr l
    by (rule closed_sequentially)
  show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using \<open>l \<in> s\<close> r l by blast
qed

lemma compact_eq_bounded_closed:
  fixes s :: "'a::heine_borel set"
  shows "compact s \<longleftrightarrow> bounded s \<and> closed s"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using compact_imp_closed compact_imp_bounded
    by blast
next
  assume ?rhs
  then show ?lhs
    using bounded_closed_imp_seq_compact[of s]
    unfolding compact_eq_seq_compact_metric
    by auto
qed

lemma compact_Inter:
  fixes \<F> :: "'a :: heine_borel set set"
  assumes com: "\<And>S. S \<in> \<F> \<Longrightarrow> compact S" and "\<F> \<noteq> {}"
  shows "compact(\<Inter> \<F>)"
  using assms
  by (meson Inf_lower all_not_in_conv bounded_subset closed_Inter compact_eq_bounded_closed)

lemma compact_closure [simp]:
  fixes S :: "'a::heine_borel set"
  shows "compact(closure S) \<longleftrightarrow> bounded S"
by (meson bounded_closure bounded_subset closed_closure closure_subset compact_eq_bounded_closed)

lemma compact_components:
  fixes s :: "'a::heine_borel set"
  shows "\<lbrakk>compact s; c \<in> components s\<rbrakk> \<Longrightarrow> compact c"
by (meson bounded_subset closed_components in_components_subset compact_eq_bounded_closed)

lemma not_compact_UNIV[simp]:
  fixes s :: "'a::{real_normed_vector,perfect_space,heine_borel} set"
  shows "~ compact (UNIV::'a set)"
    by (simp add: compact_eq_bounded_closed)

instance real :: heine_borel
proof
  fix f :: "nat \<Rightarrow> real"
  assume f: "bounded (range f)"
  obtain r :: "nat \<Rightarrow> nat" where r: "strict_mono r" "monoseq (f \<circ> r)"
    unfolding comp_def by (metis seq_monosub)
  then have "Bseq (f \<circ> r)"
    unfolding Bseq_eq_bounded using f by (force intro: bounded_subset)
  with r show "\<exists>l r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    using Bseq_monoseq_convergent[of "f \<circ> r"] by (auto simp: convergent_def)
qed

lemma compact_lemma_general:
  fixes f :: "nat \<Rightarrow> 'a"
  fixes proj::"'a \<Rightarrow> 'b \<Rightarrow> 'c::heine_borel" (infixl "proj" 60)
  fixes unproj:: "('b \<Rightarrow> 'c) \<Rightarrow> 'a"
  assumes finite_basis: "finite basis"
  assumes bounded_proj: "\<And>k. k \<in> basis \<Longrightarrow> bounded ((\<lambda>x. x proj k) ` range f)"
  assumes proj_unproj: "\<And>e k. k \<in> basis \<Longrightarrow> (unproj e) proj k = e k"
  assumes unproj_proj: "\<And>x. unproj (\<lambda>k. x proj k) = x"
  shows "\<forall>d\<subseteq>basis. \<exists>l::'a. \<exists> r::nat\<Rightarrow>nat.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) proj i) (l proj i) < e) sequentially)"
proof safe
  fix d :: "'b set"
  assume d: "d \<subseteq> basis"
  with finite_basis have "finite d"
    by (blast intro: finite_subset)
  from this d show "\<exists>l::'a. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and>
    (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) proj i) (l proj i) < e) sequentially)"
  proof (induct d)
    case empty
    then show ?case
      unfolding strict_mono_def by auto
  next
    case (insert k d)
    have k[intro]: "k \<in> basis"
      using insert by auto
    have s': "bounded ((\<lambda>x. x proj k) ` range f)"
      using k
      by (rule bounded_proj)
    obtain l1::"'a" and r1 where r1: "strict_mono r1"
      and lr1: "\<forall>e > 0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e) sequentially"
      using insert(3) using insert(4) by auto
    have f': "\<forall>n. f (r1 n) proj k \<in> (\<lambda>x. x proj k) ` range f"
      by simp
    have "bounded (range (\<lambda>i. f (r1 i) proj k))"
      by (metis (lifting) bounded_subset f' image_subsetI s')
    then obtain l2 r2 where r2:"strict_mono r2" and lr2:"((\<lambda>i. f (r1 (r2 i)) proj k) \<longlongrightarrow> l2) sequentially"
      using bounded_imp_convergent_subsequence[of "\<lambda>i. f (r1 i) proj k"]
      by (auto simp: o_def)
    define r where "r = r1 \<circ> r2"
    have r:"strict_mono r"
      using r1 and r2 unfolding r_def o_def strict_mono_def by auto
    moreover
    define l where "l = unproj (\<lambda>i. if i = k then l2 else l1 proj i)"
    {
      fix e::real
      assume "e > 0"
      from lr1 \<open>e > 0\<close> have N1: "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e) sequentially"
        by blast
      from lr2 \<open>e > 0\<close> have N2:"eventually (\<lambda>n. dist (f (r1 (r2 n)) proj k) l2 < e) sequentially"
        by (rule tendstoD)
      from r2 N1 have N1': "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 (r2 n)) proj i) (l1 proj i) < e) sequentially"
        by (rule eventually_subseq)
      have "eventually (\<lambda>n. \<forall>i\<in>(insert k d). dist (f (r n) proj i) (l proj i) < e) sequentially"
        using N1' N2
        by eventually_elim (insert insert.prems, auto simp: l_def r_def o_def proj_unproj)
    }
    ultimately show ?case by auto
  qed
qed

lemma compact_lemma:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>Basis. \<exists>l::'a. \<exists> r.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially)"
  by (rule compact_lemma_general[where unproj="\<lambda>e. \<Sum>i\<in>Basis. e i *\<^sub>R i"])
     (auto intro!: assms bounded_linear_inner_left bounded_linear_image
       simp: euclidean_representation)

instance euclidean_space \<subseteq> heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "bounded (range f)"
  then obtain l::'a and r where r: "strict_mono r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e) sequentially"
    using compact_lemma [OF f] by blast
  {
    fix e::real
    assume "e > 0"
    hence "e / real_of_nat DIM('a) > 0" by (simp add: DIM_positive)
    with l have "eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))) sequentially"
      by simp
    moreover
    {
      fix n
      assume n: "\<forall>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i) < e / (real_of_nat DIM('a))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>Basis. dist (f (r n) \<bullet> i) (l \<bullet> i))"
        apply (subst euclidean_dist_l2)
        using zero_le_dist
        apply (rule setL2_le_sum)
        done
      also have "\<dots> < (\<Sum>i\<in>(Basis::'a set). e / (real_of_nat DIM('a)))"
        apply (rule sum_strict_mono)
        using n
        apply auto
        done
      finally have "dist (f (r n)) l < e"
        by auto
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_mono)
  }
  then have *: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    by auto
qed

lemma bounded_fst: "bounded s \<Longrightarrow> bounded (fst ` s)"
  unfolding bounded_def
  by (metis (erased, hide_lams) dist_fst_le image_iff order_trans)

lemma bounded_snd: "bounded s \<Longrightarrow> bounded (snd ` s)"
  unfolding bounded_def
  by (metis (no_types, hide_lams) dist_snd_le image_iff order.trans)

instance prod :: (heine_borel, heine_borel) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a \<times> 'b"
  assume f: "bounded (range f)"
  then have "bounded (fst ` range f)"
    by (rule bounded_fst)
  then have s1: "bounded (range (fst \<circ> f))"
    by (simp add: image_comp)
  obtain l1 r1 where r1: "strict_mono r1" and l1: "(\<lambda>n. fst (f (r1 n))) \<longlonglongrightarrow> l1"
    using bounded_imp_convergent_subsequence [OF s1] unfolding o_def by fast
  from f have s2: "bounded (range (snd \<circ> f \<circ> r1))"
    by (auto simp: image_comp intro: bounded_snd bounded_subset)
  obtain l2 r2 where r2: "strict_mono r2" and l2: "((\<lambda>n. snd (f (r1 (r2 n)))) \<longlongrightarrow> l2) sequentially"
    using bounded_imp_convergent_subsequence [OF s2]
    unfolding o_def by fast
  have l1': "((\<lambda>n. fst (f (r1 (r2 n)))) \<longlongrightarrow> l1) sequentially"
    using LIMSEQ_subseq_LIMSEQ [OF l1 r2] unfolding o_def .
  have l: "((f \<circ> (r1 \<circ> r2)) \<longlongrightarrow> (l1, l2)) sequentially"
    using tendsto_Pair [OF l1' l2] unfolding o_def by simp
  have r: "strict_mono (r1 \<circ> r2)"
    using r1 r2 unfolding strict_mono_def by simp
  show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using l r by fast
qed

subsubsection \<open>Intersecting chains of compact sets\<close>

proposition bounded_closed_chain:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "B \<in> \<F>" "bounded B" and \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> closed S" and "{} \<notin> \<F>"
      and chain: "\<And>S T. S \<in> \<F> \<and> T \<in> \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    shows "\<Inter>\<F> \<noteq> {}"
proof -
  have "B \<inter> \<Inter>\<F> \<noteq> {}"
  proof (rule compact_imp_fip)
    show "compact B" "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      by (simp_all add: assms compact_eq_bounded_closed)
    show "\<lbrakk>finite \<G>; \<G> \<subseteq> \<F>\<rbrakk> \<Longrightarrow> B \<inter> \<Inter>\<G> \<noteq> {}" for \<G>
    proof (induction \<G> rule: finite_induct)
      case empty
      with assms show ?case by force
    next
      case (insert U \<G>)
      then have "U \<in> \<F>" and ne: "B \<inter> \<Inter>\<G> \<noteq> {}" by auto
      then consider "B \<subseteq> U" | "U \<subseteq> B"
          using \<open>B \<in> \<F>\<close> chain by blast
        then show ?case
        proof cases
          case 1
          then show ?thesis
            using Int_left_commute ne by auto
        next
          case 2
          have "U \<noteq> {}"
            using \<open>U \<in> \<F>\<close> \<open>{} \<notin> \<F>\<close> by blast
          moreover
          have False if "\<And>x. x \<in> U \<Longrightarrow> \<exists>Y\<in>\<G>. x \<notin> Y"
          proof -
            have "\<And>x. x \<in> U \<Longrightarrow> \<exists>Y\<in>\<G>. Y \<subseteq> U"
              by (metis chain contra_subsetD insert.prems insert_subset that)
            then obtain Y where "Y \<in> \<G>" "Y \<subseteq> U"
              by (metis all_not_in_conv \<open>U \<noteq> {}\<close>)
            moreover obtain x where "x \<in> \<Inter>\<G>"
              by (metis Int_emptyI ne)
            ultimately show ?thesis
              by (metis Inf_lower subset_eq that)
          qed
          with 2 show ?thesis
            by blast
        qed
      qed
  qed
  then show ?thesis by blast
qed

corollary compact_chain:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> compact S" "{} \<notin> \<F>"
          "\<And>S T. S \<in> \<F> \<and> T \<in> \<F> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    shows "\<Inter> \<F> \<noteq> {}"
proof (cases "\<F> = {}")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis
    by (metis False all_not_in_conv assms compact_imp_bounded compact_imp_closed bounded_closed_chain)
qed

lemma compact_nest:
  fixes F :: "'a::linorder \<Rightarrow> 'b::heine_borel set"
  assumes F: "\<And>n. compact(F n)" "\<And>n. F n \<noteq> {}" and mono: "\<And>m n. m \<le> n \<Longrightarrow> F n \<subseteq> F m"
  shows "\<Inter>range F \<noteq> {}"
proof -
  have *: "\<And>S T. S \<in> range F \<and> T \<in> range F \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
    by (metis mono image_iff le_cases)
  show ?thesis
    apply (rule compact_chain [OF _ _ *])
    using F apply (blast intro: dest: *)+
    done
qed

text\<open>The Baire property of dense sets\<close>
theorem Baire:
  fixes S::"'a::{real_normed_vector,heine_borel} set"
  assumes "closed S" "countable \<G>"
      and ope: "\<And>T. T \<in> \<G> \<Longrightarrow> openin (subtopology euclidean S) T \<and> S \<subseteq> closure T"
 shows "S \<subseteq> closure(\<Inter>\<G>)"
proof (cases "\<G> = {}")
  case True
  then show ?thesis
    using closure_subset by auto
next
  let ?g = "from_nat_into \<G>"
  case False
  then have gin: "?g n \<in> \<G>" for n
    by (simp add: from_nat_into)
  show ?thesis
  proof (clarsimp simp: closure_approachable)
    fix x and e::real
    assume "x \<in> S" "0 < e"
    obtain TF where opeF: "\<And>n. openin (subtopology euclidean S) (TF n)"
               and ne: "\<And>n. TF n \<noteq> {}"
               and subg: "\<And>n. S \<inter> closure(TF n) \<subseteq> ?g n"
               and subball: "\<And>n. closure(TF n) \<subseteq> ball x e"
               and decr: "\<And>n. TF(Suc n) \<subseteq> TF n"
    proof -
      have *: "\<exists>Y. (openin (subtopology euclidean S) Y \<and> Y \<noteq> {} \<and>
                   S \<inter> closure Y \<subseteq> ?g n \<and> closure Y \<subseteq> ball x e) \<and> Y \<subseteq> U"
        if opeU: "openin (subtopology euclidean S) U" and "U \<noteq> {}" and cloU: "closure U \<subseteq> ball x e" for U n
      proof -
        obtain T where T: "open T" "U = T \<inter> S"
          using \<open>openin (subtopology euclidean S) U\<close> by (auto simp: openin_subtopology)
        with \<open>U \<noteq> {}\<close> have "T \<inter> closure (?g n) \<noteq> {}"
          using gin ope by fastforce
        then have "T \<inter> ?g n \<noteq> {}"
          using \<open>open T\<close> open_Int_closure_eq_empty by blast
        then obtain y where "y \<in> U" "y \<in> ?g n"
          using T ope [of "?g n", OF gin] by (blast dest:  openin_imp_subset)
        moreover have "openin (subtopology euclidean S) (U \<inter> ?g n)"
          using gin ope opeU by blast
        ultimately obtain d where U: "U \<inter> ?g n \<subseteq> S" and "d > 0" and d: "ball y d \<inter> S \<subseteq> U \<inter> ?g n"
          by (force simp: openin_contains_ball)
        show ?thesis
        proof (intro exI conjI)
          show "openin (subtopology euclidean S) (S \<inter> ball y (d/2))"
            by (simp add: openin_open_Int)
          show "S \<inter> ball y (d/2) \<noteq> {}"
            using \<open>0 < d\<close> \<open>y \<in> U\<close> opeU openin_imp_subset by fastforce
          have "S \<inter> closure (S \<inter> ball y (d/2)) \<subseteq> S \<inter> closure (ball y (d/2))"
            using closure_mono by blast
          also have "... \<subseteq> ?g n"
            using \<open>d > 0\<close> d by force
          finally show "S \<inter> closure (S \<inter> ball y (d/2)) \<subseteq> ?g n" .
          have "closure (S \<inter> ball y (d/2)) \<subseteq> S \<inter> ball y d"
          proof -
            have "closure (ball y (d/2)) \<subseteq> ball y d"
              using \<open>d > 0\<close> by auto
            then have "closure (S \<inter> ball y (d/2)) \<subseteq> ball y d"
              by (meson closure_mono inf.cobounded2 subset_trans)
            then show ?thesis
              by (simp add: \<open>closed S\<close> closure_minimal)
          qed
          also have "...  \<subseteq> ball x e"
            using cloU closure_subset d by blast
          finally show "closure (S \<inter> ball y (d/2)) \<subseteq> ball x e" .
          show "S \<inter> ball y (d/2) \<subseteq> U"
            using ball_divide_subset_numeral d by blast
        qed
      qed
      let ?\<Phi> = "\<lambda>n X. openin (subtopology euclidean S) X \<and> X \<noteq> {} \<and>
                      S \<inter> closure X \<subseteq> ?g n \<and> closure X \<subseteq> ball x e"
      have "closure (S \<inter> ball x (e / 2)) \<subseteq> closure(ball x (e/2))"
        by (simp add: closure_mono)
      also have "...  \<subseteq> ball x e"
        using \<open>e > 0\<close> by auto
      finally have "closure (S \<inter> ball x (e / 2)) \<subseteq> ball x e" .
      moreover have"openin (subtopology euclidean S) (S \<inter> ball x (e / 2))" "S \<inter> ball x (e / 2) \<noteq> {}"
        using \<open>0 < e\<close> \<open>x \<in> S\<close> by auto
      ultimately obtain Y where Y: "?\<Phi> 0 Y \<and> Y \<subseteq> S \<inter> ball x (e / 2)"
            using * [of "S \<inter> ball x (e/2)" 0] by metis
      show thesis
      proof (rule exE [OF dependent_nat_choice [of ?\<Phi> "\<lambda>n X Y. Y \<subseteq> X"]])
        show "\<exists>x. ?\<Phi> 0 x"
          using Y by auto
        show "\<exists>Y. ?\<Phi> (Suc n) Y \<and> Y \<subseteq> X" if "?\<Phi> n X" for X n
          using that by (blast intro: *)
      qed (use that in metis)
    qed
    have "(\<Inter>n. S \<inter> closure (TF n)) \<noteq> {}"
    proof (rule compact_nest)
      show "\<And>n. compact (S \<inter> closure (TF n))"
        by (metis closed_closure subball bounded_subset_ballI compact_eq_bounded_closed closed_Int_compact [OF \<open>closed S\<close>])
      show "\<And>n. S \<inter> closure (TF n) \<noteq> {}"
        by (metis Int_absorb1 opeF \<open>closed S\<close> closure_eq_empty closure_minimal ne openin_imp_subset)
      show "\<And>m n. m \<le> n \<Longrightarrow> S \<inter> closure (TF n) \<subseteq> S \<inter> closure (TF m)"
        by (meson closure_mono decr dual_order.refl inf_mono lift_Suc_antimono_le)
    qed
    moreover have "(\<Inter>n. S \<inter> closure (TF n)) \<subseteq> {y \<in> \<Inter>\<G>. dist y x < e}"
    proof (clarsimp, intro conjI)
      fix y
      assume "y \<in> S" and y: "\<forall>n. y \<in> closure (TF n)"
      then show "\<forall>T\<in>\<G>. y \<in> T"
        by (metis Int_iff from_nat_into_surj [OF \<open>countable \<G>\<close>] set_mp subg)
      show "dist y x < e"
        by (metis y dist_commute mem_ball subball subsetCE)
    qed
    ultimately show "\<exists>y \<in> \<Inter>\<G>. dist y x < e"
      by auto
  qed
qed

subsubsection \<open>Completeness\<close>

lemma (in metric_space) completeI:
  assumes "\<And>f. \<forall>n. f n \<in> s \<Longrightarrow> Cauchy f \<Longrightarrow> \<exists>l\<in>s. f \<longlonglongrightarrow> l"
  shows "complete s"
  using assms unfolding complete_def by fast

lemma (in metric_space) completeE:
  assumes "complete s" and "\<forall>n. f n \<in> s" and "Cauchy f"
  obtains l where "l \<in> s" and "f \<longlonglongrightarrow> l"
  using assms unfolding complete_def by fast

(* TODO: generalize to uniform spaces *)
lemma compact_imp_complete:
  fixes s :: "'a::metric_space set"
  assumes "compact s"
  shows "complete s"
proof -
  {
    fix f
    assume as: "(\<forall>n::nat. f n \<in> s)" "Cauchy f"
    from as(1) obtain l r where lr: "l\<in>s" "strict_mono r" "(f \<circ> r) \<longlonglongrightarrow> l"
      using assms unfolding compact_def by blast

    note lr' = seq_suble [OF lr(2)]
    {
      fix e :: real
      assume "e > 0"
      from as(2) obtain N where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (f m) (f n) < e/2"
        unfolding cauchy_def
        using \<open>e > 0\<close>
        apply (erule_tac x="e/2" in allE, auto)
        done
      from lr(3)[unfolded lim_sequentially, THEN spec[where x="e/2"]]
      obtain M where M:"\<forall>n\<ge>M. dist ((f \<circ> r) n) l < e/2"
        using \<open>e > 0\<close> by auto
      {
        fix n :: nat
        assume n: "n \<ge> max N M"
        have "dist ((f \<circ> r) n) l < e/2"
          using n M by auto
        moreover have "r n \<ge> N"
          using lr'[of n] n by auto
        then have "dist (f n) ((f \<circ> r) n) < e / 2"
          using N and n by auto
        ultimately have "dist (f n) l < e"
          using dist_triangle_half_r[of "f (r n)" "f n" e l]
          by (auto simp: dist_commute)
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (f n) l < e" by blast
    }
    then have "\<exists>l\<in>s. (f \<longlongrightarrow> l) sequentially" using \<open>l\<in>s\<close>
      unfolding lim_sequentially by auto
  }
  then show ?thesis unfolding complete_def by auto
qed

lemma compact_eq_totally_bounded:
  "compact s \<longleftrightarrow> complete s \<and> (\<forall>e>0. \<exists>k. finite k \<and> s \<subseteq> (\<Union>x\<in>k. ball x e))"
    (is "_ \<longleftrightarrow> ?rhs")
proof
  assume assms: "?rhs"
  then obtain k where k: "\<And>e. 0 < e \<Longrightarrow> finite (k e)" "\<And>e. 0 < e \<Longrightarrow> s \<subseteq> (\<Union>x\<in>k e. ball x e)"
    by (auto simp: choice_iff')

  show "compact s"
  proof cases
    assume "s = {}"
    then show "compact s" by (simp add: compact_def)
  next
    assume "s \<noteq> {}"
    show ?thesis
      unfolding compact_def
    proof safe
      fix f :: "nat \<Rightarrow> 'a"
      assume f: "\<forall>n. f n \<in> s"

      define e where "e n = 1 / (2 * Suc n)" for n
      then have [simp]: "\<And>n. 0 < e n" by auto
      define B where "B n U = (SOME b. infinite {n. f n \<in> b} \<and> (\<exists>x. b \<subseteq> ball x (e n) \<inter> U))" for n U
      {
        fix n U
        assume "infinite {n. f n \<in> U}"
        then have "\<exists>b\<in>k (e n). infinite {i\<in>{n. f n \<in> U}. f i \<in> ball b (e n)}"
          using k f by (intro pigeonhole_infinite_rel) (auto simp: subset_eq)
        then obtain a where
          "a \<in> k (e n)"
          "infinite {i \<in> {n. f n \<in> U}. f i \<in> ball a (e n)}" ..
        then have "\<exists>b. infinite {i. f i \<in> b} \<and> (\<exists>x. b \<subseteq> ball x (e n) \<inter> U)"
          by (intro exI[of _ "ball a (e n) \<inter> U"] exI[of _ a]) (auto simp: ac_simps)
        from someI_ex[OF this]
        have "infinite {i. f i \<in> B n U}" "\<exists>x. B n U \<subseteq> ball x (e n) \<inter> U"
          unfolding B_def by auto
      }
      note B = this

      define F where "F = rec_nat (B 0 UNIV) B"
      {
        fix n
        have "infinite {i. f i \<in> F n}"
          by (induct n) (auto simp: F_def B)
      }
      then have F: "\<And>n. \<exists>x. F (Suc n) \<subseteq> ball x (e n) \<inter> F n"
        using B by (simp add: F_def)
      then have F_dec: "\<And>m n. m \<le> n \<Longrightarrow> F n \<subseteq> F m"
        using decseq_SucI[of F] by (auto simp: decseq_def)

      obtain sel where sel: "\<And>k i. i < sel k i" "\<And>k i. f (sel k i) \<in> F k"
      proof (atomize_elim, unfold all_conj_distrib[symmetric], intro choice allI)
        fix k i
        have "infinite ({n. f n \<in> F k} - {.. i})"
          using \<open>infinite {n. f n \<in> F k}\<close> by auto
        from infinite_imp_nonempty[OF this]
        show "\<exists>x>i. f x \<in> F k"
          by (simp add: set_eq_iff not_le conj_commute)
      qed

      define t where "t = rec_nat (sel 0 0) (\<lambda>n i. sel (Suc n) i)"
      have "strict_mono t"
        unfolding strict_mono_Suc_iff by (simp add: t_def sel)
      moreover have "\<forall>i. (f \<circ> t) i \<in> s"
        using f by auto
      moreover
      {
        fix n
        have "(f \<circ> t) n \<in> F n"
          by (cases n) (simp_all add: t_def sel)
      }
      note t = this

      have "Cauchy (f \<circ> t)"
      proof (safe intro!: metric_CauchyI exI elim!: nat_approx_posE)
        fix r :: real and N n m
        assume "1 / Suc N < r" "Suc N \<le> n" "Suc N \<le> m"
        then have "(f \<circ> t) n \<in> F (Suc N)" "(f \<circ> t) m \<in> F (Suc N)" "2 * e N < r"
          using F_dec t by (auto simp: e_def field_simps of_nat_Suc)
        with F[of N] obtain x where "dist x ((f \<circ> t) n) < e N" "dist x ((f \<circ> t) m) < e N"
          by (auto simp: subset_eq)
        with dist_triangle[of "(f \<circ> t) m" "(f \<circ> t) n" x] \<open>2 * e N < r\<close>
        show "dist ((f \<circ> t) m) ((f \<circ> t) n) < r"
          by (simp add: dist_commute)
      qed

      ultimately show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
        using assms unfolding complete_def by blast
    qed
  qed
qed (metis compact_imp_complete compact_imp_seq_compact seq_compact_imp_totally_bounded)

lemma cauchy_imp_bounded:
  assumes "Cauchy s"
  shows "bounded (range s)"
proof -
  from assms obtain N :: nat where "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < 1"
    unfolding cauchy_def by force
  then have N:"\<forall>n. N \<le> n \<longrightarrow> dist (s N) (s n) < 1" by auto
  moreover
  have "bounded (s ` {0..N})"
    using finite_imp_bounded[of "s ` {1..N}"] by auto
  then obtain a where a:"\<forall>x\<in>s ` {0..N}. dist (s N) x \<le> a"
    unfolding bounded_any_center [where a="s N"] by auto
  ultimately show "?thesis"
    unfolding bounded_any_center [where a="s N"]
    apply (rule_tac x="max a 1" in exI, auto)
    apply (erule_tac x=y in allE)
    apply (erule_tac x=y in ballE, auto)
    done
qed

instance heine_borel < complete_space
proof
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then have "bounded (range f)"
    by (rule cauchy_imp_bounded)
  then have "compact (closure (range f))"
    unfolding compact_eq_bounded_closed by auto
  then have "complete (closure (range f))"
    by (rule compact_imp_complete)
  moreover have "\<forall>n. f n \<in> closure (range f)"
    using closure_subset [of "range f"] by auto
  ultimately have "\<exists>l\<in>closure (range f). (f \<longlongrightarrow> l) sequentially"
    using \<open>Cauchy f\<close> unfolding complete_def by auto
  then show "convergent f"
    unfolding convergent_def by auto
qed

instance euclidean_space \<subseteq> banach ..

lemma complete_UNIV: "complete (UNIV :: ('a::complete_space) set)"
proof (rule completeI)
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then have "convergent f" by (rule Cauchy_convergent)
  then show "\<exists>l\<in>UNIV. f \<longlonglongrightarrow> l" unfolding convergent_def by simp
qed

lemma complete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S"
  shows "closed S"
proof (unfold closed_sequential_limits, clarify)
  fix f x assume "\<forall>n. f n \<in> S" and "f \<longlonglongrightarrow> x"
  from \<open>f \<longlonglongrightarrow> x\<close> have "Cauchy f"
    by (rule LIMSEQ_imp_Cauchy)
  with \<open>complete S\<close> and \<open>\<forall>n. f n \<in> S\<close> obtain l where "l \<in> S" and "f \<longlonglongrightarrow> l"
    by (rule completeE)
  from \<open>f \<longlonglongrightarrow> x\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "x = l"
    by (rule LIMSEQ_unique)
  with \<open>l \<in> S\<close> show "x \<in> S"
    by simp
qed

lemma complete_Int_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S" and "closed t"
  shows "complete (S \<inter> t)"
proof (rule completeI)
  fix f assume "\<forall>n. f n \<in> S \<inter> t" and "Cauchy f"
  then have "\<forall>n. f n \<in> S" and "\<forall>n. f n \<in> t"
    by simp_all
  from \<open>complete S\<close> obtain l where "l \<in> S" and "f \<longlonglongrightarrow> l"
    using \<open>\<forall>n. f n \<in> S\<close> and \<open>Cauchy f\<close> by (rule completeE)
  from \<open>closed t\<close> and \<open>\<forall>n. f n \<in> t\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "l \<in> t"
    by (rule closed_sequentially)
  with \<open>l \<in> S\<close> and \<open>f \<longlonglongrightarrow> l\<close> show "\<exists>l\<in>S \<inter> t. f \<longlonglongrightarrow> l"
    by fast
qed

lemma complete_closed_subset:
  fixes S :: "'a::metric_space set"
  assumes "closed S" and "S \<subseteq> t" and "complete t"
  shows "complete S"
  using assms complete_Int_closed [of t S] by (simp add: Int_absorb1)

lemma complete_eq_closed:
  fixes S :: "('a::complete_space) set"
  shows "complete S \<longleftrightarrow> closed S"
proof
  assume "closed S" then show "complete S"
    using subset_UNIV complete_UNIV by (rule complete_closed_subset)
next
  assume "complete S" then show "closed S"
    by (rule complete_imp_closed)
qed

lemma convergent_eq_Cauchy:
  fixes S :: "nat \<Rightarrow> 'a::complete_space"
  shows "(\<exists>l. (S \<longlongrightarrow> l) sequentially) \<longleftrightarrow> Cauchy S"
  unfolding Cauchy_convergent_iff convergent_def ..

lemma convergent_imp_bounded:
  fixes S :: "nat \<Rightarrow> 'a::metric_space"
  shows "(S \<longlongrightarrow> l) sequentially \<Longrightarrow> bounded (range S)"
  by (intro cauchy_imp_bounded LIMSEQ_imp_Cauchy)

lemma compact_cball[simp]:
  fixes x :: "'a::heine_borel"
  shows "compact (cball x e)"
  using compact_eq_bounded_closed bounded_cball closed_cball
  by blast

lemma compact_frontier_bounded[intro]:
  fixes S :: "'a::heine_borel set"
  shows "bounded S \<Longrightarrow> compact (frontier S)"
  unfolding frontier_def
  using compact_eq_bounded_closed
  by blast

lemma compact_frontier[intro]:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<Longrightarrow> compact (frontier S)"
  using compact_eq_bounded_closed compact_frontier_bounded
  by blast

corollary compact_sphere [simp]:
  fixes a :: "'a::{real_normed_vector,perfect_space,heine_borel}"
  shows "compact (sphere a r)"
using compact_frontier [of "cball a r"] by simp

corollary bounded_sphere [simp]:
  fixes a :: "'a::{real_normed_vector,perfect_space,heine_borel}"
  shows "bounded (sphere a r)"
by (simp add: compact_imp_bounded)

corollary closed_sphere  [simp]:
  fixes a :: "'a::{real_normed_vector,perfect_space,heine_borel}"
  shows "closed (sphere a r)"
by (simp add: compact_imp_closed)

lemma frontier_subset_compact:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<Longrightarrow> frontier S \<subseteq> S"
  using frontier_subset_closed compact_eq_bounded_closed
  by blast

subsection\<open>Relations among convergence and absolute convergence for power series.\<close>

lemma summable_imp_bounded:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "summable f \<Longrightarrow> bounded (range f)"
by (frule summable_LIMSEQ_zero) (simp add: convergent_imp_bounded)

lemma summable_imp_sums_bounded:
   "summable f \<Longrightarrow> bounded (range (\<lambda>n. sum f {..<n}))"
by (auto simp: summable_def sums_def dest: convergent_imp_bounded)

lemma power_series_conv_imp_absconv_weak:
  fixes a:: "nat \<Rightarrow> 'a::{real_normed_div_algebra,banach}" and w :: 'a
  assumes sum: "summable (\<lambda>n. a n * z ^ n)" and no: "norm w < norm z"
    shows "summable (\<lambda>n. of_real(norm(a n)) * w ^ n)"
proof -
  obtain M where M: "\<And>x. norm (a x * z ^ x) \<le> M"
    using summable_imp_bounded [OF sum] by (force simp: bounded_iff)
  then have *: "summable (\<lambda>n. norm (a n) * norm w ^ n)"
    by (rule_tac M=M in Abel_lemma) (auto simp: norm_mult norm_power intro: no)
  show ?thesis
    apply (rule series_comparison_complex [of "(\<lambda>n. of_real(norm(a n) * norm w ^ n))"])
    apply (simp only: summable_complex_of_real *)
    apply (auto simp: norm_mult norm_power)
    done
qed

subsection \<open>Bounded closed nest property (proof does not use Heine-Borel)\<close>

lemma bounded_closed_nest:
  fixes s :: "nat \<Rightarrow> ('a::heine_borel) set"
  assumes "\<forall>n. closed (s n)"
    and "\<forall>n. s n \<noteq> {}"
    and "\<forall>m n. m \<le> n \<longrightarrow> s n \<subseteq> s m"
    and "bounded (s 0)"
  shows "\<exists>a. \<forall>n. a \<in> s n"
proof -
  from assms(2) obtain x where x: "\<forall>n. x n \<in> s n"
    using choice[of "\<lambda>n x. x \<in> s n"] by auto
  from assms(4,1) have "seq_compact (s 0)"
    by (simp add: bounded_closed_imp_seq_compact)
  then obtain l r where lr: "l \<in> s 0" "strict_mono r" "(x \<circ> r) \<longlonglongrightarrow> l"
    using x and assms(3) unfolding seq_compact_def by blast
  have "\<forall>n. l \<in> s n"
  proof
    fix n :: nat
    have "closed (s n)"
      using assms(1) by simp
    moreover have "\<forall>i. (x \<circ> r) i \<in> s i"
      using x and assms(3) and lr(2) [THEN seq_suble] by auto
    then have "\<forall>i. (x \<circ> r) (i + n) \<in> s n"
      using assms(3) by (fast intro!: le_add2)
    moreover have "(\<lambda>i. (x \<circ> r) (i + n)) \<longlonglongrightarrow> l"
      using lr(3) by (rule LIMSEQ_ignore_initial_segment)
    ultimately show "l \<in> s n"
      by (rule closed_sequentially)
  qed
  then show ?thesis ..
qed

text \<open>Decreasing case does not even need compactness, just completeness.\<close>

lemma decreasing_closed_nest:
  fixes s :: "nat \<Rightarrow> ('a::complete_space) set"
  assumes
    "\<forall>n. closed (s n)"
    "\<forall>n. s n \<noteq> {}"
    "\<forall>m n. m \<le> n \<longrightarrow> s n \<subseteq> s m"
    "\<forall>e>0. \<exists>n. \<forall>x\<in>s n. \<forall>y\<in>s n. dist x y < e"
  shows "\<exists>a. \<forall>n. a \<in> s n"
proof -
  have "\<forall>n. \<exists>x. x \<in> s n"
    using assms(2) by auto
  then have "\<exists>t. \<forall>n. t n \<in> s n"
    using choice[of "\<lambda>n x. x \<in> s n"] by auto
  then obtain t where t: "\<forall>n. t n \<in> s n" by auto
  {
    fix e :: real
    assume "e > 0"
    then obtain N where N:"\<forall>x\<in>s N. \<forall>y\<in>s N. dist x y < e"
      using assms(4) by auto
    {
      fix m n :: nat
      assume "N \<le> m \<and> N \<le> n"
      then have "t m \<in> s N" "t n \<in> s N"
        using assms(3) t unfolding  subset_eq t by blast+
      then have "dist (t m) (t n) < e"
        using N by auto
    }
    then have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (t m) (t n) < e"
      by auto
  }
  then have "Cauchy t"
    unfolding cauchy_def by auto
  then obtain l where l:"(t \<longlongrightarrow> l) sequentially"
    using complete_UNIV unfolding complete_def by auto
  {
    fix n :: nat
    {
      fix e :: real
      assume "e > 0"
      then obtain N :: nat where N: "\<forall>n\<ge>N. dist (t n) l < e"
        using l[unfolded lim_sequentially] by auto
      have "t (max n N) \<in> s n"
        using assms(3)
        unfolding subset_eq
        apply (erule_tac x=n in allE)
        apply (erule_tac x="max n N" in allE)
        using t
        apply auto
        done
      then have "\<exists>y\<in>s n. dist y l < e"
        apply (rule_tac x="t (max n N)" in bexI)
        using N
        apply auto
        done
    }
    then have "l \<in> s n"
      using closed_approachable[of "s n" l] assms(1) by auto
  }
  then show ?thesis by auto
qed

text \<open>Strengthen it to the intersection actually being a singleton.\<close>

lemma decreasing_closed_nest_sing:
  fixes s :: "nat \<Rightarrow> 'a::complete_space set"
  assumes
    "\<forall>n. closed(s n)"
    "\<forall>n. s n \<noteq> {}"
    "\<forall>m n. m \<le> n \<longrightarrow> s n \<subseteq> s m"
    "\<forall>e>0. \<exists>n. \<forall>x \<in> (s n). \<forall> y\<in>(s n). dist x y < e"
  shows "\<exists>a. \<Inter>(range s) = {a}"
proof -
  obtain a where a: "\<forall>n. a \<in> s n"
    using decreasing_closed_nest[of s] using assms by auto
  {
    fix b
    assume b: "b \<in> \<Inter>(range s)"
    {
      fix e :: real
      assume "e > 0"
      then have "dist a b < e"
        using assms(4) and b and a by blast
    }
    then have "dist a b = 0"
      by (metis dist_eq_0_iff dist_nz less_le)
  }
  with a have "\<Inter>(range s) = {a}"
    unfolding image_def by auto
  then show ?thesis ..
qed


subsection \<open>Continuity\<close>

text\<open>Derive the epsilon-delta forms, which we often use as "definitions"\<close>

lemma continuous_within_eps_delta:
  "continuous (at x within s) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'\<in> s.  dist x' x < d --> dist (f x') (f x) < e)"
  unfolding continuous_within and Lim_within
  apply auto
  apply (metis dist_nz dist_self, blast)
  done

corollary continuous_at_eps_delta:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e > 0. \<exists>d > 0. \<forall>x'. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  using continuous_within_eps_delta [of x UNIV f] by simp

lemma continuous_at_right_real_increasing:
  fixes f :: "real \<Rightarrow> real"
  assumes nondecF: "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "continuous (at_right a) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f (a + d) - f a < e)"
  apply (simp add: greaterThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong, safe)
  apply (erule_tac x="a + d" in allE, simp)
  apply (simp add: nondecF field_simps)
  apply (drule nondecF, simp)
  done

lemma continuous_at_left_real_increasing:
  assumes nondecF: "\<And> x y. x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
  shows "(continuous (at_left (a :: real)) f) = (\<forall>e > 0. \<exists>delta > 0. f a - f (a - delta) < e)"
  apply (simp add: lessThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong, safe)
  apply (erule_tac x="a - d" in allE, simp)
  apply (simp add: nondecF field_simps)
  apply (cut_tac x="a - d" and y=x in nondecF, simp_all)
  done

text\<open>Versions in terms of open balls.\<close>

lemma continuous_within_ball:
  "continuous (at x within s) f \<longleftrightarrow>
    (\<forall>e > 0. \<exists>d > 0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix e :: real
    assume "e > 0"
    then obtain d where d: "d>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e"
      using \<open>?lhs\<close>[unfolded continuous_within Lim_within] by auto
    {
      fix y
      assume "y \<in> f ` (ball x d \<inter> s)"
      then have "y \<in> ball (f x) e"
        using d(2)
        apply (auto simp: dist_commute)
        apply (erule_tac x=xa in ballE, auto)
        using \<open>e > 0\<close>
        apply auto
        done
    }
    then have "\<exists>d>0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e"
      using \<open>d > 0\<close>
      unfolding subset_eq ball_def by (auto simp: dist_commute)
  }
  then show ?rhs by auto
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_within Lim_within ball_def subset_eq
    apply (auto simp: dist_commute)
    apply (erule_tac x=e in allE, auto)
    done
qed

lemma continuous_at_ball:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f ` (ball x d) \<subseteq> ball (f x) e)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto
    apply (erule_tac x=e in allE, auto)
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x=xa in allE)
    apply (auto simp: dist_commute)
    done
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto
    apply (erule_tac x=e in allE, auto)
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x="f xa" in allE)
    apply (auto simp: dist_commute)
    done
qed

text\<open>Define setwise continuity in terms of limits within the set.\<close>

lemma continuous_on_iff:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  unfolding continuous_on_def Lim_within
  by (metis dist_pos_lt dist_self)

lemma continuous_within_E:
  assumes "continuous (at x within s) f" "e>0"
  obtains d where "d>0"  "\<And>x'. \<lbrakk>x'\<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms apply (simp add: continuous_within_eps_delta)
  apply (drule spec [of _ e], clarify)
  apply (rule_tac d="d/2" in that, auto)
  done

lemma continuous_onI [intro?]:
  assumes "\<And>x e. \<lbrakk>e > 0; x \<in> s\<rbrakk> \<Longrightarrow> \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) \<le> e"
  shows "continuous_on s f"
apply (simp add: continuous_on_iff, clarify)
apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
done

text\<open>Some simple consequential lemmas.\<close>

lemma continuous_onE:
    assumes "continuous_on s f" "x\<in>s" "e>0"
    obtains d where "d>0"  "\<And>x'. \<lbrakk>x' \<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms
  apply (simp add: continuous_on_iff)
  apply (elim ballE allE)
  apply (auto intro: that [where d="d/2" for d])
  done

lemma uniformly_continuous_onE:
  assumes "uniformly_continuous_on s f" "0 < e"
  obtains d where "d>0" "\<And>x x'. \<lbrakk>x\<in>s; x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
using assms
by (auto simp: uniformly_continuous_on_def)

lemma continuous_at_imp_continuous_within:
  "continuous (at x) f \<Longrightarrow> continuous (at x within s) f"
  unfolding continuous_within continuous_at using Lim_at_imp_Lim_at_within by auto

lemma Lim_trivial_limit: "trivial_limit net \<Longrightarrow> (f \<longlongrightarrow> l) net"
  by simp

lemmas continuous_on = continuous_on_def \<comment> "legacy theorem name"

lemma continuous_within_subset:
  "continuous (at x within s) f \<Longrightarrow> t \<subseteq> s \<Longrightarrow> continuous (at x within t) f"
  unfolding continuous_within by(metis tendsto_within_subset)

lemma continuous_on_interior:
  "continuous_on s f \<Longrightarrow> x \<in> interior s \<Longrightarrow> continuous (at x) f"
  by (metis continuous_on_eq_continuous_at continuous_on_subset interiorE)

lemma continuous_on_eq:
  "\<lbrakk>continuous_on s f; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> continuous_on s g"
  unfolding continuous_on_def tendsto_def eventually_at_topological
  by simp

text \<open>Characterization of various kinds of continuity in terms of sequences.\<close>

lemma continuous_within_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  shows "continuous (at a within s) f \<longleftrightarrow>
    (\<forall>x. (\<forall>n::nat. x n \<in> s) \<and> (x \<longlongrightarrow> a) sequentially
         \<longrightarrow> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix x :: "nat \<Rightarrow> 'a"
    assume x: "\<forall>n. x n \<in> s" "\<forall>e>0. eventually (\<lambda>n. dist (x n) a < e) sequentially"
    fix T :: "'b set"
    assume "open T" and "f a \<in> T"
    with \<open>?lhs\<close> obtain d where "d>0" and d:"\<forall>x\<in>s. 0 < dist x a \<and> dist x a < d \<longrightarrow> f x \<in> T"
      unfolding continuous_within tendsto_def eventually_at by auto
    have "eventually (\<lambda>n. dist (x n) a < d) sequentially"
      using x(2) \<open>d>0\<close> by simp
    then have "eventually (\<lambda>n. (f \<circ> x) n \<in> T) sequentially"
    proof eventually_elim
      case (elim n)
      then show ?case
        using d x(1) \<open>f a \<in> T\<close> by auto
    qed
  }
  then show ?rhs
    unfolding tendsto_iff tendsto_def by simp
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_within tendsto_def [where l="f a"]
    by (simp add: sequentially_imp_eventually_within)
qed

lemma continuous_at_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  shows "continuous (at a) f \<longleftrightarrow>
    (\<forall>x. (x \<longlongrightarrow> a) sequentially --> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  using continuous_within_sequentially[of a UNIV f] by simp

lemma continuous_on_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  shows "continuous_on s f \<longleftrightarrow>
    (\<forall>x. \<forall>a \<in> s. (\<forall>n. x(n) \<in> s) \<and> (x \<longlongrightarrow> a) sequentially
      --> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  (is "?lhs = ?rhs")
proof
  assume ?rhs
  then show ?lhs
    using continuous_within_sequentially[of _ s f]
    unfolding continuous_on_eq_continuous_within
    by auto
next
  assume ?lhs
  then show ?rhs
    unfolding continuous_on_eq_continuous_within
    using continuous_within_sequentially[of _ s f]
    by auto
qed

lemma uniformly_continuous_on_sequentially:
  "uniformly_continuous_on s f \<longleftrightarrow> (\<forall>x y. (\<forall>n. x n \<in> s) \<and> (\<forall>n. y n \<in> s) \<and>
    (\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0 \<longrightarrow> (\<lambda>n. dist (f(x n)) (f(y n))) \<longlonglongrightarrow> 0)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix x y
    assume x: "\<forall>n. x n \<in> s"
      and y: "\<forall>n. y n \<in> s"
      and xy: "((\<lambda>n. dist (x n) (y n)) \<longlongrightarrow> 0) sequentially"
    {
      fix e :: real
      assume "e > 0"
      then obtain d where "d > 0" and d: "\<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
        using \<open>?lhs\<close>[unfolded uniformly_continuous_on_def, THEN spec[where x=e]] by auto
      obtain N where N: "\<forall>n\<ge>N. dist (x n) (y n) < d"
        using xy[unfolded lim_sequentially dist_norm] and \<open>d>0\<close> by auto
      {
        fix n
        assume "n\<ge>N"
        then have "dist (f (x n)) (f (y n)) < e"
          using N[THEN spec[where x=n]]
          using d[THEN bspec[where x="x n"], THEN bspec[where x="y n"]]
          using x and y
          by (simp add: dist_commute)
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
        by auto
    }
    then have "((\<lambda>n. dist (f(x n)) (f(y n))) \<longlongrightarrow> 0) sequentially"
      unfolding lim_sequentially and dist_real_def by auto
  }
  then show ?rhs by auto
next
  assume ?rhs
  {
    assume "\<not> ?lhs"
    then obtain e where "e > 0" "\<forall>d>0. \<exists>x\<in>s. \<exists>x'\<in>s. dist x' x < d \<and> \<not> dist (f x') (f x) < e"
      unfolding uniformly_continuous_on_def by auto
    then obtain fa where fa:
      "\<forall>x. 0 < x \<longrightarrow> fst (fa x) \<in> s \<and> snd (fa x) \<in> s \<and> dist (fst (fa x)) (snd (fa x)) < x \<and> \<not> dist (f (fst (fa x))) (f (snd (fa x))) < e"
      using choice[of "\<lambda>d x. d>0 \<longrightarrow> fst x \<in> s \<and> snd x \<in> s \<and> dist (snd x) (fst x) < d \<and> \<not> dist (f (snd x)) (f (fst x)) < e"]
      unfolding Bex_def
      by (auto simp: dist_commute)
    define x where "x n = fst (fa (inverse (real n + 1)))" for n
    define y where "y n = snd (fa (inverse (real n + 1)))" for n
    have xyn: "\<forall>n. x n \<in> s \<and> y n \<in> s"
      and xy0: "\<forall>n. dist (x n) (y n) < inverse (real n + 1)"
      and fxy:"\<forall>n. \<not> dist (f (x n)) (f (y n)) < e"
      unfolding x_def and y_def using fa
      by auto
    {
      fix e :: real
      assume "e > 0"
      then obtain N :: nat where "N \<noteq> 0" and N: "0 < inverse (real N) \<and> inverse (real N) < e"
        unfolding real_arch_inverse[of e] by auto
      {
        fix n :: nat
        assume "n \<ge> N"
        then have "inverse (real n + 1) < inverse (real N)"
          using of_nat_0_le_iff and \<open>N\<noteq>0\<close> by auto
        also have "\<dots> < e" using N by auto
        finally have "inverse (real n + 1) < e" by auto
        then have "dist (x n) (y n) < e"
          using xy0[THEN spec[where x=n]] by auto
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (x n) (y n) < e" by auto
    }
    then have "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
      using \<open>?rhs\<close>[THEN spec[where x=x], THEN spec[where x=y]] and xyn
      unfolding lim_sequentially dist_real_def by auto
    then have False using fxy and \<open>e>0\<close> by auto
  }
  then show ?lhs
    unfolding uniformly_continuous_on_def by blast
qed

lemma continuous_closed_imp_Cauchy_continuous:
  fixes S :: "('a::complete_space) set"
  shows "\<lbrakk>continuous_on S f; closed S; Cauchy \<sigma>; \<And>n. (\<sigma> n) \<in> S\<rbrakk> \<Longrightarrow> Cauchy(f o \<sigma>)"
  apply (simp add: complete_eq_closed [symmetric] continuous_on_sequentially)
  by (meson LIMSEQ_imp_Cauchy complete_def)

text\<open>The usual transformation theorems.\<close>

lemma continuous_transform_within:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at x within s) f"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x' \<in> s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "continuous (at x within s) g"
  using assms
  unfolding continuous_within
  by (force intro: Lim_transform_within)


subsubsection \<open>Structural rules for pointwise continuity\<close>

lemma continuous_infdist[continuous_intros]:
  assumes "continuous F f"
  shows "continuous F (\<lambda>x. infdist (f x) A)"
  using assms unfolding continuous_def by (rule tendsto_infdist)

lemma continuous_infnorm[continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. infnorm (f x))"
  unfolding continuous_def by (rule tendsto_infnorm)

lemma continuous_inner[continuous_intros]:
  assumes "continuous F f"
    and "continuous F g"
  shows "continuous F (\<lambda>x. inner (f x) (g x))"
  using assms unfolding continuous_def by (rule tendsto_inner)

lemmas continuous_at_inverse = isCont_inverse

subsubsection \<open>Structural rules for setwise continuity\<close>

lemma continuous_on_infnorm[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. infnorm (f x))"
  unfolding continuous_on by (fast intro: tendsto_infnorm)

lemma continuous_on_inner[continuous_intros]:
  fixes g :: "'a::topological_space \<Rightarrow> 'b::real_inner"
  assumes "continuous_on s f"
    and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. inner (f x) (g x))"
  using bounded_bilinear_inner assms
  by (rule bounded_bilinear.continuous_on)

subsubsection \<open>Structural rules for uniform continuity\<close>

lemma uniformly_continuous_on_dist[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. dist (f x) (g x))"
proof -
  {
    fix a b c d :: 'b
    have "\<bar>dist a b - dist c d\<bar> \<le> dist a c + dist b d"
      using dist_triangle2 [of a b c] dist_triangle2 [of b c d]
      using dist_triangle3 [of c d a] dist_triangle [of a d b]
      by arith
  } note le = this
  {
    fix x y
    assume f: "(\<lambda>n. dist (f (x n)) (f (y n))) \<longlonglongrightarrow> 0"
    assume g: "(\<lambda>n. dist (g (x n)) (g (y n))) \<longlonglongrightarrow> 0"
    have "(\<lambda>n. \<bar>dist (f (x n)) (g (x n)) - dist (f (y n)) (g (y n))\<bar>) \<longlonglongrightarrow> 0"
      by (rule Lim_transform_bound [OF _ tendsto_add_zero [OF f g]],
        simp add: le)
  }
  then show ?thesis
    using assms unfolding uniformly_continuous_on_sequentially
    unfolding dist_real_def by simp
qed

lemma uniformly_continuous_on_norm[continuous_intros]:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. norm (f x))"
  unfolding norm_conv_dist using assms
  by (intro uniformly_continuous_on_dist uniformly_continuous_on_const)

lemma (in bounded_linear) uniformly_continuous_on[continuous_intros]:
  fixes g :: "_::metric_space \<Rightarrow> _"
  assumes "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f (g x))"
  using assms unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff diff[symmetric]
  by (auto intro: tendsto_zero)

lemma uniformly_continuous_on_cmul[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. c *\<^sub>R f(x))"
  using bounded_linear_scaleR_right assms
  by (rule bounded_linear.uniformly_continuous_on)

lemma dist_minus:
  fixes x y :: "'a::real_normed_vector"
  shows "dist (- x) (- y) = dist x y"
  unfolding dist_norm minus_diff_minus norm_minus_cancel ..

lemma uniformly_continuous_on_minus[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. - f x)"
  unfolding uniformly_continuous_on_def dist_minus .

lemma uniformly_continuous_on_add[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x + g x)"
  using assms
  unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff add_diff_add
  by (auto intro: tendsto_add_zero)

lemma uniformly_continuous_on_diff[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x - g x)"
  using assms uniformly_continuous_on_add [of s f "- g"]
    by (simp add: fun_Compl_def uniformly_continuous_on_minus)

lemmas continuous_at_compose = isCont_o

text \<open>Continuity in terms of open preimages.\<close>

lemma continuous_at_open:
  "continuous (at x) f \<longleftrightarrow> (\<forall>t. open t \<and> f x \<in> t --> (\<exists>s. open s \<and> x \<in> s \<and> (\<forall>x' \<in> s. (f x') \<in> t)))"
  unfolding continuous_within_topological [of x UNIV f]
  unfolding imp_conjL
  by (intro all_cong imp_cong ex_cong conj_cong refl) auto

lemma continuous_imp_tendsto:
  assumes "continuous (at x0) f"
    and "x \<longlonglongrightarrow> x0"
  shows "(f \<circ> x) \<longlonglongrightarrow> (f x0)"
proof (rule topological_tendstoI)
  fix S
  assume "open S" "f x0 \<in> S"
  then obtain T where T_def: "open T" "x0 \<in> T" "\<forall>x\<in>T. f x \<in> S"
     using assms continuous_at_open by metis
  then have "eventually (\<lambda>n. x n \<in> T) sequentially"
    using assms T_def by (auto simp: tendsto_def)
  then show "eventually (\<lambda>n. (f \<circ> x) n \<in> S) sequentially"
    using T_def by (auto elim!: eventually_mono)
qed

lemma continuous_on_open:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>t. openin (subtopology euclidean (f ` s)) t \<longrightarrow>
      openin (subtopology euclidean s) {x \<in> s. f x \<in> t})"
  unfolding continuous_on_open_invariant openin_open Int_def vimage_def Int_commute
  by (simp add: imp_ex imageI conj_commute eq_commute cong: conj_cong)

lemma continuous_on_open_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. openin (subtopology euclidean T) U
                  \<longrightarrow> openin (subtopology euclidean S) {x \<in> S. f x \<in> U})"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (auto simp: openin_euclidean_subtopology_iff continuous_on_iff)
    by (metis assms image_subset_iff)
next
  have ope: "openin (subtopology euclidean T) (ball y e \<inter> T)" for y e
    by (simp add: Int_commute openin_open_Int)
  assume ?rhs
  then show ?lhs
    apply (clarsimp simp add: continuous_on_iff)
    apply (drule_tac x = "ball (f x) e \<inter> T" in spec)
    apply (clarsimp simp add: ope openin_euclidean_subtopology_iff [of S])
    by (metis (no_types, hide_lams) assms dist_commute dist_self image_subset_iff)
qed

lemma continuous_openin_preimage:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  shows
   "\<lbrakk>continuous_on S f; f ` S \<subseteq> T; openin (subtopology euclidean T) U\<rbrakk>
        \<Longrightarrow> openin (subtopology euclidean S) {x \<in> S. f x \<in> U}"
by (simp add: continuous_on_open_gen)

text \<open>Similarly in terms of closed sets.\<close>

lemma continuous_on_closed:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>t. closedin (subtopology euclidean (f ` s)) t \<longrightarrow>
      closedin (subtopology euclidean s) {x \<in> s. f x \<in> t})"
  unfolding continuous_on_closed_invariant closedin_closed Int_def vimage_def Int_commute
  by (simp add: imp_ex imageI conj_commute eq_commute cong: conj_cong)

lemma continuous_on_closed_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. closedin (subtopology euclidean T) U
                  \<longrightarrow> closedin (subtopology euclidean S) {x \<in> S. f x \<in> U})"
proof -
  have *: "U \<subseteq> T \<Longrightarrow> {x \<in> S. f x \<in> T \<and> f x \<notin> U} = S - {x \<in> S. f x \<in> U}" for U
    using assms by blast
  show ?thesis
    apply (simp add: continuous_on_open_gen [OF assms], safe)
    apply (drule_tac [!] x="T-U" in spec)
    apply (force simp: closedin_def *)
    apply (force simp: openin_closedin_eq *)
    done
qed

lemma continuous_closedin_preimage_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on S f" "f ` S \<subseteq> T" "closedin (subtopology euclidean T) U"
    shows "closedin (subtopology euclidean S) {x \<in> S. f x \<in> U}"
using assms continuous_on_closed_gen by blast

lemma continuous_on_imp_closedin:
  assumes "continuous_on S f" "closedin (subtopology euclidean (f ` S)) T"
    shows "closedin (subtopology euclidean S) {x. x \<in> S \<and> f x \<in> T}"
using assms continuous_on_closed by blast

subsection \<open>Half-global and completely global cases.\<close>

lemma continuous_openin_preimage_gen:
  assumes "continuous_on s f"  "open t"
  shows "openin (subtopology euclidean s) {x \<in> s. f x \<in> t}"
proof -
  have *: "\<forall>x. x \<in> s \<and> f x \<in> t \<longleftrightarrow> x \<in> s \<and> f x \<in> (t \<inter> f ` s)"
    by auto
  have "openin (subtopology euclidean (f ` s)) (t \<inter> f ` s)"
    using openin_open_Int[of t "f ` s", OF assms(2)] unfolding openin_open by auto
  then show ?thesis
    using assms(1)[unfolded continuous_on_open, THEN spec[where x="t \<inter> f ` s"]]
    using * by auto
qed

lemma continuous_closedin_preimage:
  assumes "continuous_on s f" and "closed t"
  shows "closedin (subtopology euclidean s) {x \<in> s. f x \<in> t}"
proof -
  have *: "\<forall>x. x \<in> s \<and> f x \<in> t \<longleftrightarrow> x \<in> s \<and> f x \<in> (t \<inter> f ` s)"
    by auto
  have "closedin (subtopology euclidean (f ` s)) (t \<inter> f ` s)"
    using closedin_closed_Int[of t "f ` s", OF assms(2)]
    by (simp add: Int_commute)
  then show ?thesis
    using assms(1)[unfolded continuous_on_closed, THEN spec[where x="t \<inter> f ` s"]]
    using * by auto
qed

lemma continuous_openin_preimage_eq:
   "continuous_on S f \<longleftrightarrow>
    (\<forall>t. open t \<longrightarrow> openin (subtopology euclidean S) {x. x \<in> S \<and> f x \<in> t})"
apply safe
apply (simp add: continuous_openin_preimage_gen)
apply (fastforce simp add: continuous_on_open openin_open)
done

lemma continuous_closedin_preimage_eq:
   "continuous_on S f \<longleftrightarrow>
    (\<forall>t. closed t \<longrightarrow> closedin (subtopology euclidean S) {x. x \<in> S \<and> f x \<in> t})"
apply safe
apply (simp add: continuous_closedin_preimage)
apply (fastforce simp add: continuous_on_closed closedin_closed)
done

lemma continuous_open_preimage:
  assumes "continuous_on s f"
    and "open s"
    and "open t"
  shows "open {x \<in> s. f x \<in> t}"
proof-
  obtain T where T: "open T" "{x \<in> s. f x \<in> t} = s \<inter> T"
    using continuous_openin_preimage_gen[OF assms(1,3)] unfolding openin_open by auto
  then show ?thesis
    using open_Int[of s T, OF assms(2)] by auto
qed

lemma continuous_closed_preimage:
  assumes "continuous_on s f"
    and "closed s"
    and "closed t"
  shows "closed {x \<in> s. f x \<in> t}"
proof-
  obtain T where "closed T" "{x \<in> s. f x \<in> t} = s \<inter> T"
    using continuous_closedin_preimage[OF assms(1,3)]
    unfolding closedin_closed by auto
  then show ?thesis using closed_Int[of s T, OF assms(2)] by auto
qed

lemma continuous_open_preimage_univ:
  "open s \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> open {x. f x \<in> s}"
  using continuous_open_preimage[of UNIV f s] open_UNIV continuous_at_imp_continuous_on by auto

lemma continuous_closed_preimage_univ:
  "closed s \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> closed {x. f x \<in> s}"
  using continuous_closed_preimage[of UNIV f s] closed_UNIV continuous_at_imp_continuous_on by auto

lemma continuous_open_vimage: "open s \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> open (f -` s)"
  unfolding vimage_def by (rule continuous_open_preimage_univ)

lemma continuous_closed_vimage: "closed s \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> closed (f -` s)"
  unfolding vimage_def by (rule continuous_closed_preimage_univ)

lemma interior_image_subset:
  assumes "inj f" "\<And>x. continuous (at x) f"
  shows "interior (f ` s) \<subseteq> f ` (interior s)"
proof
  fix x assume "x \<in> interior (f ` s)"
  then obtain T where as: "open T" "x \<in> T" "T \<subseteq> f ` s" ..
  then have "x \<in> f ` s" by auto
  then obtain y where y: "y \<in> s" "x = f y" by auto
  have "open (vimage f T)"
    using assms \<open>open T\<close> by (metis continuous_open_vimage)
  moreover have "y \<in> vimage f T"
    using \<open>x = f y\<close> \<open>x \<in> T\<close> by simp
  moreover have "vimage f T \<subseteq> s"
    using \<open>T \<subseteq> image f s\<close> \<open>inj f\<close> unfolding inj_on_def subset_eq by auto
  ultimately have "y \<in> interior s" ..
  with \<open>x = f y\<close> show "x \<in> f ` interior s" ..
qed

subsection \<open>Equality of continuous functions on closure and related results.\<close>

lemma continuous_closedin_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on s f \<Longrightarrow> closedin (subtopology euclidean s) {x \<in> s. f x = a}"
  using continuous_closedin_preimage[of s f "{a}"] by auto

lemma continuous_closed_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on s f \<Longrightarrow> closed s \<Longrightarrow> closed {x \<in> s. f x = a}"
  using continuous_closed_preimage[of s f "{a}"] by auto

lemma continuous_constant_on_closure:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes "continuous_on (closure S) f"
      and "\<And>x. x \<in> S \<Longrightarrow> f x = a"
      and "x \<in> closure S"
  shows "f x = a"
    using continuous_closed_preimage_constant[of "closure S" f a]
      assms closure_minimal[of S "{x \<in> closure S. f x = a}"] closure_subset
    unfolding subset_eq
    by auto

lemma image_closure_subset:
  assumes "continuous_on (closure s) f"
    and "closed t"
    and "(f ` s) \<subseteq> t"
  shows "f ` (closure s) \<subseteq> t"
proof -
  have "s \<subseteq> {x \<in> closure s. f x \<in> t}"
    using assms(3) closure_subset by auto
  moreover have "closed {x \<in> closure s. f x \<in> t}"
    using continuous_closed_preimage[OF assms(1)] and assms(2) by auto
  ultimately have "closure s = {x \<in> closure s . f x \<in> t}"
    using closure_minimal[of s "{x \<in> closure s. f x \<in> t}"] by auto
  then show ?thesis by auto
qed

lemma continuous_on_closure_norm_le:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous_on (closure s) f"
    and "\<forall>y \<in> s. norm(f y) \<le> b"
    and "x \<in> (closure s)"
  shows "norm (f x) \<le> b"
proof -
  have *: "f ` s \<subseteq> cball 0 b"
    using assms(2)[unfolded mem_cball_0[symmetric]] by auto
  show ?thesis
    using image_closure_subset[OF assms(1) closed_cball[of 0 b] *] assms(3)
    unfolding subset_eq
    apply (erule_tac x="f x" in ballE)
    apply (auto simp: dist_norm)
    done
qed

lemma isCont_indicator:
  fixes x :: "'a::t2_space"
  shows "isCont (indicator A :: 'a \<Rightarrow> real) x = (x \<notin> frontier A)"
proof auto
  fix x
  assume cts_at: "isCont (indicator A :: 'a \<Rightarrow> real) x" and fr: "x \<in> frontier A"
  with continuous_at_open have 1: "\<forall>V::real set. open V \<and> indicator A x \<in> V \<longrightarrow>
    (\<exists>U::'a set. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> V))" by auto
  show False
  proof (cases "x \<in> A")
    assume x: "x \<in> A"
    hence "indicator A x \<in> ({0<..<2} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({0<..<2} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y > (0::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> A" using indicator_eq_0_iff by force
    hence "x \<in> interior A" using U interiorI by auto
    thus ?thesis using fr unfolding frontier_def by simp
  next
    assume x: "x \<notin> A"
    hence "indicator A x \<in> ({-1<..<1} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({-1<..<1} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y < (1::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> -A" by auto
    hence "x \<in> interior (-A)" using U interiorI by auto
    thus ?thesis using fr interior_complement unfolding frontier_def by auto
  qed
next
  assume nfr: "x \<notin> frontier A"
  hence "x \<in> interior A \<or> x \<in> interior (-A)"
    by (auto simp: frontier_def closure_interior)
  thus "isCont ((indicator A)::'a \<Rightarrow> real) x"
  proof
    assume int: "x \<in> interior A"
    then obtain U where U: "open U" "x \<in> U" "U \<subseteq> A" unfolding interior_def by auto
    hence "\<forall>y\<in>U. indicator A y = (1::real)" unfolding indicator_def by auto
    hence "continuous_on U (indicator A)" by (simp add: continuous_on_const indicator_eq_1_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  next
    assume ext: "x \<in> interior (-A)"
    then obtain U where U: "open U" "x \<in> U" "U \<subseteq> -A" unfolding interior_def by auto
    then have "continuous_on U (indicator A)"
      using continuous_on_topological by (auto simp: subset_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  qed
qed

subsection\<open> Theorems relating continuity and uniform continuity to closures\<close>

lemma continuous_on_closure:
   "continuous_on (closure S) f \<longleftrightarrow>
    (\<forall>x e. x \<in> closure S \<and> 0 < e
           \<longrightarrow> (\<exists>d. 0 < d \<and> (\<forall>y. y \<in> S \<and> dist y x < d \<longrightarrow> dist (f y) (f x) < e)))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    unfolding continuous_on_iff  by (metis Un_iff closure_def)
next
  assume R [rule_format]: ?rhs
  show ?lhs
  proof
    fix x and e::real
    assume "0 < e" and x: "x \<in> closure S"
    obtain \<delta>::real where "\<delta> > 0"
                   and \<delta>: "\<And>y. \<lbrakk>y \<in> S; dist y x < \<delta>\<rbrakk> \<Longrightarrow> dist (f y) (f x) < e/2"
      using R [of x "e/2"] \<open>0 < e\<close> x by auto
    have "dist (f y) (f x) \<le> e" if y: "y \<in> closure S" and dyx: "dist y x < \<delta>/2" for y
    proof -
      obtain \<delta>'::real where "\<delta>' > 0"
                      and \<delta>': "\<And>z. \<lbrakk>z \<in> S; dist z y < \<delta>'\<rbrakk> \<Longrightarrow> dist (f z) (f y) < e/2"
        using R [of y "e/2"] \<open>0 < e\<close> y by auto
      obtain z where "z \<in> S" and z: "dist z y < min \<delta>' \<delta> / 2"
        using closure_approachable y
        by (metis \<open>0 < \<delta>'\<close> \<open>0 < \<delta>\<close> divide_pos_pos min_less_iff_conj zero_less_numeral)
      have "dist (f z) (f y) < e/2"
        apply (rule \<delta>' [OF \<open>z \<in> S\<close>])
        using z \<open>0 < \<delta>'\<close> by linarith
      moreover have "dist (f z) (f x) < e/2"
        apply (rule \<delta> [OF \<open>z \<in> S\<close>])
        using z \<open>0 < \<delta>\<close>  dist_commute[of y z] dist_triangle_half_r [of y] dyx by auto
      ultimately show ?thesis
        by (metis dist_commute dist_triangle_half_l less_imp_le)
    qed
    then show "\<exists>d>0. \<forall>x'\<in>closure S. dist x' x < d \<longrightarrow> dist (f x') (f x) \<le> e"
      by (rule_tac x="\<delta>/2" in exI) (simp add: \<open>\<delta> > 0\<close>)
  qed
qed

lemma continuous_on_closure_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b :: metric_space"
  shows
   "continuous_on (closure S) f \<longleftrightarrow>
    (\<forall>x a. a \<in> closure S \<and> (\<forall>n. x n \<in> S) \<and> x \<longlonglongrightarrow> a \<longrightarrow> (f \<circ> x) \<longlonglongrightarrow> f a)"
   (is "?lhs = ?rhs")
proof -
  have "continuous_on (closure S) f \<longleftrightarrow>
           (\<forall>x \<in> closure S. continuous (at x within S) f)"
    by (force simp: continuous_on_closure Topology_Euclidean_Space.continuous_within_eps_delta)
  also have "... = ?rhs"
    by (force simp: continuous_within_sequentially)
  finally show ?thesis .
qed

lemma uniformly_continuous_on_closure:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes ucont: "uniformly_continuous_on S f"
      and cont: "continuous_on (closure S) f"
    shows "uniformly_continuous_on (closure S) f"
unfolding uniformly_continuous_on_def
proof (intro allI impI)
  fix e::real
  assume "0 < e"
  then obtain d::real
    where "d>0"
      and d: "\<And>x x'. \<lbrakk>x\<in>S; x'\<in>S; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e/3"
    using ucont [unfolded uniformly_continuous_on_def, rule_format, of "e/3"] by auto
  show "\<exists>d>0. \<forall>x\<in>closure S. \<forall>x'\<in>closure S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
  proof (rule exI [where x="d/3"], clarsimp simp: \<open>d > 0\<close>)
    fix x y
    assume x: "x \<in> closure S" and y: "y \<in> closure S" and dyx: "dist y x * 3 < d"
    obtain d1::real where "d1 > 0"
           and d1: "\<And>w. \<lbrakk>w \<in> closure S; dist w x < d1\<rbrakk> \<Longrightarrow> dist (f w) (f x) < e/3"
      using cont [unfolded continuous_on_iff, rule_format, of "x" "e/3"] \<open>0 < e\<close> x by auto
     obtain x' where "x' \<in> S" and x': "dist x' x < min d1 (d / 3)"
        using closure_approachable [of x S]
        by (metis \<open>0 < d1\<close> \<open>0 < d\<close> divide_pos_pos min_less_iff_conj x zero_less_numeral)
    obtain d2::real where "d2 > 0"
           and d2: "\<forall>w \<in> closure S. dist w y < d2 \<longrightarrow> dist (f w) (f y) < e/3"
      using cont [unfolded continuous_on_iff, rule_format, of "y" "e/3"] \<open>0 < e\<close> y by auto
     obtain y' where "y' \<in> S" and y': "dist y' y < min d2 (d / 3)"
        using closure_approachable [of y S]
        by (metis \<open>0 < d2\<close> \<open>0 < d\<close> divide_pos_pos min_less_iff_conj y zero_less_numeral)
     have "dist x' x < d/3" using x' by auto
     moreover have "dist x y < d/3"
       by (metis dist_commute dyx less_divide_eq_numeral1(1))
     moreover have "dist y y' < d/3"
       by (metis (no_types) dist_commute min_less_iff_conj y')
     ultimately have "dist x' y' < d/3 + d/3 + d/3"
       by (meson dist_commute_lessI dist_triangle_lt add_strict_mono)
     then have "dist x' y' < d" by simp
     then have "dist (f x') (f y') < e/3"
       by (rule d [OF \<open>y' \<in> S\<close> \<open>x' \<in> S\<close>])
     moreover have "dist (f x') (f x) < e/3" using \<open>x' \<in> S\<close> closure_subset x' d1
       by (simp add: closure_def)
     moreover have "dist (f y') (f y) < e/3" using \<open>y' \<in> S\<close> closure_subset y' d2
       by (simp add: closure_def)
     ultimately have "dist (f y) (f x) < e/3 + e/3 + e/3"
       by (meson dist_commute_lessI dist_triangle_lt add_strict_mono)
    then show "dist (f y) (f x) < e" by simp
  qed
qed

lemma uniformly_continuous_on_extension_at_closure:
  fixes f::"'a::metric_space \<Rightarrow> 'b::complete_space"
  assumes uc: "uniformly_continuous_on X f"
  assumes "x \<in> closure X"
  obtains l where "(f \<longlongrightarrow> l) (at x within X)"
proof -
  from assms obtain xs where xs: "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X"
    by (auto simp: closure_sequential)

  from uniformly_continuous_on_Cauchy[OF uc LIMSEQ_imp_Cauchy, OF xs]
  obtain l where l: "(\<lambda>n. f (xs n)) \<longlonglongrightarrow> l"
    by atomize_elim (simp only: convergent_eq_Cauchy)

  have "(f \<longlongrightarrow> l) (at x within X)"
  proof (safe intro!: Lim_within_LIMSEQ)
    fix xs'
    assume "\<forall>n. xs' n \<noteq> x \<and> xs' n \<in> X"
      and xs': "xs' \<longlonglongrightarrow> x"
    then have "xs' n \<noteq> x" "xs' n \<in> X" for n by auto

    from uniformly_continuous_on_Cauchy[OF uc LIMSEQ_imp_Cauchy, OF \<open>xs' \<longlonglongrightarrow> x\<close> \<open>xs' _ \<in> X\<close>]
    obtain l' where l': "(\<lambda>n. f (xs' n)) \<longlonglongrightarrow> l'"
      by atomize_elim (simp only: convergent_eq_Cauchy)

    show "(\<lambda>n. f (xs' n)) \<longlonglongrightarrow> l"
    proof (rule tendstoI)
      fix e::real assume "e > 0"
      define e' where "e' \<equiv> e / 2"
      have "e' > 0" using \<open>e > 0\<close> by (simp add: e'_def)

      have "\<forall>\<^sub>F n in sequentially. dist (f (xs n)) l < e'"
        by (simp add: \<open>0 < e'\<close> l tendstoD)
      moreover
      from uc[unfolded uniformly_continuous_on_def, rule_format, OF \<open>e' > 0\<close>]
      obtain d where d: "d > 0" "\<And>x x'. x \<in> X \<Longrightarrow> x' \<in> X \<Longrightarrow> dist x x' < d \<Longrightarrow> dist (f x) (f x') < e'"
        by auto
      have "\<forall>\<^sub>F n in sequentially. dist (xs n) (xs' n) < d"
        by (auto intro!: \<open>0 < d\<close> order_tendstoD tendsto_eq_intros xs xs')
      ultimately
      show "\<forall>\<^sub>F n in sequentially. dist (f (xs' n)) l < e"
      proof eventually_elim
        case (elim n)
        have "dist (f (xs' n)) l \<le> dist (f (xs n)) (f (xs' n)) + dist (f (xs n)) l"
          by (metis dist_triangle dist_commute)
        also have "dist (f (xs n)) (f (xs' n)) < e'"
          by (auto intro!: d xs \<open>xs' _ \<in> _\<close> elim)
        also note \<open>dist (f (xs n)) l < e'\<close>
        also have "e' + e' = e" by (simp add: e'_def)
        finally show ?case by simp
      qed
    qed
  qed
  thus ?thesis ..
qed

lemma uniformly_continuous_on_extension_on_closure:
  fixes f::"'a::metric_space \<Rightarrow> 'b::complete_space"
  assumes uc: "uniformly_continuous_on X f"
  obtains g where "uniformly_continuous_on (closure X) g" "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
    "\<And>Y h x. X \<subseteq> Y \<Longrightarrow> Y \<subseteq> closure X \<Longrightarrow> continuous_on Y h \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> f x = h x) \<Longrightarrow> x \<in> Y \<Longrightarrow> h x = g x"
proof -
  from uc have cont_f: "continuous_on X f"
    by (simp add: uniformly_continuous_imp_continuous)
  obtain y where y: "(f \<longlongrightarrow> y x) (at x within X)" if "x \<in> closure X" for x
    apply atomize_elim
    apply (rule choice)
    using uniformly_continuous_on_extension_at_closure[OF assms]
    by metis
  let ?g = "\<lambda>x. if x \<in> X then f x else y x"

  have "uniformly_continuous_on (closure X) ?g"
    unfolding uniformly_continuous_on_def
  proof safe
    fix e::real assume "e > 0"
    define e' where "e' \<equiv> e / 3"
    have "e' > 0" using \<open>e > 0\<close> by (simp add: e'_def)
    from uc[unfolded uniformly_continuous_on_def, rule_format, OF \<open>0 < e'\<close>]
    obtain d where "d > 0" and d: "\<And>x x'. x \<in> X \<Longrightarrow> x' \<in> X \<Longrightarrow> dist x' x < d \<Longrightarrow> dist (f x') (f x) < e'"
      by auto
    define d' where "d' = d / 3"
    have "d' > 0" using \<open>d > 0\<close> by (simp add: d'_def)
    show "\<exists>d>0. \<forall>x\<in>closure X. \<forall>x'\<in>closure X. dist x' x < d \<longrightarrow> dist (?g x') (?g x) < e"
    proof (safe intro!: exI[where x=d'] \<open>d' > 0\<close>)
      fix x x' assume x: "x \<in> closure X" and x': "x' \<in> closure X" and dist: "dist x' x < d'"
      then obtain xs xs' where xs: "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X"
        and xs': "xs' \<longlonglongrightarrow> x'" "\<And>n. xs' n \<in> X"
        by (auto simp: closure_sequential)
      have "\<forall>\<^sub>F n in sequentially. dist (xs' n) x' < d'"
        and "\<forall>\<^sub>F n in sequentially. dist (xs n) x < d'"
        by (auto intro!: \<open>0 < d'\<close> order_tendstoD tendsto_eq_intros xs xs')
      moreover
      have "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> y x" if "x \<in> closure X" "x \<notin> X" "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X" for xs x
        using that not_eventuallyD
        by (force intro!: filterlim_compose[OF y[OF \<open>x \<in> closure X\<close>]] simp: filterlim_at)
      then have "(\<lambda>x. f (xs' x)) \<longlonglongrightarrow> ?g x'" "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> ?g x"
        using x x'
        by (auto intro!: continuous_on_tendsto_compose[OF cont_f] simp: xs' xs)
      then have "\<forall>\<^sub>F n in sequentially. dist (f (xs' n)) (?g x') < e'"
        "\<forall>\<^sub>F n in sequentially. dist (f (xs n)) (?g x) < e'"
        by (auto intro!: \<open>0 < e'\<close> order_tendstoD tendsto_eq_intros)
      ultimately
      have "\<forall>\<^sub>F n in sequentially. dist (?g x') (?g x) < e"
      proof eventually_elim
        case (elim n)
        have "dist (?g x') (?g x) \<le>
          dist (f (xs' n)) (?g x') + dist (f (xs' n)) (f (xs n)) + dist (f (xs n)) (?g x)"
          by (metis add.commute add_le_cancel_left dist_commute dist_triangle dist_triangle_le)
        also
        {
          have "dist (xs' n) (xs n) \<le> dist (xs' n) x' + dist x' x + dist (xs n) x"
            by (metis add.commute add_le_cancel_left  dist_triangle dist_triangle_le)
          also note \<open>dist (xs' n) x' < d'\<close>
          also note \<open>dist x' x < d'\<close>
          also note \<open>dist (xs n) x < d'\<close>
          finally have "dist (xs' n) (xs n) < d" by (simp add: d'_def)
        }
        with \<open>xs _ \<in> X\<close> \<open>xs' _ \<in> X\<close> have "dist (f (xs' n)) (f (xs n)) < e'"
          by (rule d)
        also note \<open>dist (f (xs' n)) (?g x') < e'\<close>
        also note \<open>dist (f (xs n)) (?g x) < e'\<close>
        finally show ?case by (simp add: e'_def)
      qed
      then show "dist (?g x') (?g x) < e" by simp
    qed
  qed
  moreover have "f x = ?g x" if "x \<in> X" for x using that by simp
  moreover
  {
    fix Y h x
    assume Y: "x \<in> Y" "X \<subseteq> Y" "Y \<subseteq> closure X" and cont_h: "continuous_on Y h"
      and extension: "(\<And>x. x \<in> X \<Longrightarrow> f x = h x)"
    {
      assume "x \<notin> X"
      have "x \<in> closure X" using Y by auto
      then obtain xs where xs: "xs \<longlonglongrightarrow> x" "\<And>n. xs n \<in> X"
        by (auto simp: closure_sequential)
      from continuous_on_tendsto_compose[OF cont_h xs(1)] xs(2) Y
      have hx: "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> h x"
        by (auto simp: set_mp extension)
      then have "(\<lambda>x. f (xs x)) \<longlonglongrightarrow> y x"
        using \<open>x \<notin> X\<close> not_eventuallyD xs(2)
        by (force intro!: filterlim_compose[OF y[OF \<open>x \<in> closure X\<close>]] simp: filterlim_at xs)
      with hx have "h x = y x" by (rule LIMSEQ_unique)
    } then
    have "h x = ?g x"
      using extension by auto
  }
  ultimately show ?thesis ..
qed

lemma bounded_uniformly_continuous_image:
  fixes f :: "'a :: heine_borel \<Rightarrow> 'b :: heine_borel"
  assumes "uniformly_continuous_on S f" "bounded S"
  shows "bounded(image f S)"
  by (metis (no_types, lifting) assms bounded_closure_image compact_closure compact_continuous_image compact_eq_bounded_closed image_cong uniformly_continuous_imp_continuous uniformly_continuous_on_extension_on_closure)

subsection\<open>Quotient maps\<close>

lemma quotient_map_imp_continuous_open:
  assumes t: "f ` s \<subseteq> t"
      and ope: "\<And>u. u \<subseteq> t
              \<Longrightarrow> (openin (subtopology euclidean s) {x. x \<in> s \<and> f x \<in> u} \<longleftrightarrow>
                   openin (subtopology euclidean t) u)"
    shows "continuous_on s f"
proof -
  have [simp]: "{x \<in> s. f x \<in> f ` s} = s" by auto
  show ?thesis
    using ope [OF t]
    apply (simp add: continuous_on_open)
    by (metis (no_types, lifting) "ope"  openin_imp_subset openin_trans)
qed

lemma quotient_map_imp_continuous_closed:
  assumes t: "f ` s \<subseteq> t"
      and ope: "\<And>u. u \<subseteq> t
                  \<Longrightarrow> (closedin (subtopology euclidean s) {x. x \<in> s \<and> f x \<in> u} \<longleftrightarrow>
                       closedin (subtopology euclidean t) u)"
    shows "continuous_on s f"
proof -
  have [simp]: "{x \<in> s. f x \<in> f ` s} = s" by auto
  show ?thesis
    using ope [OF t]
    apply (simp add: continuous_on_closed)
    by (metis (no_types, lifting) "ope" closedin_imp_subset closedin_subtopology_refl closedin_trans openin_subtopology_refl openin_subtopology_self)
qed

lemma open_map_imp_quotient_map:
  assumes contf: "continuous_on s f"
      and t: "t \<subseteq> f ` s"
      and ope: "\<And>t. openin (subtopology euclidean s) t
                   \<Longrightarrow> openin (subtopology euclidean (f ` s)) (f ` t)"
    shows "openin (subtopology euclidean s) {x \<in> s. f x \<in> t} =
           openin (subtopology euclidean (f ` s)) t"
proof -
  have "t = image f {x. x \<in> s \<and> f x \<in> t}"
    using t by blast
  then show ?thesis
    using "ope" contf continuous_on_open by fastforce
qed

lemma closed_map_imp_quotient_map:
  assumes contf: "continuous_on s f"
      and t: "t \<subseteq> f ` s"
      and ope: "\<And>t. closedin (subtopology euclidean s) t
              \<Longrightarrow> closedin (subtopology euclidean (f ` s)) (f ` t)"
    shows "openin (subtopology euclidean s) {x \<in> s. f x \<in> t} \<longleftrightarrow>
           openin (subtopology euclidean (f ` s)) t"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have *: "closedin (subtopology euclidean s) (s - {x \<in> s. f x \<in> t})"
    using closedin_diff by fastforce
  have [simp]: "(f ` s - f ` (s - {x \<in> s. f x \<in> t})) = t"
    using t by blast
  show ?rhs
    using ope [OF *, unfolded closedin_def] by auto
next
  assume ?rhs
  with contf show ?lhs
    by (auto simp: continuous_on_open)
qed

lemma continuous_right_inverse_imp_quotient_map:
  assumes contf: "continuous_on s f" and imf: "f ` s \<subseteq> t"
      and contg: "continuous_on t g" and img: "g ` t \<subseteq> s"
      and fg [simp]: "\<And>y. y \<in> t \<Longrightarrow> f(g y) = y"
      and u: "u \<subseteq> t"
    shows "openin (subtopology euclidean s) {x. x \<in> s \<and> f x \<in> u} \<longleftrightarrow>
           openin (subtopology euclidean t) u"
          (is "?lhs = ?rhs")
proof -
  have f: "\<And>z. openin (subtopology euclidean (f ` s)) z \<Longrightarrow>
                openin (subtopology euclidean s) {x \<in> s. f x \<in> z}"
  and  g: "\<And>z. openin (subtopology euclidean (g ` t)) z \<Longrightarrow>
                openin (subtopology euclidean t) {x \<in> t. g x \<in> z}"
    using contf contg by (auto simp: continuous_on_open)
  show ?thesis
  proof
    have "{x \<in> t. g x \<in> g ` t \<and> g x \<in> s \<and> f (g x) \<in> u} = {x \<in> t. f (g x) \<in> u}"
      using imf img by blast
    also have "... = u"
      using u by auto
    finally have [simp]: "{x \<in> t. g x \<in> g ` t \<and> g x \<in> s \<and> f (g x) \<in> u} = u" .
    assume ?lhs
    then have *: "openin (subtopology euclidean (g ` t)) (g ` t \<inter> {x \<in> s. f x \<in> u})"
      by (meson img openin_Int openin_subtopology_Int_subset openin_subtopology_self)
    show ?rhs
      using g [OF *] by simp
  next
    assume rhs: ?rhs
    show ?lhs
      apply (rule f)
      by (metis fg image_eqI image_subset_iff imf img openin_subopen openin_subtopology_self openin_trans rhs)
  qed
qed

lemma continuous_left_inverse_imp_quotient_map:
  assumes "continuous_on s f"
      and "continuous_on (f ` s) g"
      and  "\<And>x. x \<in> s \<Longrightarrow> g(f x) = x"
      and "u \<subseteq> f ` s"
    shows "openin (subtopology euclidean s) {x. x \<in> s \<and> f x \<in> u} \<longleftrightarrow>
           openin (subtopology euclidean (f ` s)) u"
apply (rule continuous_right_inverse_imp_quotient_map)
using assms
apply force+
done

subsection \<open>A function constant on a set\<close>

definition constant_on  (infixl "(constant'_on)" 50)
  where "f constant_on A \<equiv> \<exists>y. \<forall>x\<in>A. f x = y"

lemma constant_on_subset: "\<lbrakk>f constant_on A; B \<subseteq> A\<rbrakk> \<Longrightarrow> f constant_on B"
  unfolding constant_on_def by blast

lemma injective_not_constant:
  fixes S :: "'a::{perfect_space} set"
  shows "\<lbrakk>open S; inj_on f S; f constant_on S\<rbrakk> \<Longrightarrow> S = {}"
unfolding constant_on_def
by (metis equals0I inj_on_contraD islimpt_UNIV islimpt_def)

lemma constant_on_closureI:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes cof: "f constant_on S" and contf: "continuous_on (closure S) f"
    shows "f constant_on (closure S)"
using continuous_constant_on_closure [OF contf] cof unfolding constant_on_def
by metis

text \<open>Making a continuous function avoid some value in a neighbourhood.\<close>

lemma continuous_within_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous (at x within s) f"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> s. dist x y < e --> f y \<noteq> a"
proof -
  obtain U where "open U" and "f x \<in> U" and "a \<notin> U"
    using t1_space [OF \<open>f x \<noteq> a\<close>] by fast
  have "(f \<longlongrightarrow> f x) (at x within s)"
    using assms(1) by (simp add: continuous_within)
  then have "eventually (\<lambda>y. f y \<in> U) (at x within s)"
    using \<open>open U\<close> and \<open>f x \<in> U\<close>
    unfolding tendsto_def by fast
  then have "eventually (\<lambda>y. f y \<noteq> a) (at x within s)"
    using \<open>a \<notin> U\<close> by (fast elim: eventually_mono)
  then show ?thesis
    using \<open>f x \<noteq> a\<close> by (auto simp: dist_commute zero_less_dist_iff eventually_at)
qed

lemma continuous_at_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous (at x) f"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
  using assms continuous_within_avoid[of x UNIV f a] by simp

lemma continuous_on_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous_on s f"
    and "x \<in> s"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y \<in> s. dist x y < e \<longrightarrow> f y \<noteq> a"
  using assms(1)[unfolded continuous_on_eq_continuous_within, THEN bspec[where x=x],
    OF assms(2)] continuous_within_avoid[of x s f a]
  using assms(3)
  by auto

lemma continuous_on_open_avoid:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::t1_space"
  assumes "continuous_on s f"
    and "open s"
    and "x \<in> s"
    and "f x \<noteq> a"
  shows "\<exists>e>0. \<forall>y. dist x y < e \<longrightarrow> f y \<noteq> a"
  using assms(1)[unfolded continuous_on_eq_continuous_at[OF assms(2)], THEN bspec[where x=x], OF assms(3)]
  using continuous_at_avoid[of x f a] assms(4)
  by auto

text \<open>Proving a function is constant by proving open-ness of level set.\<close>

lemma continuous_levelset_openin_cases:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (subtopology euclidean s) {x \<in> s. f x = a}
        \<Longrightarrow> (\<forall>x \<in> s. f x \<noteq> a) \<or> (\<forall>x \<in> s. f x = a)"
  unfolding connected_clopen
  using continuous_closedin_preimage_constant by auto

lemma continuous_levelset_openin:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (subtopology euclidean s) {x \<in> s. f x = a} \<Longrightarrow>
        (\<exists>x \<in> s. f x = a)  \<Longrightarrow> (\<forall>x \<in> s. f x = a)"
  using continuous_levelset_openin_cases[of s f ]
  by meson

lemma continuous_levelset_open:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes "connected s"
    and "continuous_on s f"
    and "open {x \<in> s. f x = a}"
    and "\<exists>x \<in> s.  f x = a"
  shows "\<forall>x \<in> s. f x = a"
  using continuous_levelset_openin[OF assms(1,2), of a, unfolded openin_open]
  using assms (3,4)
  by fast

text \<open>Some arithmetical combinations (more to prove).\<close>

lemma open_scaling[intro]:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
    and "open s"
  shows "open((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  {
    fix x
    assume "x \<in> s"
    then obtain e where "e>0"
      and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> s" using assms(2)[unfolded open_dist, THEN bspec[where x=x]]
      by auto
    have "e * \<bar>c\<bar> > 0"
      using assms(1)[unfolded zero_less_abs_iff[symmetric]] \<open>e>0\<close> by auto
    moreover
    {
      fix y
      assume "dist y (c *\<^sub>R x) < e * \<bar>c\<bar>"
      then have "norm ((1 / c) *\<^sub>R y - x) < e"
        unfolding dist_norm
        using norm_scaleR[of c "(1 / c) *\<^sub>R y - x", unfolded scaleR_right_diff_distrib, unfolded scaleR_scaleR] assms(1)
          assms(1)[unfolded zero_less_abs_iff[symmetric]] by (simp del:zero_less_abs_iff)
      then have "y \<in> op *\<^sub>R c ` s"
        using rev_image_eqI[of "(1 / c) *\<^sub>R y" s y "op *\<^sub>R c"]
        using e[THEN spec[where x="(1 / c) *\<^sub>R y"]]
        using assms(1)
        unfolding dist_norm scaleR_scaleR
        by auto
    }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' (c *\<^sub>R x) < e \<longrightarrow> x' \<in> op *\<^sub>R c ` s"
      apply (rule_tac x="e * \<bar>c\<bar>" in exI, auto)
      done
  }
  then show ?thesis unfolding open_dist by auto
qed

lemma minus_image_eq_vimage:
  fixes A :: "'a::ab_group_add set"
  shows "(\<lambda>x. - x) ` A = (\<lambda>x. - x) -` A"
  by (auto intro!: image_eqI [where f="\<lambda>x. - x"])

lemma open_negations:
  fixes S :: "'a::real_normed_vector set"
  shows "open S \<Longrightarrow> open ((\<lambda>x. - x) ` S)"
  using open_scaling [of "- 1" S] by simp

lemma open_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open((\<lambda>x. a + x) ` S)"
proof -
  {
    fix x
    have "continuous (at x) (\<lambda>x. x - a)"
      by (intro continuous_diff continuous_ident continuous_const)
  }
  moreover have "{x. x - a \<in> S} = op + a ` S"
    by force
  ultimately show ?thesis
    by (metis assms continuous_open_vimage vimage_def)
qed

lemma open_affinity:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"  "c \<noteq> 0"
  shows "open ((\<lambda>x. a + c *\<^sub>R x) ` S)"
proof -
  have *: "(\<lambda>x. a + c *\<^sub>R x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. c *\<^sub>R x)"
    unfolding o_def ..
  have "op + a ` op *\<^sub>R c ` S = (op + a \<circ> op *\<^sub>R c) ` S"
    by auto
  then show ?thesis
    using assms open_translation[of "op *\<^sub>R c ` S" a]
    unfolding *
    by auto
qed

lemma interior_translation:
  fixes S :: "'a::real_normed_vector set"
  shows "interior ((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (interior S)"
proof (rule set_eqI, rule)
  fix x
  assume "x \<in> interior (op + a ` S)"
  then obtain e where "e > 0" and e: "ball x e \<subseteq> op + a ` S"
    unfolding mem_interior by auto
  then have "ball (x - a) e \<subseteq> S"
    unfolding subset_eq Ball_def mem_ball dist_norm
    by (auto simp: diff_diff_eq)
  then show "x \<in> op + a ` interior S"
    unfolding image_iff
    apply (rule_tac x="x - a" in bexI)
    unfolding mem_interior
    using \<open>e > 0\<close>
    apply auto
    done
next
  fix x
  assume "x \<in> op + a ` interior S"
  then obtain y e where "e > 0" and e: "ball y e \<subseteq> S" and y: "x = a + y"
    unfolding image_iff Bex_def mem_interior by auto
  {
    fix z
    have *: "a + y - z = y + a - z" by auto
    assume "z \<in> ball x e"
    then have "z - a \<in> S"
      using e[unfolded subset_eq, THEN bspec[where x="z - a"]]
      unfolding mem_ball dist_norm y group_add_class.diff_diff_eq2 *
      by auto
    then have "z \<in> op + a ` S"
      unfolding image_iff by (auto intro!: bexI[where x="z - a"])
  }
  then have "ball x e \<subseteq> op + a ` S"
    unfolding subset_eq by auto
  then show "x \<in> interior (op + a ` S)"
    unfolding mem_interior using \<open>e > 0\<close> by auto
qed

subsection \<open>Topological properties of linear functions.\<close>

lemma linear_lim_0:
  assumes "bounded_linear f"
  shows "(f \<longlongrightarrow> 0) (at (0))"
proof -
  interpret f: bounded_linear f by fact
  have "(f \<longlongrightarrow> f 0) (at 0)"
    using tendsto_ident_at by (rule f.tendsto)
  then show ?thesis unfolding f.zero .
qed

lemma linear_continuous_at:
  assumes "bounded_linear f"
  shows "continuous (at a) f"
  unfolding continuous_at using assms
  apply (rule bounded_linear.tendsto)
  apply (rule tendsto_ident_at)
  done

lemma linear_continuous_within:
  "bounded_linear f \<Longrightarrow> continuous (at x within s) f"
  using continuous_at_imp_continuous_within[of x f s] using linear_continuous_at[of f] by auto

lemma linear_continuous_on:
  "bounded_linear f \<Longrightarrow> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

subsubsection\<open>Relating linear images to open/closed/interior/closure.\<close>

proposition open_surjective_linear_image:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "open A" "linear f" "surj f"
    shows "open(f ` A)"
unfolding open_dist
proof clarify
  fix x
  assume "x \<in> A"
  have "bounded (inv f ` Basis)"
    by (simp add: finite_imp_bounded)
  with bounded_pos obtain B where "B > 0" and B: "\<And>x. x \<in> inv f ` Basis \<Longrightarrow> norm x \<le> B"
    by metis
  obtain e where "e > 0" and e: "\<And>z. dist z x < e \<Longrightarrow> z \<in> A"
    by (metis open_dist \<open>x \<in> A\<close> \<open>open A\<close>)
  define \<delta> where "\<delta> \<equiv> e / B / DIM('b)"
  show "\<exists>e>0. \<forall>y. dist y (f x) < e \<longrightarrow> y \<in> f ` A"
  proof (intro exI conjI)
    show "\<delta> > 0"
      using \<open>e > 0\<close> \<open>B > 0\<close>  by (simp add: \<delta>_def divide_simps)
    have "y \<in> f ` A" if "dist y (f x) * (B * real DIM('b)) < e" for y
    proof -
      define u where "u \<equiv> y - f x"
      show ?thesis
      proof (rule image_eqI)
        show "y = f (x + (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R inv f i))"
          apply (simp add: linear_add linear_sum linear.scaleR \<open>linear f\<close> surj_f_inv_f \<open>surj f\<close>)
          apply (simp add: euclidean_representation u_def)
          done
        have "dist (x + (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R inv f i)) x \<le> (\<Sum>i\<in>Basis. norm ((u \<bullet> i) *\<^sub>R inv f i))"
          by (simp add: dist_norm sum_norm_le)
        also have "... = (\<Sum>i\<in>Basis. \<bar>u \<bullet> i\<bar> * norm (inv f i))"
          by simp
        also have "... \<le> (\<Sum>i\<in>Basis. \<bar>u \<bullet> i\<bar>) * B"
          by (simp add: B sum_distrib_right sum_mono mult_left_mono)
        also have "... \<le> DIM('b) * dist y (f x) * B"
          apply (rule mult_right_mono [OF sum_bounded_above])
          using \<open>0 < B\<close> by (auto simp: Basis_le_norm dist_norm u_def)
        also have "... < e"
          by (metis mult.commute mult.left_commute that)
        finally show "x + (\<Sum>i\<in>Basis. (u \<bullet> i) *\<^sub>R inv f i) \<in> A"
          by (rule e)
      qed
    qed
    then show "\<forall>y. dist y (f x) < \<delta> \<longrightarrow> y \<in> f ` A"
      using \<open>e > 0\<close> \<open>B > 0\<close>
      by (auto simp: \<delta>_def divide_simps mult_less_0_iff)
  qed
qed

corollary open_bijective_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
    shows "open(f ` A) \<longleftrightarrow> open A"
proof
  assume "open(f ` A)"
  then have "open(f -` (f ` A))"
    using assms by (force simp: linear_continuous_at linear_conv_bounded_linear continuous_open_vimage)
  then show "open A"
    by (simp add: assms bij_is_inj inj_vimage_image_eq)
next
  assume "open A"
  then show "open(f ` A)"
    by (simp add: assms bij_is_surj open_surjective_linear_image)
qed

corollary interior_bijective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "bij f"
  shows "interior (f ` S) = f ` interior S"  (is "?lhs = ?rhs")
proof safe
  fix x
  assume x: "x \<in> ?lhs"
  then obtain T where "open T" and "x \<in> T" and "T \<subseteq> f ` S"
    by (metis interiorE)
  then show "x \<in> ?rhs"
    by (metis (no_types, hide_lams) assms subsetD interior_maximal open_bijective_linear_image_eq subset_image_iff)
next
  fix x
  assume x: "x \<in> interior S"
  then show "f x \<in> interior (f ` S)"
    by (meson assms imageI image_mono interiorI interior_subset open_bijective_linear_image_eq open_interior)
qed

lemma interior_injective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "inj f"
   shows "interior(f ` S) = f ` (interior S)"
  by (simp add: linear_injective_imp_surjective assms bijI interior_bijective_linear_image)

lemma interior_surjective_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a::euclidean_space"
  assumes "linear f" "surj f"
   shows "interior(f ` S) = f ` (interior S)"
  by (simp add: assms interior_injective_linear_image linear_surjective_imp_injective)

lemma interior_negations:
  fixes S :: "'a::euclidean_space set"
  shows "interior(uminus ` S) = image uminus (interior S)"
  by (simp add: bij_uminus interior_bijective_linear_image linear_uminus)

text \<open>Also bilinear functions, in composition form.\<close>

lemma bilinear_continuous_at_compose:
  "continuous (at x) f \<Longrightarrow> continuous (at x) g \<Longrightarrow> bounded_bilinear h \<Longrightarrow>
    continuous (at x) (\<lambda>x. h (f x) (g x))"
  unfolding continuous_at
  using Lim_bilinear[of f "f x" "(at x)" g "g x" h]
  by auto

lemma bilinear_continuous_within_compose:
  "continuous (at x within s) f \<Longrightarrow> continuous (at x within s) g \<Longrightarrow> bounded_bilinear h \<Longrightarrow>
    continuous (at x within s) (\<lambda>x. h (f x) (g x))"
  by (rule Limits.bounded_bilinear.continuous)

lemma bilinear_continuous_on_compose:
  "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> bounded_bilinear h \<Longrightarrow>
    continuous_on s (\<lambda>x. h (f x) (g x))"
  by (rule Limits.bounded_bilinear.continuous_on)

text \<open>Preservation of compactness and connectedness under continuous function.\<close>

lemma compact_eq_openin_cover:
  "compact S \<longleftrightarrow>
    (\<forall>C. (\<forall>c\<in>C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"
proof safe
  fix C
  assume "compact S" and "\<forall>c\<in>C. openin (subtopology euclidean S) c" and "S \<subseteq> \<Union>C"
  then have "\<forall>c\<in>{T. open T \<and> S \<inter> T \<in> C}. open c" and "S \<subseteq> \<Union>{T. open T \<and> S \<inter> T \<in> C}"
    unfolding openin_open by force+
  with \<open>compact S\<close> obtain D where "D \<subseteq> {T. open T \<and> S \<inter> T \<in> C}" and "finite D" and "S \<subseteq> \<Union>D"
    by (meson compactE)
  then have "image (\<lambda>T. S \<inter> T) D \<subseteq> C \<and> finite (image (\<lambda>T. S \<inter> T) D) \<and> S \<subseteq> \<Union>(image (\<lambda>T. S \<inter> T) D)"
    by auto
  then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
next
  assume 1: "\<forall>C. (\<forall>c\<in>C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
        (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D)"
  show "compact S"
  proof (rule compactI)
    fix C
    let ?C = "image (\<lambda>T. S \<inter> T) C"
    assume "\<forall>t\<in>C. open t" and "S \<subseteq> \<Union>C"
    then have "(\<forall>c\<in>?C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>?C"
      unfolding openin_open by auto
    with 1 obtain D where "D \<subseteq> ?C" and "finite D" and "S \<subseteq> \<Union>D"
      by metis
    let ?D = "inv_into C (\<lambda>T. S \<inter> T) ` D"
    have "?D \<subseteq> C \<and> finite ?D \<and> S \<subseteq> \<Union>?D"
    proof (intro conjI)
      from \<open>D \<subseteq> ?C\<close> show "?D \<subseteq> C"
        by (fast intro: inv_into_into)
      from \<open>finite D\<close> show "finite ?D"
        by (rule finite_imageI)
      from \<open>S \<subseteq> \<Union>D\<close> show "S \<subseteq> \<Union>?D"
        apply (rule subset_trans, clarsimp)
        apply (frule subsetD [OF \<open>D \<subseteq> ?C\<close>, THEN f_inv_into_f])
        apply (erule rev_bexI, fast)
        done
    qed
    then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
  qed
qed

lemma connected_continuous_image:
  assumes "continuous_on s f"
    and "connected s"
  shows "connected(f ` s)"
proof -
  {
    fix T
    assume as:
      "T \<noteq> {}"
      "T \<noteq> f ` s"
      "openin (subtopology euclidean (f ` s)) T"
      "closedin (subtopology euclidean (f ` s)) T"
    have "{x \<in> s. f x \<in> T} = {} \<or> {x \<in> s. f x \<in> T} = s"
      using assms(1)[unfolded continuous_on_open, THEN spec[where x=T]]
      using assms(1)[unfolded continuous_on_closed, THEN spec[where x=T]]
      using assms(2)[unfolded connected_clopen, THEN spec[where x="{x \<in> s. f x \<in> T}"]] as(3,4) by auto
    then have False using as(1,2)
      using as(4)[unfolded closedin_def topspace_euclidean_subtopology] by auto
  }
  then show ?thesis
    unfolding connected_clopen by auto
qed

lemma connected_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "linear f" and "connected s"
  shows "connected (f ` s)"
using connected_continuous_image assms linear_continuous_on linear_conv_bounded_linear by blast

text \<open>Continuity implies uniform continuity on a compact domain.\<close>

subsection \<open>Continuity implies uniform continuity on a compact domain.\<close>

text\<open>From the proof of the Heine-Borel theorem: Lemma 2 in section 3.7, page 69 of
J. C. Burkill and H. Burkill. A Second Course in Mathematical Analysis (CUP, 2002)\<close>

lemma Heine_Borel_lemma:
  assumes "compact S" and Ssub: "S \<subseteq> \<Union>\<G>" and op: "\<And>G. G \<in> \<G> \<Longrightarrow> open G"
  obtains e where "0 < e" "\<And>x. x \<in> S \<Longrightarrow> \<exists>G \<in> \<G>. ball x e \<subseteq> G"
proof -
  have False if neg: "\<And>e. 0 < e \<Longrightarrow> \<exists>x \<in> S. \<forall>G \<in> \<G>. \<not> ball x e \<subseteq> G"
  proof -
    have "\<exists>x \<in> S. \<forall>G \<in> \<G>. \<not> ball x (1 / Suc n) \<subseteq> G" for n
      using neg by simp
    then obtain f where "\<And>n. f n \<in> S" and fG: "\<And>G n. G \<in> \<G> \<Longrightarrow> \<not> ball (f n) (1 / Suc n) \<subseteq> G"
      by metis
    then obtain l r where "l \<in> S" "strict_mono r" and to_l: "(f \<circ> r) \<longlonglongrightarrow> l"
      using \<open>compact S\<close> compact_def that by metis
    then obtain G where "l \<in> G" "G \<in> \<G>"
      using Ssub by auto
    then obtain e where "0 < e" and e: "\<And>z. dist z l < e \<Longrightarrow> z \<in> G"
      using op open_dist by blast
    obtain N1 where N1: "\<And>n. n \<ge> N1 \<Longrightarrow> dist (f (r n)) l < e/2"
      using to_l apply (simp add: lim_sequentially)
      using \<open>0 < e\<close> half_gt_zero that by blast
    obtain N2 where N2: "of_nat N2 > 2/e"
      using reals_Archimedean2 by blast
    obtain x where "x \<in> ball (f (r (max N1 N2))) (1 / real (Suc (r (max N1 N2))))" and "x \<notin> G"
      using fG [OF \<open>G \<in> \<G>\<close>, of "r (max N1 N2)"] by blast
    then have "dist (f (r (max N1 N2))) x < 1 / real (Suc (r (max N1 N2)))"
      by simp
    also have "... \<le> 1 / real (Suc (max N1 N2))"
      apply (simp add: divide_simps del: max.bounded_iff)
      using \<open>strict_mono r\<close> seq_suble by blast
    also have "... \<le> 1 / real (Suc N2)"
      by (simp add: field_simps)
    also have "... < e/2"
      using N2 \<open>0 < e\<close> by (simp add: field_simps)
    finally have "dist (f (r (max N1 N2))) x < e / 2" .
    moreover have "dist (f (r (max N1 N2))) l < e/2"
      using N1 max.cobounded1 by blast
    ultimately have "dist x l < e"
      using dist_triangle_half_r by blast
    then show ?thesis
      using e \<open>x \<notin> G\<close> by blast
  qed
  then show ?thesis
    by (meson that)
qed

lemma compact_uniformly_equicontinuous:
  assumes "compact S"
      and cont: "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk>
                        \<Longrightarrow> \<exists>d. 0 < d \<and>
                                (\<forall>f \<in> \<F>. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
      and "0 < e"
  obtains d where "0 < d"
                  "\<And>f x x'. \<lbrakk>f \<in> \<F>; x \<in> S; x' \<in> S; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
proof -
  obtain d where d_pos: "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk> \<Longrightarrow> 0 < d x e"
     and d_dist : "\<And>x x' e f. \<lbrakk>dist x' x < d x e; x \<in> S; x' \<in> S; 0 < e; f \<in> \<F>\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
    using cont by metis
  let ?\<G> = "((\<lambda>x. ball x (d x (e / 2))) ` S)"
  have Ssub: "S \<subseteq> \<Union> ?\<G>"
    by clarsimp (metis d_pos \<open>0 < e\<close> dist_self half_gt_zero_iff)
  then obtain k where "0 < k" and k: "\<And>x. x \<in> S \<Longrightarrow> \<exists>G \<in> ?\<G>. ball x k \<subseteq> G"
    by (rule Heine_Borel_lemma [OF \<open>compact S\<close>]) auto
  moreover have "dist (f v) (f u) < e" if "f \<in> \<F>" "u \<in> S" "v \<in> S" "dist v u < k" for f u v
  proof -
    obtain G where "G \<in> ?\<G>" "u \<in> G" "v \<in> G"
      using k that
      by (metis \<open>dist v u < k\<close> \<open>u \<in> S\<close> \<open>0 < k\<close> centre_in_ball subsetD dist_commute mem_ball)
    then obtain w where w: "dist w u < d w (e / 2)" "dist w v < d w (e / 2)" "w \<in> S"
      by auto
    with that d_dist have "dist (f w) (f v) < e/2"
      by (metis \<open>0 < e\<close> dist_commute half_gt_zero)
    moreover
    have "dist (f w) (f u) < e/2"
      using that d_dist w by (metis \<open>0 < e\<close> dist_commute divide_pos_pos zero_less_numeral)
    ultimately show ?thesis
      using dist_triangle_half_r by blast
  qed
  ultimately show ?thesis using that by blast
qed

corollary compact_uniformly_continuous:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: metric_space"
  assumes f: "continuous_on S f" and S: "compact S"
  shows "uniformly_continuous_on S f"
  using f
    unfolding continuous_on_iff uniformly_continuous_on_def
    by (force intro: compact_uniformly_equicontinuous [OF S, of "{f}"])

subsection \<open>Topological stuff about the set of Reals\<close>

lemma open_real:
  fixes s :: "real set"
  shows "open s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>e>0. \<forall>x'. \<bar>x' - x\<bar> < e --> x' \<in> s)"
  unfolding open_dist dist_norm by simp

lemma islimpt_approachable_real:
  fixes s :: "real set"
  shows "x islimpt s \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> s. x' \<noteq> x \<and> \<bar>x' - x\<bar> < e)"
  unfolding islimpt_approachable dist_norm by simp

lemma closed_real:
  fixes s :: "real set"
  shows "closed s \<longleftrightarrow> (\<forall>x. (\<forall>e>0.  \<exists>x' \<in> s. x' \<noteq> x \<and> \<bar>x' - x\<bar> < e) \<longrightarrow> x \<in> s)"
  unfolding closed_limpt islimpt_approachable dist_norm by simp

lemma continuous_at_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'. norm(x' - x) < d --> \<bar>f x' - f x\<bar> < e)"
  unfolding continuous_at
  unfolding Lim_at
  unfolding dist_norm
  apply auto
  apply (erule_tac x=e in allE, auto)
  apply (rule_tac x=d in exI, auto)
  apply (erule_tac x=x' in allE, auto)
  apply (erule_tac x=e in allE, auto)
  done

lemma continuous_on_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous_on s f \<longleftrightarrow>
    (\<forall>x \<in> s. \<forall>e>0. \<exists>d>0. (\<forall>x' \<in> s. norm(x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e))"
  unfolding continuous_on_iff dist_norm by simp

text \<open>Hence some handy theorems on distance, diameter etc. of/from a set.\<close>

lemma distance_attains_sup:
  assumes "compact s" "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<forall>y\<in>s. dist a y \<le> dist a x"
proof (rule continuous_attains_sup [OF assms])
  {
    fix x
    assume "x\<in>s"
    have "(dist a \<longlongrightarrow> dist a x) (at x within s)"
      by (intro tendsto_dist tendsto_const tendsto_ident_at)
  }
  then show "continuous_on s (dist a)"
    unfolding continuous_on ..
qed

text \<open>For \emph{minimal} distance, we only need closure, not compactness.\<close>

lemma distance_attains_inf:
  fixes a :: "'a::heine_borel"
  assumes "closed s" and "s \<noteq> {}"
  obtains x where "x\<in>s" "\<And>y. y \<in> s \<Longrightarrow> dist a x \<le> dist a y"
proof -
  from assms obtain b where "b \<in> s" by auto
  let ?B = "s \<inter> cball a (dist b a)"
  have "?B \<noteq> {}" using \<open>b \<in> s\<close>
    by (auto simp: dist_commute)
  moreover have "continuous_on ?B (dist a)"
    by (auto intro!: continuous_at_imp_continuous_on continuous_dist continuous_ident continuous_const)
  moreover have "compact ?B"
    by (intro closed_Int_compact \<open>closed s\<close> compact_cball)
  ultimately obtain x where "x \<in> ?B" "\<forall>y\<in>?B. dist a x \<le> dist a y"
    by (metis continuous_attains_inf)
  with that show ?thesis by fastforce
qed


subsection \<open>Cartesian products\<close>

lemma bounded_Times:
  assumes "bounded s" "bounded t"
  shows "bounded (s \<times> t)"
proof -
  obtain x y a b where "\<forall>z\<in>s. dist x z \<le> a" "\<forall>z\<in>t. dist y z \<le> b"
    using assms [unfolded bounded_def] by auto
  then have "\<forall>z\<in>s \<times> t. dist (x, y) z \<le> sqrt (a\<^sup>2 + b\<^sup>2)"
    by (auto simp: dist_Pair_Pair real_sqrt_le_mono add_mono power_mono)
  then show ?thesis unfolding bounded_any_center [where a="(x, y)"] by auto
qed

lemma mem_Times_iff: "x \<in> A \<times> B \<longleftrightarrow> fst x \<in> A \<and> snd x \<in> B"
  by (induct x) simp

lemma seq_compact_Times: "seq_compact s \<Longrightarrow> seq_compact t \<Longrightarrow> seq_compact (s \<times> t)"
  unfolding seq_compact_def
  apply clarify
  apply (drule_tac x="fst \<circ> f" in spec)
  apply (drule mp, simp add: mem_Times_iff)
  apply (clarify, rename_tac l1 r1)
  apply (drule_tac x="snd \<circ> f \<circ> r1" in spec)
  apply (drule mp, simp add: mem_Times_iff)
  apply (clarify, rename_tac l2 r2)
  apply (rule_tac x="(l1, l2)" in rev_bexI, simp)
  apply (rule_tac x="r1 \<circ> r2" in exI)
  apply (rule conjI, simp add: strict_mono_def)
  apply (drule_tac f=r2 in LIMSEQ_subseq_LIMSEQ, assumption)
  apply (drule (1) tendsto_Pair) back
  apply (simp add: o_def)
  done

lemma compact_Times:
  assumes "compact s" "compact t"
  shows "compact (s \<times> t)"
proof (rule compactI)
  fix C
  assume C: "\<forall>t\<in>C. open t" "s \<times> t \<subseteq> \<Union>C"
  have "\<forall>x\<in>s. \<exists>a. open a \<and> x \<in> a \<and> (\<exists>d\<subseteq>C. finite d \<and> a \<times> t \<subseteq> \<Union>d)"
  proof
    fix x
    assume "x \<in> s"
    have "\<forall>y\<in>t. \<exists>a b c. c \<in> C \<and> open a \<and> open b \<and> x \<in> a \<and> y \<in> b \<and> a \<times> b \<subseteq> c" (is "\<forall>y\<in>t. ?P y")
    proof
      fix y
      assume "y \<in> t"
      with \<open>x \<in> s\<close> C obtain c where "c \<in> C" "(x, y) \<in> c" "open c" by auto
      then show "?P y" by (auto elim!: open_prod_elim)
    qed
    then obtain a b c where b: "\<And>y. y \<in> t \<Longrightarrow> open (b y)"
      and c: "\<And>y. y \<in> t \<Longrightarrow> c y \<in> C \<and> open (a y) \<and> open (b y) \<and> x \<in> a y \<and> y \<in> b y \<and> a y \<times> b y \<subseteq> c y"
      by metis
    then have "\<forall>y\<in>t. open (b y)" "t \<subseteq> (\<Union>y\<in>t. b y)" by auto
    with compactE_image[OF \<open>compact t\<close>] obtain D where D: "D \<subseteq> t" "finite D" "t \<subseteq> (\<Union>y\<in>D. b y)"
      by metis
    moreover from D c have "(\<Inter>y\<in>D. a y) \<times> t \<subseteq> (\<Union>y\<in>D. c y)"
      by (fastforce simp: subset_eq)
    ultimately show "\<exists>a. open a \<and> x \<in> a \<and> (\<exists>d\<subseteq>C. finite d \<and> a \<times> t \<subseteq> \<Union>d)"
      using c by (intro exI[of _ "c`D"] exI[of _ "\<Inter>(a`D)"] conjI) (auto intro!: open_INT)
  qed
  then obtain a d where a: "\<And>x. x\<in>s \<Longrightarrow> open (a x)" "s \<subseteq> (\<Union>x\<in>s. a x)"
    and d: "\<And>x. x \<in> s \<Longrightarrow> d x \<subseteq> C \<and> finite (d x) \<and> a x \<times> t \<subseteq> \<Union>d x"
    unfolding subset_eq UN_iff by metis
  moreover
  from compactE_image[OF \<open>compact s\<close> a]
  obtain e where e: "e \<subseteq> s" "finite e" and s: "s \<subseteq> (\<Union>x\<in>e. a x)"
    by auto
  moreover
  {
    from s have "s \<times> t \<subseteq> (\<Union>x\<in>e. a x \<times> t)"
      by auto
    also have "\<dots> \<subseteq> (\<Union>x\<in>e. \<Union>d x)"
      using d \<open>e \<subseteq> s\<close> by (intro UN_mono) auto
    finally have "s \<times> t \<subseteq> (\<Union>x\<in>e. \<Union>d x)" .
  }
  ultimately show "\<exists>C'\<subseteq>C. finite C' \<and> s \<times> t \<subseteq> \<Union>C'"
    by (intro exI[of _ "(\<Union>x\<in>e. d x)"]) (auto simp: subset_eq)
qed

text\<open>Hence some useful properties follow quite easily.\<close>

lemma compact_scaling:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  let ?f = "\<lambda>x. scaleR c x"
  have *: "bounded_linear ?f" by (rule bounded_linear_scaleR_right)
  show ?thesis
    using compact_continuous_image[of s ?f] continuous_at_imp_continuous_on[of s ?f]
    using linear_continuous_at[OF *] assms
    by auto
qed

lemma compact_negations:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. - x) ` s)"
  using compact_scaling [OF assms, of "- 1"] by auto

lemma compact_sums:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"
    and "compact t"
  shows "compact {x + y | x y. x \<in> s \<and> y \<in> t}"
proof -
  have *: "{x + y | x y. x \<in> s \<and> y \<in> t} = (\<lambda>z. fst z + snd z) ` (s \<times> t)"
    apply auto
    unfolding image_iff
    apply (rule_tac x="(xa, y)" in bexI)
    apply auto
    done
  have "continuous_on (s \<times> t) (\<lambda>z. fst z + snd z)"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  then show ?thesis
    unfolding * using compact_continuous_image compact_Times [OF assms] by auto
qed

lemma compact_differences:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"
    and "compact t"
  shows "compact {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x - y | x y. x\<in>s \<and> y \<in> t} =  {x + y | x y. x \<in> s \<and> y \<in> (uminus ` t)}"
    apply auto
    apply (rule_tac x= xa in exI, auto)
    done
  then show ?thesis
    using compact_sums[OF assms(1) compact_negations[OF assms(2)]] by auto
qed

lemma compact_translation:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. a + x) ` s)"
proof -
  have "{x + y |x y. x \<in> s \<and> y \<in> {a}} = (\<lambda>x. a + x) ` s"
    by auto
  then show ?thesis
    using compact_sums[OF assms compact_sing[of a]] by auto
qed

lemma compact_affinity:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have "op + a ` op *\<^sub>R c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s"
    by auto
  then show ?thesis
    using compact_translation[OF compact_scaling[OF assms], of a c] by auto
qed

text \<open>Hence we get the following.\<close>

lemma compact_sup_maxdistance:
  fixes s :: "'a::metric_space set"
  assumes "compact s"
    and "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. \<forall>u\<in>s. \<forall>v\<in>s. dist u v \<le> dist x y"
proof -
  have "compact (s \<times> s)"
    using \<open>compact s\<close> by (intro compact_Times)
  moreover have "s \<times> s \<noteq> {}"
    using \<open>s \<noteq> {}\<close> by auto
  moreover have "continuous_on (s \<times> s) (\<lambda>x. dist (fst x) (snd x))"
    by (intro continuous_at_imp_continuous_on ballI continuous_intros)
  ultimately show ?thesis
    using continuous_attains_sup[of "s \<times> s" "\<lambda>x. dist (fst x) (snd x)"] by auto
qed

subsection \<open>The diameter of a set.\<close>

definition diameter :: "'a::metric_space set \<Rightarrow> real" where
  "diameter S = (if S = {} then 0 else SUP (x,y):S\<times>S. dist x y)"

lemma diameter_empty [simp]: "diameter{} = 0"
  by (auto simp: diameter_def)

lemma diameter_singleton [simp]: "diameter{x} = 0"
  by (auto simp: diameter_def)

lemma diameter_le:
  assumes "S \<noteq> {} \<or> 0 \<le> d"
      and no: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> norm(x - y) \<le> d"
    shows "diameter S \<le> d"
using assms
  by (auto simp: dist_norm diameter_def intro: cSUP_least)

lemma diameter_bounded_bound:
  fixes s :: "'a :: metric_space set"
  assumes s: "bounded s" "x \<in> s" "y \<in> s"
  shows "dist x y \<le> diameter s"
proof -
  from s obtain z d where z: "\<And>x. x \<in> s \<Longrightarrow> dist z x \<le> d"
    unfolding bounded_def by auto
  have "bdd_above (case_prod dist ` (s\<times>s))"
  proof (intro bdd_aboveI, safe)
    fix a b
    assume "a \<in> s" "b \<in> s"
    with z[of a] z[of b] dist_triangle[of a b z]
    show "dist a b \<le> 2 * d"
      by (simp add: dist_commute)
  qed
  moreover have "(x,y) \<in> s\<times>s" using s by auto
  ultimately have "dist x y \<le> (SUP (x,y):s\<times>s. dist x y)"
    by (rule cSUP_upper2) simp
  with \<open>x \<in> s\<close> show ?thesis
    by (auto simp: diameter_def)
qed

lemma diameter_lower_bounded:
  fixes s :: "'a :: metric_space set"
  assumes s: "bounded s"
    and d: "0 < d" "d < diameter s"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. d < dist x y"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  moreover have "s \<noteq> {}"
    using d by (auto simp: diameter_def)
  ultimately have "diameter s \<le> d"
    by (auto simp: not_less diameter_def intro!: cSUP_least)
  with \<open>d < diameter s\<close> show False by auto
qed

lemma diameter_bounded:
  assumes "bounded s"
  shows "\<forall>x\<in>s. \<forall>y\<in>s. dist x y \<le> diameter s"
    and "\<forall>d>0. d < diameter s \<longrightarrow> (\<exists>x\<in>s. \<exists>y\<in>s. dist x y > d)"
  using diameter_bounded_bound[of s] diameter_lower_bounded[of s] assms
  by auto

lemma diameter_compact_attained:
  assumes "compact s"
    and "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. dist x y = diameter s"
proof -
  have b: "bounded s" using assms(1)
    by (rule compact_imp_bounded)
  then obtain x y where xys: "x\<in>s" "y\<in>s"
    and xy: "\<forall>u\<in>s. \<forall>v\<in>s. dist u v \<le> dist x y"
    using compact_sup_maxdistance[OF assms] by auto
  then have "diameter s \<le> dist x y"
    unfolding diameter_def
    apply clarsimp
    apply (rule cSUP_least, fast+)
    done
  then show ?thesis
    by (metis b diameter_bounded_bound order_antisym xys)
qed

lemma diameter_ge_0:
  assumes "bounded S"  shows "0 \<le> diameter S"
  by (metis all_not_in_conv assms diameter_bounded_bound diameter_empty dist_self order_refl)

lemma diameter_subset:
  assumes "S \<subseteq> T" "bounded T"
  shows "diameter S \<le> diameter T"
proof (cases "S = {} \<or> T = {}")
  case True
  with assms show ?thesis
    by (force simp: diameter_ge_0)
next
  case False
  then have "bdd_above ((\<lambda>x. case x of (x, xa) \<Rightarrow> dist x xa) ` (T \<times> T))"
    using \<open>bounded T\<close> diameter_bounded_bound by (force simp: bdd_above_def)
  with False \<open>S \<subseteq> T\<close> show ?thesis
    apply (simp add: diameter_def)
    apply (rule cSUP_subset_mono, auto)
    done
qed

lemma diameter_closure:
  assumes "bounded S"
  shows "diameter(closure S) = diameter S"
proof (rule order_antisym)
  have "False" if "diameter S < diameter (closure S)"
  proof -
    define d where "d = diameter(closure S) - diameter(S)"
    have "d > 0"
      using that by (simp add: d_def)
    then have "diameter(closure(S)) - d / 2 < diameter(closure(S))"
      by simp
    have dd: "diameter (closure S) - d / 2 = (diameter(closure(S)) + diameter(S)) / 2"
      by (simp add: d_def divide_simps)
     have bocl: "bounded (closure S)"
      using assms by blast
    moreover have "0 \<le> diameter S"
      using assms diameter_ge_0 by blast
    ultimately obtain x y where "x \<in> closure S" "y \<in> closure S" and xy: "diameter(closure(S)) - d / 2 < dist x y"
      using diameter_bounded(2) [OF bocl, rule_format, of "diameter(closure(S)) - d / 2"] \<open>d > 0\<close> d_def by auto
    then obtain x' y' where x'y': "x' \<in> S" "dist x' x < d/4" "y' \<in> S" "dist y' y < d/4"
      using closure_approachable
      by (metis \<open>0 < d\<close> zero_less_divide_iff zero_less_numeral)
    then have "dist x' y' \<le> diameter S"
      using assms diameter_bounded_bound by blast
    with x'y' have "dist x y \<le> d / 4 + diameter S + d / 4"
      by (meson add_mono_thms_linordered_semiring(1) dist_triangle dist_triangle3 less_eq_real_def order_trans)
    then show ?thesis
      using xy d_def by linarith
  qed
  then show "diameter (closure S) \<le> diameter S"
    by fastforce
  next
    show "diameter S \<le> diameter (closure S)"
      by (simp add: assms bounded_closure closure_subset diameter_subset)
qed

lemma diameter_cball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(cball a r) = (if r < 0 then 0 else 2*r)"
proof -
  have "diameter(cball a r) = 2*r" if "r \<ge> 0"
  proof (rule order_antisym)
    show "diameter (cball a r) \<le> 2*r"
    proof (rule diameter_le)
      fix x y assume "x \<in> cball a r" "y \<in> cball a r"
      then have "norm (x - a) \<le> r" "norm (a - y) \<le> r"
        by (auto simp: dist_norm norm_minus_commute)
      then have "norm (x - y) \<le> r+r"
        using norm_diff_triangle_le by blast
      then show "norm (x - y) \<le> 2*r" by simp
    qed (simp add: that)
    have "2*r = dist (a + r *\<^sub>R (SOME i. i \<in> Basis)) (a - r *\<^sub>R (SOME i. i \<in> Basis))"
      apply (simp add: dist_norm)
      by (metis abs_of_nonneg mult.right_neutral norm_numeral norm_scaleR norm_some_Basis real_norm_def scaleR_2 that)
    also have "... \<le> diameter (cball a r)"
      apply (rule diameter_bounded_bound)
      using that by (auto simp: dist_norm)
    finally show "2*r \<le> diameter (cball a r)" .
  qed
  then show ?thesis by simp
qed

lemma diameter_ball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(ball a r) = (if r < 0 then 0 else 2*r)"
proof -
  have "diameter(ball a r) = 2*r" if "r > 0"
    by (metis bounded_ball diameter_closure closure_ball diameter_cball less_eq_real_def linorder_not_less that)
  then show ?thesis
    by (simp add: diameter_def)
qed

lemma diameter_closed_interval [simp]: "diameter {a..b} = (if b < a then 0 else b-a)"
proof -
  have "{a .. b} = cball ((a+b)/2) ((b-a)/2)"
    by (auto simp: dist_norm abs_if divide_simps split: if_split_asm)
  then show ?thesis
    by simp
qed

lemma diameter_open_interval [simp]: "diameter {a<..<b} = (if b < a then 0 else b-a)"
proof -
  have "{a <..< b} = ball ((a+b)/2) ((b-a)/2)"
    by (auto simp: dist_norm abs_if divide_simps split: if_split_asm)
  then show ?thesis
    by simp
qed

proposition Lebesgue_number_lemma:
  assumes "compact S" "\<C> \<noteq> {}" "S \<subseteq> \<Union>\<C>" and ope: "\<And>B. B \<in> \<C> \<Longrightarrow> open B"
  obtains \<delta> where "0 < \<delta>" "\<And>T. \<lbrakk>T \<subseteq> S; diameter T < \<delta>\<rbrakk> \<Longrightarrow> \<exists>B \<in> \<C>. T \<subseteq> B"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (metis \<open>\<C> \<noteq> {}\<close> zero_less_one empty_subsetI equals0I subset_trans that)
next
  case False
  { fix x assume "x \<in> S"
    then obtain C where C: "x \<in> C" "C \<in> \<C>"
      using \<open>S \<subseteq> \<Union>\<C>\<close> by blast
    then obtain r where r: "r>0" "ball x (2*r) \<subseteq> C"
      by (metis mult.commute mult_2_right not_le ope openE real_sum_of_halves zero_le_numeral zero_less_mult_iff)
    then have "\<exists>r C. r > 0 \<and> ball x (2*r) \<subseteq> C \<and> C \<in> \<C>"
      using C by blast
  }
  then obtain r where r: "\<And>x. x \<in> S \<Longrightarrow> r x > 0 \<and> (\<exists>C \<in> \<C>. ball x (2*r x) \<subseteq> C)"
    by metis
  then have "S \<subseteq> (\<Union>x \<in> S. ball x (r x))"
    by auto
  then obtain \<T> where "finite \<T>" "S \<subseteq> \<Union>\<T>" and \<T>: "\<T> \<subseteq> (\<lambda>x. ball x (r x)) ` S"
    by (rule compactE [OF \<open>compact S\<close>]) auto
  then obtain S0 where "S0 \<subseteq> S" "finite S0" and S0: "\<T> = (\<lambda>x. ball x (r x)) ` S0"
    by (meson finite_subset_image)
  then have "S0 \<noteq> {}"
    using False \<open>S \<subseteq> \<Union>\<T>\<close> by auto
  define \<delta> where "\<delta> = Inf (r ` S0)"
  have "\<delta> > 0"
    using \<open>finite S0\<close> \<open>S0 \<subseteq> S\<close> \<open>S0 \<noteq> {}\<close> r by (auto simp: \<delta>_def finite_less_Inf_iff)
  show ?thesis
  proof
    show "0 < \<delta>"
      by (simp add: \<open>0 < \<delta>\<close>)
    show "\<exists>B \<in> \<C>. T \<subseteq> B" if "T \<subseteq> S" and dia: "diameter T < \<delta>" for T
    proof (cases "T = {}")
      case True
      then show ?thesis
        using \<open>\<C> \<noteq> {}\<close> by blast
    next
      case False
      then obtain y where "y \<in> T" by blast
      then have "y \<in> S"
        using \<open>T \<subseteq> S\<close> by auto
      then obtain x where "x \<in> S0" and x: "y \<in> ball x (r x)"
        using \<open>S \<subseteq> \<Union>\<T>\<close> S0 that by blast
      have "ball y \<delta> \<subseteq> ball y (r x)"
        by (metis \<delta>_def \<open>S0 \<noteq> {}\<close> \<open>finite S0\<close> \<open>x \<in> S0\<close> empty_is_image finite_imageI finite_less_Inf_iff imageI less_irrefl not_le subset_ball)
      also have "... \<subseteq> ball x (2*r x)"
        by clarsimp (metis dist_commute dist_triangle_less_add mem_ball mult_2 x)
      finally obtain C where "C \<in> \<C>" "ball y \<delta> \<subseteq> C"
        by (meson r \<open>S0 \<subseteq> S\<close> \<open>x \<in> S0\<close> dual_order.trans subsetCE)
      have "bounded T"
        using \<open>compact S\<close> bounded_subset compact_imp_bounded \<open>T \<subseteq> S\<close> by blast
      then have "T \<subseteq> ball y \<delta>"
        using \<open>y \<in> T\<close> dia diameter_bounded_bound by fastforce
      then show ?thesis
        apply (rule_tac x=C in bexI)
        using \<open>ball y \<delta> \<subseteq> C\<close> \<open>C \<in> \<C>\<close> by auto
    qed
  qed
qed


subsection \<open>Compact sets and the closure operation.\<close>

lemma closed_scaling:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closed ((\<lambda>x. c *\<^sub>R x) ` S)"
proof (cases "c = 0")
  case True then show ?thesis
    by (auto simp: image_constant_conv)
next
  case False
  from assms have "closed ((\<lambda>x. inverse c *\<^sub>R x) -` S)"
    by (simp add: continuous_closed_vimage)
  also have "(\<lambda>x. inverse c *\<^sub>R x) -` S = (\<lambda>x. c *\<^sub>R x) ` S"
    using \<open>c \<noteq> 0\<close> by (auto elim: image_eqI [rotated])
  finally show ?thesis .
qed

lemma closed_negations:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closed ((\<lambda>x. -x) ` S)"
  using closed_scaling[OF assms, of "- 1"] by simp

lemma compact_closed_sums:
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S" and "closed T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  let ?S = "{x + y |x y. x \<in> S \<and> y \<in> T}"
  {
    fix x l
    assume as: "\<forall>n. x n \<in> ?S"  "(x \<longlongrightarrow> l) sequentially"
    from as(1) obtain f where f: "\<forall>n. x n = fst (f n) + snd (f n)"  "\<forall>n. fst (f n) \<in> S"  "\<forall>n. snd (f n) \<in> T"
      using choice[of "\<lambda>n y. x n = (fst y) + (snd y) \<and> fst y \<in> S \<and> snd y \<in> T"] by auto
    obtain l' r where "l'\<in>S" and r: "strict_mono r" and lr: "(((\<lambda>n. fst (f n)) \<circ> r) \<longlongrightarrow> l') sequentially"
      using assms(1)[unfolded compact_def, THEN spec[where x="\<lambda> n. fst (f n)"]] using f(2) by auto
    have "((\<lambda>n. snd (f (r n))) \<longlongrightarrow> l - l') sequentially"
      using tendsto_diff[OF LIMSEQ_subseq_LIMSEQ[OF as(2) r] lr] and f(1)
      unfolding o_def
      by auto
    then have "l - l' \<in> T"
      using assms(2)[unfolded closed_sequential_limits,
        THEN spec[where x="\<lambda> n. snd (f (r n))"],
        THEN spec[where x="l - l'"]]
      using f(3)
      by auto
    then have "l \<in> ?S"
      using \<open>l' \<in> S\<close>
      apply auto
      apply (rule_tac x=l' in exI)
      apply (rule_tac x="l - l'" in exI, auto)
      done
  }
  moreover have "?S = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by force
  ultimately show ?thesis
    unfolding closed_sequential_limits
    by (metis (no_types, lifting))
qed

lemma closed_compact_sums:
  fixes S T :: "'a::real_normed_vector set"
  assumes "closed S" "compact T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  have "(\<Union>x\<in> T. \<Union>y \<in> S. {x + y}) = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by auto
  then show ?thesis
    using compact_closed_sums[OF assms(2,1)] by simp
qed

lemma compact_closed_differences:
  fixes S T :: "'a::real_normed_vector set"
  assumes "compact S" "closed T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> uminus ` T. {x + y}) = (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
    by force
  then show ?thesis
    using compact_closed_sums[OF assms(1) closed_negations[OF assms(2)]] by auto
qed

lemma closed_compact_differences:
  fixes S T :: "'a::real_normed_vector set"
  assumes "closed S" "compact T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> uminus ` T. {x + y}) = {x - y |x y. x \<in> S \<and> y \<in> T}"
    by auto
 then show ?thesis
  using closed_compact_sums[OF assms(1) compact_negations[OF assms(2)]] by simp
qed

lemma closed_translation:
  fixes a :: "'a::real_normed_vector"
  assumes "closed S"
  shows "closed ((\<lambda>x. a + x) ` S)"
proof -
  have "(\<Union>x\<in> {a}. \<Union>y \<in> S. {x + y}) = (op + a ` S)" by auto
  then show ?thesis
    using compact_closed_sums[OF compact_sing[of a] assms] by auto
qed

lemma translation_Compl:
  fixes a :: "'a::ab_group_add"
  shows "(\<lambda>x. a + x) ` (- t) = - ((\<lambda>x. a + x) ` t)"
  apply (auto simp: image_iff)
  apply (rule_tac x="x - a" in bexI, auto)
  done

lemma translation_UNIV:
  fixes a :: "'a::ab_group_add"
  shows "range (\<lambda>x. a + x) = UNIV"
  apply (auto simp: image_iff)
  apply (rule_tac x="x - a" in exI, auto)
  done

lemma translation_diff:
  fixes a :: "'a::ab_group_add"
  shows "(\<lambda>x. a + x) ` (s - t) = ((\<lambda>x. a + x) ` s) - ((\<lambda>x. a + x) ` t)"
  by auto

lemma translation_Int:
  fixes a :: "'a::ab_group_add"
  shows "(\<lambda>x. a + x) ` (s \<inter> t) = ((\<lambda>x. a + x) ` s) \<inter> ((\<lambda>x. a + x) ` t)"
  by auto

lemma closure_translation:
  fixes a :: "'a::real_normed_vector"
  shows "closure ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (closure s)"
proof -
  have *: "op + a ` (- s) = - op + a ` s"
    apply auto
    unfolding image_iff
    apply (rule_tac x="x - a" in bexI, auto)
    done
  show ?thesis
    unfolding closure_interior translation_Compl
    using interior_translation[of a "- s"]
    unfolding *
    by auto
qed

lemma frontier_translation:
  fixes a :: "'a::real_normed_vector"
  shows "frontier((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (frontier s)"
  unfolding frontier_def translation_diff interior_translation closure_translation
  by auto

lemma sphere_translation:
  fixes a :: "'n::euclidean_space"
  shows "sphere (a+c) r = op+a ` sphere c r"
apply safe
apply (rule_tac x="x-a" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma cball_translation:
  fixes a :: "'n::euclidean_space"
  shows "cball (a+c) r = op+a ` cball c r"
apply safe
apply (rule_tac x="x-a" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma ball_translation:
  fixes a :: "'n::euclidean_space"
  shows "ball (a+c) r = op+a ` ball c r"
apply safe
apply (rule_tac x="x-a" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done


subsection \<open>Separation between points and sets\<close>

lemma separate_point_closed:
  fixes s :: "'a::heine_borel set"
  assumes "closed s" and "a \<notin> s"
  shows "\<exists>d>0. \<forall>x\<in>s. d \<le> dist a x"
proof (cases "s = {}")
  case True
  then show ?thesis by(auto intro!: exI[where x=1])
next
  case False
  from assms obtain x where "x\<in>s" "\<forall>y\<in>s. dist a x \<le> dist a y"
    using \<open>s \<noteq> {}\<close> by (blast intro: distance_attains_inf [of s a])
  with \<open>x\<in>s\<close> show ?thesis using dist_pos_lt[of a x] and\<open>a \<notin> s\<close>
    by blast
qed

lemma separate_compact_closed:
  fixes s t :: "'a::heine_borel set"
  assumes "compact s"
    and t: "closed t" "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof cases
  assume "s \<noteq> {} \<and> t \<noteq> {}"
  then have "s \<noteq> {}" "t \<noteq> {}" by auto
  let ?inf = "\<lambda>x. infdist x t"
  have "continuous_on s ?inf"
    by (auto intro!: continuous_at_imp_continuous_on continuous_infdist continuous_ident)
  then obtain x where x: "x \<in> s" "\<forall>y\<in>s. ?inf x \<le> ?inf y"
    using continuous_attains_inf[OF \<open>compact s\<close> \<open>s \<noteq> {}\<close>] by auto
  then have "0 < ?inf x"
    using t \<open>t \<noteq> {}\<close> in_closed_iff_infdist_zero by (auto simp: less_le infdist_nonneg)
  moreover have "\<forall>x'\<in>s. \<forall>y\<in>t. ?inf x \<le> dist x' y"
    using x by (auto intro: order_trans infdist_le)
  ultimately show ?thesis by auto
qed (auto intro!: exI[of _ 1])

lemma separate_closed_compact:
  fixes s t :: "'a::heine_borel set"
  assumes "closed s"
    and "compact t"
    and "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof -
  have *: "t \<inter> s = {}"
    using assms(3) by auto
  show ?thesis
    using separate_compact_closed[OF assms(2,1) *]
    apply auto
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x=y in ballE)
    apply (auto simp: dist_commute)
    done
qed


subsection \<open>Closure of halfspaces and hyperplanes\<close>

lemma isCont_open_vimage:
  assumes "\<And>x. isCont f x"
    and "open s"
  shows "open (f -` s)"
proof -
  from assms(1) have "continuous_on UNIV f"
    unfolding isCont_def continuous_on_def by simp
  then have "open {x \<in> UNIV. f x \<in> s}"
    using open_UNIV \<open>open s\<close> by (rule continuous_open_preimage)
  then show "open (f -` s)"
    by (simp add: vimage_def)
qed

lemma isCont_closed_vimage:
  assumes "\<And>x. isCont f x"
    and "closed s"
  shows "closed (f -` s)"
  using assms unfolding closed_def vimage_Compl [symmetric]
  by (rule isCont_open_vimage)

lemma continuous_on_closed_Collect_le:
  fixes f g :: "'a::t2_space \<Rightarrow> real"
  assumes f: "continuous_on s f" and g: "continuous_on s g" and s: "closed s"
  shows "closed {x \<in> s. f x \<le> g x}"
proof -
  have "closed ((\<lambda>x. g x - f x) -` {0..} \<inter> s)"
    using closed_real_atLeast continuous_on_diff [OF g f]
    by (simp add: continuous_on_closed_vimage [OF s])
  also have "((\<lambda>x. g x - f x) -` {0..} \<inter> s) = {x\<in>s. f x \<le> g x}"
    by auto
  finally show ?thesis .
qed

lemma continuous_at_inner: "continuous (at x) (inner a)"
  unfolding continuous_at by (intro tendsto_intros)

lemma closed_halfspace_le: "closed {x. inner a x \<le> b}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_halfspace_ge: "closed {x. inner a x \<ge> b}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_hyperplane: "closed {x. inner a x = b}"
  by (simp add: closed_Collect_eq continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_halfspace_component_le: "closed {x::'a::euclidean_space. x\<bullet>i \<le> a}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_halfspace_component_ge: "closed {x::'a::euclidean_space. x\<bullet>i \<ge> a}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_interval_left:
  fixes b :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. x\<bullet>i \<le> b\<bullet>i}"
  by (simp add: Collect_ball_eq closed_INT closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_interval_right:
  fixes a :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. a\<bullet>i \<le> x\<bullet>i}"
  by (simp add: Collect_ball_eq closed_INT closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma continuous_le_on_closure:
  fixes a::real
  assumes f: "continuous_on (closure s) f"
      and x: "x \<in> closure(s)"
      and xlo: "\<And>x. x \<in> s ==> f(x) \<le> a"
    shows "f(x) \<le> a"
    using image_closure_subset [OF f]
  using image_closure_subset [OF f] closed_halfspace_le [of "1::real" a] assms
  by force

lemma continuous_ge_on_closure:
  fixes a::real
  assumes f: "continuous_on (closure s) f"
      and x: "x \<in> closure(s)"
      and xlo: "\<And>x. x \<in> s ==> f(x) \<ge> a"
    shows "f(x) \<ge> a"
  using image_closure_subset [OF f] closed_halfspace_ge [of a "1::real"] assms
  by force

text \<open>Openness of halfspaces.\<close>

lemma open_halfspace_lt: "open {x. inner a x < b}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

lemma open_halfspace_gt: "open {x. inner a x > b}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

lemma open_halfspace_component_lt: "open {x::'a::euclidean_space. x\<bullet>i < a}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

lemma open_halfspace_component_gt: "open {x::'a::euclidean_space. x\<bullet>i > a}"
  by (simp add: open_Collect_less continuous_on_inner continuous_on_const continuous_on_id)

text \<open>This gives a simple derivation of limit component bounds.\<close>

lemma Lim_component_le:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. f(x)\<bullet>i \<le> b) net"
  shows "l\<bullet>i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_inner[OF assms(1) tendsto_const] assms(3)])

lemma Lim_component_ge:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. b \<le> (f x)\<bullet>i) net"
  shows "b \<le> l\<bullet>i"
  by (rule tendsto_le[OF assms(2) tendsto_inner[OF assms(1) tendsto_const] tendsto_const assms(3)])

lemma Lim_component_eq:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes net: "(f \<longlongrightarrow> l) net" "\<not> trivial_limit net"
    and ev:"eventually (\<lambda>x. f(x)\<bullet>i = b) net"
  shows "l\<bullet>i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff]
  using Lim_component_ge[OF net, of b i]
  using Lim_component_le[OF net, of i b]
  by auto

text \<open>Limits relative to a union.\<close>

lemma eventually_within_Un:
  "eventually P (at x within (s \<union> t)) \<longleftrightarrow>
    eventually P (at x within s) \<and> eventually P (at x within t)"
  unfolding eventually_at_filter
  by (auto elim!: eventually_rev_mp)

lemma Lim_within_union:
 "(f \<longlongrightarrow> l) (at x within (s \<union> t)) \<longleftrightarrow>
  (f \<longlongrightarrow> l) (at x within s) \<and> (f \<longlongrightarrow> l) (at x within t)"
  unfolding tendsto_def
  by (auto simp: eventually_within_Un)

lemma Lim_topological:
  "(f \<longlongrightarrow> l) net \<longleftrightarrow>
    trivial_limit net \<or> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net)"
  unfolding tendsto_def trivial_limit_eq by auto

text \<open>Continuity relative to a union.\<close>

lemma continuous_on_Un_local:
    "\<lbrakk>closedin (subtopology euclidean (s \<union> t)) s; closedin (subtopology euclidean (s \<union> t)) t;
      continuous_on s f; continuous_on t f\<rbrakk>
     \<Longrightarrow> continuous_on (s \<union> t) f"
  unfolding continuous_on closedin_limpt
  by (metis Lim_trivial_limit Lim_within_union Un_iff trivial_limit_within)

lemma continuous_on_cases_local:
     "\<lbrakk>closedin (subtopology euclidean (s \<union> t)) s; closedin (subtopology euclidean (s \<union> t)) t;
       continuous_on s f; continuous_on t g;
       \<And>x. \<lbrakk>x \<in> s \<and> ~P x \<or> x \<in> t \<and> P x\<rbrakk> \<Longrightarrow> f x = g x\<rbrakk>
      \<Longrightarrow> continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)"
  by (rule continuous_on_Un_local) (auto intro: continuous_on_eq)

lemma continuous_on_cases_le:
  fixes h :: "'a :: topological_space \<Rightarrow> real"
  assumes "continuous_on {t \<in> s. h t \<le> a} f"
      and "continuous_on {t \<in> s. a \<le> h t} g"
      and h: "continuous_on s h"
      and "\<And>t. \<lbrakk>t \<in> s; h t = a\<rbrakk> \<Longrightarrow> f t = g t"
    shows "continuous_on s (\<lambda>t. if h t \<le> a then f(t) else g(t))"
proof -
  have s: "s = {t \<in> s. h t \<in> atMost a} \<union> {t \<in> s. h t \<in> atLeast a}"
    by force
  have 1: "closedin (subtopology euclidean s) {t \<in> s. h t \<in> atMost a}"
    by (rule continuous_closedin_preimage [OF h closed_atMost])
  have 2: "closedin (subtopology euclidean s) {t \<in> s. h t \<in> atLeast a}"
    by (rule continuous_closedin_preimage [OF h closed_atLeast])
  show ?thesis
    apply (rule continuous_on_subset [of s, OF _ order_refl])
    apply (subst s)
    apply (rule continuous_on_cases_local)
    using 1 2 s assms apply auto
    done
qed

lemma continuous_on_cases_1:
  fixes s :: "real set"
  assumes "continuous_on {t \<in> s. t \<le> a} f"
      and "continuous_on {t \<in> s. a \<le> t} g"
      and "a \<in> s \<Longrightarrow> f a = g a"
    shows "continuous_on s (\<lambda>t. if t \<le> a then f(t) else g(t))"
using assms
by (auto simp: continuous_on_id intro: continuous_on_cases_le [where h = id, simplified])

text\<open>Some more convenient intermediate-value theorem formulations.\<close>

lemma connected_ivt_hyperplane:
  assumes "connected s"
    and "x \<in> s"
    and "y \<in> s"
    and "inner a x \<le> b"
    and "b \<le> inner a y"
  shows "\<exists>z \<in> s. inner a z = b"
proof (rule ccontr)
  assume as:"\<not> (\<exists>z\<in>s. inner a z = b)"
  let ?A = "{x. inner a x < b}"
  let ?B = "{x. inner a x > b}"
  have "open ?A" "open ?B"
    using open_halfspace_lt and open_halfspace_gt by auto
  moreover
  have "?A \<inter> ?B = {}" by auto
  moreover
  have "s \<subseteq> ?A \<union> ?B" using as by auto
  ultimately
  show False
    using assms(1)[unfolded connected_def not_ex,
      THEN spec[where x="?A"], THEN spec[where x="?B"]]
    using assms(2-5)
    by auto
qed

lemma connected_ivt_component:
  fixes x::"'a::euclidean_space"
  shows "connected s \<Longrightarrow>
    x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow>
    x\<bullet>k \<le> a \<Longrightarrow> a \<le> y\<bullet>k \<Longrightarrow> (\<exists>z\<in>s.  z\<bullet>k = a)"
  using connected_ivt_hyperplane[of s x y "k::'a" a]
  by (auto simp: inner_commute)


subsection \<open>Intervals\<close>

lemma open_box[intro]: "open (box a b)"
proof -
  have "open (\<Inter>i\<in>Basis. (op \<bullet> i) -` {a \<bullet> i <..< b \<bullet> i})"
    by (auto intro!: continuous_open_vimage continuous_inner continuous_ident continuous_const)
  also have "(\<Inter>i\<in>Basis. (op \<bullet> i) -` {a \<bullet> i <..< b \<bullet> i}) = box a b"
    by (auto simp: box_def inner_commute)
  finally show ?thesis .
qed

instance euclidean_space \<subseteq> second_countable_topology
proof
  define a where "a f = (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have a: "\<And>f. (\<Sum>i\<in>Basis. fst (f i) *\<^sub>R i) = a f"
    by simp
  define b where "b f = (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i)" for f :: "'a \<Rightarrow> real \<times> real"
  then have b: "\<And>f. (\<Sum>i\<in>Basis. snd (f i) *\<^sub>R i) = b f"
    by simp
  define B where "B = (\<lambda>f. box (a f) (b f)) ` (Basis \<rightarrow>\<^sub>E (\<rat> \<times> \<rat>))"

  have "Ball B open" by (simp add: B_def open_box)
  moreover have "(\<forall>A. open A \<longrightarrow> (\<exists>B'\<subseteq>B. \<Union>B' = A))"
  proof safe
    fix A::"'a set"
    assume "open A"
    show "\<exists>B'\<subseteq>B. \<Union>B' = A"
      apply (rule exI[of _ "{b\<in>B. b \<subseteq> A}"])
      apply (subst (3) open_UNION_box[OF \<open>open A\<close>])
      apply (auto simp: a b B_def)
      done
  qed
  ultimately
  have "topological_basis B"
    unfolding topological_basis_def by blast
  moreover
  have "countable B"
    unfolding B_def
    by (intro countable_image countable_PiE finite_Basis countable_SIGMA countable_rat)
  ultimately show "\<exists>B::'a set set. countable B \<and> open = generate_topology B"
    by (blast intro: topological_basis_imp_subbasis)
qed

instance euclidean_space \<subseteq> polish_space ..

lemma closed_cbox[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "closed (cbox a b)"
proof -
  have "closed (\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i})"
    by (intro closed_INT ballI continuous_closed_vimage allI
      linear_continuous_at closed_real_atLeastAtMost finite_Basis bounded_linear_inner_left)
  also have "(\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i}) = cbox a b"
    by (auto simp: cbox_def)
  finally show "closed (cbox a b)" .
qed

lemma interior_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "interior (cbox a b) = box a b" (is "?L = ?R")
proof(rule subset_antisym)
  show "?R \<subseteq> ?L"
    using box_subset_cbox open_box
    by (rule interior_maximal)
  {
    fix x
    assume "x \<in> interior (cbox a b)"
    then obtain s where s: "open s" "x \<in> s" "s \<subseteq> cbox a b" ..
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> cbox a b"
      unfolding open_dist and subset_eq by auto
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "dist (x - (e / 2) *\<^sub>R i) x < e"
        and "dist (x + (e / 2) *\<^sub>R i) x < e"
        unfolding dist_norm
        apply auto
        unfolding norm_minus_cancel
        using norm_Basis[OF i] \<open>e>0\<close>
        apply auto
        done
      then have "a \<bullet> i \<le> (x - (e / 2) *\<^sub>R i) \<bullet> i" and "(x + (e / 2) *\<^sub>R i) \<bullet> i \<le> b \<bullet> i"
        using e[THEN spec[where x="x - (e/2) *\<^sub>R i"]]
          and e[THEN spec[where x="x + (e/2) *\<^sub>R i"]]
        unfolding mem_box
        using i
        by blast+
      then have "a \<bullet> i < x \<bullet> i" and "x \<bullet> i < b \<bullet> i"
        using \<open>e>0\<close> i
        by (auto simp: inner_diff_left inner_Basis inner_add_left)
    }
    then have "x \<in> box a b"
      unfolding mem_box by auto
  }
  then show "?L \<subseteq> ?R" ..
qed

lemma bounded_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (cbox a b)"
proof -
  let ?b = "\<Sum>i\<in>Basis. \<bar>a\<bullet>i\<bar> + \<bar>b\<bullet>i\<bar>"
  {
    fix x :: "'a"
    assume x: "\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
    {
      fix i :: 'a
      assume "i \<in> Basis"
      then have "\<bar>x\<bullet>i\<bar> \<le> \<bar>a\<bullet>i\<bar> + \<bar>b\<bullet>i\<bar>"
        using x[THEN bspec[where x=i]] by auto
    }
    then have "(\<Sum>i\<in>Basis. \<bar>x \<bullet> i\<bar>) \<le> ?b"
      apply -
      apply (rule sum_mono, auto)
      done
    then have "norm x \<le> ?b"
      using norm_le_l1[of x] by auto
  }
  then show ?thesis
    unfolding cbox_def bounded_iff by auto
qed

lemma bounded_box [simp]:
  fixes a :: "'a::euclidean_space"
  shows "bounded (box a b)"
  using bounded_cbox[of a b]
  using box_subset_cbox[of a b]
  using bounded_subset[of "cbox a b" "box a b"]
  by simp

lemma not_interval_UNIV [simp]:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> UNIV" "box a b \<noteq> UNIV"
  using bounded_box[of a b] bounded_cbox[of a b] by force+

lemma not_interval_UNIV2 [simp]:
  fixes a :: "'a::euclidean_space"
  shows "UNIV \<noteq> cbox a b" "UNIV \<noteq> box a b"
  using bounded_box[of a b] bounded_cbox[of a b] by force+

lemma compact_cbox [simp]:
  fixes a :: "'a::euclidean_space"
  shows "compact (cbox a b)"
  using bounded_closed_imp_seq_compact[of "cbox a b"] using bounded_cbox[of a b]
  by (auto simp: compact_eq_seq_compact_metric)

proposition is_interval_compact:
   "is_interval S \<and> compact S \<longleftrightarrow> (\<exists>a b. S = cbox a b)"   (is "?lhs = ?rhs")
proof (cases "S = {}")
  case True
  with empty_as_interval show ?thesis by auto
next
  case False
  show ?thesis
  proof
    assume L: ?lhs
    then have "is_interval S" "compact S" by auto
    define a where "a \<equiv> \<Sum>i\<in>Basis. (INF x:S. x \<bullet> i) *\<^sub>R i"
    define b where "b \<equiv> \<Sum>i\<in>Basis. (SUP x:S. x \<bullet> i) *\<^sub>R i"
    have 1: "\<And>x i. \<lbrakk>x \<in> S; i \<in> Basis\<rbrakk> \<Longrightarrow> (INF x:S. x \<bullet> i) \<le> x \<bullet> i"
      by (simp add: cInf_lower bounded_inner_imp_bdd_below compact_imp_bounded L)
    have 2: "\<And>x i. \<lbrakk>x \<in> S; i \<in> Basis\<rbrakk> \<Longrightarrow> x \<bullet> i \<le> (SUP x:S. x \<bullet> i)"
      by (simp add: cSup_upper bounded_inner_imp_bdd_above compact_imp_bounded L)
    have 3: "x \<in> S" if inf: "\<And>i. i \<in> Basis \<Longrightarrow> (INF x:S. x \<bullet> i) \<le> x \<bullet> i"
                   and sup: "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<le> (SUP x:S. x \<bullet> i)" for x
    proof (rule mem_box_componentwiseI [OF \<open>is_interval S\<close>])
      fix i::'a
      assume i: "i \<in> Basis"
      have cont: "continuous_on S (\<lambda>x. x \<bullet> i)"
        by (intro continuous_intros)
      obtain a where "a \<in> S" and a: "\<And>y. y\<in>S \<Longrightarrow> a \<bullet> i \<le> y \<bullet> i"
        using continuous_attains_inf [OF \<open>compact S\<close> False cont] by blast
      obtain b where "b \<in> S" and b: "\<And>y. y\<in>S \<Longrightarrow> y \<bullet> i \<le> b \<bullet> i"
        using continuous_attains_sup [OF \<open>compact S\<close> False cont] by blast
      have "a \<bullet> i \<le> (INF x:S. x \<bullet> i)"
        by (simp add: False a cINF_greatest)
      also have "\<dots> \<le> x \<bullet> i"
        by (simp add: i inf)
      finally have ai: "a \<bullet> i \<le> x \<bullet> i" .
      have "x \<bullet> i \<le> (SUP x:S. x \<bullet> i)"
        by (simp add: i sup)
      also have "(SUP x:S. x \<bullet> i) \<le> b \<bullet> i"
        by (simp add: False b cSUP_least)
      finally have bi: "x \<bullet> i \<le> b \<bullet> i" .
      show "x \<bullet> i \<in> (\<lambda>x. x \<bullet> i) ` S"
        apply (rule_tac x="\<Sum>j\<in>Basis. (if j = i then x \<bullet> i else a \<bullet> j) *\<^sub>R j" in image_eqI)
        apply (simp add: i)
        apply (rule mem_is_intervalI [OF \<open>is_interval S\<close> \<open>a \<in> S\<close> \<open>b \<in> S\<close>])
        using i ai bi apply force
        done
    qed
    have "S = cbox a b"
      by (auto simp: a_def b_def mem_box intro: 1 2 3)
    then show ?rhs
      by blast
  next
    assume R: ?rhs
    then show ?lhs
      using compact_cbox is_interval_cbox by blast
  qed
qed


lemma box_midpoint:
  fixes a :: "'a::euclidean_space"
  assumes "box a b \<noteq> {}"
  shows "((1/2) *\<^sub>R (a + b)) \<in> box a b"
proof -
  {
    fix i :: 'a
    assume "i \<in> Basis"
    then have "a \<bullet> i < ((1 / 2) *\<^sub>R (a + b)) \<bullet> i \<and> ((1 / 2) *\<^sub>R (a + b)) \<bullet> i < b \<bullet> i"
      using assms[unfolded box_ne_empty, THEN bspec[where x=i]] by (auto simp: inner_add_left)
  }
  then show ?thesis unfolding mem_box by auto
qed

lemma open_cbox_convex:
  fixes x :: "'a::euclidean_space"
  assumes x: "x \<in> box a b"
    and y: "y \<in> cbox a b"
    and e: "0 < e" "e \<le> 1"
  shows "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<in> box a b"
proof -
  {
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "a \<bullet> i = e * (a \<bullet> i) + (1 - e) * (a \<bullet> i)"
      unfolding left_diff_distrib by simp
    also have "\<dots> < e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
      apply (rule add_less_le_mono)
      using e unfolding mult_less_cancel_left and mult_le_cancel_left
      apply simp_all
      using x unfolding mem_box using i
      apply simp
      using y unfolding mem_box using i
      apply simp
      done
    finally have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i"
      unfolding inner_simps by auto
    moreover
    {
      have "b \<bullet> i = e * (b\<bullet>i) + (1 - e) * (b\<bullet>i)"
        unfolding left_diff_distrib by simp
      also have "\<dots> > e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
        apply (rule add_less_le_mono)
        using e unfolding mult_less_cancel_left and mult_le_cancel_left
        apply simp_all
        using x
        unfolding mem_box
        using i
        apply simp
        using y
        unfolding mem_box
        using i
        apply simp
        done
      finally have "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
        unfolding inner_simps by auto
    }
    ultimately have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i \<and> (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
      by auto
  }
  then show ?thesis
    unfolding mem_box by auto
qed

lemma closure_cbox [simp]: "closure (cbox a b) = cbox a b"
  by (simp add: closed_cbox)

lemma closure_box [simp]:
  fixes a :: "'a::euclidean_space"
   assumes "box a b \<noteq> {}"
  shows "closure (box a b) = cbox a b"
proof -
  have ab: "a <e b"
    using assms by (simp add: eucl_less_def box_ne_empty)
  let ?c = "(1 / 2) *\<^sub>R (a + b)"
  {
    fix x
    assume as:"x \<in> cbox a b"
    define f where [abs_def]: "f n = x + (inverse (real n + 1)) *\<^sub>R (?c - x)" for n
    {
      fix n
      assume fn: "f n <e b \<longrightarrow> a <e f n \<longrightarrow> f n = x" and xc: "x \<noteq> ?c"
      have *: "0 < inverse (real n + 1)" "inverse (real n + 1) \<le> 1"
        unfolding inverse_le_1_iff by auto
      have "(inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b)) + (1 - inverse (real n + 1)) *\<^sub>R x =
        x + (inverse (real n + 1)) *\<^sub>R (((1 / 2) *\<^sub>R (a + b)) - x)"
        by (auto simp: algebra_simps)
      then have "f n <e b" and "a <e f n"
        using open_cbox_convex[OF box_midpoint[OF assms] as *]
        unfolding f_def by (auto simp: box_def eucl_less_def)
      then have False
        using fn unfolding f_def using xc by auto
    }
    moreover
    {
      assume "\<not> (f \<longlongrightarrow> x) sequentially"
      {
        fix e :: real
        assume "e > 0"
        then have "\<exists>N::nat. inverse (real (N + 1)) < e"
          using real_arch_inverse[of e]
          apply (auto simp: Suc_pred')
          apply (metis Suc_pred' of_nat_Suc)
          done
        then obtain N :: nat where N: "inverse (real (N + 1)) < e"
          by auto
        have "inverse (real n + 1) < e" if "N \<le> n" for n
          by (auto intro!: that le_less_trans [OF _ N])
        then have "\<exists>N::nat. \<forall>n\<ge>N. inverse (real n + 1) < e" by auto
      }
      then have "((\<lambda>n. inverse (real n + 1)) \<longlongrightarrow> 0) sequentially"
        unfolding lim_sequentially by(auto simp: dist_norm)
      then have "(f \<longlongrightarrow> x) sequentially"
        unfolding f_def
        using tendsto_add[OF tendsto_const, of "\<lambda>n::nat. (inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x)" 0 sequentially x]
        using tendsto_scaleR [OF _ tendsto_const, of "\<lambda>n::nat. inverse (real n + 1)" 0 sequentially "((1 / 2) *\<^sub>R (a + b) - x)"]
        by auto
    }
    ultimately have "x \<in> closure (box a b)"
      using as and box_midpoint[OF assms]
      unfolding closure_def
      unfolding islimpt_sequential
      by (cases "x=?c") (auto simp: in_box_eucl_less)
  }
  then show ?thesis
    using closure_minimal[OF box_subset_cbox, of a b] by blast
qed

lemma bounded_subset_box_symmetric:
  fixes s::"('a::euclidean_space) set"
  assumes "bounded s"
  shows "\<exists>a. s \<subseteq> box (-a) a"
proof -
  obtain b where "b>0" and b: "\<forall>x\<in>s. norm x \<le> b"
    using assms[unfolded bounded_pos] by auto
  define a :: 'a where "a = (\<Sum>i\<in>Basis. (b + 1) *\<^sub>R i)"
  {
    fix x
    assume "x \<in> s"
    fix i :: 'a
    assume i: "i \<in> Basis"
    then have "(-a)\<bullet>i < x\<bullet>i" and "x\<bullet>i < a\<bullet>i"
      using b[THEN bspec[where x=x], OF \<open>x\<in>s\<close>]
      using Basis_le_norm[OF i, of x]
      unfolding inner_simps and a_def
      by auto
  }
  then show ?thesis
    by (auto intro: exI[where x=a] simp add: box_def)
qed

lemma bounded_subset_open_interval:
  fixes s :: "('a::euclidean_space) set"
  shows "bounded s \<Longrightarrow> (\<exists>a b. s \<subseteq> box a b)"
  by (auto dest!: bounded_subset_box_symmetric)

lemma bounded_subset_cbox_symmetric:
  fixes s :: "('a::euclidean_space) set"
   assumes "bounded s"
  shows "\<exists>a. s \<subseteq> cbox (-a) a"
proof -
  obtain a where "s \<subseteq> box (-a) a"
    using bounded_subset_box_symmetric[OF assms] by auto
  then show ?thesis
    using box_subset_cbox[of "-a" a] by auto
qed

lemma bounded_subset_cbox:
  fixes s :: "('a::euclidean_space) set"
  shows "bounded s \<Longrightarrow> \<exists>a b. s \<subseteq> cbox a b"
  using bounded_subset_cbox_symmetric[of s] by auto

lemma frontier_cbox:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (cbox a b) = cbox a b - box a b"
  unfolding frontier_def unfolding interior_cbox and closure_closed[OF closed_cbox] ..

lemma frontier_box:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (box a b) = (if box a b = {} then {} else cbox a b - box a b)"
proof (cases "box a b = {}")
  case True
  then show ?thesis
    using frontier_empty by auto
next
  case False
  then show ?thesis
    unfolding frontier_def and closure_box[OF False] and interior_open[OF open_box]
    by auto
qed

lemma inter_interval_mixed_eq_empty:
  fixes a :: "'a::euclidean_space"
   assumes "box c d \<noteq> {}"
  shows "box a b \<inter> cbox c d = {} \<longleftrightarrow> box a b \<inter> box c d = {}"
  unfolding closure_box[OF assms, symmetric]
  unfolding open_Int_closure_eq_empty[OF open_box] ..

lemma diameter_cbox:
  fixes a b::"'a::euclidean_space"
  shows "(\<forall>i \<in> Basis. a \<bullet> i \<le> b \<bullet> i) \<Longrightarrow> diameter (cbox a b) = dist a b"
  by (force simp: diameter_def intro!: cSup_eq_maximum setL2_mono
     simp: euclidean_dist_l2[where 'a='a] cbox_def dist_norm)

lemma eucl_less_eq_halfspaces:
  fixes a :: "'a::euclidean_space"
  shows "{x. x <e a} = (\<Inter>i\<in>Basis. {x. x \<bullet> i < a \<bullet> i})"
    "{x. a <e x} = (\<Inter>i\<in>Basis. {x. a \<bullet> i < x \<bullet> i})"
  by (auto simp: eucl_less_def)

lemma eucl_le_eq_halfspaces:
  fixes a :: "'a::euclidean_space"
  shows "{x. \<forall>i\<in>Basis. x \<bullet> i \<le> a \<bullet> i} = (\<Inter>i\<in>Basis. {x. x \<bullet> i \<le> a \<bullet> i})"
    "{x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i} = (\<Inter>i\<in>Basis. {x. a \<bullet> i \<le> x \<bullet> i})"
  by auto

lemma open_Collect_eucl_less[simp, intro]:
  fixes a :: "'a::euclidean_space"
  shows "open {x. x <e a}"
    "open {x. a <e x}"
  by (auto simp: eucl_less_eq_halfspaces open_halfspace_component_lt open_halfspace_component_gt)

lemma closed_Collect_eucl_le[simp, intro]:
  fixes a :: "'a::euclidean_space"
  shows "closed {x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i}"
    "closed {x. \<forall>i\<in>Basis. x \<bullet> i \<le> a \<bullet> i}"
  unfolding eucl_le_eq_halfspaces
  by (simp_all add: closed_INT closed_Collect_le  continuous_on_inner continuous_on_const continuous_on_id)

lemma image_affinity_cbox: fixes m::real
  fixes a b c :: "'a::euclidean_space"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` cbox a b =
    (if cbox a b = {} then {}
     else (if 0 \<le> m then cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)
     else cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c)))"
proof (cases "m = 0")
  case True
  {
    fix x
    assume "\<forall>i\<in>Basis. x \<bullet> i \<le> c \<bullet> i" "\<forall>i\<in>Basis. c \<bullet> i \<le> x \<bullet> i"
    then have "x = c"
      apply -
      apply (subst euclidean_eq_iff)
      apply (auto intro: order_antisym)
      done
  }
  moreover have "c \<in> cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)"
    unfolding True by (auto simp: cbox_sing)
  ultimately show ?thesis using True by (auto simp: cbox_def)
next
  case False
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m > 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
      by (auto simp: inner_distrib)
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m < 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i"
      by (auto simp: mult_left_mono_neg inner_distrib)
  }
  moreover
  {
    fix y
    assume "m > 0" and "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> y \<bullet> i" and "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp: pos_le_divide_eq pos_divide_le_eq mult.commute inner_distrib inner_diff_left)
      done
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i" "m < 0"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp: neg_le_divide_eq neg_divide_le_eq mult.commute inner_distrib inner_diff_left)
      done
  }
  ultimately show ?thesis using False by (auto simp: cbox_def)
qed

lemma image_smult_cbox:"(\<lambda>x. m *\<^sub>R (x::_::euclidean_space)) ` cbox a b =
  (if cbox a b = {} then {} else if 0 \<le> m then cbox (m *\<^sub>R a) (m *\<^sub>R b) else cbox (m *\<^sub>R b) (m *\<^sub>R a))"
  using image_affinity_cbox[of m 0 a b] by auto

lemma islimpt_greaterThanLessThan1:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "a islimpt {a<..<b}"
proof (rule islimptI)
  fix T
  assume "open T" "a \<in> T"
  from open_right[OF this \<open>a < b\<close>]
  obtain c where c: "a < c" "{a..<c} \<subseteq> T" by auto
  with assms dense[of a "min c b"]
  show "\<exists>y\<in>{a<..<b}. y \<in> T \<and> y \<noteq> a"
    by (metis atLeastLessThan_iff greaterThanLessThan_iff min_less_iff_conj
      not_le order.strict_implies_order subset_eq)
qed

lemma islimpt_greaterThanLessThan2:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "b islimpt {a<..<b}"
proof (rule islimptI)
  fix T
  assume "open T" "b \<in> T"
  from open_left[OF this \<open>a < b\<close>]
  obtain c where c: "c < b" "{c<..b} \<subseteq> T" by auto
  with assms dense[of "max a c" b]
  show "\<exists>y\<in>{a<..<b}. y \<in> T \<and> y \<noteq> b"
    by (metis greaterThanAtMost_iff greaterThanLessThan_iff max_less_iff_conj
      not_le order.strict_implies_order subset_eq)
qed

lemma closure_greaterThanLessThan[simp]:
  fixes a b::"'a::{linorder_topology, dense_order}"
  shows "a < b \<Longrightarrow> closure {a <..< b} = {a .. b}" (is "_ \<Longrightarrow> ?l = ?r")
proof
  have "?l \<subseteq> closure ?r"
    by (rule closure_mono) auto
  thus "closure {a<..<b} \<subseteq> {a..b}" by simp
qed (auto simp: closure_def order.order_iff_strict islimpt_greaterThanLessThan1
  islimpt_greaterThanLessThan2)

lemma closure_greaterThan[simp]:
  fixes a b::"'a::{no_top, linorder_topology, dense_order}"
  shows "closure {a<..} = {a..}"
proof -
  from gt_ex obtain b where "a < b" by auto
  hence "{a<..} = {a<..<b} \<union> {b..}" by auto
  also have "closure \<dots> = {a..}" using \<open>a < b\<close> unfolding closure_Un
    by auto
  finally show ?thesis .
qed

lemma closure_lessThan[simp]:
  fixes b::"'a::{no_bot, linorder_topology, dense_order}"
  shows "closure {..<b} = {..b}"
proof -
  from lt_ex obtain a where "a < b" by auto
  hence "{..<b} = {a<..<b} \<union> {..a}" by auto
  also have "closure \<dots> = {..b}" using \<open>a < b\<close> unfolding closure_Un
    by auto
  finally show ?thesis .
qed

lemma closure_atLeastLessThan[simp]:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows "closure {a ..< b} = {a .. b}"
proof -
  from assms have "{a ..< b} = {a} \<union> {a <..< b}" by auto
  also have "closure \<dots> = {a .. b}" unfolding closure_Un
    by (auto simp: assms less_imp_le)
  finally show ?thesis .
qed

lemma closure_greaterThanAtMost[simp]:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows "closure {a <.. b} = {a .. b}"
proof -
  from assms have "{a <.. b} = {b} \<union> {a <..< b}" by auto
  also have "closure \<dots> = {a .. b}" unfolding closure_Un
    by (auto simp: assms less_imp_le)
  finally show ?thesis .
qed


subsection \<open>Homeomorphisms\<close>

definition "homeomorphism s t f g \<longleftrightarrow>
  (\<forall>x\<in>s. (g(f x) = x)) \<and> (f ` s = t) \<and> continuous_on s f \<and>
  (\<forall>y\<in>t. (f(g y) = y)) \<and> (g ` t = s) \<and> continuous_on t g"

lemma homeomorphismI [intro?]:
  assumes "continuous_on S f" "continuous_on T g"
          "f ` S \<subseteq> T" "g ` T \<subseteq> S" "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "\<And>y. y \<in> T \<Longrightarrow> f(g y) = y"
    shows "homeomorphism S T f g"
  using assms by (force simp: homeomorphism_def)

lemma homeomorphism_translation:
  fixes a :: "'a :: real_normed_vector"
  shows "homeomorphism (op + a ` S) S (op + (- a)) (op + a)"
unfolding homeomorphism_def by (auto simp: algebra_simps continuous_intros)

lemma homeomorphism_ident: "homeomorphism T T (\<lambda>a. a) (\<lambda>a. a)"
  by (rule homeomorphismI) (auto simp: continuous_on_id)

lemma homeomorphism_compose:
  assumes "homeomorphism S T f g" "homeomorphism T U h k"
    shows "homeomorphism S U (h o f) (g o k)"
  using assms
  unfolding homeomorphism_def
  by (intro conjI ballI continuous_on_compose) (auto simp: image_comp [symmetric])

lemma homeomorphism_symD: "homeomorphism S t f g \<Longrightarrow> homeomorphism t S g f"
  by (simp add: homeomorphism_def)

lemma homeomorphism_sym: "homeomorphism S t f g = homeomorphism t S g f"
  by (force simp: homeomorphism_def)

definition homeomorphic :: "'a::topological_space set \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
    (infixr "homeomorphic" 60)
  where "s homeomorphic t \<equiv> (\<exists>f g. homeomorphism s t f g)"

lemma homeomorphic_empty [iff]:
     "S homeomorphic {} \<longleftrightarrow> S = {}" "{} homeomorphic S \<longleftrightarrow> S = {}"
  by (auto simp: homeomorphic_def homeomorphism_def)

lemma homeomorphic_refl: "s homeomorphic s"
  unfolding homeomorphic_def homeomorphism_def
  using continuous_on_id
  apply (rule_tac x = "(\<lambda>x. x)" in exI)
  apply (rule_tac x = "(\<lambda>x. x)" in exI)
  apply blast
  done

lemma homeomorphic_sym: "s homeomorphic t \<longleftrightarrow> t homeomorphic s"
  unfolding homeomorphic_def homeomorphism_def
  by blast

lemma homeomorphic_trans [trans]:
  assumes "S homeomorphic T"
      and "T homeomorphic U"
    shows "S homeomorphic U"
  using assms
  unfolding homeomorphic_def
by (metis homeomorphism_compose)

lemma homeomorphic_minimal:
  "s homeomorphic t \<longleftrightarrow>
    (\<exists>f g. (\<forall>x\<in>s. f(x) \<in> t \<and> (g(f(x)) = x)) \<and>
           (\<forall>y\<in>t. g(y) \<in> s \<and> (f(g(y)) = y)) \<and>
           continuous_on s f \<and> continuous_on t g)"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (fastforce simp: homeomorphic_def homeomorphism_def)
next
  assume ?rhs
  then show ?lhs
    apply clarify
    unfolding homeomorphic_def homeomorphism_def
    by (metis equalityI image_subset_iff subsetI)
 qed

lemma homeomorphicI [intro?]:
   "\<lbrakk>f ` S = T; g ` T = S;
     continuous_on S f; continuous_on T g;
     \<And>x. x \<in> S \<Longrightarrow> g(f(x)) = x;
     \<And>y. y \<in> T \<Longrightarrow> f(g(y)) = y\<rbrakk> \<Longrightarrow> S homeomorphic T"
unfolding homeomorphic_def homeomorphism_def by metis

lemma homeomorphism_of_subsets:
   "\<lbrakk>homeomorphism S T f g; S' \<subseteq> S; T'' \<subseteq> T; f ` S' = T'\<rbrakk>
    \<Longrightarrow> homeomorphism S' T' f g"
apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
by (metis subsetD imageI)

lemma homeomorphism_apply1: "\<lbrakk>homeomorphism S T f g; x \<in> S\<rbrakk> \<Longrightarrow> g(f x) = x"
  by (simp add: homeomorphism_def)

lemma homeomorphism_apply2: "\<lbrakk>homeomorphism S T f g; x \<in> T\<rbrakk> \<Longrightarrow> f(g x) = x"
  by (simp add: homeomorphism_def)

lemma homeomorphism_image1: "homeomorphism S T f g \<Longrightarrow> f ` S = T"
  by (simp add: homeomorphism_def)

lemma homeomorphism_image2: "homeomorphism S T f g \<Longrightarrow> g ` T = S"
  by (simp add: homeomorphism_def)

lemma homeomorphism_cont1: "homeomorphism S T f g \<Longrightarrow> continuous_on S f"
  by (simp add: homeomorphism_def)

lemma homeomorphism_cont2: "homeomorphism S T f g \<Longrightarrow> continuous_on T g"
  by (simp add: homeomorphism_def)

lemma continuous_on_no_limpt:
   "(\<And>x. \<not> x islimpt S) \<Longrightarrow> continuous_on S f"
  unfolding continuous_on_def
  by (metis UNIV_I empty_iff eventually_at_topological islimptE open_UNIV tendsto_def trivial_limit_within)

lemma continuous_on_finite:
  fixes S :: "'a::t1_space set"
  shows "finite S \<Longrightarrow> continuous_on S f"
by (metis continuous_on_no_limpt islimpt_finite)

lemma homeomorphic_finite:
  fixes S :: "'a::t1_space set" and T :: "'b::t1_space set"
  assumes "finite T"
  shows "S homeomorphic T \<longleftrightarrow> finite S \<and> finite T \<and> card S = card T" (is "?lhs = ?rhs")
proof
  assume "S homeomorphic T"
  with assms show ?rhs
    apply (auto simp: homeomorphic_def homeomorphism_def)
     apply (metis finite_imageI)
    by (metis card_image_le finite_imageI le_antisym)
next
  assume R: ?rhs
  with finite_same_card_bij obtain h where "bij_betw h S T"
    by auto
  with R show ?lhs
    apply (auto simp: homeomorphic_def homeomorphism_def continuous_on_finite)
    apply (rule_tac x=h in exI)
    apply (rule_tac x="inv_into S h" in exI)
    apply (auto simp:  bij_betw_inv_into_left bij_betw_inv_into_right bij_betw_imp_surj_on inv_into_into bij_betwE)
    apply (metis bij_betw_def bij_betw_inv_into)
    done
qed

text \<open>Relatively weak hypotheses if a set is compact.\<close>

lemma homeomorphism_compact:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes "compact s" "continuous_on s f"  "f ` s = t"  "inj_on f s"
  shows "\<exists>g. homeomorphism s t f g"
proof -
  define g where "g x = (SOME y. y\<in>s \<and> f y = x)" for x
  have g: "\<forall>x\<in>s. g (f x) = x"
    using assms(3) assms(4)[unfolded inj_on_def] unfolding g_def by auto
  {
    fix y
    assume "y \<in> t"
    then obtain x where x:"f x = y" "x\<in>s"
      using assms(3) by auto
    then have "g (f x) = x" using g by auto
    then have "f (g y) = y" unfolding x(1)[symmetric] by auto
  }
  then have g':"\<forall>x\<in>t. f (g x) = x" by auto
  moreover
  {
    fix x
    have "x\<in>s \<Longrightarrow> x \<in> g ` t"
      using g[THEN bspec[where x=x]]
      unfolding image_iff
      using assms(3)
      by (auto intro!: bexI[where x="f x"])
    moreover
    {
      assume "x\<in>g ` t"
      then obtain y where y:"y\<in>t" "g y = x" by auto
      then obtain x' where x':"x'\<in>s" "f x' = y"
        using assms(3) by auto
      then have "x \<in> s"
        unfolding g_def
        using someI2[of "\<lambda>b. b\<in>s \<and> f b = y" x' "\<lambda>x. x\<in>s"]
        unfolding y(2)[symmetric] and g_def
        by auto
    }
    ultimately have "x\<in>s \<longleftrightarrow> x \<in> g ` t" ..
  }
  then have "g ` t = s" by auto
  ultimately show ?thesis
    unfolding homeomorphism_def homeomorphic_def
    apply (rule_tac x=g in exI)
    using g and assms(3) and continuous_on_inv[OF assms(2,1), of g, unfolded assms(3)] and assms(2)
    apply auto
    done
qed

lemma homeomorphic_compact:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  shows "compact s \<Longrightarrow> continuous_on s f \<Longrightarrow> (f ` s = t) \<Longrightarrow> inj_on f s \<Longrightarrow> s homeomorphic t"
  unfolding homeomorphic_def by (metis homeomorphism_compact)

text\<open>Preservation of topological properties.\<close>

lemma homeomorphic_compactness: "s homeomorphic t \<Longrightarrow> (compact s \<longleftrightarrow> compact t)"
  unfolding homeomorphic_def homeomorphism_def
  by (metis compact_continuous_image)

text\<open>Results on translation, scaling etc.\<close>

lemma homeomorphic_scaling:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
  shows "s homeomorphic ((\<lambda>x. c *\<^sub>R x) ` s)"
  unfolding homeomorphic_minimal
  apply (rule_tac x="\<lambda>x. c *\<^sub>R x" in exI)
  apply (rule_tac x="\<lambda>x. (1 / c) *\<^sub>R x" in exI)
  using assms
  apply (auto simp: continuous_intros)
  done

lemma homeomorphic_translation:
  fixes s :: "'a::real_normed_vector set"
  shows "s homeomorphic ((\<lambda>x. a + x) ` s)"
  unfolding homeomorphic_minimal
  apply (rule_tac x="\<lambda>x. a + x" in exI)
  apply (rule_tac x="\<lambda>x. -a + x" in exI)
  using continuous_on_add [OF continuous_on_const continuous_on_id, of s a]
    continuous_on_add [OF continuous_on_const continuous_on_id, of "plus a ` s" "- a"]
  apply auto
  done

lemma homeomorphic_affinity:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
  shows "s homeomorphic ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have *: "op + a ` op *\<^sub>R c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s" by auto
  show ?thesis
    using homeomorphic_trans
    using homeomorphic_scaling[OF assms, of s]
    using homeomorphic_translation[of "(\<lambda>x. c *\<^sub>R x) ` s" a]
    unfolding *
    by auto
qed

lemma homeomorphic_balls:
  fixes a b ::"'a::real_normed_vector"
  assumes "0 < d"  "0 < e"
  shows "(ball a d) homeomorphic  (ball b e)" (is ?th)
    and "(cball a d) homeomorphic (cball b e)" (is ?cth)
proof -
  show ?th unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    apply (auto intro!: continuous_intros
      simp: dist_commute dist_norm pos_divide_less_eq mult_strict_left_mono)
    done
  show ?cth unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    apply (auto intro!: continuous_intros
      simp: dist_commute dist_norm pos_divide_le_eq mult_strict_left_mono)
    done
qed

lemma homeomorphic_spheres:
  fixes a b ::"'a::real_normed_vector"
  assumes "0 < d"  "0 < e"
  shows "(sphere a d) homeomorphic (sphere b e)"
unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    apply (auto intro!: continuous_intros
      simp: dist_commute dist_norm pos_divide_less_eq mult_strict_left_mono)
    done

lemma homeomorphic_ball01_UNIV:
  "ball (0::'a::real_normed_vector) 1 homeomorphic (UNIV:: 'a set)"
  (is "?B homeomorphic ?U")
proof
  have "x \<in> (\<lambda>z. z /\<^sub>R (1 - norm z)) ` ball 0 1" for x::'a
    apply (rule_tac x="x /\<^sub>R (1 + norm x)" in image_eqI)
     apply (auto simp: divide_simps)
    using norm_ge_zero [of x] apply linarith+
    done
  then show "(\<lambda>z::'a. z /\<^sub>R (1 - norm z)) ` ?B = ?U"
    by blast
  have "x \<in> range (\<lambda>z. (1 / (1 + norm z)) *\<^sub>R z)" if "norm x < 1" for x::'a
    apply (rule_tac x="x /\<^sub>R (1 - norm x)" in image_eqI)
    using that apply (auto simp: divide_simps)
    done
  then show "(\<lambda>z::'a. z /\<^sub>R (1 + norm z)) ` ?U = ?B"
    by (force simp: divide_simps dest: add_less_zeroD)
  show "continuous_on (ball 0 1) (\<lambda>z. z /\<^sub>R (1 - norm z))"
    by (rule continuous_intros | force)+
  show "continuous_on UNIV (\<lambda>z. z /\<^sub>R (1 + norm z))"
    apply (intro continuous_intros)
    apply (metis le_add_same_cancel1 norm_ge_zero not_le zero_less_one)
    done
  show "\<And>x. x \<in> ball 0 1 \<Longrightarrow>
         x /\<^sub>R (1 - norm x) /\<^sub>R (1 + norm (x /\<^sub>R (1 - norm x))) = x"
    by (auto simp: divide_simps)
  show "\<And>y. y /\<^sub>R (1 + norm y) /\<^sub>R (1 - norm (y /\<^sub>R (1 + norm y))) = y"
    apply (auto simp: divide_simps)
    apply (metis le_add_same_cancel1 norm_ge_zero not_le zero_less_one)
    done
qed

proposition homeomorphic_ball_UNIV:
  fixes a ::"'a::real_normed_vector"
  assumes "0 < r" shows "ball a r homeomorphic (UNIV:: 'a set)"
  using assms homeomorphic_ball01_UNIV homeomorphic_balls(1) homeomorphic_trans zero_less_one by blast

subsection\<open>Inverse function property for open/closed maps\<close>

lemma continuous_on_inverse_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
  shows "continuous_on T g"
proof -
  from imf injf have gTS: "g ` T = S"
    by force
  from imf injf have fU: "U \<subseteq> S \<Longrightarrow> (f ` U) = {x \<in> T. g x \<in> U}" for U
    by force
  show ?thesis
    by (simp add: continuous_on_open [of T g] gTS) (metis openin_imp_subset fU oo)
qed

lemma continuous_on_inverse_closed_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    and oo: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
  shows "continuous_on T g"
proof -
  from imf injf have gTS: "g ` T = S"
    by force
  from imf injf have fU: "U \<subseteq> S \<Longrightarrow> (f ` U) = {x \<in> T. g x \<in> U}" for U
    by force
  show ?thesis
    by (simp add: continuous_on_closed [of T g] gTS) (metis closedin_imp_subset fU oo)
qed

lemma homeomorphism_injective_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "inj_on f S"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_open_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_injective_closed_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "inj_on f S"
    and oo: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_closed_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_imp_open_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "openin (subtopology euclidean S) U"
  shows "openin (subtopology euclidean T) (f ` U)"
proof -
  from hom oo have [simp]: "f ` U = {y. y \<in> T \<and> g y \<in> U}"
    using openin_subset by (fastforce simp: homeomorphism_def rev_image_eqI)
  from hom have "continuous_on T g"
    unfolding homeomorphism_def by blast
  moreover have "g ` T = S"
    by (metis hom homeomorphism_def)
  ultimately show ?thesis
    by (simp add: continuous_on_open oo)
qed

lemma homeomorphism_imp_closed_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "closedin (subtopology euclidean S) U"
  shows "closedin (subtopology euclidean T) (f ` U)"
proof -
  from hom oo have [simp]: "f ` U = {y. y \<in> T \<and> g y \<in> U}"
    using closedin_subset by (fastforce simp: homeomorphism_def rev_image_eqI)
  from hom have "continuous_on T g"
    unfolding homeomorphism_def by blast
  moreover have "g ` T = S"
    by (metis hom homeomorphism_def)
  ultimately show ?thesis
    by (simp add: continuous_on_closed oo)
qed


subsection \<open>"Isometry" (up to constant bounds) of injective linear map etc.\<close>

lemma cauchy_isometric:
  assumes e: "e > 0"
    and s: "subspace s"
    and f: "bounded_linear f"
    and normf: "\<forall>x\<in>s. norm (f x) \<ge> e * norm x"
    and xs: "\<forall>n. x n \<in> s"
    and cf: "Cauchy (f \<circ> x)"
  shows "Cauchy x"
proof -
  interpret f: bounded_linear f by fact
  have "\<exists>N. \<forall>n\<ge>N. norm (x n - x N) < d" if "d > 0" for d :: real
  proof -
    from that obtain N where N: "\<forall>n\<ge>N. norm (f (x n) - f (x N)) < e * d"
      using cf[unfolded Cauchy_def o_def dist_norm, THEN spec[where x="e*d"]] e
      by auto
    have "norm (x n - x N) < d" if "n \<ge> N" for n
    proof -
      have "e * norm (x n - x N) \<le> norm (f (x n - x N))"
        using subspace_diff[OF s, of "x n" "x N"]
        using xs[THEN spec[where x=N]] and xs[THEN spec[where x=n]]
        using normf[THEN bspec[where x="x n - x N"]]
        by auto
      also have "norm (f (x n - x N)) < e * d"
        using \<open>N \<le> n\<close> N unfolding f.diff[symmetric] by auto
      finally show ?thesis
        using \<open>e>0\<close> by simp
    qed
    then show ?thesis by auto
  qed
  then show ?thesis
    by (simp add: Cauchy_altdef2 dist_norm)
qed

lemma complete_isometric_image:
  assumes "0 < e"
    and s: "subspace s"
    and f: "bounded_linear f"
    and normf: "\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)"
    and cs: "complete s"
  shows "complete (f ` s)"
proof -
  have "\<exists>l\<in>f ` s. (g \<longlongrightarrow> l) sequentially"
    if as:"\<forall>n::nat. g n \<in> f ` s" and cfg:"Cauchy g" for g
  proof -
    from that obtain x where "\<forall>n. x n \<in> s \<and> g n = f (x n)"
      using choice[of "\<lambda> n xa. xa \<in> s \<and> g n = f xa"] by auto
    then have x: "\<forall>n. x n \<in> s" "\<forall>n. g n = f (x n)" by auto
    then have "f \<circ> x = g" by (simp add: fun_eq_iff)
    then obtain l where "l\<in>s" and l:"(x \<longlongrightarrow> l) sequentially"
      using cs[unfolded complete_def, THEN spec[where x=x]]
      using cauchy_isometric[OF \<open>0 < e\<close> s f normf] and cfg and x(1)
      by auto
    then show ?thesis
      using linear_continuous_at[OF f, unfolded continuous_at_sequentially, THEN spec[where x=x], of l]
      by (auto simp: \<open>f \<circ> x = g\<close>)
  qed
  then show ?thesis
    unfolding complete_def by auto
qed

lemma injective_imp_isometric:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes s: "closed s" "subspace s"
    and f: "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0"
  shows "\<exists>e>0. \<forall>x\<in>s. norm (f x) \<ge> e * norm x"
proof (cases "s \<subseteq> {0::'a}")
  case True
  have "norm x \<le> norm (f x)" if "x \<in> s" for x
  proof -
    from True that have "x = 0" by auto
    then show ?thesis by simp
  qed
  then show ?thesis
    by (auto intro!: exI[where x=1])
next
  case False
  interpret f: bounded_linear f by fact
  from False obtain a where a: "a \<noteq> 0" "a \<in> s"
    by auto
  from False have "s \<noteq> {}"
    by auto
  let ?S = "{f x| x. x \<in> s \<and> norm x = norm a}"
  let ?S' = "{x::'a. x\<in>s \<and> norm x = norm a}"
  let ?S'' = "{x::'a. norm x = norm a}"

  have "?S'' = frontier (cball 0 (norm a))"
    by (simp add: sphere_def dist_norm)
  then have "compact ?S''" by (metis compact_cball compact_frontier)
  moreover have "?S' = s \<inter> ?S''" by auto
  ultimately have "compact ?S'"
    using closed_Int_compact[of s ?S''] using s(1) by auto
  moreover have *:"f ` ?S' = ?S" by auto
  ultimately have "compact ?S"
    using compact_continuous_image[OF linear_continuous_on[OF f(1)], of ?S'] by auto
  then have "closed ?S"
    using compact_imp_closed by auto
  moreover from a have "?S \<noteq> {}" by auto
  ultimately obtain b' where "b'\<in>?S" "\<forall>y\<in>?S. norm b' \<le> norm y"
    using distance_attains_inf[of ?S 0] unfolding dist_0_norm by auto
  then obtain b where "b\<in>s"
    and ba: "norm b = norm a"
    and b: "\<forall>x\<in>{x \<in> s. norm x = norm a}. norm (f b) \<le> norm (f x)"
    unfolding *[symmetric] unfolding image_iff by auto

  let ?e = "norm (f b) / norm b"
  have "norm b > 0"
    using ba and a and norm_ge_zero by auto
  moreover have "norm (f b) > 0"
    using f(2)[THEN bspec[where x=b], OF \<open>b\<in>s\<close>]
    using \<open>norm b >0\<close> by simp
  ultimately have "0 < norm (f b) / norm b" by simp
  moreover
  have "norm (f b) / norm b * norm x \<le> norm (f x)" if "x\<in>s" for x
  proof (cases "x = 0")
    case True
    then show "norm (f b) / norm b * norm x \<le> norm (f x)"
      by auto
  next
    case False
    with \<open>a \<noteq> 0\<close> have *: "0 < norm a / norm x"
      unfolding zero_less_norm_iff[symmetric] by simp
    have "\<forall>x\<in>s. c *\<^sub>R x \<in> s" for c
      using s[unfolded subspace_def] by simp
    with \<open>x \<in> s\<close> \<open>x \<noteq> 0\<close> have "(norm a / norm x) *\<^sub>R x \<in> {x \<in> s. norm x = norm a}"
      by simp
    with \<open>x \<noteq> 0\<close> \<open>a \<noteq> 0\<close> show "norm (f b) / norm b * norm x \<le> norm (f x)"
      using b[THEN bspec[where x="(norm a / norm x) *\<^sub>R x"]]
      unfolding f.scaleR and ba
      by (auto simp: mult.commute pos_le_divide_eq pos_divide_le_eq)
  qed
  ultimately show ?thesis by auto
qed

lemma closed_injective_image_subspace:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace s" "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0" "closed s"
  shows "closed(f ` s)"
proof -
  obtain e where "e > 0" and e: "\<forall>x\<in>s. e * norm x \<le> norm (f x)"
    using injective_imp_isometric[OF assms(4,1,2,3)] by auto
  show ?thesis
    using complete_isometric_image[OF \<open>e>0\<close> assms(1,2) e] and assms(4)
    unfolding complete_eq_closed[symmetric] by auto
qed


subsection \<open>Some properties of a canonical subspace\<close>

lemma subspace_substandard: "subspace {x::'a::euclidean_space. (\<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0)}"
  by (auto simp: subspace_def inner_add_left)

lemma closed_substandard: "closed {x::'a::euclidean_space. \<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0}"
  (is "closed ?A")
proof -
  let ?D = "{i\<in>Basis. P i}"
  have "closed (\<Inter>i\<in>?D. {x::'a. x\<bullet>i = 0})"
    by (simp add: closed_INT closed_Collect_eq continuous_on_inner
        continuous_on_const continuous_on_id)
  also have "(\<Inter>i\<in>?D. {x::'a. x\<bullet>i = 0}) = ?A"
    by auto
  finally show "closed ?A" .
qed

lemma dim_substandard:
  assumes d: "d \<subseteq> Basis"
  shows "dim {x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0} = card d" (is "dim ?A = _")
proof (rule dim_unique)
  from d show "d \<subseteq> ?A"
    by (auto simp: inner_Basis)
  from d show "independent d"
    by (rule independent_mono [OF independent_Basis])
  have "x \<in> span d" if "\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0" for x
  proof -
    have "finite d"
      by (rule finite_subset [OF d finite_Basis])
    then have "(\<Sum>i\<in>d. (x \<bullet> i) *\<^sub>R i) \<in> span d"
      by (simp add: span_sum span_clauses)
    also have "(\<Sum>i\<in>d. (x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i)"
      by (rule sum.mono_neutral_cong_left [OF finite_Basis d]) (auto simp: that)
    finally show "x \<in> span d"
      by (simp only: euclidean_representation)
  qed
  then show "?A \<subseteq> span d" by auto
qed simp

text \<open>Hence closure and completeness of all subspaces.\<close>
lemma ex_card:
  assumes "n \<le> card A"
  shows "\<exists>S\<subseteq>A. card S = n"
proof (cases "finite A")
  case True
  from ex_bij_betw_nat_finite[OF this] obtain f where f: "bij_betw f {0..<card A} A" ..
  moreover from f \<open>n \<le> card A\<close> have "{..< n} \<subseteq> {..< card A}" "inj_on f {..< n}"
    by (auto simp: bij_betw_def intro: subset_inj_on)
  ultimately have "f ` {..< n} \<subseteq> A" "card (f ` {..< n}) = n"
    by (auto simp: bij_betw_def card_image)
  then show ?thesis by blast
next
  case False
  with \<open>n \<le> card A\<close> show ?thesis by force
qed

lemma closed_subspace:
  fixes s :: "'a::euclidean_space set"
  assumes "subspace s"
  shows "closed s"
proof -
  have "dim s \<le> card (Basis :: 'a set)"
    using dim_subset_UNIV by auto
  with ex_card[OF this] obtain d :: "'a set" where t: "card d = dim s" and d: "d \<subseteq> Basis"
    by auto
  let ?t = "{x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  have "\<exists>f. linear f \<and> f ` {x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} = s \<and>
      inj_on f {x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
    using dim_substandard[of d] t d assms
    by (intro subspace_isomorphism[OF subspace_substandard[of "\<lambda>i. i \<notin> d"]]) (auto simp: inner_Basis)
  then obtain f where f:
      "linear f"
      "f ` {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} = s"
      "inj_on f {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
    by blast
  interpret f: bounded_linear f
    using f by (simp add: linear_conv_bounded_linear)
  have "x \<in> ?t \<Longrightarrow> f x = 0 \<Longrightarrow> x = 0" for x
    using f.zero d f(3)[THEN inj_onD, of x 0] by auto
  moreover have "closed ?t" by (rule closed_substandard)
  moreover have "subspace ?t" by (rule subspace_substandard)
  ultimately show ?thesis
    using closed_injective_image_subspace[of ?t f]
    unfolding f(2) using f(1) unfolding linear_conv_bounded_linear by auto
qed

lemma complete_subspace: "subspace s \<Longrightarrow> complete s"
  for s :: "'a::euclidean_space set"
  using complete_eq_closed closed_subspace by auto

lemma closed_span [iff]: "closed (span s)"
  for s :: "'a::euclidean_space set"
  by (simp add: closed_subspace)

lemma dim_closure [simp]: "dim (closure s) = dim s" (is "?dc = ?d")
  for s :: "'a::euclidean_space set"
proof -
  have "?dc \<le> ?d"
    using closure_minimal[OF span_inc, of s]
    using closed_subspace[OF subspace_span, of s]
    using dim_subset[of "closure s" "span s"]
    by simp
  then show ?thesis
    using dim_subset[OF closure_subset, of s]
    by simp
qed


subsection \<open>Affine transformations of intervals\<close>

lemma real_affinity_le: "0 < m \<Longrightarrow> m * x + c \<le> y \<longleftrightarrow> x \<le> inverse m * y + - (c / m)"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_le_affinity: "0 < m \<Longrightarrow> y \<le> m * x + c \<longleftrightarrow> inverse m * y + - (c / m) \<le> x"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_affinity_lt: "0 < m \<Longrightarrow> m * x + c < y \<longleftrightarrow> x < inverse m * y + - (c / m)"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_lt_affinity: "0 < m \<Longrightarrow> y < m * x + c \<longleftrightarrow> inverse m * y + - (c / m) < x"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_affinity_eq: "m \<noteq> 0 \<Longrightarrow> m * x + c = y \<longleftrightarrow> x = inverse m * y + - (c / m)"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m * x + c  \<longleftrightarrow> inverse m * y + - (c / m) = x"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)


subsection \<open>Banach fixed point theorem (not really topological ...)\<close>

theorem banach_fix:
  assumes s: "complete s" "s \<noteq> {}"
    and c: "0 \<le> c" "c < 1"
    and f: "f ` s \<subseteq> s"
    and lipschitz: "\<forall>x\<in>s. \<forall>y\<in>s. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x\<in>s. f x = x"
proof -
  from c have "1 - c > 0" by simp

  from s(2) obtain z0 where z0: "z0 \<in> s" by blast
  define z where "z n = (f ^^ n) z0" for n
  with f z0 have z_in_s: "z n \<in> s" for n :: nat
    by (induct n) auto
  define d where "d = dist (z 0) (z 1)"

  have fzn: "f (z n) = z (Suc n)" for n
    by (simp add: z_def)
  have cf_z: "dist (z n) (z (Suc n)) \<le> (c ^ n) * d" for n :: nat
  proof (induct n)
    case 0
    then show ?case
      by (simp add: d_def)
  next
    case (Suc m)
    with \<open>0 \<le> c\<close> have "c * dist (z m) (z (Suc m)) \<le> c ^ Suc m * d"
      using mult_left_mono[of "dist (z m) (z (Suc m))" "c ^ m * d" c] by simp
    then show ?case
      using lipschitz[THEN bspec[where x="z m"], OF z_in_s, THEN bspec[where x="z (Suc m)"], OF z_in_s]
      by (simp add: fzn mult_le_cancel_left)
  qed

  have cf_z2: "(1 - c) * dist (z m) (z (m + n)) \<le> (c ^ m) * d * (1 - c ^ n)" for n m :: nat
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc k)
    from c have "(1 - c) * dist (z m) (z (m + Suc k)) \<le>
        (1 - c) * (dist (z m) (z (m + k)) + dist (z (m + k)) (z (Suc (m + k))))"
      by (simp add: dist_triangle)
    also from c cf_z[of "m + k"] have "\<dots> \<le> (1 - c) * (dist (z m) (z (m + k)) + c ^ (m + k) * d)"
      by simp
    also from Suc have "\<dots> \<le> c ^ m * d * (1 - c ^ k) + (1 - c) * c ^ (m + k) * d"
      by (simp add: field_simps)
    also have "\<dots> = (c ^ m) * (d * (1 - c ^ k) + (1 - c) * c ^ k * d)"
      by (simp add: power_add field_simps)
    also from c have "\<dots> \<le> (c ^ m) * d * (1 - c ^ Suc k)"
      by (simp add: field_simps)
    finally show ?case by simp
  qed

  have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (z m) (z n) < e" if "e > 0" for e
  proof (cases "d = 0")
    case True
    from \<open>1 - c > 0\<close> have "(1 - c) * x \<le> 0 \<longleftrightarrow> x \<le> 0" for x
      by (metis mult_zero_left mult.commute real_mult_le_cancel_iff1)
    with c cf_z2[of 0] True have "z n = z0" for n
      by (simp add: z_def)
    with \<open>e > 0\<close> show ?thesis by simp
  next
    case False
    with zero_le_dist[of "z 0" "z 1"] have "d > 0"
      by (metis d_def less_le)
    with \<open>1 - c > 0\<close> \<open>e > 0\<close> have "0 < e * (1 - c) / d"
      by simp
    with c obtain N where N: "c ^ N < e * (1 - c) / d"
      using real_arch_pow_inv[of "e * (1 - c) / d" c] by auto
    have *: "dist (z m) (z n) < e" if "m > n" and as: "m \<ge> N" "n \<ge> N" for m n :: nat
    proof -
      from c \<open>n \<ge> N\<close> have *: "c ^ n \<le> c ^ N"
        using power_decreasing[OF \<open>n\<ge>N\<close>, of c] by simp
      from c \<open>m > n\<close> have "1 - c ^ (m - n) > 0"
        using power_strict_mono[of c 1 "m - n"] by simp
      with \<open>d > 0\<close> \<open>0 < 1 - c\<close> have **: "d * (1 - c ^ (m - n)) / (1 - c) > 0"
        by simp
      from cf_z2[of n "m - n"] \<open>m > n\<close>
      have "dist (z m) (z n) \<le> c ^ n * d * (1 - c ^ (m - n)) / (1 - c)"
        by (simp add: pos_le_divide_eq[OF \<open>1 - c > 0\<close>] mult.commute dist_commute)
      also have "\<dots> \<le> c ^ N * d * (1 - c ^ (m - n)) / (1 - c)"
        using mult_right_mono[OF * order_less_imp_le[OF **]]
        by (simp add: mult.assoc)
      also have "\<dots> < (e * (1 - c) / d) * d * (1 - c ^ (m - n)) / (1 - c)"
        using mult_strict_right_mono[OF N **] by (auto simp: mult.assoc)
      also from c \<open>d > 0\<close> \<open>1 - c > 0\<close> have "\<dots> = e * (1 - c ^ (m - n))"
        by simp
      also from c \<open>1 - c ^ (m - n) > 0\<close> \<open>e > 0\<close> have "\<dots> \<le> e"
        using mult_right_le_one_le[of e "1 - c ^ (m - n)"] by auto
      finally show ?thesis by simp
    qed
    have "dist (z n) (z m) < e" if "N \<le> m" "N \<le> n" for m n :: nat
    proof (cases "n = m")
      case True
      with \<open>e > 0\<close> show ?thesis by simp
    next
      case False
      with *[of n m] *[of m n] and that show ?thesis
        by (auto simp: dist_commute nat_neq_iff)
    qed
    then show ?thesis by auto
  qed
  then have "Cauchy z"
    by (simp add: cauchy_def)
  then obtain x where "x\<in>s" and x:"(z \<longlongrightarrow> x) sequentially"
    using s(1)[unfolded compact_def complete_def, THEN spec[where x=z]] and z_in_s by auto

  define e where "e = dist (f x) x"
  have "e = 0"
  proof (rule ccontr)
    assume "e \<noteq> 0"
    then have "e > 0"
      unfolding e_def using zero_le_dist[of "f x" x]
      by (metis dist_eq_0_iff dist_nz e_def)
    then obtain N where N:"\<forall>n\<ge>N. dist (z n) x < e / 2"
      using x[unfolded lim_sequentially, THEN spec[where x="e/2"]] by auto
    then have N':"dist (z N) x < e / 2" by auto
    have *: "c * dist (z N) x \<le> dist (z N) x"
      unfolding mult_le_cancel_right2
      using zero_le_dist[of "z N" x] and c
      by (metis dist_eq_0_iff dist_nz order_less_asym less_le)
    have "dist (f (z N)) (f x) \<le> c * dist (z N) x"
      using lipschitz[THEN bspec[where x="z N"], THEN bspec[where x=x]]
      using z_in_s[of N] \<open>x\<in>s\<close>
      using c
      by auto
    also have "\<dots> < e / 2"
      using N' and c using * by auto
    finally show False
      unfolding fzn
      using N[THEN spec[where x="Suc N"]] and dist_triangle_half_r[of "z (Suc N)" "f x" e x]
      unfolding e_def
      by auto
  qed
  then have "f x = x" by (auto simp: e_def)
  moreover have "y = x" if "f y = y" "y \<in> s" for y
  proof -
    from \<open>x \<in> s\<close> \<open>f x = x\<close> that have "dist x y \<le> c * dist x y"
      using lipschitz[THEN bspec[where x=x], THEN bspec[where x=y]] by simp
    with c and zero_le_dist[of x y] have "dist x y = 0"
      by (simp add: mult_le_cancel_right1)
    then show ?thesis by simp
  qed
  ultimately show ?thesis
    using \<open>x\<in>s\<close> by blast
qed


subsection \<open>Edelstein fixed point theorem\<close>

theorem edelstein_fix:
  fixes s :: "'a::metric_space set"
  assumes s: "compact s" "s \<noteq> {}"
    and gs: "(g ` s) \<subseteq> s"
    and dist: "\<forall>x\<in>s. \<forall>y\<in>s. x \<noteq> y \<longrightarrow> dist (g x) (g y) < dist x y"
  shows "\<exists>!x\<in>s. g x = x"
proof -
  let ?D = "(\<lambda>x. (x, x)) ` s"
  have D: "compact ?D" "?D \<noteq> {}"
    by (rule compact_continuous_image)
       (auto intro!: s continuous_Pair continuous_ident simp: continuous_on_eq_continuous_within)

  have "\<And>x y e. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> 0 < e \<Longrightarrow> dist y x < e \<Longrightarrow> dist (g y) (g x) < e"
    using dist by fastforce
  then have "continuous_on s g"
    by (auto simp: continuous_on_iff)
  then have cont: "continuous_on ?D (\<lambda>x. dist ((g \<circ> fst) x) (snd x))"
    unfolding continuous_on_eq_continuous_within
    by (intro continuous_dist ballI continuous_within_compose)
       (auto intro!: continuous_fst continuous_snd continuous_ident simp: image_image)

  obtain a where "a \<in> s" and le: "\<And>x. x \<in> s \<Longrightarrow> dist (g a) a \<le> dist (g x) x"
    using continuous_attains_inf[OF D cont] by auto

  have "g a = a"
  proof (rule ccontr)
    assume "g a \<noteq> a"
    with \<open>a \<in> s\<close> gs have "dist (g (g a)) (g a) < dist (g a) a"
      by (intro dist[rule_format]) auto
    moreover have "dist (g a) a \<le> dist (g (g a)) (g a)"
      using \<open>a \<in> s\<close> gs by (intro le) auto
    ultimately show False by auto
  qed
  moreover have "\<And>x. x \<in> s \<Longrightarrow> g x = x \<Longrightarrow> x = a"
    using dist[THEN bspec[where x=a]] \<open>g a = a\<close> and \<open>a\<in>s\<close> by auto
  ultimately show "\<exists>!x\<in>s. g x = x"
    using \<open>a \<in> s\<close> by blast
qed


lemma cball_subset_cball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "cball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r < 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "r < 0")
    case True
    then show ?rhs by simp
  next
    case False
    then have [simp]: "r \<ge> 0" by simp
    have "norm (a - a') + r \<le> r'"
    proof (cases "a = a'")
      case True
      then show ?thesis
        using subsetD [where c = "a + r *\<^sub>R (SOME i. i \<in> Basis)", OF \<open>?lhs\<close>] subsetD [where c = a, OF \<open>?lhs\<close>]
        by (force simp: SOME_Basis dist_norm)
    next
      case False
      have "norm (a' - (a + (r / norm (a - a')) *\<^sub>R (a - a'))) = norm (a' - a - (r / norm (a - a')) *\<^sub>R (a - a'))"
        by (simp add: algebra_simps)
      also have "... = norm ((-1 - (r / norm (a - a'))) *\<^sub>R (a - a'))"
        by (simp add: algebra_simps)
      also from \<open>a \<noteq> a'\<close> have "... = \<bar>- norm (a - a') - r\<bar>"
        by (simp add: abs_mult_pos field_simps)
      finally have [simp]: "norm (a' - (a + (r / norm (a - a')) *\<^sub>R (a - a'))) = \<bar>norm (a - a') + r\<bar>"
        by linarith
      from \<open>a \<noteq> a'\<close> show ?thesis
        using subsetD [where c = "a' + (1 + r / norm(a - a')) *\<^sub>R (a - a')", OF \<open>?lhs\<close>]
        by (simp add: dist_norm scaleR_add_left)
    qed
    then show ?rhs
      by (simp add: dist_norm)
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp: ball_def dist_norm)
      (metis add.commute add_le_cancel_right dist_norm dist_triangle3 order_trans)
qed

lemma cball_subset_ball_iff: "cball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r < r' \<or> r < 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for a :: "'a::euclidean_space"
proof
  assume ?lhs
  then show ?rhs
  proof (cases "r < 0")
    case True then
    show ?rhs by simp
  next
    case False
    then have [simp]: "r \<ge> 0" by simp
    have "norm (a - a') + r < r'"
    proof (cases "a = a'")
      case True
      then show ?thesis
        using subsetD [where c = "a + r *\<^sub>R (SOME i. i \<in> Basis)", OF \<open>?lhs\<close>] subsetD [where c = a, OF \<open>?lhs\<close>]
        by (force simp: SOME_Basis dist_norm)
    next
      case False
      have False if "norm (a - a') + r \<ge> r'"
      proof -
        from that have "\<bar>r' - norm (a - a')\<bar> \<le> r"
          by (simp split: abs_split)
            (metis \<open>0 \<le> r\<close> \<open>?lhs\<close> centre_in_cball dist_commute dist_norm less_asym mem_ball subset_eq)
        then show ?thesis
          using subsetD [where c = "a + (r' / norm(a - a') - 1) *\<^sub>R (a - a')", OF \<open>?lhs\<close>] \<open>a \<noteq> a'\<close>
          by (simp add: dist_norm field_simps)
            (simp add: diff_divide_distrib scaleR_left_diff_distrib)
      qed
      then show ?thesis by force
    qed
    then show ?rhs by (simp add: dist_norm)
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp: ball_def dist_norm)
      (metis add.commute add_le_cancel_right dist_norm dist_triangle3 le_less_trans)
qed

lemma ball_subset_cball_iff: "ball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
  (is "?lhs = ?rhs")
  for a :: "'a::euclidean_space"
proof (cases "r \<le> 0")
  case True
  then show ?thesis
    using dist_not_less_zero less_le_trans by force
next
  case False
  show ?thesis
  proof
    assume ?lhs
    then have "(cball a r \<subseteq> cball a' r')"
      by (metis False closed_cball closure_ball closure_closed closure_mono not_less)
    with False show ?rhs
      by (fastforce iff: cball_subset_cball_iff)
  next
    assume ?rhs
    with False show ?lhs
      using ball_subset_cball cball_subset_cball_iff by blast
  qed
qed

lemma ball_subset_ball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "ball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
        (is "?lhs = ?rhs")
proof (cases "r \<le> 0")
  case True then show ?thesis
    using dist_not_less_zero less_le_trans by force
next
  case False show ?thesis
  proof
    assume ?lhs
    then have "0 < r'"
      by (metis (no_types) False \<open>?lhs\<close> centre_in_ball dist_norm le_less_trans mem_ball norm_ge_zero not_less set_mp)
    then have "(cball a r \<subseteq> cball a' r')"
      by (metis False\<open>?lhs\<close> closure_ball closure_mono not_less)
    then show ?rhs
      using False cball_subset_cball_iff by fastforce
  next
  assume ?rhs then show ?lhs
    apply (auto simp: ball_def)
    apply (metis add.commute add_le_cancel_right dist_commute dist_triangle_lt not_le order_trans)
    using dist_not_less_zero order.strict_trans2 apply blast
    done
  qed
qed


lemma ball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = ball y e \<longleftrightarrow> d \<le> 0 \<and> e \<le> 0 \<or> x=y \<and> d=e"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "d \<le> 0 \<or> e \<le> 0")
    case True
      with \<open>?lhs\<close> show ?rhs
        by safe (simp_all only: ball_eq_empty [of y e, symmetric] ball_eq_empty [of x d, symmetric])
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      apply (auto simp: set_eq_subset ball_subset_ball_iff dist_norm norm_minus_commute algebra_simps)
      apply (metis add_le_same_cancel1 le_add_same_cancel1 norm_ge_zero norm_pths(2) order_trans)
      apply (metis add_increasing2 add_le_imp_le_right eq_iff norm_ge_zero)
      done
  qed
next
  assume ?rhs then show ?lhs
    by (auto simp: set_eq_subset ball_subset_ball_iff)
qed

lemma cball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = cball y e \<longleftrightarrow> d < 0 \<and> e < 0 \<or> x=y \<and> d=e"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "d < 0 \<or> e < 0")
    case True
      with \<open>?lhs\<close> show ?rhs
        by safe (simp_all only: cball_eq_empty [of y e, symmetric] cball_eq_empty [of x d, symmetric])
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      apply (auto simp: set_eq_subset cball_subset_cball_iff dist_norm norm_minus_commute algebra_simps)
      apply (metis add_le_same_cancel1 le_add_same_cancel1 norm_ge_zero norm_pths(2) order_trans)
      apply (metis add_increasing2 add_le_imp_le_right eq_iff norm_ge_zero)
      done
  qed
next
  assume ?rhs then show ?lhs
    by (auto simp: set_eq_subset cball_subset_cball_iff)
qed

lemma ball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = cball y e \<longleftrightarrow> d \<le> 0 \<and> e < 0" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (auto simp: set_eq_subset ball_subset_cball_iff cball_subset_ball_iff algebra_simps)
    apply (metis add_increasing2 add_le_cancel_right add_less_same_cancel1 dist_not_less_zero less_le_trans zero_le_dist)
    apply (metis add_less_same_cancel1 dist_not_less_zero less_le_trans not_le)
    using \<open>?lhs\<close> ball_eq_empty cball_eq_empty apply blast+
    done
next
  assume ?rhs then show ?lhs by auto
qed

lemma cball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = ball y e \<longleftrightarrow> d < 0 \<and> e \<le> 0"
  using ball_eq_cball_iff by blast

lemma finite_ball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>ball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
proof -
  obtain e1 where "0 < e1" and e1_b:"ball p e1 \<subseteq> S"
    using open_contains_ball_eq[OF \<open>open S\<close>] assms by auto
  obtain e2 where "0 < e2" and "\<forall>x\<in>X. x \<noteq> p \<longrightarrow> e2 \<le> dist p x"
    using finite_set_avoid[OF \<open>finite X\<close>,of p] by auto
  hence "\<forall>w\<in>ball p (min e1 e2). w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)" using e1_b by auto
  thus "\<exists>e>0. \<forall>w\<in>ball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> X)" using \<open>e2>0\<close> \<open>e1>0\<close>
    apply (rule_tac x="min e1 e2" in exI)
    by auto
qed

lemma finite_cball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>cball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
proof -
  obtain e1 where "e1>0" and e1: "\<forall>w\<in>ball p e1. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
    using finite_ball_avoid[OF assms] by auto
  define e2 where "e2 \<equiv> e1/2"
  have "e2>0" and "e2 < e1" unfolding e2_def using \<open>e1>0\<close> by auto
  then have "cball p e2 \<subseteq> ball p e1" by (subst cball_subset_ball_iff,auto)
  then show "\<exists>e>0. \<forall>w\<in>cball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> X)" using \<open>e2>0\<close> e1 by auto
qed

subsection\<open>Various separability-type properties\<close>

lemma univ_second_countable:
  obtains \<B> :: "'a::euclidean_space set set"
  where "countable \<B>" "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
       "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
by (metis ex_countable_basis topological_basis_def)

lemma subset_second_countable:
  obtains \<B> :: "'a:: euclidean_space set set"
    where "countable \<B>"
          "{} \<notin> \<B>"
          "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
          "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>"
      and opeB: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
      and \<B>:    "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
  proof -
    obtain \<C> :: "'a set set"
      where "countable \<C>" and ope: "\<And>C. C \<in> \<C> \<Longrightarrow> open C"
        and \<C>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<C> \<and> S = \<Union>U"
      by (metis univ_second_countable that)
    show ?thesis
    proof
      show "countable ((\<lambda>C. S \<inter> C) ` \<C>)"
        by (simp add: \<open>countable \<C>\<close>)
      show "\<And>C. C \<in> op \<inter> S ` \<C> \<Longrightarrow> openin (subtopology euclidean S) C"
        using ope by auto
      show "\<And>T. openin (subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>\<subseteq>op \<inter> S ` \<C>. T = \<Union>\<U>"
        by (metis \<C> image_mono inf_Sup openin_open)
    qed
  qed
  show ?thesis
  proof
    show "countable (\<B> - {{}})"
      using \<open>countable \<B>\<close> by blast
    show "\<And>C. \<lbrakk>C \<in> \<B> - {{}}\<rbrakk> \<Longrightarrow> openin (subtopology euclidean S) C"
      by (simp add: \<open>\<And>C. C \<in> \<B> \<Longrightarrow> openin (subtopology euclidean S) C\<close>)
    show "\<exists>\<U>\<subseteq>\<B> - {{}}. T = \<Union>\<U>" if "openin (subtopology euclidean S) T" for T
      using \<B> [OF that]
      apply clarify
      apply (rule_tac x="\<U> - {{}}" in exI, auto)
        done
  qed auto
qed

lemma univ_second_countable_sequence:
  obtains B :: "nat \<Rightarrow> 'a::euclidean_space set"
    where "inj B" "\<And>n. open(B n)" "\<And>S. open S \<Longrightarrow> \<exists>k. S = \<Union>{B n |n. n \<in> k}"
proof -
  obtain \<B> :: "'a set set"
  where "countable \<B>"
    and op: "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
    and Un: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
    using univ_second_countable by blast
  have *: "infinite (range (\<lambda>n. ball (0::'a) (inverse(Suc n))))"
    apply (rule Infinite_Set.range_inj_infinite)
    apply (simp add: inj_on_def ball_eq_ball_iff)
    done
  have "infinite \<B>"
  proof
    assume "finite \<B>"
    then have "finite (Union ` (Pow \<B>))"
      by simp
    then have "finite (range (\<lambda>n. ball (0::'a) (inverse(Suc n))))"
      apply (rule rev_finite_subset)
      by (metis (no_types, lifting) PowI image_eqI image_subset_iff Un [OF open_ball])
    with * show False by simp
  qed
  obtain f :: "nat \<Rightarrow> 'a set" where "\<B> = range f" "inj f"
    by (blast intro: countable_as_injective_image [OF \<open>countable \<B>\<close> \<open>infinite \<B>\<close>])
  have *: "\<exists>k. S = \<Union>{f n |n. n \<in> k}" if "open S" for S
    using Un [OF that]
    apply clarify
    apply (rule_tac x="f-`U" in exI)
    using \<open>inj f\<close> \<open>\<B> = range f\<close> apply force
    done
  show ?thesis
    apply (rule that [OF \<open>inj f\<close> _ *])
    apply (auto simp: \<open>\<B> = range f\<close> op)
    done
qed

proposition separable:
  fixes S :: "'a:: euclidean_space set"
  obtains T where "countable T" "T \<subseteq> S" "S \<subseteq> closure T"
proof -
  obtain \<B> :: "'a:: euclidean_space set set"
    where "countable \<B>"
      and "{} \<notin> \<B>"
      and ope: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
      and if_ope: "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
    by (meson subset_second_countable)
  then obtain f where f: "\<And>C. C \<in> \<B> \<Longrightarrow> f C \<in> C"
    by (metis equals0I)
  show ?thesis
  proof
    show "countable (f ` \<B>)"
      by (simp add: \<open>countable \<B>\<close>)
    show "f ` \<B> \<subseteq> S"
      using ope f openin_imp_subset by blast
    show "S \<subseteq> closure (f ` \<B>)"
    proof (clarsimp simp: closure_approachable)
      fix x and e::real
      assume "x \<in> S" "0 < e"
      have "openin (subtopology euclidean S) (S \<inter> ball x e)"
        by (simp add: openin_Int_open)
      with if_ope obtain \<U> where  \<U>: "\<U> \<subseteq> \<B>" "S \<inter> ball x e = \<Union>\<U>"
        by meson
      show "\<exists>C \<in> \<B>. dist (f C) x < e"
      proof (cases "\<U> = {}")
        case True
        then show ?thesis
          using \<open>0 < e\<close>  \<U> \<open>x \<in> S\<close> by auto
      next
        case False
        then obtain C where "C \<in> \<U>" by blast
        show ?thesis
        proof
          show "dist (f C) x < e"
            by (metis Int_iff Union_iff \<U> \<open>C \<in> \<U>\<close> dist_commute f mem_ball subsetCE)
          show "C \<in> \<B>"
            using \<open>\<U> \<subseteq> \<B>\<close> \<open>C \<in> \<U>\<close> by blast
        qed
      qed
    qed
  qed
qed

proposition Lindelof:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> open S"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>" "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
      and \<B>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
    using univ_second_countable by blast
  define \<D> where "\<D> \<equiv> {S. S \<in> \<B> \<and> (\<exists>U. U \<in> \<F> \<and> S \<subseteq> U)}"
  have "countable \<D>"
    apply (rule countable_subset [OF _ \<open>countable \<B>\<close>])
    apply (force simp: \<D>_def)
    done
  have "\<And>S. \<exists>U. S \<in> \<D> \<longrightarrow> U \<in> \<F> \<and> S \<subseteq> U"
    by (simp add: \<D>_def)
  then obtain G where G: "\<And>S. S \<in> \<D> \<longrightarrow> G S \<in> \<F> \<and> S \<subseteq> G S"
    by metis
  have "\<Union>\<F> \<subseteq> \<Union>\<D>"
    unfolding \<D>_def by (blast dest: \<F> \<B>)
  moreover have "\<Union>\<D> \<subseteq> \<Union>\<F>"
    using \<D>_def by blast
  ultimately have eq1: "\<Union>\<F> = \<Union>\<D>" ..
  have eq2: "\<Union>\<D> = UNION \<D> G"
    using G eq1 by auto
  show ?thesis
    apply (rule_tac \<F>' = "G ` \<D>" in that)
    using G \<open>countable \<D>\<close>  apply (auto simp: eq1 eq2)
    done
qed

lemma Lindelof_openin:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> openin (subtopology euclidean U) S"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
proof -
  have "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>T. open T \<and> S = U \<inter> T"
    using assms by (simp add: openin_open)
  then obtain tf where tf: "\<And>S. S \<in> \<F> \<Longrightarrow> open (tf S) \<and> (S = U \<inter> tf S)"
    by metis
  have [simp]: "\<And>\<F>'. \<F>' \<subseteq> \<F> \<Longrightarrow> \<Union>\<F>' = U \<inter> \<Union>(tf ` \<F>')"
    using tf by fastforce
  obtain \<G> where "countable \<G> \<and> \<G> \<subseteq> tf ` \<F>" "\<Union>\<G> = UNION \<F> tf"
    using tf by (force intro: Lindelof [of "tf ` \<F>"])
  then obtain \<F>' where \<F>': "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
    by (clarsimp simp add: countable_subset_image)
  then show ?thesis ..
qed

lemma countable_disjoint_open_subsets:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> open S" and pw: "pairwise disjnt \<F>"
    shows "countable \<F>"
proof -
  obtain \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
    by (meson assms Lindelof)
  with pw have "\<F> \<subseteq> insert {} \<F>'"
    by (fastforce simp add: pairwise_def disjnt_iff)
  then show ?thesis
    by (simp add: \<open>countable \<F>'\<close> countable_subset)
qed

lemma closedin_compact:
   "\<lbrakk>compact S; closedin (subtopology euclidean S) T\<rbrakk> \<Longrightarrow> compact T"
by (metis closedin_closed compact_Int_closed)

lemma closedin_compact_eq:
  fixes S :: "'a::t2_space set"
  shows
   "compact S
         \<Longrightarrow> (closedin (subtopology euclidean S) T \<longleftrightarrow>
              compact T \<and> T \<subseteq> S)"
by (metis closedin_imp_subset closedin_compact closed_subset compact_imp_closed)

lemma continuous_imp_closed_map:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "closedin (subtopology euclidean S) U"
          "continuous_on S f" "image f S = T" "compact S"
    shows "closedin (subtopology euclidean T) (image f U)"
  by (metis assms closedin_compact_eq compact_continuous_image continuous_on_subset subset_image_iff)

lemma continuous_imp_quotient_map:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on S f" "image f S = T" "compact S" "U \<subseteq> T"
    shows "openin (subtopology euclidean S) {x. x \<in> S \<and> f x \<in> U} \<longleftrightarrow>
           openin (subtopology euclidean T) U"
  by (metis (no_types, lifting) Collect_cong assms closed_map_imp_quotient_map continuous_imp_closed_map)

subsection\<open> Finite intersection property\<close>

text\<open>Also developed in HOL's toplogical spaces theory, but the Heine-Borel type class isn't available there.\<close>

lemma closed_imp_fip:
  fixes S :: "'a::heine_borel set"
  assumes "closed S"
      and T: "T \<in> \<F>" "bounded T"
      and clof: "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      and none: "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F>' \<noteq> {}"
    shows "S \<inter> \<Inter>\<F> \<noteq> {}"
proof -
  have "compact (S \<inter> T)"
    using \<open>closed S\<close> clof compact_eq_bounded_closed T by blast
  then have "(S \<inter> T) \<inter> \<Inter>\<F> \<noteq> {}"
    apply (rule compact_imp_fip)
     apply (simp add: clof)
    by (metis Int_assoc complete_lattice_class.Inf_insert finite_insert insert_subset none \<open>T \<in> \<F>\<close>)
  then show ?thesis by blast
qed

lemma clconnected_closedin_eqosed_imp_fip_compact:
  fixes S :: "'a::heine_borel set"
  shows
   "\<lbrakk>closed S; \<And>T. T \<in> \<F> \<Longrightarrow> compact T;
     \<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F>' \<noteq> {}\<rbrakk>
        \<Longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}"
by (metis Inf_greatest closed_imp_fip compact_eq_bounded_closed empty_subsetI finite.emptyI inf.orderE)

lemma closed_fip_heine_borel:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "closed S" "T \<in> \<F>" "bounded T"
      and "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      and "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> \<Inter>\<F>' \<noteq> {}"
    shows "\<Inter>\<F> \<noteq> {}"
proof -
  have "UNIV \<inter> \<Inter>\<F> \<noteq> {}"
    using assms closed_imp_fip [OF closed_UNIV] by auto
  then show ?thesis by simp
qed

lemma compact_fip_heine_borel:
  fixes \<F> :: "'a::heine_borel set set"
  assumes clof: "\<And>T. T \<in> \<F> \<Longrightarrow> compact T"
      and none: "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> \<Inter>\<F>' \<noteq> {}"
    shows "\<Inter>\<F> \<noteq> {}"
by (metis InterI all_not_in_conv clof closed_fip_heine_borel compact_eq_bounded_closed none)

lemma compact_sequence_with_limit:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel"
  shows "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> compact (insert l (range f))"
apply (simp add: compact_eq_bounded_closed, auto)
apply (simp add: convergent_imp_bounded)
by (simp add: closed_limpt islimpt_insert sequence_unique_limpt)


subsection\<open>Componentwise limits and continuity\<close>

text\<open>But is the premise really necessary? Need to generalise @{thm euclidean_dist_l2}\<close>
lemma Euclidean_dist_upper: "i \<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  by (metis (no_types) member_le_setL2 euclidean_dist_l2 finite_Basis)

text\<open>But is the premise @{term \<open>i \<in> Basis\<close>} really necessary?\<close>
lemma open_preimage_inner:
  assumes "open S" "i \<in> Basis"
    shows "open {x. x \<bullet> i \<in> S}"
proof (rule openI, simp)
  fix x
  assume x: "x \<bullet> i \<in> S"
  with assms obtain e where "0 < e" and e: "ball (x \<bullet> i) e \<subseteq> S"
    by (auto simp: open_contains_ball_eq)
  have "\<exists>e>0. ball (y \<bullet> i) e \<subseteq> S" if dxy: "dist x y < e / 2" for y
  proof (intro exI conjI)
    have "dist (x \<bullet> i) (y \<bullet> i) < e / 2"
      by (meson \<open>i \<in> Basis\<close> dual_order.trans Euclidean_dist_upper not_le that)
    then have "dist (x \<bullet> i) z < e" if "dist (y \<bullet> i) z < e / 2" for z
      by (metis dist_commute dist_triangle_half_l that)
    then have "ball (y \<bullet> i) (e / 2) \<subseteq> ball (x \<bullet> i) e"
      using mem_ball by blast
      with e show "ball (y \<bullet> i) (e / 2) \<subseteq> S"
        by (metis order_trans)
  qed (simp add: \<open>0 < e\<close>)
  then show "\<exists>e>0. ball x e \<subseteq> {s. s \<bullet> i \<in> S}"
    by (metis (no_types, lifting) \<open>0 < e\<close> \<open>open S\<close> half_gt_zero_iff mem_Collect_eq mem_ball open_contains_ball_eq subsetI)
qed

proposition tendsto_componentwise_iff:
  fixes f :: "_ \<Rightarrow> 'b::euclidean_space"
  shows "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>i \<in> Basis. ((\<lambda>x. (f x \<bullet> i)) \<longlongrightarrow> (l \<bullet> i)) F)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding tendsto_def
    apply clarify
    apply (drule_tac x="{s. s \<bullet> i \<in> S}" in spec)
    apply (auto simp: open_preimage_inner)
    done
next
  assume R: ?rhs
  then have "\<And>e. e > 0 \<Longrightarrow> \<forall>i\<in>Basis. \<forall>\<^sub>F x in F. dist (f x \<bullet> i) (l \<bullet> i) < e"
    unfolding tendsto_iff by blast
  then have R': "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F x in F. \<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e"
      by (simp add: eventually_ball_finite_distrib [symmetric])
  show ?lhs
  unfolding tendsto_iff
  proof clarify
    fix e::real
    assume "0 < e"
    have *: "setL2 (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis < e"
             if "\<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e / real DIM('b)" for x
    proof -
      have "setL2 (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis \<le> sum (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis"
        by (simp add: setL2_le_sum)
      also have "... < DIM('b) * (e / real DIM('b))"
        apply (rule sum_bounded_above_strict)
        using that by auto
      also have "... = e"
        by (simp add: field_simps)
      finally show "setL2 (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis < e" .
    qed
    have "\<forall>\<^sub>F x in F. \<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e / DIM('b)"
      apply (rule R')
      using \<open>0 < e\<close> by simp
    then show "\<forall>\<^sub>F x in F. dist (f x) l < e"
      apply (rule eventually_mono)
      apply (subst euclidean_dist_l2)
      using * by blast
  qed
qed


corollary continuous_componentwise:
   "continuous F f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous F (\<lambda>x. (f x \<bullet> i)))"
by (simp add: continuous_def tendsto_componentwise_iff [symmetric])

corollary continuous_on_componentwise:
  fixes S :: "'a :: t2_space set"
  shows "continuous_on S f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous_on S (\<lambda>x. (f x \<bullet> i)))"
  apply (simp add: continuous_on_eq_continuous_within)
  using continuous_componentwise by blast

lemma linear_componentwise_iff:
     "(linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. linear (\<lambda>x. f' x \<bullet> i))"
  apply (auto simp: linear_iff inner_left_distrib)
   apply (metis inner_left_distrib euclidean_eq_iff)
  by (metis euclidean_eqI inner_scaleR_left)

lemma bounded_linear_componentwise_iff:
     "(bounded_linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. bounded_linear (\<lambda>x. f' x \<bullet> i))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: bounded_linear_inner_left_comp)
next
  assume ?rhs
  then have "(\<forall>i\<in>Basis. \<exists>K. \<forall>x. \<bar>f' x \<bullet> i\<bar> \<le> norm x * K)" "linear f'"
    by (auto simp: bounded_linear_def bounded_linear_axioms_def linear_componentwise_iff [symmetric] ball_conj_distrib)
  then obtain F where F: "\<And>i x. i \<in> Basis \<Longrightarrow> \<bar>f' x \<bullet> i\<bar> \<le> norm x * F i"
    by metis
  have "norm (f' x) \<le> norm x * sum F Basis" for x
  proof -
    have "norm (f' x) \<le> (\<Sum>i\<in>Basis. \<bar>f' x \<bullet> i\<bar>)"
      by (rule norm_le_l1)
    also have "... \<le> (\<Sum>i\<in>Basis. norm x * F i)"
      by (metis F sum_mono)
    also have "... = norm x * sum F Basis"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  then show ?lhs
    by (force simp: bounded_linear_def bounded_linear_axioms_def \<open>linear f'\<close>)
qed

subsection\<open>Pasting functions together\<close>

subsubsection\<open>on open sets\<close>

lemma pasting_lemma:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes clo: "\<And>i. i \<in> I \<Longrightarrow> openin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_on S g"
proof (clarsimp simp: continuous_openin_preimage_eq)
  fix U :: "'b set"
  assume "open U"
  have S: "\<And>i. i \<in> I \<Longrightarrow> (T i) \<subseteq> S"
    using clo openin_imp_subset by blast
  have *: "{x \<in> S. g x \<in> U} = \<Union>{{x. x \<in> (T i) \<and> (f i x) \<in> U} |i. i \<in> I}"
    apply (auto simp: dest: S)
      apply (metis (no_types, lifting) g mem_Collect_eq)
    using clo f g openin_imp_subset by fastforce
  show "openin (subtopology euclidean S) {x \<in> S. g x \<in> U}"
    apply (subst *)
    apply (rule openin_Union, clarify)
    apply (metis (full_types) \<open>open U\<close> cont clo openin_trans continuous_openin_preimage_gen)
    done
qed

lemma pasting_lemma_exists:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes S: "S \<subseteq> (\<Union>i \<in> I. T i)"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> openin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_on S g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> S \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_on S (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma [OF clo cont])
     apply (blast intro: f)+
    apply (metis (mono_tags, lifting) S UN_iff subsetCE someI)
    done
next
  fix x i
  assume "i \<in> I" "x \<in> S \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed

subsubsection\<open>Likewise on closed sets, with a finiteness assumption\<close>

lemma pasting_lemma_closed:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "finite I"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_on S g"
proof (clarsimp simp: continuous_closedin_preimage_eq)
  fix U :: "'b set"
  assume "closed U"
  have *: "{x \<in> S. g x \<in> U} = \<Union>{{x. x \<in> (T i) \<and> (f i x) \<in> U} |i. i \<in> I}"
    apply auto
    apply (metis (no_types, lifting) g mem_Collect_eq)
    using clo closedin_closed apply blast
    apply (metis Int_iff f g clo closedin_limpt inf.absorb_iff2)
    done
  show "closedin (subtopology euclidean S) {x \<in> S. g x \<in> U}"
    apply (subst *)
    apply (rule closedin_Union)
    using \<open>finite I\<close> apply simp
    apply (blast intro: \<open>closed U\<close> continuous_closedin_preimage cont clo closedin_trans)
    done
qed

lemma pasting_lemma_exists_closed:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "finite I"
      and S: "S \<subseteq> (\<Union>i \<in> I. T i)"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_on S g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> S \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_on S (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma_closed [OF \<open>finite I\<close> clo cont])
     apply (blast intro: f)+
    apply (metis (mono_tags, lifting) S UN_iff subsetCE someI)
    done
next
  fix x i
  assume "i \<in> I" "x \<in> S \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed

lemma tube_lemma:
  assumes "compact K"
  assumes "open W"
  assumes "{x0} \<times> K \<subseteq> W"
  shows "\<exists>X0. x0 \<in> X0 \<and> open X0 \<and> X0 \<times> K \<subseteq> W"
proof -
  {
    fix y assume "y \<in> K"
    then have "(x0, y) \<in> W" using assms by auto
    with \<open>open W\<close>
    have "\<exists>X0 Y. open X0 \<and> open Y \<and> x0 \<in> X0 \<and> y \<in> Y \<and> X0 \<times> Y \<subseteq> W"
      by (rule open_prod_elim) blast
  }
  then obtain X0 Y where
    *: "\<forall>y \<in> K. open (X0 y) \<and> open (Y y) \<and> x0 \<in> X0 y \<and> y \<in> Y y \<and> X0 y \<times> Y y \<subseteq> W"
    by metis
  from * have "\<forall>t\<in>Y ` K. open t" "K \<subseteq> \<Union>(Y ` K)" by auto
  with \<open>compact K\<close> obtain CC where CC: "CC \<subseteq> Y ` K" "finite CC" "K \<subseteq> \<Union>CC"
    by (meson compactE)
  then obtain c where c: "\<And>C. C \<in> CC \<Longrightarrow> c C \<in> K \<and> C = Y (c C)"
    by (force intro!: choice)
  with * CC show ?thesis
    by (force intro!: exI[where x="\<Inter>C\<in>CC. X0 (c C)"]) (* SLOW *)
qed

lemma continuous_on_prod_compactE:
  fixes fx::"'a::topological_space \<times> 'b::topological_space \<Rightarrow> 'c::metric_space"
    and e::real
  assumes cont_fx: "continuous_on (U \<times> C) fx"
  assumes "compact C"
  assumes [intro]: "x0 \<in> U"
  notes [continuous_intros] = continuous_on_compose2[OF cont_fx]
  assumes "e > 0"
  obtains X0 where "x0 \<in> X0" "open X0"
    "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
proof -
  define psi where "psi = (\<lambda>(x, t). dist (fx (x, t)) (fx (x0, t)))"
  define W0 where "W0 = {(x, t) \<in> U \<times> C. psi (x, t) < e}"
  have W0_eq: "W0 = psi -` {..<e} \<inter> U \<times> C"
    by (auto simp: vimage_def W0_def)
  have "open {..<e}" by simp
  have "continuous_on (U \<times> C) psi"
    by (auto intro!: continuous_intros simp: psi_def split_beta')
  from this[unfolded continuous_on_open_invariant, rule_format, OF \<open>open {..<e}\<close>]
  obtain W where W: "open W" "W \<inter> U \<times> C = W0 \<inter> U \<times> C"
    unfolding W0_eq by blast
  have "{x0} \<times> C \<subseteq> W \<inter> U \<times> C"
    unfolding W
    by (auto simp: W0_def psi_def \<open>0 < e\<close>)
  then have "{x0} \<times> C \<subseteq> W" by blast
  from tube_lemma[OF \<open>compact C\<close> \<open>open W\<close> this]
  obtain X0 where X0: "x0 \<in> X0" "open X0" "X0 \<times> C \<subseteq> W"
    by blast

  have "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
  proof safe
    fix x assume x: "x \<in> X0" "x \<in> U"
    fix t assume t: "t \<in> C"
    have "dist (fx (x, t)) (fx (x0, t)) = psi (x, t)"
      by (auto simp: psi_def)
    also
    {
      have "(x, t) \<in> X0 \<times> C"
        using t x
        by auto
      also note \<open>\<dots> \<subseteq> W\<close>
      finally have "(x, t) \<in> W" .
      with t x have "(x, t) \<in> W \<inter> U \<times> C"
        by blast
      also note \<open>W \<inter> U \<times> C = W0 \<inter> U \<times> C\<close>
      finally  have "psi (x, t) < e"
        by (auto simp: W0_def)
    }
    finally show "dist (fx (x, t)) (fx (x0, t)) \<le> e" by simp
  qed
  from X0(1,2) this show ?thesis ..
qed


subsection\<open>Constancy of a function from a connected set into a finite, disconnected or discrete set\<close>

text\<open>Still missing: versions for a set that is smaller than R, or countable.\<close>

lemma continuous_disconnected_range_constant:
  assumes S: "connected S"
      and conf: "continuous_on S f"
      and fim: "f ` S \<subseteq> t"
      and cct: "\<And>y. y \<in> t \<Longrightarrow> connected_component_set t y = {y}"
    shows "\<exists>a. \<forall>x \<in> S. f x = a"
proof (cases "S = {}")
  case True then show ?thesis by force
next
  case False
  { fix x assume "x \<in> S"
    then have "f ` S \<subseteq> {f x}"
    by (metis connected_continuous_image conf connected_component_maximal fim image_subset_iff rev_image_eqI S cct)
  }
  with False show ?thesis
    by blast
qed

lemma discrete_subset_disconnected:
  fixes S :: "'a::topological_space set"
  fixes t :: "'b::real_normed_vector set"
  assumes conf: "continuous_on S f"
      and no: "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
   shows "f ` S \<subseteq> {y. connected_component_set (f ` S) y = {y}}"
proof -
  { fix x assume x: "x \<in> S"
    then obtain e where "e>0" and ele: "\<And>y. \<lbrakk>y \<in> S; f y \<noteq> f x\<rbrakk> \<Longrightarrow> e \<le> norm (f y - f x)"
      using conf no [OF x] by auto
    then have e2: "0 \<le> e / 2"
      by simp
    have "f y = f x" if "y \<in> S" and ccs: "f y \<in> connected_component_set (f ` S) (f x)" for y
      apply (rule ccontr)
      using connected_closed [of "connected_component_set (f ` S) (f x)"] \<open>e>0\<close>
      apply (simp add: del: ex_simps)
      apply (drule spec [where x="cball (f x) (e / 2)"])
      apply (drule spec [where x="- ball(f x) e"])
      apply (auto simp: dist_norm open_closed [symmetric] simp del: le_divide_eq_numeral1 dest!: connected_component_in)
        apply (metis diff_self e2 ele norm_minus_commute norm_zero not_less)
       using centre_in_cball connected_component_refl_eq e2 x apply blast
      using ccs
      apply (force simp: cball_def dist_norm norm_minus_commute dest: ele [OF \<open>y \<in> S\<close>])
      done
    moreover have "connected_component_set (f ` S) (f x) \<subseteq> f ` S"
      by (auto simp: connected_component_in)
    ultimately have "connected_component_set (f ` S) (f x) = {f x}"
      by (auto simp: x)
  }
  with assms show ?thesis
    by blast
qed

lemma finite_implies_discrete:
  fixes S :: "'a::topological_space set"
  assumes "finite (f ` S)"
  shows "(\<forall>x \<in> S. \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x))"
proof -
  have "\<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)" if "x \<in> S" for x
  proof (cases "f ` S - {f x} = {}")
    case True
    with zero_less_numeral show ?thesis
      by (fastforce simp add: Set.image_subset_iff cong: conj_cong)
  next
    case False
    then obtain z where z: "z \<in> S" "f z \<noteq> f x"
      by blast
    have finn: "finite {norm (z - f x) |z. z \<in> f ` S - {f x}}"
      using assms by simp
    then have *: "0 < Inf{norm(z - f x) | z. z \<in> f ` S - {f x}}"
      apply (rule finite_imp_less_Inf)
      using z apply force+
      done
    show ?thesis
      by (force intro!: * cInf_le_finite [OF finn])
  qed
  with assms show ?thesis
    by blast
qed

text\<open>This proof requires the existence of two separate values of the range type.\<close>
lemma finite_range_constant_imp_connected:
  assumes "\<And>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
              \<lbrakk>continuous_on S f; finite(f ` S)\<rbrakk> \<Longrightarrow> \<exists>a. \<forall>x \<in> S. f x = a"
    shows "connected S"
proof -
  { fix t u
    assume clt: "closedin (subtopology euclidean S) t"
       and clu: "closedin (subtopology euclidean S) u"
       and tue: "t \<inter> u = {}" and tus: "t \<union> u = S"
    have conif: "continuous_on S (\<lambda>x. if x \<in> t then 0 else 1)"
      apply (subst tus [symmetric])
      apply (rule continuous_on_cases_local)
      using clt clu tue
      apply (auto simp: tus continuous_on_const)
      done
    have fi: "finite ((\<lambda>x. if x \<in> t then 0 else 1) ` S)"
      by (rule finite_subset [of _ "{0,1}"]) auto
    have "t = {} \<or> u = {}"
      using assms [OF conif fi] tus [symmetric]
      by (auto simp: Ball_def) (metis IntI empty_iff one_neq_zero tue)
  }
  then show ?thesis
    by (simp add: connected_closedin_eq)
qed

lemma continuous_disconnected_range_constant_eq:
      "(connected S \<longleftrightarrow>
           (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
            \<forall>t. continuous_on S f \<and> f ` S \<subseteq> t \<and> (\<forall>y \<in> t. connected_component_set t y = {y})
            \<longrightarrow> (\<exists>a::'b. \<forall>x \<in> S. f x = a)))" (is ?thesis1)
  and continuous_discrete_range_constant_eq:
      "(connected S \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on S f \<and>
          (\<forall>x \<in> S. \<exists>e. 0 < e \<and> (\<forall>y. y \<in> S \<and> (f y \<noteq> f x) \<longrightarrow> e \<le> norm(f y - f x)))
          \<longrightarrow> (\<exists>a::'b. \<forall>x \<in> S. f x = a)))" (is ?thesis2)
  and continuous_finite_range_constant_eq:
      "(connected S \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on S f \<and> finite (f ` S)
          \<longrightarrow> (\<exists>a::'b. \<forall>x \<in> S. f x = a)))" (is ?thesis3)
proof -
  have *: "\<And>s t u v. \<lbrakk>s \<Longrightarrow> t; t \<Longrightarrow> u; u \<Longrightarrow> v; v \<Longrightarrow> s\<rbrakk>
    \<Longrightarrow> (s \<longleftrightarrow> t) \<and> (s \<longleftrightarrow> u) \<and> (s \<longleftrightarrow> v)"
    by blast
  have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
    apply (rule *)
    using continuous_disconnected_range_constant apply metis
    apply clarify
    apply (frule discrete_subset_disconnected; blast)
    apply (blast dest: finite_implies_discrete)
    apply (blast intro!: finite_range_constant_imp_connected)
    done
  then show ?thesis1 ?thesis2 ?thesis3
    by blast+
qed

lemma continuous_discrete_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes S: "connected S"
      and "continuous_on S f"
      and "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
    obtains a where "\<And>x. x \<in> S \<Longrightarrow> f x = a"
  using continuous_discrete_range_constant_eq [THEN iffD1, OF S] assms
  by blast

lemma continuous_finite_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes "connected S"
      and "continuous_on S f"
      and "finite (f ` S)"
    obtains a where "\<And>x. x \<in> S \<Longrightarrow> f x = a"
  using assms continuous_finite_range_constant_eq
  by blast



subsection \<open>Continuous Extension\<close>

definition clamp :: "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "clamp a b x = (if (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)
    then (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i)
    else a)"

lemma clamp_in_interval[simp]:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  shows "clamp a b x \<in> cbox a b"
  unfolding clamp_def
  using box_ne_empty(1)[of a b] assms by (auto simp: cbox_def)

lemma clamp_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "clamp a b x = x"
  using assms
  by (auto simp: clamp_def mem_box intro!: euclidean_eqI[where 'a='a])

lemma clamp_empty_interval:
  assumes "i \<in> Basis" "a \<bullet> i > b \<bullet> i"
  shows "clamp a b = (\<lambda>_. a)"
  using assms
  by (force simp: clamp_def[abs_def] split: if_splits intro!: ext)

lemma dist_clamps_le_dist_args:
  fixes x :: "'a::euclidean_space"
  shows "dist (clamp a b y) (clamp a b x) \<le> dist y x"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  then have "(\<Sum>i\<in>Basis. (dist (clamp a b y \<bullet> i) (clamp a b x \<bullet> i))\<^sup>2) \<le>
    (\<Sum>i\<in>Basis. (dist (y \<bullet> i) (x \<bullet> i))\<^sup>2)"
    by (auto intro!: sum_mono simp: clamp_def dist_real_def abs_le_square_iff[symmetric])
  then show ?thesis
    by (auto intro: real_sqrt_le_mono
      simp: euclidean_dist_l2[where y=x] euclidean_dist_l2[where y="clamp a b x"] setL2_def)
qed (auto simp: clamp_def)

lemma clamp_continuous_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
    and x :: 'a
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous (at x) (\<lambda>x. f (clamp a b x))"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  show ?thesis
    unfolding continuous_at_eps_delta
  proof safe
    fix x :: 'a
    fix e :: real
    assume "e > 0"
    moreover have "clamp a b x \<in> cbox a b"
      by (simp add: clamp_in_interval le)
    moreover note f_cont[simplified continuous_on_iff]
    ultimately
    obtain d where d: "0 < d"
      "\<And>x'. x' \<in> cbox a b \<Longrightarrow> dist x' (clamp a b x) < d \<Longrightarrow> dist (f x') (f (clamp a b x)) < e"
      by force
    show "\<exists>d>0. \<forall>x'. dist x' x < d \<longrightarrow>
      dist (f (clamp a b x')) (f (clamp a b x)) < e"
      using le
      by (auto intro!: d clamp_in_interval dist_clamps_le_dist_args[THEN le_less_trans])
  qed
qed (auto simp: clamp_empty_interval)

lemma clamp_continuous_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous_on S (\<lambda>x. f (clamp a b x))"
  using assms
  by (auto intro: continuous_at_imp_continuous_on clamp_continuous_at)

lemma clamp_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes bounded: "bounded (f ` (cbox a b))"
  shows "bounded (range (\<lambda>x. f (clamp a b x)))"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  from bounded obtain c where f_bound: "\<forall>x\<in>f ` cbox a b. dist undefined x \<le> c"
    by (auto simp: bounded_any_center[where a=undefined])
  then show ?thesis
    by (auto intro!: exI[where x=c] clamp_in_interval[OF le[rule_format]]
        simp: bounded_any_center[where a=undefined])
qed (auto simp: clamp_empty_interval image_def)


definition ext_cont :: "('a::euclidean_space \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  where "ext_cont f a b = (\<lambda>x. f (clamp a b x))"

lemma ext_cont_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "ext_cont f a b x = f x"
  using assms
  unfolding ext_cont_def
  by (auto simp: clamp_def mem_box intro!: euclidean_eqI[where 'a='a] arg_cong[where f=f])

lemma continuous_on_ext_cont[continuous_intros]:
  "continuous_on (cbox a b) f \<Longrightarrow> continuous_on S (ext_cont f a b)"
  by (auto intro!: clamp_continuous_on simp: ext_cont_def)

no_notation
  eucl_less (infix "<e" 50)

end
