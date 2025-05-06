(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

chapter \<open>Topology\<close>

theory Elementary_Topology
imports
  "HOL-Library.Set_Idioms"
  "HOL-Library.Disjoint_Sets"
  Product_Vector
begin

section \<open>Elementary Topology\<close>


subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Affine transformations of intervals\<close>

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
  by (metis real_affinity_eq)

lemma image_linear_greaterThan:
  fixes x::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "((\<lambda>x. c*x+b) ` {x<..}) = (if c>0 then {c*x+b <..} else {..< c*x+b})"
using  \<open>c\<noteq>0\<close>
  apply (auto simp add:image_iff field_simps)    
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
done

lemma image_linear_lessThan:
  fixes x::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "((\<lambda>x. c*x+b) ` {..<x}) = (if c>0 then {..<c*x+b} else {c*x+b<..})"
using \<open>c\<noteq>0\<close>
  apply (auto simp add:image_iff field_simps)    
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
done


subsection \<open>Topological Basis\<close>

context topological_space
begin

definition\<^marker>\<open>tag important\<close> "topological_basis B \<longleftrightarrow>
  (\<forall>b\<in>B. open b) \<and> (\<forall>x. open x \<longrightarrow> (\<exists>B'. B' \<subseteq> B \<and> \<Union>B' = x))"

lemma topological_basis:
  "topological_basis B \<longleftrightarrow> (\<forall>x. open x \<longleftrightarrow> (\<exists>B'. B' \<subseteq> B \<and> \<Union>B' = x))"
    (is "?lhs = ?rhs")
  by (metis bot.extremum cSup_singleton insert_subset open_Union subsetD
      topological_basis_def)

lemma topological_basis_iff:
  assumes "\<And>B'. B' \<in> B \<Longrightarrow> open B'"
  shows "topological_basis B \<longleftrightarrow> (\<forall>O'. open O' \<longrightarrow> (\<forall>x\<in>O'. \<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'))"
    (is "_ \<longleftrightarrow> ?rhs")
proof safe
  fix O' and x::'a
  assume H: "topological_basis B" "open O'" "x \<in> O'"
  then obtain B' where "B'\<subseteq>B" "\<Union>B' = O'"
    by (force simp add: topological_basis_def)
  then show "\<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'" 
    using H by auto
next
  assume H: ?rhs
  show "topological_basis B"
    unfolding topological_basis_def
  proof (intro conjI strip assms)
    fix O' :: "'a set"
    assume "open O'"
    with H obtain f where "\<forall>x\<in>O'. f x \<in> B \<and> x \<in> f x \<and> f x \<subseteq> O'"
      by metis
    then show "\<exists>B'\<subseteq>B. \<Union>B' = O'"
      by (auto intro: exI[where x="{f x |x. x \<in> O'}"])
  qed
qed

lemma topological_basisI:
  assumes "\<And>B'. B' \<in> B \<Longrightarrow> open B'"
    and "\<And>O' x. open O' \<Longrightarrow> x \<in> O' \<Longrightarrow> \<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'"
  shows "topological_basis B"
  by (simp add: assms topological_basis_iff)

lemma topological_basisE:
  fixes O'
  assumes "topological_basis B"
    and "open O'"
    and "x \<in> O'"
  obtains B' where "B' \<in> B" "x \<in> B'" "B' \<subseteq> O'"
  by (metis assms topological_basis_def topological_basis_iff)

lemma topological_basis_open:
  assumes "topological_basis B" and "X \<in> B"
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
  assumes "topological_basis B" and "\<And>B'. B' \<noteq> {} \<Longrightarrow> f B' \<in> B'"
  shows "\<forall>X. open X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>B' \<in> B. f B' \<in> X)"
  by (metis assms equals0D in_mono topological_basisE)

end

lemma topological_basis_prod:
  assumes A: "topological_basis A"
    and B: "topological_basis B"
  shows "topological_basis ((\<lambda>(a, b). a \<times> b) ` (A \<times> B))"
proof -
  have "\<exists>X\<subseteq>A \<times> B. (\<Union>(a,b)\<in>X. a \<times> b) = S" if "open S" for S
  proof -
    have "(x, y) \<in> (\<Union>(a, b)\<in>{X \<in> A \<times> B. fst X \<times> snd X \<subseteq> S}. a \<times> b)"
      if xy: "(x, y) \<in> S" for x y
    proof -
      obtain a b where a: "open a""x \<in> a" and b: "open b" "y \<in> b" and "a \<times> b \<subseteq> S"
        by (metis open_prod_elim[OF \<open>open S\<close>] xy mem_Sigma_iff)
      moreover obtain A0 where "A0 \<in> A" "x \<in> A0" "A0 \<subseteq> a"
        using A a b topological_basisE by blast
      moreover
      from B b obtain B0 where "B0 \<in> B" "y \<in> B0" "B0 \<subseteq> b"
        by (rule topological_basisE)
      ultimately show ?thesis
        by (intro UN_I[of "(A0, B0)"]) auto
    qed
    then have "(\<Union>(a, b)\<in>{x \<in> A \<times> B. fst x \<times> snd x \<subseteq> S}. a \<times> b) = S"
      by force
    then show ?thesis
      using subset_eq by force
  qed
  with A B open_Times show ?thesis
    unfolding topological_basis_def
    by (smt (verit) SigmaE imageE image_mono case_prod_conv)
qed


subsection \<open>Countable Basis\<close>

locale\<^marker>\<open>tag important\<close> countable_basis = topological_space p for p::"'a set \<Rightarrow> bool" +
  fixes B :: "'a set set"
  assumes is_basis: "topological_basis B"
    and countable_basis: "countable B"
begin

lemma open_countable_basis_ex:
  assumes "p X"
  shows "\<exists>B' \<subseteq> B. X = \<Union>B'"
  using assms countable_basis is_basis
  unfolding topological_basis_def by blast

lemma open_countable_basisE:
  assumes "p X"
  obtains B' where "B' \<subseteq> B" "X = \<Union>B'"
  using assms open_countable_basis_ex by auto

lemma countable_dense_exists:
  "\<exists>D::'a set. countable D \<and> (\<forall>X. p X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>d \<in> D. d \<in> X))"
proof -
  let ?f = "(\<lambda>B'. SOME x. x \<in> B')"
  have "countable (?f ` B)" using countable_basis by simp
  with basis_dense[OF is_basis, of ?f] show ?thesis
    by (intro exI[where x="?f ` B"]) (metis (mono_tags) all_not_in_conv imageI someI)
qed

lemma countable_dense_setE:
  obtains D :: "'a set"
  where "countable D" "\<And>X. p X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d \<in> D. d \<in> X"
  using countable_dense_exists by blast

end

lemma countable_basis_openI: "countable_basis open B"
  if "countable B" "topological_basis B"
  using that
  by unfold_locales
    (simp_all add: topological_basis topological_space.topological_basis topological_space_axioms)

lemma (in first_countable_topology) first_countable_basisE:
  fixes x :: 'a
  obtains \<A> where "countable \<A>" "\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A" "\<And>A. A \<in> \<A> \<Longrightarrow> open A"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> (\<exists>A\<in>\<A>. A \<subseteq> S)"
proof -
  obtain \<A> where \<A>: "(\<forall>i::nat. x \<in> \<A> i \<and> open (\<A> i))" "(\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
    using first_countable_basis[of x] by metis
  moreover have "countable (range \<A>)"
    by simp
  ultimately show thesis
    by (smt (verit, best) imageE rangeI that)
qed

lemma (in first_countable_topology) first_countable_basis_Int_stableE:
  obtains \<A> where "countable \<A>" "\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A" "\<And>A. A \<in> \<A> \<Longrightarrow> open A"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> (\<exists>A\<in>\<A>. A \<subseteq> S)"
    "\<And>A B. A \<in> \<A> \<Longrightarrow> B \<in> \<A> \<Longrightarrow> A \<inter> B \<in> \<A>"
proof atomize_elim
  obtain \<B> where \<B>:
    "countable \<B>"
    "\<And>B. B \<in> \<B> \<Longrightarrow> x \<in> B"
    "\<And>B. B \<in> \<B> \<Longrightarrow> open B"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>B\<in>\<B>. B \<subseteq> S"
    by (rule first_countable_basisE) blast
  define \<A> where [abs_def]:
    "\<A> = (\<lambda>N. \<Inter>((\<lambda>n. from_nat_into \<B> n) ` N)) ` (Collect finite::nat set set)"
  then show "\<exists>\<A>. countable \<A> \<and> (\<forall>A. A \<in> \<A> \<longrightarrow> x \<in> A) \<and> (\<forall>A. A \<in> \<A> \<longrightarrow> open A) \<and>
        (\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> (\<exists>A\<in>\<A>. A \<subseteq> S)) \<and> (\<forall>A B. A \<in> \<A> \<longrightarrow> B \<in> \<A> \<longrightarrow> A \<inter> B \<in> \<A>)"
  proof (intro exI conjI strip)
    show "countable \<A>"
      unfolding \<A>_def by (intro countable_image countable_Collect_finite)
    fix A
    assume "A \<in> \<A>"
    then show "x \<in> A" "open A"
      using \<B>(4)[OF open_UNIV] by (auto simp: \<A>_def intro: \<B> from_nat_into)
  next
    let ?int = "\<lambda>N. \<Inter>(from_nat_into \<B> ` N)"
    fix A B
    assume "A \<in> \<A>" "B \<in> \<A>"
    then obtain N M where "A = ?int N" "B = ?int M" "finite (N \<union> M)"
      by (auto simp: \<A>_def)
    then show "A \<inter> B \<in> \<A>"
      by (auto simp: \<A>_def intro!: image_eqI[where x="N \<union> M"])
  next
    fix S
    assume "open S" "x \<in> S"
    then obtain a where a: "a\<in>\<B>" "a \<subseteq> S" using \<B> by blast
    moreover have "a\<in>\<A>"
      unfolding \<A>_def 
    proof (rule image_eqI)
      show "a = \<Inter> (from_nat_into \<B> ` {to_nat_on \<B> a})"
        by (simp add: \<B> a)
    qed auto
    ultimately show "\<exists>a\<in>\<A>. a \<subseteq> S"
      by blast 
  qed
qed

lemma (in topological_space) first_countableI:
  assumes "countable \<A>"
    and 1: "\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A" "\<And>A. A \<in> \<A> \<Longrightarrow> open A"
    and 2: "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>A\<in>\<A>. A \<subseteq> S"
  shows "\<exists>\<A>::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> \<A> i \<and> open (\<A> i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
proof (intro exI[of _ "from_nat_into _"] conjI strip)
  fix i
  have "\<A> \<noteq> {}" using 2[of UNIV] by auto
  show "x \<in> from_nat_into \<A> i" "open (from_nat_into \<A> i)"
    using range_from_nat_into_subset[OF \<open>\<A> \<noteq> {}\<close>] 1 by auto
next
  fix S
  assume "open S \<and> x\<in>S" 
  then show "\<exists>i. from_nat_into \<A> i \<subseteq> S"
    by (metis "2" \<open>countable \<A>\<close> from_nat_into_surj)
qed

instance prod :: (first_countable_topology, first_countable_topology) first_countable_topology
proof
  fix x :: "'a \<times> 'b"
  obtain \<A> where \<A>:
      "countable \<A>"
      "\<And>a. a \<in> \<A> \<Longrightarrow> fst x \<in> a"
      "\<And>a. a \<in> \<A> \<Longrightarrow> open a"
      "\<And>S. open S \<Longrightarrow> fst x \<in> S \<Longrightarrow> \<exists>a\<in>\<A>. a \<subseteq> S"
    by (rule first_countable_basisE[of "fst x"]) blast
  obtain B where B:
      "countable B"
      "\<And>a. a \<in> B \<Longrightarrow> snd x \<in> a"
      "\<And>a. a \<in> B \<Longrightarrow> open a"
      "\<And>S. open S \<Longrightarrow> snd x \<in> S \<Longrightarrow> \<exists>a\<in>B. a \<subseteq> S"
    by (rule first_countable_basisE[of "snd x"]) blast
  show "\<exists>\<A>::nat \<Rightarrow> ('a \<times> 'b) set.
    (\<forall>i. x \<in> \<A> i \<and> open (\<A> i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
  proof (rule first_countableI[of "(\<lambda>(a, b). a \<times> b) ` (\<A> \<times> B)"], safe)
    fix a b
    assume x: "a \<in> \<A>" "b \<in> B"
    show "x \<in> a \<times> b" 
      by (simp add: \<A>(2) B(2) mem_Times_iff x)
    show "open (a \<times> b)"
      by (simp add: \<A>(3) B(3) open_Times x)
  next
    fix S
    assume "open S" "x \<in> S"
    then obtain a' b' where a'b': "open a'" "open b'" "x \<in> a' \<times> b'" "a' \<times> b' \<subseteq> S"
      by (rule open_prod_elim)
    moreover
    obtain a b where "a \<in> \<A>" "a \<subseteq> a'" "b \<in> B" "b \<subseteq> b'"
      by (meson B(4) \<A>(4) a'b' mem_Times_iff)
    ultimately
    show "\<exists>a\<in>(\<lambda>(a, b). a \<times> b) ` (\<A> \<times> B). a \<subseteq> S"
      by (auto intro!: bexI[of _ "a \<times> b"] bexI[of _ a] bexI[of _ b])
  qed (simp add: \<A> B)
qed

class second_countable_topology = topological_space +
  assumes ex_countable_subbasis:
    "\<exists>B::'a set set. countable B \<and> open = generate_topology B"
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
    have "\<exists>B'\<subseteq>Inter ` {b. finite b \<and> b \<subseteq> B}. \<Union>B' = S" if "open S" for S
    proof -
      have "\<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. (\<Union>b\<in>B'. \<Inter>b) = S"
        using that unfolding B 
      proof induct
        case UNIV
        show ?case by (intro exI[of _ "{{}}"]) simp
      next
        case (Int a b)
        then obtain x y where x: "a = \<Union>(Inter ` x)" "\<And>i. i \<in> x \<Longrightarrow> finite i \<and> i \<subseteq> B"
          and y: "b = \<Union>(Inter ` y)" "\<And>i. i \<in> y \<Longrightarrow> finite i \<and> i \<subseteq> B"
          by blast
        show ?case
          unfolding x y Int_UN_distrib2
          by (intro exI[of _ "{i \<union> j| i j.  i \<in> x \<and> j \<in> y}"]) (auto dest: x(2) y(2))
      next
        case (UN K)
        then have "\<forall>k\<in>K. \<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. \<Union> (Inter ` B') = k" by auto
        then obtain k where
            "\<forall>ka\<in>K. k ka \<subseteq> {b. finite b \<and> b \<subseteq> B} \<and> \<Union>(Inter ` (k ka)) = ka"
          unfolding bchoice_iff ..
        then show "\<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. \<Union> (Inter ` B') = \<Union>K"
          by (intro exI[of _ "\<Union>(k ` K)"]) auto
      next
        case (Basis S)
        then show ?case
          by (intro exI[of _ "{{S}}"]) auto
      qed
      then show ?thesis
        unfolding subset_image_iff by blast 
    qed
    then show "topological_basis ?B"
      unfolding topological_basis_def
      by (safe intro!: open_Inter) (simp_all add: B generate_topology.Basis subset_eq)
  qed
qed


end

lemma univ_second_countable:
  obtains \<B> :: "'a::second_countable_topology set set"
  where "countable \<B>" "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
       "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
by (metis ex_countable_basis topological_basis_def)

proposition Lindelof:
  fixes \<F> :: "'a::second_countable_topology set set"
  assumes \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> open S"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>" "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
      and \<B>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
    using univ_second_countable by blast
  define \<D> where "\<D> \<equiv> {S. S \<in> \<B> \<and> (\<exists>U. U \<in> \<F> \<and> S \<subseteq> U)}"
  have "countable \<D>"
    by (simp add: \<D>_def \<open>countable \<B>\<close>)
  have "\<And>S. \<exists>U. S \<in> \<D> \<longrightarrow> U \<in> \<F> \<and> S \<subseteq> U"
    by (simp add: \<D>_def)
  then obtain G where G: "\<And>S. S \<in> \<D> \<longrightarrow> G S \<in> \<F> \<and> S \<subseteq> G S"
    by metis
  have eq1: "\<Union>\<F> = \<Union>\<D>"
    unfolding \<D>_def by (blast dest: \<F> \<B>)
  also have "\<dots> = \<Union> (G ` \<D>)"
    using G eq1 by auto
  finally show ?thesis
    by (metis G \<open>countable \<D>\<close> countable_image image_subset_iff that)
qed

lemma countable_disjoint_open_subsets:
  fixes \<F> :: "'a::second_countable_topology set set"
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

sublocale second_countable_topology <
  countable_basis "open" "SOME B. countable B \<and> topological_basis B"
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
  proof (cases "\<exists>z. x < z \<and> z < y")
    case True
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    then obtain V where "V \<in> A" "z \<in> V" "V \<subseteq> U" 
      using topological_basisE[OF \<open>topological_basis A\<close>]
      by (metis U_def greaterThanLessThan_iff z)
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using \<open>z \<in> V\<close> by (metis someI2)
    with \<open>V \<in> A\<close> \<open>V \<subseteq> U\<close> show ?thesis
      by (force simp: B2_def U_def w_def)
  next
    case False
    then have *: "\<And>z. z > x \<Longrightarrow> z \<ge> y" by auto
    define U where "U = {x<..}"
    then have "open U" by simp
    then obtain "V" where "V \<in> A" "y \<in> V" "V \<subseteq> U" 
      using topological_basisE[OF \<open>topological_basis A\<close>] U_def \<open>x < y\<close> by blast
    have "U = {y..}" unfolding U_def using * \<open>x < y\<close> by auto
    then have "V \<subseteq> {y..}" using \<open>V \<subseteq> U\<close> by simp
    then have "(LEAST w. w \<in> V) = y" using \<open>y \<in> V\<close> by (meson Least_equality atLeast_iff subsetCE)
    then show ?thesis
      using B1_def \<open>V \<in> A\<close> that by blast
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
  proof (cases "\<exists>z. x < z \<and> z < y")
    case True
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    then obtain "V" where "V \<in> A" "z \<in> V" "V \<subseteq> U" 
      using topological_basisE[OF \<open>topological_basis A\<close>]
      by (metis U_def greaterThanLessThan_iff z)
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" 
      using \<open>z \<in> V\<close> by (metis someI2)
    then have "x \<le> w \<and> w < y" 
      using \<open>w \<in> V\<close> \<open>V \<subseteq> U\<close> U_def by fastforce
    then show ?thesis
      using B2_def \<open>V \<in> A\<close> w_def by blast
  next
    case False
    then have *: "\<And>z. z < y \<Longrightarrow> z \<le> x" using leI by blast
    define U where "U = {..<y}"
    then have "open U" by simp
    then obtain "V" where "V \<in> A" "x \<in> V" "V \<subseteq> U" 
      using topological_basisE[OF \<open>topological_basis A\<close>] U_def \<open>x < y\<close> by blast
    have "U = {..x}" unfolding U_def using * \<open>x < y\<close> by auto
    then have "V \<subseteq> {..x}" 
      using \<open>V \<subseteq> U\<close> by simp
    then have "(GREATEST x. x \<in> V) = x" 
      using \<open>x \<in> V\<close> by (meson Greatest_equality atMost_iff subsetCE)
    then show ?thesis
      using B1_def \<open>V \<in> A\<close> that by blast
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
    then show ?thesis
      using \<open>z < y\<close> by auto
  qed
  then show ?thesis using B(1) by auto
qed


subsection \<open>Polish spaces\<close>

text \<open>Textbooks define Polish spaces as completely metrizable.
  We assume the topology to be complete for a given metric.\<close>

class polish_space = complete_space + second_countable_topology


subsection \<open>Limit Points\<close>

definition\<^marker>\<open>tag important\<close> (in topological_space) islimpt:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infixr \<open>islimpt\<close> 60)
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

lemma islimpt_UNIV_iff: "x islimpt UNIV \<longleftrightarrow> \<not> open {x}"
  unfolding islimpt_def by (safe, fast, case_tac "T = {x}", fast, fast)

lemma islimpt_punctured: "x islimpt S = x islimpt (S-{x})"
  unfolding islimpt_def by blast

text \<open>A perfect space has no isolated points.\<close>

lemma islimpt_UNIV [simp, intro]: "x islimpt UNIV"
  for x :: "'a::perfect_space"
  unfolding islimpt_UNIV_iff by (rule not_open_singleton)

lemma closed_limpt: "closed S \<longleftrightarrow> (\<forall>x. x islimpt S \<longrightarrow> x \<in> S)"
  unfolding closed_def open_subopen [of "-S"]
  by (metis Compl_iff islimptE islimptI open_subopen subsetI)

lemma islimpt_EMPTY[simp]: "\<not> x islimpt {}"
  by (auto simp: islimpt_def)

lemma islimpt_Un: "x islimpt (S \<union> T) \<longleftrightarrow> x islimpt S \<or> x islimpt T"
  by (simp add: islimpt_iff_eventually eventually_conj_iff)

lemma islimpt_finite_union_iff:
  assumes "finite A"
  shows   "z islimpt (\<Union>x\<in>A. B x) \<longleftrightarrow> (\<exists>x\<in>A. z islimpt B x)"
  using assms by (induction rule: finite_induct) (simp_all add: islimpt_Un)

lemma islimpt_insert:
  fixes x :: "'a::t1_space"
  shows "x islimpt (insert a S) \<longleftrightarrow> x islimpt S"
proof
  assume "x islimpt (insert a S)"
  then show "x islimpt S"
    by (metis closed_limpt closed_singleton empty_iff insert_iff insert_is_Un islimpt_Un islimpt_def)
next
  assume "x islimpt S"
  then show "x islimpt (insert a S)"
    by (rule islimpt_subset) auto
qed

lemma islimpt_finite:
  fixes x :: "'a::t1_space"
  shows "finite S \<Longrightarrow> \<not> x islimpt S"
  by (induct set: finite) (simp_all add: islimpt_insert)

lemma islimpt_Un_finite:
  fixes x :: "'a::t1_space"
  shows "finite S \<Longrightarrow> x islimpt (S \<union> T) \<longleftrightarrow> x islimpt T"
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
  then have "\<exists>x. x \<in> (T \<inter> S - {l})"
    by (metis ex_in_conv finite.emptyI infinite_remove)
  then show "\<exists>y\<in>S. y \<in> T \<and> y \<noteq> l"
    by auto
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
      by (metis all_not_in_conv finite.emptyI)
    then have "\<exists>a. i < a \<and> f a \<in> A (Suc n)"
      by (force simp: linorder_not_le)
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
    have "eventually (\<lambda>i. f (r i) \<in> A i) sequentially"
    proof
      fix i assume "Suc 0 \<le> i" then show "f (r i) \<in> A i"
        by (cases i) (simp_all add: r_def s)
    qed
    ultimately show "eventually (\<lambda>i. f (r i) \<in> S) sequentially"
      by eventually_elim auto
  qed
  ultimately show "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by (auto simp: convergent_def comp_def)
qed

lemma islimpt_range_imp_convergent_subsequence:
  fixes l :: "'a :: {t1_space, first_countable_topology}"
  assumes l: "l islimpt (range f)"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
  using l unfolding islimpt_eq_acc_point
  by (rule acc_point_range_imp_convergent_subsequence)

lemma sequence_unique_limpt:
  fixes f :: "nat \<Rightarrow> 'a::t2_space"
  assumes f: "(f \<longlongrightarrow> l) sequentially" and l': "l' islimpt (range f)"
  shows "l' = l"
proof (rule ccontr)
  assume "l' \<noteq> l"
  obtain s t where "open s" "open t" "l' \<in> s" "l \<in> t" "s \<inter> t = {}"
    using hausdorff [OF \<open>l' \<noteq> l\<close>] by auto
  then obtain N where "\<forall>n\<ge>N. f n \<in> t"
    by (meson f lim_explicit)

  have "UNIV = {..<N} \<union> {N..}"
    by auto
  then have "l' islimpt (f ` {..<N} \<union> f ` {N..})"
    by (metis l' image_Un)
  then have "l' islimpt (f ` {N..})"
    by (simp add: islimpt_Un_finite)
  then obtain y where "y \<in> f ` {N..}" "y \<in> s" "y \<noteq> l'"
    using \<open>l' \<in> s\<close> \<open>open s\<close> by (rule islimptE)
  with \<open>\<forall>n\<ge>N. f n \<in> t\<close> \<open>s \<inter> t = {}\<close> show False
    by blast
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

lemma islimpt_isCont_image:
  fixes f :: "'a :: {first_countable_topology, t2_space} \<Rightarrow> 'b :: {first_countable_topology, t2_space}"
  assumes "x islimpt A" and "isCont f x" and ev: "eventually (\<lambda>y. f y \<noteq> f x) (at x)"
  shows   "f x islimpt f ` A"
proof -
  from assms(1) obtain g where g: "g \<longlonglongrightarrow> x" "range g \<subseteq> A - {x}"
    unfolding islimpt_sequential by blast
  have "filterlim g (at x) sequentially"
    using g by (auto simp: filterlim_at intro!: always_eventually)
  then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> f (g n) \<noteq> f x"
    by (metis (mono_tags, lifting) ev eventually_at_top_linorder filterlim_iff)
  have "(\<lambda>x. g (x + N)) \<longlonglongrightarrow> x"
    using g(1) by (rule LIMSEQ_ignore_initial_segment)
  hence "(\<lambda>x. f (g (x + N))) \<longlonglongrightarrow> f x"
    using assms(2) isCont_tendsto_compose by blast
  moreover have "range (\<lambda>x. f (g (x + N))) \<subseteq> f ` A - {f x}"
    using g(2) N by auto
  ultimately show ?thesis
    unfolding islimpt_sequential by (intro exI[of _ "\<lambda>x. f (g (x + N))"]) auto
qed

lemma islimpt_image:
  assumes "z islimpt g -` A \<inter> B" "g z \<notin> A" "z \<in> B" "continuous_on B g"
  shows   "g z islimpt A"
  using assms
  by (simp add: islimpt_def vimage_def continuous_on_topological Bex_def) metis
  

subsection \<open>Interior of a Set\<close>

definition\<^marker>\<open>tag important\<close> interior :: "('a::topological_space) set \<Rightarrow> 'a set" where
"interior S = \<Union>{T. open T \<and> T \<subseteq> S}"

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
  by (meson interior_eq interior_subset not_open_singleton subset_singletonD)

lemma interior_Int [simp]: "interior (S \<inter> T) = interior S \<inter> interior T"
proof
  show "interior S \<inter> interior T \<subseteq> interior (S \<inter> T)"
    by (meson Int_mono interior_subset open_Int open_interior open_subset_interior)
qed (simp add: interior_mono)

lemma eventually_nhds_in_nhd: "x \<in> interior s \<Longrightarrow> eventually (\<lambda>y. y \<in> s) (nhds x)"
  using interior_subset[of s] by (subst eventually_nhds) blast

lemma interior_limit_point [intro]:
  fixes x :: "'a::perfect_space"
  assumes x: "x \<in> interior S"
  shows "x islimpt S"
proof -
  obtain T where "x \<in> T" "T \<subseteq> S" "open T"
    using interior_subset x by blast
  with x islimpt_UNIV [of x]  show ?thesis
    unfolding islimpt_def by (metis (full_types) Int_iff open_Int subsetD)
qed

lemma open_imp_islimpt:
  fixes x::"'a:: perfect_space"
  assumes "open S" "x\<in>S"
  shows "x islimpt S"
  using assms interior_eq interior_limit_point by auto

lemma islimpt_Int_eventually:
  assumes "x islimpt A" "eventually (\<lambda>y. y \<in> B) (at x)"
  shows   "x islimpt A \<inter> B"
  using assms unfolding islimpt_def eventually_at_filter eventually_nhds
  by (metis Int_iff UNIV_I open_Int)

lemma islimpt_conv_frequently_at:
  "x islimpt A \<longleftrightarrow> frequently (\<lambda>y. y \<in> A) (at x)"
  by (simp add: frequently_def islimpt_iff_eventually)

lemma frequently_at_imp_islimpt:
  assumes "frequently (\<lambda>y. y \<in> A) (at x)"
  shows   "x islimpt A"
  by (simp add: assms islimpt_conv_frequently_at)  

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
    then obtain R where R: "open R" "x \<in> R" "R \<subseteq> S \<union> T" ..
    show "x \<in> interior S"
    proof (rule ccontr)
      assume "x \<notin> interior S"
      with \<open>x \<in> R\<close> \<open>open R\<close> obtain y where "y \<in> R - S"
        unfolding interior_def by fast
      with R show False
        by (metis Diff_subset_conv cS empty_iff iT interiorI open_Diff)
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

lemma countable_disjoint_nonempty_interior_subsets:
  fixes \<F> :: "'a::second_countable_topology set set"
  assumes pw: "pairwise disjnt \<F>" and int: "\<And>S. \<lbrakk>S \<in> \<F>; interior S = {}\<rbrakk> \<Longrightarrow> S = {}"
  shows "countable \<F>"
proof (rule countable_image_inj_on)
  have "disjoint (interior ` \<F>)"
    using pw by (simp add: disjoint_image_subset interior_subset)
  then show "countable (interior ` \<F>)"
    by (auto intro: countable_disjoint_open_subsets)
  show "inj_on interior \<F>"
    using pw
    unfolding inj_on_def pairwise_def disjnt_def
    by (metis inf.idem int interior_Int interior_empty)
qed

subsection \<open>Closure of a Set\<close>

definition\<^marker>\<open>tag important\<close> closure :: "('a::topological_space) set \<Rightarrow> 'a set" where
  "closure S = S \<union> {x . x islimpt S}"

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
  then have "x islimpt (S \<inter> T)" if "x islimpt T"
    by (metis IntD1 eventually_at_in_open' inf_commute islimpt_Int_eventually that)
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
  assume T: "A \<times> B \<subseteq> T" "closed T"
  have False
    if ab: "a \<in> closure A" "b \<in> closure B" and "(a, b) \<notin> T" for a b
  proof -
    obtain C D where "open C" "open D" "C \<times> D \<subseteq> - T" "a \<in> C" "b \<in> D"
      by (metis ComplI SigmaE2 \<open>closed T\<close> \<open>(a, b) \<notin> T\<close> open_Compl open_prod_elim)
    then obtain "\<not> C \<subseteq> - A" "\<not> D \<subseteq> - B"
      by (meson ab disjoint_iff inf_shunt open_Int_closure_eq_empty)
    then show False
      using T \<open>C \<times> D \<subseteq> - T\<close> by auto
  qed
  then show "closure A \<times> closure B \<subseteq> T"
    by blast
qed

lemma closure_open_Int_superset:
  assumes "open S" "S \<subseteq> closure T"
  shows "closure(S \<inter> T) = closure S"
proof
  show "closure S \<subseteq> closure (S \<inter> T)"
    by (metis assms closed_closure closure_minimal inf.absorb_iff1 open_Int_closure_subset)
qed (simp add: closure_mono)

lemma closure_Int: "closure (\<Inter>I) \<subseteq> \<Inter>{closure S |S. S \<in> I}"
  by (simp add: INF_greatest Inter_lower Setcompr_eq_image closure_mono)

lemma islimpt_in_closure: "(x islimpt S) = (x\<in>closure(S-{x}))"
  unfolding closure_def using islimpt_punctured by blast

lemma connected_imp_connected_closure: "connected S \<Longrightarrow> connected (closure S)"
  by (rule connectedI) (meson closure_subset open_Int open_Int_closure_eq_empty subset_trans connectedD)

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


subsection \<open>Frontier (also known as boundary)\<close>

definition\<^marker>\<open>tag important\<close> frontier :: "('a::topological_space) set \<Rightarrow> 'a set" where
  "frontier S = closure S - interior S"

lemma frontier_closed [iff]: "closed (frontier S)"
  by (simp add: frontier_def closed_Diff)

lemma frontier_closures: "frontier S = closure S \<inter> closure (- S)"
  by (auto simp: frontier_def interior_closure)

lemma frontier_Int: "frontier(S \<inter> T) = closure(S \<inter> T) \<inter> (frontier S \<union> frontier T)"
proof -
  have "closure (S \<inter> T) \<subseteq> closure S" "closure (S \<inter> T) \<subseteq> closure T"
    by (simp_all add: closure_mono)
  then show ?thesis
    by (auto simp: frontier_closures)
qed

lemma frontier_Int_subset: "frontier(S \<inter> T) \<subseteq> frontier S \<union> frontier T"
  by (auto simp: frontier_Int)

lemma frontier_Int_closed:
  assumes "closed S" "closed T"
  shows "frontier(S \<inter> T) = (frontier S \<inter> T) \<union> (S \<inter> frontier T)"
  by (simp add: Int_Un_distrib assms closed_Int frontier_closures inf_commute inf_left_commute)

lemma frontier_subset_closed: "closed S \<Longrightarrow> frontier S \<subseteq> S"
  by (metis frontier_def closure_closed Diff_subset)

lemma frontier_empty [simp]: "frontier {} = {}"
  by (simp add: frontier_def)

lemma frontier_subset_eq: "frontier S \<subseteq> S \<longleftrightarrow> closed S"
  by (metis Diff_subset_conv closure_subset_eq frontier_def interior_subset subset_Un_eq)

lemma frontier_complement [simp]: "frontier (- S) = frontier S"
  by (auto simp: frontier_def closure_complement interior_complement)

lemma frontier_Un_subset: "frontier(S \<union> T) \<subseteq> frontier S \<union> frontier T"
  by (metis compl_sup frontier_Int_subset frontier_complement)

lemma frontier_disjoint_eq: "frontier S \<inter> S = {} \<longleftrightarrow> open S"
  using frontier_complement frontier_subset_eq[of "- S"]
  unfolding open_closed by auto

lemma frontier_UNIV [simp]: "frontier UNIV = {}"
  using frontier_complement frontier_empty by fastforce

lemma frontier_interiors: "frontier s = - interior(s) - interior(-s)"
  by (simp add: Int_commute frontier_def interior_closure)

lemma frontier_interior_subset: "frontier(interior S) \<subseteq> frontier S"
  by (simp add: Diff_mono frontier_interiors interior_mono interior_subset)

lemma closure_Un_frontier: "closure S = S \<union> frontier S"
  by (simp add: closure_def frontier_closures sup_inf_distrib1)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Filters and the ``eventually true'' quantifier\<close>

text \<open>Identify Trivial limits, where we can't approach arbitrarily closely.\<close>

lemma trivial_limit_within: "trivial_limit (at a within S) \<longleftrightarrow> \<not> a islimpt S"
    unfolding trivial_limit_def eventually_at_topological islimpt_def
    by blast

lemma trivial_limit_at_iff: "trivial_limit (at a) \<longleftrightarrow> \<not> a islimpt UNIV"
  using trivial_limit_within [of a UNIV] by simp

lemma trivial_limit_at: "\<not> trivial_limit (at a)"
  for a :: "'a::perfect_space"
  by (rule at_neq_bot)

lemma not_trivial_limit_within: "\<not> trivial_limit (at x within S) = (x \<in> closure (S - {x}))"
  using islimpt_in_closure by (metis trivial_limit_within)

lemma not_in_closure_trivial_limitI:
  "x \<notin> closure S \<Longrightarrow> trivial_limit (at x within S)"
  using not_trivial_limit_within[of x S]
  by (metis Diff_empty Diff_insert0 closure_subset subsetD)

lemma filterlim_at_within_closure_implies_filterlim: "filterlim f l (at x within S)"
  if "x \<in> closure S \<Longrightarrow> filterlim f l (at x within S)"
  by (metis bot.extremum filterlim_iff_le_filtercomap not_in_closure_trivial_limitI that)

lemma at_within_eq_bot_iff: "at c within A = bot \<longleftrightarrow> c \<notin> closure (A - {c})"
  using not_trivial_limit_within[of c A] by blast

subsection \<open>Limits\<close>

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
  by (metis assms at_within_open_subset interior_subset open_interior)

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

lemma Lim_left_bound:
  fixes f :: "'a :: {linorder_topology, conditionally_complete_linorder, no_bot} \<Rightarrow>
    'b :: {linorder_topology, conditionally_complete_linorder}"
  assumes mono: "\<And>a b. a \<in> I \<Longrightarrow> b \<in> I \<Longrightarrow> b < x \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> f b"
    and bnd: "\<And>b. b \<in> I \<Longrightarrow> b < x \<Longrightarrow> f b \<le> K"
  shows "(f \<longlongrightarrow> Sup (f ` ({..<x} \<inter> I))) (at x within ({..<x} \<inter> I))"
proof (cases "{..<x} \<inter> I = {}")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule order_tendstoI)
    fix b
    assume b: "Sup (f ` ({..<x} \<inter> I)) < b"
    {
      fix y
      assume "y \<in> {..<x} \<inter> I"
      with False bnd have "f y \<le> Sup (f ` ({..<x} \<inter> I))" by (auto intro!: cSup_upper bdd_aboveI2)
      with b have "f y < b" by order
    }
    then show "eventually (\<lambda>x. f x < b) (at x within ({..<x} \<inter> I))"
      by (auto simp: eventually_at_filter intro: exI[of _ 1] zero_less_one)
  next
    fix b
    assume "b < Sup (f ` ({..<x} \<inter> I))"
    from less_cSupD[OF _ this] False obtain y where y: "y < x" "y \<in> I" "b < f y" by auto
    then have "eventually (\<lambda>x. x \<in> I \<longrightarrow> b < f x) (at_left x)"
      unfolding eventually_at_left[OF \<open>y < x\<close>] by (metis mono order_less_le order_less_le_trans)
    then show "eventually (\<lambda>x. b < f x) (at x within ({..<x} \<inter> I))"
      unfolding eventually_at_filter by eventually_elim simp
  qed
qed


text\<open>These are special for limits out of the same topological space.\<close>

lemma Lim_within_id: "(id \<longlongrightarrow> a) (at a within s)"
  unfolding id_def by (rule tendsto_ident_at)

lemma Lim_at_id: "(id \<longlongrightarrow> a) (at a)"
  unfolding id_def by (rule tendsto_ident_at)

text\<open>It's also sometimes useful to extract the limit point from the filter.\<close>

abbreviation netlimit :: "'a::t2_space filter \<Rightarrow> 'a"
  where "netlimit F \<equiv> Lim F (\<lambda>x. x)"

lemma netlimit_at [simp]:
  fixes a :: "'a::{perfect_space,t2_space}"
  shows "netlimit (at a) = a"
  using Lim_ident_at [of a UNIV] by simp

lemma lim_within_interior:
  "x \<in> interior S \<Longrightarrow> (f \<longlongrightarrow> l) (at x within S) \<longleftrightarrow> (f \<longlongrightarrow> l) (at x)"
  by (metis at_within_interior)

lemma netlimit_within_interior:
  fixes x :: "'a::{t2_space,perfect_space}"
  assumes "x \<in> interior S"
  shows "netlimit (at x within S) = x"
  using assms by (metis at_within_interior netlimit_at)

text\<open>Useful lemmas on closure and set of possible sequential limits.\<close>

lemma closure_sequential:
  fixes l :: "'a::first_countable_topology"
  shows "l \<in> closure S \<longleftrightarrow> (\<exists>x. (\<forall>n. x n \<in> S) \<and> (x \<longlongrightarrow> l) sequentially)"
  by (auto simp: closure_def islimpt_sequential)

lemma closed_sequential_limits:
  fixes S :: "'a::first_countable_topology set"
  shows "closed S \<longleftrightarrow> (\<forall>x l. (\<forall>n. x n \<in> S) \<and> (x \<longlongrightarrow> l) sequentially \<longrightarrow> l \<in> S)"
by (metis closure_sequential closure_subset_eq subset_iff)

lemma tendsto_If_within_closures:
  assumes f: "x \<in> S \<union> (closure S \<inter> closure T) \<Longrightarrow>
      (f \<longlongrightarrow> l x) (at x within S \<union> (closure S \<inter> closure T))"
  assumes g: "x \<in> T \<union> (closure S \<inter> closure T) \<Longrightarrow>
      (g \<longlongrightarrow> l x) (at x within T \<union> (closure S \<inter> closure T))"
  assumes "x \<in> S \<union> T"
  shows "((\<lambda>x. if x \<in> S then f x else g x) \<longlongrightarrow> l x) (at x within S \<union> T)"
proof -
  have *: "(S \<union> T) \<inter> {x. x \<in> S} = S" "(S \<union> T) \<inter> {x. x \<notin> S} = T - S"
    by auto
  have "(f \<longlongrightarrow> l x) (at x within S)"
    using tendsto_within_subset[OF f] \<open>x \<in> S \<union> T\<close>
    by (metis Int_iff Un_iff Un_upper1 closure_def filterlim_at_within_closure_implies_filterlim)
  moreover
  have "(g \<longlongrightarrow> l x) (at x within T - S)"
    using tendsto_within_subset g \<open>x \<in> S \<union> T\<close>
    by (metis IntI Un_Diff_Int Un_iff Un_upper1 closure_def filterlim_at_within_closure_implies_filterlim) 
  ultimately show ?thesis
    by (intro filterlim_at_within_If) (simp_all only: *)
qed


subsection \<open>Compactness\<close>

lemma brouwer_compactness_lemma:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  assumes "compact S"
    and "continuous_on S f"
    and "\<not> (\<exists>x\<in>S. f x = 0)"
  obtains d where "0 < d" and "\<forall>x\<in>S. d \<le> norm (f x)"
proof (cases "S = {}")
  case True
  show thesis
    by (rule that [of 1]) (auto simp: True)
next
  case False
  have "continuous_on S (norm \<circ> f)"
    by (rule continuous_intros continuous_on_norm assms(2))+
  with False obtain x where x: "x \<in> S" "\<forall>y\<in>S. (norm \<circ> f) x \<le> (norm \<circ> f) y"
    using continuous_attains_inf[OF assms(1), of "norm \<circ> f"]
    unfolding o_def
    by auto
  then show ?thesis
    by (metis assms(3) that comp_apply zero_less_norm_iff)
qed

subsubsection \<open>Bolzano-Weierstrass property\<close>

proposition Heine_Borel_imp_Bolzano_Weierstrass:
  assumes "compact S"
    and "infinite T"
    and "T \<subseteq> S"
  shows "\<exists>x \<in> S. x islimpt T"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> S. x islimpt T)"
  then obtain f where f: "\<forall>x\<in>S. x \<in> f x \<and> open (f x) \<and> (\<forall>y\<in>T. y \<in> f x \<longrightarrow> y = x)"
    unfolding islimpt_def by metis
  obtain g where g: "g \<subseteq> {T. \<exists>x. x \<in> S \<and> T = f x}" "finite g" "S \<subseteq> \<Union>g"
    using assms(1)[unfolded compact_eq_Heine_Borel, THEN spec[where x="{T. \<exists>x. x\<in>S \<and> T = f x}"]]
    using f by auto
  then have g': "\<forall>x\<in>g. \<exists>y \<in> S. x = f y"
    by auto
  have "inj_on f T"
    unfolding inj_on_def using \<open>T \<subseteq> S\<close> f by blast
  then have "infinite (f ` T)"
    using assms(2) using finite_imageD by auto
  moreover
  have False if "x \<in> T" "f x \<notin> g" for x
    using \<open>T \<subseteq> S\<close>  f g' \<open>S \<subseteq> \<Union>g\<close> that by force
  then have "f ` T \<subseteq> g" by auto
  ultimately show False
    using g(2) using finite_subset by auto
qed

lemma sequence_infinite_lemma:
  fixes f :: "nat \<Rightarrow> 'a::t1_space"
  assumes "\<And>n. f n \<noteq> l"
    and "(f \<longlongrightarrow> l) sequentially"
  shows "infinite (range f)"
proof
  assume "finite (range f)"
  then have "l \<notin> range f \<and> closed (range f)"
    using \<open>finite (range f)\<close> assms(1) finite_imp_closed by blast
  then have "eventually (\<lambda>n. f n \<in> - range f) sequentially"
    by (metis Compl_iff assms(2) open_Compl topological_tendstoD)
  then show False
    unfolding eventually_sequentially by auto
qed

lemma Bolzano_Weierstrass_imp_closed:
  fixes S :: "'a::{first_countable_topology,t2_space} set"
  assumes "\<forall>T. infinite T \<and> T \<subseteq> S --> (\<exists>x \<in> S. x islimpt T)"
  shows "closed S"
proof -
  {
    fix x l
    assume \<section>: "\<forall>n. x n \<in> S" "(x \<longlongrightarrow> l) sequentially"
    have "l \<in> S"
    proof (cases "\<forall>n. x n \<noteq> l")
      case True
      with \<section> have "infinite (range x)"
        using sequence_infinite_lemma[of x l] by auto
      with \<section> assms show "l\<in>S" 
        using sequence_unique_limpt \<section> True by blast 
    qed (use \<section> in auto)
  }
  then show ?thesis
    unfolding closed_sequential_limits by auto
qed

lemma closure_insert:
  fixes x :: "'a::t1_space"
  shows "closure (insert x S) = insert x (closure S)"
  by (metis closed_singleton closure_Un closure_closed insert_is_Un)

lemma finite_not_islimpt_in_compact:
  assumes "compact A" "\<And>z. z \<in> A \<Longrightarrow> \<not>z islimpt B"
  shows   "finite (A \<inter> B)"
  by (meson Heine_Borel_imp_Bolzano_Weierstrass assms inf_le1 inf_le2 islimpt_subset)


text\<open>In particular, some common special cases.\<close>

lemma compact_Un [intro]:
  assumes "compact S"
    and "compact T"
  shows " compact (S \<union> T)"
proof (rule compactI)
  fix f
  assume *: "Ball f open" "S \<union> T \<subseteq> \<Union>f"
  from * \<open>compact S\<close> obtain s' where "s' \<subseteq> f \<and> finite s' \<and> S \<subseteq> \<Union>s'"
    unfolding compact_eq_Heine_Borel by (auto elim!: allE[of _ f])
  moreover
  from * \<open>compact T\<close> obtain t' where "t' \<subseteq> f \<and> finite t' \<and> T \<subseteq> \<Union>t'"
    unfolding compact_eq_Heine_Borel by (auto elim!: allE[of _ f])
  ultimately show "\<exists>f'\<subseteq>f. finite f' \<and> S \<union> T \<subseteq> \<Union>f'"
    by (auto intro!: exI[of _ "s' \<union> t'"])
qed

lemma compact_Union [intro]: "finite S \<Longrightarrow> (\<And>T. T \<in> S \<Longrightarrow> compact T) \<Longrightarrow> compact (\<Union>S)"
  by (induct set: finite) auto

lemma compact_UN [intro]:
  "finite A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> compact (B x)) \<Longrightarrow> compact (\<Union>x\<in>A. B x)"
  by blast

lemma closed_Int_compact [intro]:
  assumes "closed S" and "compact T"
  shows "compact (S \<inter> T)"
  using compact_Int_closed [of T S] assms
  by (simp add: Int_commute)

lemma compact_Int [intro]:
  fixes S T :: "'a :: t2_space set"
  assumes "compact S" and "compact T"
  shows "compact (S \<inter> T)"
  using assms by (intro compact_Int_closed compact_imp_closed)

lemma compact_sing [simp]: "compact {a}"
  unfolding compact_eq_Heine_Borel by auto

lemma compact_insert [simp]:
  assumes "compact S"
  shows "compact (insert x S)"
  by (metis assms compact_Un compact_sing insert_is_Un)

lemma finite_imp_compact: "finite S \<Longrightarrow> compact S"
  by (induct set: finite) simp_all

lemma open_delete:
  fixes S :: "'a::t1_space set"
  shows "open S \<Longrightarrow> open (S - {x})"
  by (simp add: open_Diff)


text\<open>Compactness expressed with filters\<close>

lemma closure_iff_nhds_not_empty:
  "x \<in> closure X \<longleftrightarrow> (\<forall>A. \<forall>S\<subseteq>A. open S \<longrightarrow> x \<in> S \<longrightarrow> X \<inter> A \<noteq> {})"
proof -
  have "\<forall>A S. S \<subseteq> A \<longrightarrow> open S \<longrightarrow> x \<in> S \<longrightarrow> X \<inter> A \<noteq> {} \<Longrightarrow> x \<in> closure X"
    by (metis ComplI Diff_disjoint Diff_eq closure_interior inf_top_left 
        interior_subset open_interior)
  then show ?thesis
    using open_Int_closure_eq_empty by fastforce
qed

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
    unfolding Z_def by (auto elim: eventually_mono intro: subsetD[OF closure_subset])
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
    with open_Int_closure_eq_empty[of S "{x. R x}"] x
    have "S \<inter> {x. R x} \<noteq> {}" by (auto simp: Z_def)
    moreover assume "Ball S Q" "\<forall>x. Q x \<and> R x \<longrightarrow> bot x"
    ultimately show False by (auto simp: set_eq_iff)
  qed
  with \<open>x \<in> U\<close> show "\<exists>x\<in>U. inf (nhds x) F \<noteq> bot"
    by (metis eventually_bot)
next
  fix A
  assume A: "\<forall>a\<in>A. closed a" "\<forall>B\<subseteq>A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}" "U \<inter> \<Inter>A = {}"
  define F where "F = (INF a\<in>insert U A. principal a)"
  have "F \<noteq> bot"
    unfolding F_def
  proof (rule INF_filter_not_bot)
    fix X
    assume X: "X \<subseteq> insert U A" "finite X"
    with A(2)[THEN spec, of "X - {U}"] have "U \<inter> \<Inter>(X - {U}) \<noteq> {}"
      by auto
    with X show "(INF a\<in>X. principal a) \<noteq> bot"
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
      by (metis INF_lower F_def insertCI)
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

definition\<^marker>\<open>tag important\<close> countably_compact :: "('a::topological_space) set \<Rightarrow> bool" where
"countably_compact U \<longleftrightarrow>
  (\<forall>A. countable A \<longrightarrow> (\<forall>a\<in>A. open a) \<longrightarrow> U \<subseteq> \<Union>A
     \<longrightarrow> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T))"

lemma countably_compactE:
  assumes "countably_compact s" and "\<forall>t\<in>C. open t" and "s \<subseteq> \<Union>C" "countable C"
  obtains C' where "C' \<subseteq> C" and "finite C'" and "s \<subseteq> \<Union>C'"
  using assms unfolding countably_compact_def by metis

lemma countably_compactI:
  assumes "\<And>C. \<forall>t\<in>C. open t \<Longrightarrow> s \<subseteq> \<Union>C \<Longrightarrow> countable C \<Longrightarrow> \<exists>C'\<subseteq>C. finite C' \<and> s \<subseteq> \<Union>C'"
  shows "countably_compact s"
  using assms unfolding countably_compact_def by metis

lemma compact_imp_countably_compact: "compact U \<Longrightarrow> countably_compact U"
  by (auto simp: compact_eq_Heine_Borel countably_compact_def)

lemma countably_compact_imp_compact:
  assumes "countably_compact U"
    and ccover: "countable B" "\<forall>b\<in>B. open b"
    and basis: "\<And>T x. open T \<Longrightarrow> x \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>b\<in>B. x \<in> b \<and> b \<inter> U \<subseteq> T"
  shows "compact U"
  using \<open>countably_compact U\<close>
  unfolding compact_eq_Heine_Borel countably_compact_def
proof safe
  fix A
  assume A: "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A"
  assume *: "\<forall>A. countable A \<longrightarrow> (\<forall>a\<in>A. open a) \<longrightarrow> U \<subseteq> \<Union>A \<longrightarrow> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T)"
  moreover define C where "C = {b\<in>B. \<exists>a\<in>A. b \<inter> U \<subseteq> a}"
  ultimately have "countable C" "\<forall>a\<in>C. open a"
    unfolding C_def using ccover by auto
  moreover
  have "\<Union>A \<inter> U \<subseteq> \<Union>C"
  proof clarify
    fix x a
    assume "x \<in> U" "x \<in> a" "a \<in> A"
    with basis[of a x] A show "x \<in> \<Union>C"
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

proposition countably_compact_imp_compact_second_countable:
  "countably_compact U \<Longrightarrow> compact (U :: 'a :: second_countable_topology set)"
proof (rule countably_compact_imp_compact)
  fix T and x :: 'a
  assume "open T" "x \<in> T"
  from topological_basisE[OF is_basis this] 
  show "\<exists>b\<in>SOME B. countable B \<and> topological_basis B. x \<in> b \<and> b \<inter> U \<subseteq> T"
    by (metis le_infI1)
qed (insert countable_basis topological_basis_open[OF is_basis], auto)

lemma countably_compact_eq_compact:
  "countably_compact U \<longleftrightarrow> compact (U :: 'a :: second_countable_topology set)"
  using countably_compact_imp_compact_second_countable compact_imp_countably_compact by blast

subsubsection\<open>Sequential compactness\<close>

definition\<^marker>\<open>tag important\<close> seq_compact :: "'a::topological_space set \<Rightarrow> bool" where
  "seq_compact S \<longleftrightarrow>
    (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l))"

lemma seq_compactI:
  assumes "\<And>f. \<forall>n. f n \<in> S \<Longrightarrow> \<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
  shows "seq_compact S"
  unfolding seq_compact_def using assms by fast

lemma seq_compactE:
  assumes "seq_compact S" "\<forall>n. f n \<in> S"
  obtains l r where "l \<in> S" "strict_mono (r :: nat \<Rightarrow> nat)" "(f \<circ> r) \<longlonglongrightarrow> l"
  using assms unfolding seq_compact_def by fast

lemma seq_compact_Int_closed:
  assumes "seq_compact S" and "closed T"
  shows "seq_compact (S \<inter> T)"
proof (rule seq_compactI)
  fix f assume "\<forall>n::nat. f n \<in> S \<inter> T"
  hence "\<forall>n. f n \<in> S" and "\<forall>n. f n \<in> T"
    by simp_all
  from \<open>seq_compact S\<close> and \<open>\<forall>n. f n \<in> S\<close>
  obtain l r where "l \<in> S" and r: "strict_mono r" and l: "(f \<circ> r) \<longlonglongrightarrow> l"
    by (rule seq_compactE)
  from \<open>\<forall>n. f n \<in> T\<close> have "\<forall>n. (f \<circ> r) n \<in> T"
    by simp
  with \<open>l \<in> S\<close> and r and l show "\<exists>l\<in>S \<inter> T. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by (metis Int_iff \<open>closed T\<close> closed_sequentially)
qed

lemma seq_compact_closed_subset:
  assumes "closed S" and "S \<subseteq> T" and "seq_compact T"
  shows "seq_compact S"
  using assms seq_compact_Int_closed [of T S] by (simp add: Int_absorb1)

lemma seq_compact_imp_countably_compact:
  fixes U :: "'a :: first_countable_topology set"
  assumes "seq_compact U"
  shows "countably_compact U"
proof (intro countably_compactI)
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
      with r(2) A(1) from_nat_into[OF \<open>A \<noteq> {}\<close>]
      have "eventually (\<lambda>i. X (r i) \<in> from_nat_into A n) sequentially"
        unfolding tendsto_def by fastforce
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
    have "X (r i) \<in> A i" if "Suc 0 \<le> i" for i
      using that by (cases i) (simp_all add: r_def s)
    then have "eventually (\<lambda>i. X (r i) \<in> A i) sequentially"
      by (auto simp: eventually_sequentially)
    ultimately show "eventually (\<lambda>i. X (r i) \<in> S) sequentially"
      by eventually_elim auto
  qed
  ultimately show "\<exists>x \<in> U. \<exists>r. strict_mono r \<and> (X \<circ> r) \<longlonglongrightarrow> x"
    using \<open>x \<in> U\<close> by (auto simp: convergent_def comp_def)
qed

lemma countably_compact_imp_acc_point:
  assumes "countably_compact S"
    and "countable T"
    and "infinite T"
    and "T \<subseteq> S"
  shows "\<exists>x\<in>S. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> T)"
proof (rule ccontr)
  define C where "C = (\<lambda>F. interior (F \<union> (- T))) ` {F. finite F \<and> F \<subseteq> T }"
  note \<open>countably_compact S\<close>
  moreover have "\<forall>T\<in>C. open T"
    by (auto simp: C_def)
  moreover
  assume "\<not> (\<exists>x\<in>S. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> T))"
  then have S: "\<And>x. x \<in> S \<Longrightarrow> \<exists>U. x\<in>U \<and> open U \<and> finite (U \<inter> T)" by metis
  have "\<And>x U. \<lbrakk>T \<subseteq> S; x \<in> U; open U; finite (U \<inter> T)\<rbrakk> \<Longrightarrow> x \<in> \<Union> C"
    unfolding C_def
    by (auto intro!: UN_I [where a="U \<inter> T"] interiorI simp add: finite_subset)
  then have "S \<subseteq> \<Union>C"
    using \<open>T \<subseteq> S\<close> S by force
  moreover
  from \<open>countable T\<close> have "countable C"
    unfolding C_def by (auto intro: countable_Collect_finite_subset)
  ultimately
  obtain D where "D \<subseteq> C" "finite D" "S \<subseteq> \<Union>D"
    by (rule countably_compactE)
  then obtain E where E: "E \<subseteq> {F. finite F \<and> F \<subseteq> T }" "finite E"
    and S: "S \<subseteq> (\<Union>F\<in>E. interior (F \<union> (- T)))"
    by (metis (lifting) finite_subset_image C_def)
  from S \<open>T \<subseteq> S\<close> have "T \<subseteq> \<Union>E"
    using interior_subset by blast
  moreover have "finite (\<Union>E)"
    using E by auto
  ultimately show False using \<open>infinite T\<close>
    by (auto simp: finite_subset)
qed

lemma countable_acc_point_imp_seq_compact:
  fixes S :: "'a::first_countable_topology set"
  assumes "\<And>T. \<lbrakk>infinite T; countable T; T \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>x\<in>S. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> T)"
  shows "seq_compact S"
  unfolding seq_compact_def
proof (intro strip)
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> S"
  show "\<exists>l\<in>S. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
  proof (cases "finite (range f)")
    case True
    obtain l where "infinite {n. f n = f l}"
      using pigeonhole_infinite[OF _ True] by auto
    then obtain r :: "nat \<Rightarrow> nat" where "strict_mono  r" and fr: "\<forall>n. f (r n) = f l"
      using infinite_enumerate by blast
    then have "strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> f l"
      by (simp add: fr o_def)
    with f show "\<exists>l\<in>S. \<exists>r. strict_mono  r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
      by auto
  next
    case False
    with f assms obtain l where "l \<in> S" "\<forall>U. l\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> range f)"
      by (metis image_subset_iff uncountable_def) 
    with \<open>l \<in> S\<close> show "\<exists>l\<in>S. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
      by (meson acc_point_range_imp_convergent_subsequence) 
  qed
qed

lemma seq_compact_eq_countably_compact:
  fixes U :: "'a :: first_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> countably_compact U"
  by (metis countable_acc_point_imp_seq_compact countably_compact_imp_acc_point seq_compact_imp_countably_compact)

lemma seq_compact_eq_acc_point:
  fixes S :: "'a :: first_countable_topology set"
  shows "seq_compact S \<longleftrightarrow>
    (\<forall>T. infinite T \<and> countable T \<and> T \<subseteq> S --> (\<exists>x\<in>S. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> T)))"
  by (metis countable_acc_point_imp_seq_compact countably_compact_imp_acc_point seq_compact_imp_countably_compact)

lemma seq_compact_eq_compact:
  fixes U :: "'a :: second_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> compact U"
  using seq_compact_eq_countably_compact countably_compact_eq_compact by blast

proposition Bolzano_Weierstrass_imp_seq_compact:
  fixes S :: "'a::{t1_space, first_countable_topology} set"
  shows "(\<And>T. \<lbrakk>infinite T; T \<subseteq> S\<rbrakk> \<Longrightarrow>\<exists>x \<in> S. x islimpt T) \<Longrightarrow> seq_compact S"
  by (rule countable_acc_point_imp_seq_compact) (metis islimpt_eq_acc_point)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Cartesian products\<close>

lemma seq_compact_Times:
  assumes "seq_compact S" "seq_compact T"
  shows "seq_compact (S \<times> T)"
  unfolding seq_compact_def
proof clarify
  fix h :: "nat \<Rightarrow> 'a \<times> 'b"
  assume "\<forall>n. h n \<in> S \<times> T"
  then have *: "\<And>n. (fst \<circ> h) n \<in> S" "\<And>n. (snd \<circ> h) n \<in> T"
    by (simp_all add: mem_Times_iff)
  then obtain lS and rS :: "nat\<Rightarrow>nat"
    where "lS\<in>S" "strict_mono rS" and lS: "(fst \<circ> h \<circ> rS) \<longlonglongrightarrow> lS"
    using assms seq_compact_def by metis
  then obtain lT and rT :: "nat\<Rightarrow>nat" 
    where  "lT\<in>T" "strict_mono rT" and lT: "(snd \<circ> h \<circ> rS \<circ> rT) \<longlonglongrightarrow> lT"
    using assms seq_compact_def *
    by (metis (mono_tags, lifting) comp_apply) 
  have "strict_mono (rS \<circ> rT)"
    by (simp add: \<open>strict_mono rS\<close> \<open>strict_mono rT\<close> strict_mono_o)
  moreover have "(h \<circ> (rS \<circ> rT)) \<longlonglongrightarrow> (lS,lT)"
    using tendsto_Pair [OF LIMSEQ_subseq_LIMSEQ [OF lS \<open>strict_mono rT\<close>] lT]
    by (simp add: o_def)
  ultimately show "\<exists>l\<in>S \<times> T. \<exists>r. strict_mono r \<and> (h \<circ> r) \<longlonglongrightarrow> l"
    using \<open>lS \<in> S\<close> \<open>lT \<in> T\<close> by blast
qed

lemma compact_Times:
  assumes "compact S" "compact T"
  shows "compact (S \<times> T)"
proof (rule compactI)
  fix \<C>
  assume C: "\<forall>T\<in>\<C>. open T" "S \<times> T \<subseteq> \<Union>\<C>"
  have "\<forall>x\<in>S. \<exists>A. open A \<and> x \<in> A \<and> (\<exists>D\<subseteq>\<C>. finite D \<and> A \<times> T \<subseteq> \<Union>D)"
  proof
    fix x
    assume "x \<in> S"
    have "\<forall>y\<in>T. \<exists>A B C. C \<in> \<C> \<and> open A \<and> open B \<and> x \<in> A \<and> y \<in> B \<and> A \<times> B \<subseteq> C"
      by (smt (verit, ccfv_threshold) C UnionE \<open>x \<in> S\<close> mem_Sigma_iff open_prod_def subsetD)
    then obtain a b c where b: "\<And>y. y \<in> T \<Longrightarrow> open (b y)"
      and c: "\<And>y. y \<in> T \<Longrightarrow> c y \<in> \<C> \<and> open (a y) \<and> open (b y) \<and> x \<in> a y \<and> y \<in> b y \<and> a y \<times> b y \<subseteq> c y"
      by metis
    then have "\<forall>y\<in>T. open (b y)" "T \<subseteq> (\<Union>y\<in>T. b y)" by auto
    with compactE_image[OF \<open>compact T\<close>] obtain D where D: "D \<subseteq> T" "finite D" "T \<subseteq> (\<Union>y\<in>D. b y)"
      by metis
    moreover from D c have "(\<Inter>y\<in>D. a y) \<times> T \<subseteq> (\<Union>y\<in>D. c y)"
      by (fastforce simp: subset_eq)
    ultimately show "\<exists>a. open a \<and> x \<in> a \<and> (\<exists>d\<subseteq>\<C>. finite d \<and> a \<times> T \<subseteq> \<Union>d)"
      using c exI[of _ "c`D"] exI[of _ "\<Inter>(a`D)"] by (simp add: open_INT subset_eq)
  qed
  then obtain a d where a: "\<And>x. x\<in>S \<Longrightarrow> open (a x)" "S \<subseteq> (\<Union>x\<in>S. a x)"
    and d: "\<And>x. x \<in> S \<Longrightarrow> d x \<subseteq> \<C> \<and> finite (d x) \<and> a x \<times> T \<subseteq> \<Union>(d x)"
    unfolding subset_eq UN_iff by metis
  moreover
  from compactE_image[OF \<open>compact S\<close> a]
  obtain e where e: "e \<subseteq> S" "finite e" and S: "S \<subseteq> (\<Union>x\<in>e. a x)"
    by auto
  moreover
  have "S \<times> T \<subseteq> (\<Union>x\<in>e. \<Union>(d x))"
    by (smt (verit, del_insts) S SigmaE UN_iff d e(1) mem_Sigma_iff subset_eq)
  ultimately show "\<exists>C'\<subseteq>\<C>. finite C' \<and> S \<times> T \<subseteq> \<Union>C'"
    by (force simp: subset_eq intro!: exI[of _ "\<Union>x\<in>e. d x"])
qed


lemma tube_lemma:
  assumes "compact K"
  assumes "open W"
  assumes "{x0} \<times> K \<subseteq> W"
  shows "\<exists>X0. x0 \<in> X0 \<and> open X0 \<and> X0 \<times> K \<subseteq> W"
proof -
    have "\<exists>X0 Y. open X0 \<and> open Y \<and> x0 \<in> X0 \<and> y \<in> Y \<and> X0 \<times> Y \<subseteq> W" if "y \<in> K" for y
      using assms open_prod_def subsetD that by fastforce
  then obtain X0 Y where
    *: "\<forall>y \<in> K. open (X0 y) \<and> open (Y y) \<and> x0 \<in> X0 y \<and> y \<in> Y y \<and> X0 y \<times> Y y \<subseteq> W"
    by metis
  from * have "\<forall>t\<in>Y ` K. open t" "K \<subseteq> \<Union>(Y ` K)" by auto
  with \<open>compact K\<close> obtain CC where CC: "CC \<subseteq> Y ` K" "finite CC" "K \<subseteq> \<Union>CC"
    by (meson compactE)
  then obtain c where c: "\<And>C. C \<in> CC \<Longrightarrow> c C \<in> K \<and> C = Y (c C)"
    by (force intro!: choice)
  with * CC show ?thesis
    by (bestsimp intro!: exI[where x="\<Inter>C\<in>CC. X0 (c C)"]) (* SLOW *)
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
  then obtain W where W: "open W" "W \<inter> U \<times> C = W0 \<inter> U \<times> C"
    unfolding W0_eq
    by (metis \<open>open {..<e}\<close> continuous_on_open_invariant inf_right_idem) 
  have "{x0} \<times> C \<subseteq> W \<inter> U \<times> C"
    unfolding W
    by (auto simp: W0_def psi_def \<open>0 < e\<close>)
  then have "{x0} \<times> C \<subseteq> W" by blast
  from tube_lemma[OF \<open>compact C\<close> \<open>open W\<close> this]
  obtain X0 where X0: "x0 \<in> X0" "open X0" "X0 \<times> C \<subseteq> W"
    by blast

  have "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
  proof clarify
    fix x assume x: "x \<in> X0" "x \<in> U"
    fix t assume t: "t \<in> C"
    have "dist (fx (x, t)) (fx (x0, t)) = psi (x, t)"
      by (auto simp: psi_def)
    also have "psi (x, t) < e"
      using W(2) W0_def X0(3) t x by fastforce
    finally show "dist (fx (x,t)) (fx (x0,t)) \<le> e" by simp
  qed
  from X0(1,2) this show ?thesis ..
qed


subsection \<open>Continuity\<close>

lemma continuous_at_imp_continuous_within:
  "continuous (at x) f \<Longrightarrow> continuous (at x within s) f"
  unfolding continuous_within continuous_at using Lim_at_imp_Lim_at_within by auto

lemma Lim_trivial_limit: "trivial_limit net \<Longrightarrow> (f \<longlongrightarrow> l) net"
  by simp

lemmas continuous_on = continuous_on_def \<comment> \<open>legacy theorem name\<close>

lemma continuous_within_subset:
  "continuous (at x within S) f \<Longrightarrow> t \<subseteq> S \<Longrightarrow> continuous (at x within t) f"
  unfolding continuous_within by(metis tendsto_within_subset)

lemma continuous_on_interior:
  "continuous_on S f \<Longrightarrow> x \<in> interior S \<Longrightarrow> continuous (at x) f"
  by (metis continuous_on_eq_continuous_at continuous_on_subset interiorE)

lemma continuous_on_eq:
  "\<lbrakk>continuous_on S f; \<And>x. x \<in> S \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> continuous_on S g"
  unfolding continuous_on_def tendsto_def eventually_at_topological
  by simp

text \<open>Characterization of various kinds of continuity in terms of sequences.\<close>

lemma continuous_within_sequentiallyI:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  assumes "\<And>u::nat \<Rightarrow> 'a. u \<longlonglongrightarrow> a \<Longrightarrow> (\<forall>n. u n \<in> S) \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f a"
  shows "continuous (at a within S) f"
  using assms unfolding continuous_within tendsto_def[where l = "f a"]
  by (auto intro!: sequentially_imp_eventually_within)

lemma continuous_within_tendsto_compose:
  fixes f::"'a::t2_space \<Rightarrow> 'b::topological_space"
  assumes f: "continuous (at a within S) f"
         and  "eventually (\<lambda>n. x n \<in> S) F" "(x \<longlongrightarrow> a) F "
  shows "((\<lambda>n. f (x n)) \<longlongrightarrow> f a) F"
proof -
  have *: "filterlim x (inf (nhds a) (principal S)) F"
    by (simp add: assms filterlim_inf filterlim_principal)
  show ?thesis
    using "*" f continuous_within filterlim_compose tendsto_at_within_iff_tendsto_nhds by blast
qed

lemma continuous_within_tendsto_compose':
  fixes f::"'a::t2_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at a within S) f" "\<And>n. x n \<in> S" "(x \<longlongrightarrow> a) F "
  shows "((\<lambda>n. f (x n)) \<longlongrightarrow> f a) F"
  using always_eventually assms continuous_within_tendsto_compose by blast

lemma continuous_within_sequentially:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  shows "continuous (at a within S) f \<longleftrightarrow>
    (\<forall>x. (\<forall>n::nat. x n \<in> S) \<and> (x \<longlongrightarrow> a) sequentially
         \<longrightarrow> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  using continuous_within_tendsto_compose'[of a S f _ sequentially]
  using continuous_within_sequentiallyI[of a S f]
  by (auto simp: o_def)

lemma continuous_at_sequentiallyI:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  assumes "\<And>u. u \<longlonglongrightarrow> a \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f a"
  shows "continuous (at a) f"
  using continuous_within_sequentiallyI[of a UNIV f] assms by auto

lemma continuous_at_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  shows "continuous (at a) f \<longleftrightarrow>
    (\<forall>x. (x \<longlongrightarrow> a) sequentially --> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  using continuous_within_sequentially[of a UNIV f] by simp

lemma continuous_on_sequentiallyI:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  assumes "\<And>u a. (\<forall>n. u n \<in> S) \<Longrightarrow> a \<in> S \<Longrightarrow> u \<longlonglongrightarrow> a \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f a"
  shows "continuous_on S f"
  using assms unfolding continuous_on_eq_continuous_within
  using continuous_within_sequentiallyI[of _ S f] by auto

lemma continuous_on_sequentially:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  shows "continuous_on S f \<longleftrightarrow>
    (\<forall>x. \<forall>a \<in> S. (\<forall>n. x(n) \<in> S) \<and> (x \<longlongrightarrow> a) sequentially
      \<longrightarrow> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  by (meson continuous_on_eq_continuous_within continuous_within_sequentially)

subsection \<open>Homeomorphisms\<close>

definition\<^marker>\<open>tag important\<close> "homeomorphism S T f g \<longleftrightarrow>
  (\<forall>x\<in>S. (g(f x) = x)) \<and> (f ` S = T) \<and> continuous_on S f \<and>
  (\<forall>y\<in>T. (f(g y) = y)) \<and> (g ` T = S) \<and> continuous_on T g"

lemma homeomorphismI [intro?]:
  assumes "continuous_on S f" "continuous_on T g"
    "f ` S \<subseteq> T" "g ` T \<subseteq> S" "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "\<And>y. y \<in> T \<Longrightarrow> f(g y) = y"
  shows "homeomorphism S T f g"
  using assms by (force simp: homeomorphism_def)

lemma homeomorphism_translation:
  fixes a :: "'a :: real_normed_vector"
  shows "homeomorphism ((+) a ` S) S ((+) (- a)) ((+) a)"
  unfolding homeomorphism_def by (auto simp: algebra_simps continuous_intros)

lemma homeomorphism_ident: "homeomorphism T T (\<lambda>a. a) (\<lambda>a. a)"
  by (rule homeomorphismI) auto

lemma homeomorphism_compose:
  assumes "homeomorphism S T f g" "homeomorphism T U h k"
    shows "homeomorphism S U (h o f) (g o k)"
  using assms
  unfolding homeomorphism_def
  by (intro conjI ballI continuous_on_compose) (auto simp: image_iff)

lemma homeomorphism_cong:
  "homeomorphism X' Y' f' g'"
    if "homeomorphism X Y f g" "X' = X" "Y' = Y" "\<And>x. x \<in> X \<Longrightarrow> f' x = f x" "\<And>y. y \<in> Y \<Longrightarrow> g' y = g y"
  using that by (auto simp add: homeomorphism_def)

lemma homeomorphism_empty [simp]:
  "homeomorphism {} {} f g"
  unfolding homeomorphism_def by auto

lemma homeomorphism_symD: "homeomorphism S t f g \<Longrightarrow> homeomorphism t S g f"
  by (simp add: homeomorphism_def)

lemma homeomorphism_sym: "homeomorphism S t f g = homeomorphism t S g f"
  by (force simp: homeomorphism_def)

lemma continuous_on_translation_eq:
  fixes g :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_vector"
  shows "continuous_on A ((+) a \<circ> g) = continuous_on A g"
proof -
  have g: "g = (\<lambda>x. -a + x) \<circ> ((\<lambda>x. a + x) \<circ> g)"
    by force
  show ?thesis
    by (metis (no_types, opaque_lifting) g continuous_on_compose homeomorphism_def homeomorphism_translation)
qed

definition\<^marker>\<open>tag important\<close> homeomorphic :: "'a::topological_space set \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
    (infixr \<open>homeomorphic\<close> 60)
  where "s homeomorphic t \<equiv> (\<exists>f g. homeomorphism s t f g)"

lemma homeomorphic_empty [iff]:
     "S homeomorphic {} \<longleftrightarrow> S = {}" "{} homeomorphic S \<longleftrightarrow> S = {}"
  by (auto simp: homeomorphic_def homeomorphism_def)

lemma homeomorphic_refl: "S homeomorphic S"
  using homeomorphic_def homeomorphism_ident by fastforce

lemma homeomorphic_sym: "S homeomorphic T \<longleftrightarrow> T homeomorphic S"
  unfolding homeomorphic_def homeomorphism_def
  by blast

lemma homeomorphic_trans [trans]:
  assumes "S homeomorphic T" and "T homeomorphic U"
  shows "S homeomorphic U"
  using assms unfolding homeomorphic_def
  by (metis homeomorphism_compose)

lemma homeomorphic_minimal:
  "S homeomorphic T \<longleftrightarrow>
    (\<exists>f g. (\<forall>x\<in>S. f(x) \<in> T \<and> (g(f(x)) = x)) \<and>
           (\<forall>y\<in>T. g(y) \<in> S \<and> (f(g(y)) = y)) \<and>
           continuous_on S f \<and> continuous_on T g)" (is "?L=?R")
proof
  assume "S homeomorphic T"
  then obtain f g where \<section>: "homeomorphism S T f g"
    using homeomorphic_def by blast
  show ?R
  proof (intro exI conjI)
    show "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
      by (metis "\<section>" homeomorphism_def imageI)+
    show "continuous_on S f" "continuous_on T g"
      using "\<section>" homeomorphism_def by blast+
  qed
qed (force simp: homeomorphic_def homeomorphism_def image_iff)

lemma homeomorphicI [intro?]:
   "\<lbrakk>f ` S = T; g ` T = S;
     continuous_on S f; continuous_on T g;
     \<And>x. x \<in> S \<Longrightarrow> g(f(x)) = x;
     \<And>y. y \<in> T \<Longrightarrow> f(g(y)) = y\<rbrakk> \<Longrightarrow> S homeomorphic T"
unfolding homeomorphic_def homeomorphism_def by metis

lemma homeomorphism_of_subsets:
   "\<lbrakk>homeomorphism S T f g; S' \<subseteq> S; T'' \<subseteq> T; f ` S' = T'\<rbrakk>
    \<Longrightarrow> homeomorphism S' T' f g"
  by (smt (verit, del_insts) continuous_on_subset homeomorphismI homeomorphism_def imageE subset_eq)

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
  shows "S homeomorphic T \<longleftrightarrow> finite S \<and> card S = card T" (is "?lhs = ?rhs")
proof
  assume "S homeomorphic T"
  with assms show ?rhs
    by (metis (full_types) card_image_le finite_imageI homeomorphic_def homeomorphism_def le_antisym)
next
  assume R: ?rhs
  with finite_same_card_bij assms obtain h where h: "bij_betw h S T"
    by auto
  show ?lhs
    unfolding homeomorphic_def homeomorphism_def 
  proof (intro exI conjI)
    show "continuous_on S h" "continuous_on T (inv_into S h)"
      by (simp_all add: assms R continuous_on_finite)
  qed (use h in \<open>auto simp: bij_betw_def\<close>)
qed

text \<open>Relatively weak hypotheses if a set is compact.\<close>

lemma homeomorphism_compact:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes "compact S" "continuous_on S f"  "f ` S = T"  "inj_on f S"
  shows "\<exists>g. homeomorphism S T f g"
proof -
  obtain g where g: "\<forall>x\<in>S. g (f x) = x" "\<forall>x\<in>T. f (g x) = x" "g ` T = S"
    using assms the_inv_into_f_f by fastforce 
  with assms show ?thesis
    unfolding homeomorphism_def homeomorphic_def by (metis continuous_on_inv)
qed

lemma homeomorphic_compact:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  shows "compact S \<Longrightarrow> continuous_on S f \<Longrightarrow> (f ` S = T) \<Longrightarrow> inj_on f S \<Longrightarrow> S homeomorphic T"
  unfolding homeomorphic_def by (metis homeomorphism_compact)

text\<open>Preservation of topological properties.\<close>

lemma homeomorphic_compactness: "S homeomorphic T \<Longrightarrow> (compact S \<longleftrightarrow> compact T)"
  unfolding homeomorphic_def homeomorphism_def
  by (metis compact_continuous_image)


subsection\<^marker>\<open>tag unimportant\<close> \<open>On Linorder Topologies\<close>

lemma islimpt_greaterThanLessThan1:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "a islimpt {a<..<b}"
proof (rule islimptI)
  fix T
  assume "open T" "a \<in> T"
  then obtain c where c: "a < c" "{a..<c} \<subseteq> T"
    by (meson assms open_right)
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

end