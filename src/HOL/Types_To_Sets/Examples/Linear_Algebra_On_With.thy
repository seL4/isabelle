(*  Title:      HOL/Types_To_Sets/Examples/Linear_Algebra_On_With.thy
    Author:     Fabian Immler, TU München
*)
theory Linear_Algebra_On_With
  imports
    Group_On_With
    Complex_Main
begin

definition span_with
  where "span_with pls zero scl b =
    {sum_with pls zero (\<lambda>a. scl (r a) a) t | t r. finite t \<and> t \<subseteq> b}"

lemma span_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows "((A ===> A ===> A) ===> A ===> ((=) ===> A ===> A) ===> rel_set A ===> rel_set A)
    span_with span_with"
  unfolding span_with_def
proof (intro rel_funI)
  fix p p' z z' X X' and s s'::"'c \<Rightarrow> _"
  assume transfer_rules[transfer_rule]: "(A ===> A ===> A) p p'" "A z z'" "((=) ===> A ===> A) s s'" "rel_set A X X'"
  have "Domainp A z" using \<open>A z z'\<close> by force
  have *: "t \<subseteq> X \<Longrightarrow> (\<forall>x\<in>t. Domainp A x)" for t
    by (meson Domainp.DomainI \<open>rel_set A X X'\<close> rel_setD1 set_mp)
  note swt=sum_with_transfer[OF assms(1,2,2), THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_funD, OF transfer_rules(1,2)]
  have DsI: "Domainp A (sum_with p z r t)" if "\<And>x. x \<in> t \<Longrightarrow> Domainp A (r x)" "t \<subseteq> Collect (Domainp A)" for r t
  proof cases
    assume ex: "\<exists>C. r ` t \<subseteq> C \<and> comm_monoid_add_on_with C p z"
    have "Domainp (rel_set A) t" using that by (auto simp: Domainp_set)
    from ex_comm_monoid_add_around_imageE[OF ex transfer_rules(1,2) this that(1)]
    obtain C where C: "comm_monoid_add_on_with C p z" "r ` t \<subseteq> C" "Domainp (rel_set A) C" by auto
    from sum_with_mem[OF C(1,2)] C(3)
    show ?thesis
      by auto (meson C(3) Domainp_set)
  qed (use \<open>A z _\<close> in \<open>auto simp: sum_with_def\<close>)
  from Domainp_apply2I[OF transfer_rules(3)]
  have Domainp_sI: "Domainp A x \<Longrightarrow> Domainp A (s y x)" for x y by auto
  show "rel_set A
    {sum_with p z (\<lambda>a. s (r a) a) t |t r. finite t \<and> t \<subseteq> X}
        {sum_with p' z' (\<lambda>a. s' (r a) a) t |t r. finite t \<and> t \<subseteq> X'}"
    apply (transfer_prover_start, transfer_step+)
    using *
    by (auto simp: intro!: DsI Domainp_sI)
qed

definition dependent_with
  where "dependent_with pls zero scl s =
    (\<exists>t u. finite t \<and> t \<subseteq> s \<and> (sum_with pls zero (\<lambda>v. scl (u v) v) t = zero \<and> (\<exists>v\<in>t. u v \<noteq> 0)))"

lemma dependent_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows "((A ===> A ===> A) ===> A ===> ((=) ===> A ===> A) ===> rel_set A ===> (=))
    dependent_with dependent_with"
  unfolding dependent_with_def dependent_with_def
proof (intro rel_funI)
  fix p p' z z' X X' and s s'::"'c \<Rightarrow> _"
  assume [transfer_rule]: "(A ===> A ===> A) p p'" "A z z'" "((=) ===> A ===> A) s s'" "rel_set A X X'"
  have *: "t \<subseteq> X \<Longrightarrow> (\<forall>x\<in>t. Domainp A x)" for t
    by (meson Domainp.DomainI \<open>rel_set A X X'\<close> rel_setD1 set_mp)
  show "(\<exists>t u. finite t \<and> t \<subseteq> X \<and> sum_with p z (\<lambda>v. s (u v) v) t = z \<and> (\<exists>v\<in>t. u v \<noteq> 0)) =
    (\<exists>t u. finite t \<and> t \<subseteq> X' \<and> sum_with p' z' (\<lambda>v. s' (u v) v) t = z' \<and> (\<exists>v\<in>t. u v \<noteq> 0))"
    apply (transfer_prover_start, transfer_step+)
    using *
    by (auto simp: intro!: sum_with_mem)
qed

definition subspace_with
  where "subspace_with pls zero scl S \<longleftrightarrow> zero \<in> S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. pls x y \<in> S) \<and> (\<forall>c. \<forall>x\<in>S. scl c x \<in> S)"

lemma subspace_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> A ===> A) ===> A ===> ((=) ===> A ===> A) ===> rel_set A ===> (=))
    subspace_with subspace_with"
  unfolding span_with_def subspace_with_def
  by transfer_prover

definition "module_on_with S pls mns um zero (scl::'a::comm_ring_1\<Rightarrow>_) \<longleftrightarrow>
  ab_group_add_on_with S pls zero mns um \<and>
        ((\<forall>a. \<forall>x\<in>S.
                 \<forall>y\<in>S. scl a (pls x y) = pls (scl a x) (scl a y)) \<and>
         (\<forall>a b. \<forall>x\<in>S. scl (a + b) x = pls (scl a x) (scl b x))) \<and>
        (\<forall>a b. \<forall>x\<in>S. scl a (scl b x) = scl (a * b) x) \<and>
        (\<forall>x\<in>S. scl 1 x = x) \<and>
        (\<forall>a. \<forall>x\<in>S. scl a x \<in> S)"

definition "vector_space_on_with S pls mns um zero (scl::'a::field\<Rightarrow>_) \<longleftrightarrow>
  module_on_with S pls mns um zero scl"

definition "module_pair_on_with S S' pls mns um zero (scl::'a::comm_ring_1\<Rightarrow>_) pls' mns' um' zero' (scl'::'a::comm_ring_1\<Rightarrow>_) \<longleftrightarrow>
  module_on_with S pls mns um zero scl \<and> module_on_with S' pls' mns' um' zero' scl'"

definition "vector_space_pair_on_with S S' pls mns um zero (scl::'a::field\<Rightarrow>_) pls' mns' um' zero' (scl'::'a::field\<Rightarrow>_) \<longleftrightarrow>
  module_pair_on_with S S' pls mns um zero scl pls' mns' um' zero' scl'"

definition "module_hom_on_with S1 S2 plus1 minus1 uminus1 zero1 (scale1::'a::comm_ring_1\<Rightarrow>_)
  plus2 minus2 uminus2 zero2 (scale2::'a::comm_ring_1\<Rightarrow>_) f \<longleftrightarrow>
        module_pair_on_with S1 S2 plus1 minus1 uminus1 zero1 scale1
         plus2 minus2 uminus2 zero2 scale2 \<and>
        (\<forall>x\<in>S1. \<forall>y\<in>S1. f (plus1 x y) = plus2 (f x) (f y)) \<and>
        (\<forall>s. \<forall>x\<in>S1. f (scale1 s x) = scale2 s (f x))"

definition "linear_on_with S1 S2 plus1 minus1 uminus1 zero1 (scale1::'a::field\<Rightarrow>_)
  plus2 minus2 uminus2 zero2 (scale2::'a::field\<Rightarrow>_) f \<longleftrightarrow>
  module_hom_on_with S1 S2 plus1 minus1 uminus1 zero1 scale1
  plus2 minus2 uminus2 zero2 scale2 f"

definition dim_on_with
  where "dim_on_with S pls zero scale V =
    (if \<exists>b \<subseteq> S. \<not> dependent_with pls zero scale b \<and> span_with pls zero scale b = span_with pls zero scale V
      then card (SOME b. b \<subseteq> S \<and>\<not> dependent_with pls zero scale b \<and> span_with pls zero scale b = span_with pls zero scale V)
      else 0)"

definition "finite_dimensional_vector_space_on_with S pls mns um zero (scl::'a::field\<Rightarrow>_) basis \<longleftrightarrow>
  vector_space_on_with S pls mns um zero scl \<and>
    finite basis \<and>
    \<not> dependent_with pls zero scl basis \<and>
    span_with pls zero scl basis = S"

definition "finite_dimensional_vector_space_pair_on_with S S' pls mns um zero (scl::'a::field\<Rightarrow>_) b
  pls' mns' um' zero' (scl'::'a::field\<Rightarrow>_) b' \<longleftrightarrow>
  finite_dimensional_vector_space_on_with S pls mns um zero (scl::'a::field\<Rightarrow>_) b \<and>
  finite_dimensional_vector_space_on_with S' pls' mns' um' zero' (scl'::'a::field\<Rightarrow>_) b'"

context module begin

lemma span_with:
  "span = (\<lambda>X. span_with (+) 0 scale X)"
  unfolding span_explicit span_with_def sum_with ..

lemma dependent_with:
  "dependent = (\<lambda>X. dependent_with (+) 0 scale X)"
  unfolding dependent_explicit dependent_with_def sum_with ..

lemma subspace_with:
  "subspace = (\<lambda>X. subspace_with (+) 0 scale X)"
  unfolding subspace_def subspace_with_def ..

end

lemmas [explicit_ab_group_add] = module.span_with module.dependent_with module.subspace_with

lemma module_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows
    "(rel_set A ===> (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===> (=))
      module_on_with module_on_with"
  unfolding module_on_with_def
  by transfer_prover

lemma vector_space_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows
    "(rel_set A ===> (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===> (=))
      vector_space_on_with vector_space_on_with"
  unfolding vector_space_on_with_def
  by transfer_prover

context vector_space begin

lemma dim_with: "dim = (\<lambda>X. dim_on_with UNIV (+) 0 scale X)"
  unfolding dim_def dim_on_with_def dependent_with span_with by force

end

lemmas [explicit_ab_group_add] = vector_space.dim_with

lemma module_pair_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A" "right_total C" "bi_unique C"
  shows
    "(rel_set A ===> rel_set C ===>
    (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===>
    (C ===> C ===> C) ===> (C ===> C ===> C) ===> (C ===> C) ===> C ===> ((=) ===> C ===> C) ===>
    (=)) module_pair_on_with module_pair_on_with"
  unfolding module_pair_on_with_def
  by transfer_prover

lemma module_hom_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A" "right_total C" "bi_unique C"
  shows
    "(rel_set A ===> rel_set C ===>
    (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===>
    (C ===> C ===> C) ===> (C ===> C ===> C) ===> (C ===> C) ===> C ===> ((=) ===> C ===> C) ===>
    (A ===> C) ===> (=)) module_hom_on_with module_hom_on_with"
  unfolding module_hom_on_with_def
  by transfer_prover

lemma linear_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A" "right_total C" "bi_unique C"
  shows
    "(rel_set A ===> rel_set C ===>
    (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===>
    (C ===> C ===> C) ===> (C ===> C ===> C) ===> (C ===> C) ===> C ===> ((=) ===> C ===> C) ===>
    (A ===> C) ===> (=)) linear_on_with linear_on_with"
  unfolding linear_on_with_def
  by transfer_prover

subsubsection \<open>Explicit locale formulations\<close>

lemma module_on_with[explicit_ab_group_add]: "module s \<longleftrightarrow> module_on_with UNIV (+) (-) uminus 0 s"
  and vector_space_on_with[explicit_ab_group_add]: "vector_space t \<longleftrightarrow> vector_space_on_with UNIV (+) (-) uminus 0 t"
  by (auto simp: module_def module_on_with_def ab_group_add_axioms
      vector_space_def vector_space_on_with_def)

lemma vector_space_with_imp_module_with[explicit_ab_group_add]:
  "vector_space_on_with S (+) (-) uminus 0 s \<Longrightarrow> module_on_with S (+) (-) uminus 0 s"
  by (simp add: vector_space_on_with_def)

lemma finite_dimensional_vector_space_on_with[explicit_ab_group_add]:
    "finite_dimensional_vector_space t b \<longleftrightarrow> finite_dimensional_vector_space_on_with UNIV (+) (-) uminus 0 t b"
  by (auto simp: finite_dimensional_vector_space_on_with_def finite_dimensional_vector_space_def
    finite_dimensional_vector_space_axioms_def explicit_ab_group_add)

lemma vector_space_with_imp_finite_dimensional_vector_space_with[explicit_ab_group_add]:
  "finite_dimensional_vector_space_on_with S (+) (-) uminus 0 s basis \<Longrightarrow>
  vector_space_on_with S  (+) (-) uminus 0 s"
  by (auto simp: finite_dimensional_vector_space_on_with_def)

lemma module_hom_on_with[explicit_ab_group_add]:
  "module_hom s1 s2 f \<longleftrightarrow> module_hom_on_with UNIV UNIV (+) (-) uminus 0 s1 (+) (-) uminus 0 s2 f"
  and linear_with[explicit_ab_group_add]:
  "Vector_Spaces.linear t1 t2 f \<longleftrightarrow> linear_on_with UNIV UNIV (+) (-) uminus 0 t1 (+) (-) uminus 0 t2 f"
  and module_pair_on_with[explicit_ab_group_add]:
  "module_pair s1 s2 \<longleftrightarrow> module_pair_on_with UNIV UNIV (+) (-) uminus 0 s1 (+) (-) uminus 0 s2"
  by (auto simp: module_hom_def module_hom_on_with_def module_pair_on_with_def
      Vector_Spaces.linear_def linear_on_with_def vector_space_on_with
      module_on_with_def vector_space_on_with_def
      module_hom_axioms_def module_pair_def module_on_with)

lemma vector_space_pair_with[explicit_ab_group_add]:
  "vector_space_pair s1 s2 \<longleftrightarrow> vector_space_pair_on_with UNIV UNIV (+) (-) uminus 0 s1  (+) (-) uminus 0 s2"
  by (auto simp: module_pair_on_with_def explicit_ab_group_add
      vector_space_pair_on_with_def vector_space_pair_def module_on_with_def vector_space_on_with_def)

lemma finite_dimensional_vector_space_pair_with[explicit_ab_group_add]:
  "finite_dimensional_vector_space_pair s1 b1 s2 b2 \<longleftrightarrow>
    finite_dimensional_vector_space_pair_on_with UNIV UNIV (+) (-) uminus 0 s1 b1 (+) (-) uminus 0 s2 b2"
  by (auto simp: finite_dimensional_vector_space_pair_def
      finite_dimensional_vector_space_pair_on_with_def finite_dimensional_vector_space_on_with)


lemma module_pair_with_imp_module_with[explicit_ab_group_add]:
  "module_on_with S (+) (-) uminus 0 s"
  "module_on_with T (+) (-) uminus 0 t"
  if "module_pair_on_with S T (+) (-) uminus 0 s (+) (-) uminus 0 t"
  using that
  unfolding module_pair_on_with_def
  by simp_all

lemma vector_space_pair_with_imp_vector_space_with[explicit_ab_group_add]:
  "vector_space_on_with S (+) (-) uminus 0 s"
  "vector_space_on_with T (+) (-) uminus 0 t"
  if "vector_space_pair_on_with S T(+) (-) uminus 0 s (+) (-) uminus 0 t"
  using that
  by (auto simp: vector_space_pair_on_with_def module_pair_on_with_def vector_space_on_with_def)

lemma finite_dimensional_vector_space_pair_with_imp_finite_dimensional_vector_space_with[explicit_ab_group_add]:
  "finite_dimensional_vector_space_on_with S (+) (-) uminus 0 s b"
  "finite_dimensional_vector_space_on_with T (+) (-) uminus 0 t c"
  if "finite_dimensional_vector_space_pair_on_with S T (+) (-) uminus 0 s b (+) (-) uminus 0 t c"
  using that
  unfolding finite_dimensional_vector_space_pair_on_with_def
  by simp_all

lemma finite_dimensional_vector_space_pair_with_imp_vector_space_with[explicit_ab_group_add]:
  \<comment>\<open>this rule is strange: why is it needed, but not the one with \<open>module_with\<close> as conclusions?\<close>
  "vector_space_on_with S (+) (-) uminus 0 s"
  "vector_space_on_with T (+) (-) uminus 0 t"
  if "finite_dimensional_vector_space_pair_on_with S T (+) (-) uminus 0 s b (+) (-) uminus 0 t c"
  using that
  by (auto simp: finite_dimensional_vector_space_pair_on_with_def finite_dimensional_vector_space_on_with_def)

lemma finite_dimensional_vector_space_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows
    "(rel_set A ===>
    (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===>
    rel_set A ===>
    (=)) (finite_dimensional_vector_space_on_with) finite_dimensional_vector_space_on_with"
  unfolding finite_dimensional_vector_space_on_with_def
  by transfer_prover

lemma finite_dimensional_vector_space_pair_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A" "right_total C" "bi_unique C"
  shows
    "(rel_set A ===> rel_set C ===>
    (A ===> A ===> A) ===> (A ===> A ===> A) ===> (A ===> A) ===> A ===> ((=) ===> A ===> A) ===>
    rel_set A ===>
    (C ===> C ===> C) ===> (C ===> C ===> C) ===> (C ===> C) ===> C ===> ((=) ===> C ===> C) ===>
    rel_set C ===>
    (=)) (finite_dimensional_vector_space_pair_on_with) finite_dimensional_vector_space_pair_on_with"
  unfolding finite_dimensional_vector_space_pair_on_with_def
  by transfer_prover

end