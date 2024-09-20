(*  Title:      HOL/Types_To_Sets/Examples/Linear_Algebra_On.thy
    Author:     Fabian Immler, TU München
*)
theory Linear_Algebra_On
  imports
    "Prerequisites"
    "../Types_To_Sets"
    Linear_Algebra_On_With
begin

subsection \<open>Rewrite rules to make \<open>ab_group_add\<close> operations implicit.\<close>

named_theorems implicit_ab_group_add

lemmas [implicit_ab_group_add] = sum_with[symmetric]

lemma semigroup_add_on_with_eq[implicit_ab_group_add]:
  "semigroup_add_on_with S ((+)::_::semigroup_add \<Rightarrow> _) \<longleftrightarrow> (\<forall>a\<in>S. \<forall>b\<in>S. a + b \<in> S)"
  by (simp add: semigroup_add_on_with_Ball_def ac_simps)

lemma ab_semigroup_add_on_with_eq[implicit_ab_group_add]:
  "ab_semigroup_add_on_with S ((+)::_::ab_semigroup_add \<Rightarrow> _) = semigroup_add_on_with S (+)"
  unfolding ab_semigroup_add_on_with_Ball_def
  by (simp add: semigroup_add_on_with_eq ac_simps)

lemma comm_monoid_add_on_with_eq[implicit_ab_group_add]:
  "comm_monoid_add_on_with S ((+)::_::comm_monoid_add \<Rightarrow> _) 0 \<longleftrightarrow> semigroup_add_on_with S (+) \<and> 0 \<in> S"
  unfolding comm_monoid_add_on_with_Ball_def
  by (simp add: ab_semigroup_add_on_with_eq ac_simps)

lemma ab_group_add_on_with[implicit_ab_group_add]:
  "ab_group_add_on_with S ((+)::_::ab_group_add \<Rightarrow> _) 0 (-) uminus \<longleftrightarrow>
    comm_monoid_add_on_with S (+) 0 \<and> (\<forall>a\<in>S. -a\<in>S)"
  unfolding ab_group_add_on_with_Ball_def
  by simp

subsection \<open>Definitions \<^emph>\<open>on\<close> carrier set\<close>

locale module_on =
  fixes S and scale :: "'a::comm_ring_1 \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*s\<close> 75)
  assumes scale_right_distrib_on [algebra_simps]: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> a *s (x + y) = a *s x + a *s y"
    and scale_left_distrib_on [algebra_simps]: "x \<in> S \<Longrightarrow> (a + b) *s x = a *s x + b *s x"
    and scale_scale_on [simp]: "x \<in> S \<Longrightarrow> a *s (b *s x) = (a * b) *s x"
    and scale_one_on [simp]: "x \<in> S \<Longrightarrow> 1 *s x = x"
    and mem_add: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x + y \<in> S"
    and mem_zero: "0 \<in> S"
    and mem_scale: "x \<in> S \<Longrightarrow> a *s x \<in> S"
begin

lemma S_ne: "S \<noteq> {}" using mem_zero by auto

lemma scale_minus_left_on: "scale (- a) x = - scale a x" if "x \<in> S"
  by (metis add_cancel_right_right scale_left_distrib_on neg_eq_iff_add_eq_0 that)

lemma mem_uminus: "x \<in> S \<Longrightarrow> -x \<in> S"
  by (metis mem_scale scale_minus_left_on scale_one_on)

definition subspace :: "'b set \<Rightarrow> bool"
  where subspace_on_def: "subspace T \<longleftrightarrow> 0 \<in> T \<and> (\<forall>x\<in>T. \<forall>y\<in>T. x + y \<in> T) \<and> (\<forall>c. \<forall>x\<in>T. c *s x \<in> T)"

definition span :: "'b set \<Rightarrow> 'b set"
  where span_on_def: "span b = {sum (\<lambda>a. r a *s  a) t | t r. finite t \<and> t \<subseteq> b}"

definition dependent :: "'b set \<Rightarrow> bool"
  where dependent_on_def: "dependent s \<longleftrightarrow> (\<exists>t u. finite t \<and> t \<subseteq> s \<and> (sum (\<lambda>v. u v *s v) t = 0 \<and> (\<exists>v\<in>t. u v \<noteq> 0)))"

lemma implicit_subspace_with[implicit_ab_group_add]: "subspace_with (+) 0 (*s) = subspace"
  unfolding subspace_on_def subspace_with_def ..

lemma implicit_dependent_with[implicit_ab_group_add]: "dependent_with (+) 0 (*s) = dependent"
  unfolding dependent_on_def dependent_with_def sum_with ..

lemma implicit_span_with[implicit_ab_group_add]: "span_with (+) 0 (*s) = span"
  unfolding span_on_def span_with_def sum_with ..

end

lemma implicit_module_on_with[implicit_ab_group_add]:
  "module_on_with S (+) (-) uminus 0 = module_on S"
proof (intro ext iffI)
  fix s::"'a\<Rightarrow>'b\<Rightarrow>'b" assume "module_on S s"
  then interpret module_on S s .
  show "module_on_with S (+) (-) uminus 0 s"
    by (auto simp: module_on_with_def implicit_ab_group_add
        mem_add mem_zero mem_uminus scale_right_distrib_on scale_left_distrib_on mem_scale)
qed (auto simp: module_on_with_def module_on_def implicit_ab_group_add)

locale module_pair_on = m1: module_on S1 scale1 +
                        m2: module_on S2 scale2
                        for S1:: "'b::ab_group_add set" and S2::"'c::ab_group_add set"
                          and scale1::"'a::comm_ring_1 \<Rightarrow> _" and scale2::"'a \<Rightarrow> _"

lemma implicit_module_pair_on_with[implicit_ab_group_add]:
  "module_pair_on_with S1 S2 (+) (-) uminus 0 s1 (+) (-) uminus 0 s2 = module_pair_on S1 S2 s1 s2"
  unfolding module_pair_on_with_def implicit_module_on_with module_pair_on_def ..

locale module_hom_on = m1: module_on S1 s1 + m2: module_on S2 s2
  for S1 :: "'b::ab_group_add set" and S2 :: "'c::ab_group_add set"
    and s1 :: "'a::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> 'b" (infixr \<open>*a\<close> 75)
    and s2 :: "'a::comm_ring_1 \<Rightarrow> 'c \<Rightarrow> 'c" (infixr \<open>*b\<close> 75) +
  fixes f :: "'b \<Rightarrow> 'c"
  assumes add: "\<And>b1 b2. b1 \<in> S1 \<Longrightarrow> b2 \<in> S1 \<Longrightarrow> f (b1 + b2) = f b1 + f b2"
    and scale: "\<And>b. b \<in> S1 \<Longrightarrow> f (r *a b) = r *b f b"

lemma implicit_module_hom_on_with[implicit_ab_group_add]:
  "module_hom_on_with S1 S2 (+) (-) uminus 0 s1 (+) (-) uminus 0 s2 = module_hom_on S1 S2 s1 s2"
  unfolding module_hom_on_with_def implicit_module_pair_on_with module_hom_on_def module_pair_on_def
    module_hom_on_axioms_def
  by (auto intro!: ext)

locale vector_space_on = module_on S scale
  for S and scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr \<open>*s\<close> 75)
begin

definition dim :: "'b set \<Rightarrow> nat"
  where "dim V = (if \<exists>b\<subseteq>S. \<not> dependent b \<and> span b = span V
    then card (SOME b. b \<subseteq> S \<and> \<not> dependent b \<and> span b = span V)
    else 0)"

lemma implicit_dim_with[implicit_ab_group_add]: "dim_on_with S (+) 0 (*s) = dim"
  unfolding dim_on_with_def dim_def implicit_ab_group_add ..

end

lemma vector_space_on_alt_def: "vector_space_on S = module_on S"
  unfolding vector_space_on_def module_on_def
  by auto

lemma implicit_vector_space_on_with[implicit_ab_group_add]:
  "vector_space_on_with S (+) (-) uminus 0 = vector_space_on S"
  unfolding vector_space_on_alt_def vector_space_on_def vector_space_on_with_def implicit_module_on_with ..

locale linear_on = module_hom_on S1 S2 s1 s2 f
  for S1 S2 and s1::"'a::field \<Rightarrow> 'b \<Rightarrow> 'b::ab_group_add"
    and s2::"'a::field \<Rightarrow> 'c \<Rightarrow> 'c::ab_group_add"
    and f

lemma implicit_linear_on_with[implicit_ab_group_add]:
  "linear_on_with S1 S2 (+) (-) uminus 0 s1 (+) (-) uminus 0 s2 = linear_on S1 S2 s1 s2"
  unfolding linear_on_with_def linear_on_def implicit_module_hom_on_with ..

locale finite_dimensional_vector_space_on = vector_space_on S scale for S scale +
  fixes basis :: "'a set"
  assumes finite_Basis: "finite basis"
  and independent_Basis: "\<not> dependent basis"
  and span_Basis: "span basis = S" and basis_subset: "basis \<subseteq> S"

locale vector_space_pair_on = m1: vector_space_on S1 scale1 +
  m2: vector_space_on S2 scale2
  for S1:: "'b::ab_group_add set" and S2::"'c::ab_group_add set"
    and scale1::"'a::field \<Rightarrow> _" and scale2::"'a \<Rightarrow> _"

locale finite_dimensional_vector_space_pair_1_on =
  vs1: finite_dimensional_vector_space_on S1 scale1 Basis1 +
  vs2: vector_space_on S2 scale2
  for S1 S2
    and scale1::"'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
    and scale2::"'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c"
    and Basis1

locale finite_dimensional_vector_space_pair_on =
  vs1: finite_dimensional_vector_space_on S1 scale1 Basis1 +
  vs2: finite_dimensional_vector_space_on S2 scale2 Basis2
  for S1 S2
    and scale1::"'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b"
    and scale2::"'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c"
    and Basis1 Basis2


subsection \<open>Local Typedef for Subspace\<close>

locale local_typedef_module_on = module_on S scale
  for S and scale::"'a::comm_ring_1\<Rightarrow>'b\<Rightarrow>'b::ab_group_add" and s::"'s itself" +
  assumes Ex_type_definition_S: "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S"
begin

lemma mem_sum: "sum f X \<in> S" if "\<And>x. x \<in> X \<Longrightarrow> f x \<in> S"
  using that
  by (induction X rule: infinite_finite_induct) (auto intro!: mem_zero mem_add)

sublocale local_typedef S "TYPE('s)"
  using Ex_type_definition_S by unfold_locales

sublocale local_typedef_ab_group_add_on_with "(+)::'b\<Rightarrow>'b\<Rightarrow>'b" "0::'b" "(-)" uminus S "TYPE('s)"
  using mem_zero mem_add mem_scale[of _ "-1"]
  by unfold_locales (auto simp: scale_minus_left_on)

context includes lifting_syntax begin

definition scale_S::"'a \<Rightarrow> 's \<Rightarrow> 's" where "scale_S = (id ---> rep ---> Abs) scale"

lemma scale_S_transfer[transfer_rule]: "((=) ===> cr_S ===> cr_S) scale scale_S"
  unfolding scale_S_def
  by (auto simp: cr_S_def mem_scale intro!: rel_funI)

end

lemma type_module_on_with: "module_on_with UNIV plus_S minus_S uminus_S (zero_S::'s) scale_S"
proof -
  have "module_on_with {x. x \<in> S} (+) (-) uminus 0 scale"
    using module_on_axioms
    by (auto simp: module_on_with_def module_on_def ab_group_add_on_with_Ball_def
        comm_monoid_add_on_with_Ball_def mem_uminus
        ab_semigroup_add_on_with_Ball_def semigroup_add_on_with_def)
  then show ?thesis
    by transfer'
qed

lemma UNIV_transfer[transfer_rule]: "(rel_set cr_S) S UNIV"
  by (auto simp: rel_set_def cr_S_def) (metis Abs_inverse)

end

context includes lifting_syntax begin

lemma Eps_unique_transfer_lemma:
  "f' (Eps (\<lambda>x. Domainp A x \<and> f x)) = g' (Eps g)"
  if [transfer_rule]: "right_total A" "(A ===> (=)) f g" "(A ===> (=)) f' g'"
    and holds: "\<exists>x. Domainp A x \<and> f x"
    and unique_g: "\<And>x y. g x \<Longrightarrow> g y \<Longrightarrow> g' x = g' y"
proof -
  define Epsg where "Epsg = Eps g"
  have "\<exists>x. g x"
    by transfer (simp add: holds)
  then have "g Epsg"
    unfolding Epsg_def
    by (rule someI_ex)
  obtain x where x[transfer_rule]: "A x Epsg"
    by (meson \<open>right_total A\<close> right_totalE)
  then have "Domainp A x" by auto
  from \<open>g Epsg\<close>[untransferred] have "f x" .
  from unique_g have unique:
    "\<And>x y. Domainp A x \<Longrightarrow> Domainp A y \<Longrightarrow> f x \<Longrightarrow> f y \<Longrightarrow> f' x = f' y"
    by transfer
  have "f' (Eps (\<lambda>x. Domainp A x \<and> f x)) = f' x"
    apply (rule unique[OF _ \<open>Domainp A x\<close> _ \<open>f x\<close>])
    apply (metis (mono_tags, lifting) local.holds someI_ex)
    apply (metis (mono_tags, lifting) local.holds someI_ex)
    done
  show "f' (SOME x. Domainp A x \<and> f x) = g' (Eps g)"
    using x \<open>f' (Eps _) = f' x\<close> Epsg_def
    using rel_funE that(3) by fastforce
qed

end

locale local_typedef_vector_space_on = local_typedef_module_on S scale s + vector_space_on S scale
  for S and scale::"'a::field\<Rightarrow>'b\<Rightarrow>'b::ab_group_add" and s::"'s itself"
begin

lemma type_vector_space_on_with: "vector_space_on_with UNIV plus_S minus_S uminus_S (zero_S::'s) scale_S"
  using type_module_on_with
  by (auto simp: vector_space_on_with_def)

context includes lifting_syntax begin

definition dim_S::"'s set \<Rightarrow> nat" where "dim_S = dim_on_with UNIV plus_S zero_S scale_S"

lemma transfer_dim[transfer_rule]: "(rel_set cr_S ===> (=)) dim dim_S"
proof (rule rel_funI)
  fix V V'
  assume [transfer_rule]: "rel_set cr_S V V'"
  then have subset: "V \<subseteq> S"
    by (auto simp: rel_set_def cr_S_def)
  then have "span V \<subseteq> S"
    by (auto simp: span_on_def intro!: mem_sum mem_scale)
  note type_dim_eq_card =
    vector_space.dim_eq_card[var_simplified explicit_ab_group_add, unoverload_type 'd,
      OF type.ab_group_add_axioms type_vector_space_on_with]
  have *: "(\<exists>b\<subseteq>UNIV. \<not> dependent_with plus_S zero_S scale_S b \<and> span_with plus_S zero_S scale_S b = span_with plus_S zero_S scale_S V') \<longleftrightarrow>
    (\<exists>b\<subseteq>S. \<not> local.dependent b \<and> local.span b = local.span V)"
    unfolding subset_iff
    by transfer (simp add: implicit_ab_group_add Ball_def)
  have **[symmetric]:
    "card (SOME b. Domainp (rel_set cr_S) b \<and> (\<not> dependent_with (+) 0 scale b \<and> span_with (+) 0 scale b = span_with (+) 0 scale V)) =
      card (SOME b. \<not> dependent_with plus_S zero_S scale_S b \<and> span_with plus_S zero_S scale_S b = span_with plus_S zero_S scale_S V')"
    if "b \<subseteq> S" "\<not>dependent b" "span b = span V" for b
    apply (rule Eps_unique_transfer_lemma[where f'=card and g'=card])
    subgoal by (rule right_total_rel_set) (rule transfer_raw)
    subgoal by transfer_prover
    subgoal by transfer_prover
    subgoal using that by (auto simp: implicit_ab_group_add Domainp_set Domainp_cr_S)
    subgoal premises prems for b c
    proof -
      from type_dim_eq_card[of b V'] type_dim_eq_card[of c V'] prems
      show ?thesis by simp
    qed
    done
  show "local.dim V = dim_S V'"
    unfolding dim_def dim_S_def * dim_on_with_def
    by (auto simp: ** Domainp_set Domainp_cr_S implicit_ab_group_add subset_eq)
qed

end


end

locale local_typedef_finite_dimensional_vector_space_on = local_typedef_vector_space_on S scale s +
  finite_dimensional_vector_space_on S scale Basis
  for S and scale::"'a::field\<Rightarrow>'b\<Rightarrow>'b::ab_group_add" and Basis and s::"'s itself"
begin

definition "Basis_S = Abs ` Basis"

lemma Basis_S_transfer[transfer_rule]: "rel_set cr_S Basis Basis_S"
  using Abs_inverse rep_inverse basis_subset
  by (force simp: rel_set_def Basis_S_def cr_S_def)

lemma type_finite_dimensional_vector_space_on_with:
  "finite_dimensional_vector_space_on_with UNIV plus_S minus_S uminus_S zero_S scale_S Basis_S"
proof -
  have "finite Basis_S" by transfer (rule finite_Basis)
  moreover have "\<not> dependent_with plus_S zero_S scale_S Basis_S"
    by transfer (simp add: implicit_dependent_with independent_Basis)
  moreover have "span_with plus_S zero_S scale_S Basis_S = UNIV"
    by transfer (simp add: implicit_span_with span_Basis)
  ultimately show ?thesis
    using type_vector_space_on_with
    by (auto simp: finite_dimensional_vector_space_on_with_def)
qed

end

locale local_typedef_module_pair =
  lt1: local_typedef_module_on S1 scale1 s +
  lt2: local_typedef_module_on S2 scale2 t
  for S1::"'b::ab_group_add set" and scale1::"'a::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> 'b" and s::"'s itself"
    and S2::"'c::ab_group_add set" and scale2::"'a \<Rightarrow> 'c \<Rightarrow> 'c" and t::"'t itself"
begin

lemma type_module_pair_on_with:
  "module_pair_on_with UNIV UNIV lt1.plus_S lt1.minus_S lt1.uminus_S (lt1.zero_S::'s) lt1.scale_S
  lt2.plus_S lt2.minus_S lt2.uminus_S (lt2.zero_S::'t) lt2.scale_S"
  by (simp add: lt1.type_module_on_with lt2.type_module_on_with module_pair_on_with_def)

end

locale local_typedef_vector_space_pair =
  local_typedef_module_pair S1 scale1 s S2 scale2 t
  for S1::"'b::ab_group_add set" and scale1::"'a::field \<Rightarrow> 'b \<Rightarrow> 'b" and s::"'s itself"
    and S2::"'c::ab_group_add set" and scale2::"'a \<Rightarrow> 'c \<Rightarrow> 'c" and t::"'t itself"
begin

lemma type_vector_space_pair_on_with:
  "vector_space_pair_on_with UNIV UNIV lt1.plus_S lt1.minus_S lt1.uminus_S (lt1.zero_S::'s) lt1.scale_S
  lt2.plus_S lt2.minus_S lt2.uminus_S (lt2.zero_S::'t) lt2.scale_S"
  by (simp add: type_module_pair_on_with vector_space_pair_on_with_def)

sublocale lt1: local_typedef_vector_space_on S1 scale1 s by unfold_locales
sublocale lt2: local_typedef_vector_space_on S2 scale2 t by unfold_locales

end

locale local_typedef_finite_dimensional_vector_space_pair_1 =
  lt1: local_typedef_finite_dimensional_vector_space_on S1 scale1 Basis1 s +
  lt2: local_typedef_vector_space_on S2 scale2 t
  for S1::"'b::ab_group_add set" and scale1::"'a::field \<Rightarrow> 'b \<Rightarrow> 'b" and Basis1 and s::"'s itself"
    and S2::"'c::ab_group_add set" and scale2::"'a \<Rightarrow> 'c \<Rightarrow> 'c" and t::"'t itself"
begin

lemma type_finite_dimensional_vector_space_pair_1_on_with:
  "finite_dimensional_vector_space_pair_1_on_with UNIV UNIV lt1.plus_S lt1.minus_S lt1.uminus_S (lt1.zero_S::'s) lt1.scale_S lt1.Basis_S
  lt2.plus_S lt2.minus_S lt2.uminus_S (lt2.zero_S::'t) lt2.scale_S"
  by (simp add: finite_dimensional_vector_space_pair_1_on_with_def
      lt1.type_finite_dimensional_vector_space_on_with lt2.type_vector_space_on_with)

end

locale local_typedef_finite_dimensional_vector_space_pair =
  lt1: local_typedef_finite_dimensional_vector_space_on S1 scale1 Basis1 s +
  lt2: local_typedef_finite_dimensional_vector_space_on S2 scale2 Basis2 t
  for S1::"'b::ab_group_add set" and scale1::"'a::field \<Rightarrow> 'b \<Rightarrow> 'b" and Basis1 and s::"'s itself"
    and S2::"'c::ab_group_add set" and scale2::"'a \<Rightarrow> 'c \<Rightarrow> 'c" and Basis2 and t::"'t itself"
begin

lemma type_finite_dimensional_vector_space_pair_on_with:
  "finite_dimensional_vector_space_pair_on_with UNIV UNIV lt1.plus_S lt1.minus_S lt1.uminus_S (lt1.zero_S::'s) lt1.scale_S lt1.Basis_S
  lt2.plus_S lt2.minus_S lt2.uminus_S (lt2.zero_S::'t) lt2.scale_S lt2.Basis_S"
  by (simp add: finite_dimensional_vector_space_pair_on_with_def
      lt1.type_finite_dimensional_vector_space_on_with
      lt2.type_finite_dimensional_vector_space_on_with)

end


subsection \<open>Transfer from type-based \<^theory>\<open>HOL.Modules\<close> and \<^theory>\<open>HOL.Vector_Spaces\<close>\<close>

lemmas [transfer_rule] = right_total_fun_eq_transfer
  and [transfer_rule del] = vimage_parametric

subsubsection \<open>Modules\<close>

context module_on begin

context includes lifting_syntax assumes ltd: "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S" begin

interpretation local_typedef_module_on S scale "TYPE('s)" by unfold_locales fact

text\<open>Get theorem names:\<close>
print_locale! module
text\<open>Then replace:
\<^verbatim>\<open>notes[^"]*"([^"]*).*\<close>
with
\<^verbatim>\<open>$1 = module.$1\<close>
\<close>
text \<open>TODO: automate systematic naming!\<close>
lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'd,
    OF type.ab_group_add_axioms type_module_on_with,
    untransferred,
    var_simplified implicit_ab_group_add]:
    lt_scale_left_commute = module.scale_left_commute
  and lt_scale_zero_left = module.scale_zero_left
  and lt_scale_minus_left = module.scale_minus_left
  and lt_scale_left_diff_distrib = module.scale_left_diff_distrib
  and lt_scale_sum_left = module.scale_sum_left
  and lt_scale_zero_right = module.scale_zero_right
  and lt_scale_minus_right = module.scale_minus_right
  and lt_scale_right_diff_distrib = module.scale_right_diff_distrib
  and lt_scale_sum_right = module.scale_sum_right
  and lt_sum_constant_scale = module.sum_constant_scale
  and lt_subspace_def = module.subspace_def
  and lt_subspaceI = module.subspaceI
  and lt_subspace_single_0 = module.subspace_single_0
  and lt_subspace_0 = module.subspace_0
  and lt_subspace_add = module.subspace_add
  and lt_subspace_scale = module.subspace_scale
  and lt_subspace_neg = module.subspace_neg
  and lt_subspace_diff = module.subspace_diff
  and lt_subspace_sum = module.subspace_sum
  and lt_subspace_inter = module.subspace_inter
  and lt_span_explicit = module.span_explicit
  and lt_span_explicit' = module.span_explicit'
  and lt_span_finite = module.span_finite
  and lt_span_induct_alt = module.span_induct_alt
  and lt_span_mono = module.span_mono
  and lt_span_base = module.span_base
  and lt_span_superset = module.span_superset
  and lt_span_zero = module.span_zero
  and lt_span_add = module.span_add
  and lt_span_scale = module.span_scale
  and lt_subspace_span = module.subspace_span
  and lt_span_neg = module.span_neg
  and lt_span_diff = module.span_diff
  and lt_span_sum = module.span_sum
  and lt_span_minimal = module.span_minimal
  and lt_span_unique = module.span_unique
  and lt_span_subspace_induct = module.span_subspace_induct
  and lt_span_induct = module.span_induct
  and lt_span_empty = module.span_empty
  and lt_span_subspace = module.span_subspace
  and lt_span_span = module.span_span
  and lt_span_add_eq = module.span_add_eq
  and lt_span_add_eq2 = module.span_add_eq2
  and lt_span_singleton = module.span_singleton
  and lt_span_Un = module.span_Un
  and lt_span_insert = module.span_insert
  and lt_span_breakdown = module.span_breakdown
  and lt_span_breakdown_eq = module.span_breakdown_eq
  and lt_span_clauses = module.span_clauses
  and lt_span_eq_iff = module.span_eq_iff
  and lt_span_eq = module.span_eq
  and lt_eq_span_insert_eq = module.eq_span_insert_eq
  and lt_dependent_explicit = module.dependent_explicit
  and lt_dependent_mono = module.dependent_mono
  and lt_independent_mono = module.independent_mono
  and lt_dependent_zero = module.dependent_zero
  and lt_independent_empty = module.independent_empty
  and lt_independent_explicit_module = module.independent_explicit_module
  and lt_independentD = module.independentD
  and lt_independent_Union_directed = module.independent_Union_directed
  and lt_dependent_finite = module.dependent_finite
  and lt_independentD_alt = module.independentD_alt
  and lt_independentD_unique = module.independentD_unique
  and lt_spanning_subset_independent = module.spanning_subset_independent
  and lt_module_hom_scale_self = module.module_hom_scale_self
  and lt_module_hom_scale_left = module.module_hom_scale_left
  and lt_module_hom_id = module.module_hom_id
  and lt_module_hom_ident = module.module_hom_ident
  and lt_module_hom_uminus = module.module_hom_uminus
  and lt_subspace_UNIV = module.subspace_UNIV
(* should work but don't:
  and span_def = module.span_def
  and span_UNIV = module.span_UNIV
  and lt_span_alt = module.span_alt
  and dependent_alt = module.dependent_alt
  and independent_alt = module.independent_alt
  and unique_representation = module.unique_representation
  and subspace_Int = module.subspace_Int
  and subspace_Inter = module.subspace_Inter
*)
(* not expected to work:
and representation_ne_zero = module.representation_ne_zero
and representation_ne_zero = module.representation_ne_zero
and finite_representation = module.finite_representation
and sum_nonzero_representation_eq = module.sum_nonzero_representation_eq
and sum_representation_eq = module.sum_representation_eq
and representation_eqI = module.representation_eqI
and representation_basis = module.representation_basis
and representation_zero = module.representation_zero
and representation_diff = module.representation_diff
and representation_neg = module.representation_neg
and representation_add = module.representation_add
and representation_sum = module.representation_sum
and representation_scale = module.representation_scale
and representation_extend = module.representation_extend
end
*)

end

lemmas_with [cancel_type_definition,
    OF S_ne,
    folded subset_iff',
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
      scale_left_commute = lt_scale_left_commute
  and scale_zero_left = lt_scale_zero_left
  and scale_minus_left = lt_scale_minus_left
  and scale_left_diff_distrib = lt_scale_left_diff_distrib
  and scale_sum_left = lt_scale_sum_left
  and scale_zero_right = lt_scale_zero_right
  and scale_minus_right = lt_scale_minus_right
  and scale_right_diff_distrib = lt_scale_right_diff_distrib
  and scale_sum_right = lt_scale_sum_right
  and sum_constant_scale = lt_sum_constant_scale
  and subspace_def = lt_subspace_def
  and subspaceI = lt_subspaceI
  and subspace_single_0 = lt_subspace_single_0
  and subspace_0 = lt_subspace_0
  and subspace_add = lt_subspace_add
  and subspace_scale = lt_subspace_scale
  and subspace_neg = lt_subspace_neg
  and subspace_diff = lt_subspace_diff
  and subspace_sum = lt_subspace_sum
  and subspace_inter = lt_subspace_inter
  and span_explicit = lt_span_explicit
  and span_explicit' = lt_span_explicit'
  and span_finite = lt_span_finite
  and span_induct_alt[consumes 1, case_names base step, induct set : span] = lt_span_induct_alt
  and span_mono = lt_span_mono
  and span_base = lt_span_base
  and span_superset = lt_span_superset
  and span_zero = lt_span_zero
  and span_add = lt_span_add
  and span_scale = lt_span_scale
  and subspace_span = lt_subspace_span
  and span_neg = lt_span_neg
  and span_diff = lt_span_diff
  and span_sum = lt_span_sum
  and span_minimal = lt_span_minimal
  and span_unique = lt_span_unique
  and span_subspace_induct[consumes 2] = lt_span_subspace_induct
  and span_induct[consumes 1, case_names base step, induct set : span] = lt_span_induct
  and span_empty = lt_span_empty
  and span_subspace = lt_span_subspace
  and span_span = lt_span_span
  and span_add_eq = lt_span_add_eq
  and span_add_eq2 = lt_span_add_eq2
  and span_singleton = lt_span_singleton
  and span_Un = lt_span_Un
  and span_insert = lt_span_insert
  and span_breakdown = lt_span_breakdown
  and span_breakdown_eq = lt_span_breakdown_eq
  and span_clauses = lt_span_clauses
  and span_eq_iff = lt_span_eq_iff
  and span_eq = lt_span_eq
  and eq_span_insert_eq = lt_eq_span_insert_eq
  and dependent_explicit = lt_dependent_explicit
  and dependent_mono = lt_dependent_mono
  and independent_mono = lt_independent_mono
  and dependent_zero = lt_dependent_zero
  and independent_empty = lt_independent_empty
  and independent_explicit_module = lt_independent_explicit_module
  and independentD = lt_independentD
  and independent_Union_directed = lt_independent_Union_directed
  and dependent_finite = lt_dependent_finite
  and independentD_alt = lt_independentD_alt
  and independentD_unique = lt_independentD_unique
  and spanning_subset_independent = lt_spanning_subset_independent
  and module_hom_scale_self = lt_module_hom_scale_self
  and module_hom_scale_left = lt_module_hom_scale_left
  and module_hom_id = lt_module_hom_id
  and module_hom_ident = lt_module_hom_ident
  and module_hom_uminus = lt_module_hom_uminus
  and subspace_UNIV = lt_subspace_UNIV
end

subsubsection \<open>Vector Spaces\<close>

context vector_space_on begin

context includes lifting_syntax assumes "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S" begin

interpretation local_typedef_vector_space_on S scale "TYPE('s)" by unfold_locales fact

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'd,
    OF type.ab_group_add_axioms type_vector_space_on_with,
    folded dim_S_def,
    untransferred,
    var_simplified implicit_ab_group_add]:
    lt_linear_id = vector_space.linear_id
and lt_linear_ident = vector_space.linear_ident
and lt_linear_scale_self = vector_space.linear_scale_self
and lt_linear_scale_left = vector_space.linear_scale_left
and lt_linear_uminus = vector_space.linear_uminus
and lt_linear_imp_scale["consumes" - 1, "case_names" "1"] = vector_space.linear_imp_scale
and lt_scale_eq_0_iff = vector_space.scale_eq_0_iff
and lt_scale_left_imp_eq = vector_space.scale_left_imp_eq
and lt_scale_right_imp_eq = vector_space.scale_right_imp_eq
and lt_scale_cancel_left = vector_space.scale_cancel_left
and lt_scale_cancel_right = vector_space.scale_cancel_right
and lt_injective_scale = vector_space.injective_scale
and lt_dependent_def = vector_space.dependent_def
and lt_dependent_single = vector_space.dependent_single
and lt_in_span_insert = vector_space.in_span_insert
and lt_dependent_insertD = vector_space.dependent_insertD
and lt_independent_insertI = vector_space.independent_insertI
and lt_independent_insert = vector_space.independent_insert
and lt_maximal_independent_subset_extend["consumes" - 1, "case_names" "1"] = vector_space.maximal_independent_subset_extend
and lt_maximal_independent_subset["consumes" - 1, "case_names" "1"] = vector_space.maximal_independent_subset
and lt_in_span_delete = vector_space.in_span_delete
and lt_span_redundant = vector_space.span_redundant
and lt_span_trans = vector_space.span_trans
and lt_span_insert_0 = vector_space.span_insert_0
and lt_span_delete_0 = vector_space.span_delete_0
and lt_span_image_scale = vector_space.span_image_scale
and lt_exchange_lemma = vector_space.exchange_lemma
and lt_independent_span_bound = vector_space.independent_span_bound
and lt_independent_explicit_finite_subsets = vector_space.independent_explicit_finite_subsets
and lt_independent_if_scalars_zero = vector_space.independent_if_scalars_zero
and lt_subspace_sums = vector_space.subspace_sums
and lt_dim_unique = vector_space.dim_unique
and lt_dim_eq_card = vector_space.dim_eq_card
and lt_basis_card_eq_dim = vector_space.basis_card_eq_dim
and lt_basis_exists = vector_space.basis_exists
and lt_dim_eq_card_independent = vector_space.dim_eq_card_independent
and lt_dim_span = vector_space.dim_span
and lt_dim_span_eq_card_independent = vector_space.dim_span_eq_card_independent
and lt_dim_le_card = vector_space.dim_le_card
and lt_span_eq_dim = vector_space.span_eq_dim
and lt_dim_le_card' = vector_space.dim_le_card'
and lt_span_card_ge_dim = vector_space.span_card_ge_dim
and lt_dim_with = vector_space.dim_with
(* should work but don't:v

and lt_bij_if_span_eq_span_bases = vector_space.bij_if_span_eq_span_bases
*)
(* not expected to work:
and lt_dim_def = vector_space.dim_def
and lt_extend_basis_superset = vector_space.extend_basis_superset
and lt_independent_extend_basis = vector_space.independent_extend_basis
and lt_span_extend_basis = vector_space.span_extend_basis
*)

end

lemmas_with [cancel_type_definition,
    OF S_ne,
    folded subset_iff',
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
    linear_id = lt_linear_id
and linear_ident = lt_linear_ident
and linear_scale_self = lt_linear_scale_self
and linear_scale_left = lt_linear_scale_left
and linear_uminus = lt_linear_uminus
and linear_imp_scale["consumes" - 1, "case_names" "1"] = lt_linear_imp_scale
and scale_eq_0_iff = lt_scale_eq_0_iff
and scale_left_imp_eq = lt_scale_left_imp_eq
and scale_right_imp_eq = lt_scale_right_imp_eq
and scale_cancel_left = lt_scale_cancel_left
and scale_cancel_right = lt_scale_cancel_right
and dependent_def = lt_dependent_def
and dependent_single = lt_dependent_single
and in_span_insert = lt_in_span_insert
and dependent_insertD = lt_dependent_insertD
and independent_insertI = lt_independent_insertI
and independent_insert = lt_independent_insert
and maximal_independent_subset_extend["consumes" - 1, "case_names" "1"] = lt_maximal_independent_subset_extend
and maximal_independent_subset["consumes" - 1, "case_names" "1"] = lt_maximal_independent_subset
and in_span_delete = lt_in_span_delete
and span_redundant = lt_span_redundant
and span_trans = lt_span_trans
and span_insert_0 = lt_span_insert_0
and span_delete_0 = lt_span_delete_0
and span_image_scale = lt_span_image_scale
and exchange_lemma = lt_exchange_lemma
and independent_span_bound = lt_independent_span_bound
and independent_explicit_finite_subsets = lt_independent_explicit_finite_subsets
and independent_if_scalars_zero = lt_independent_if_scalars_zero
and subspace_sums = lt_subspace_sums
and dim_unique = lt_dim_unique
and dim_eq_card = lt_dim_eq_card
and basis_card_eq_dim = lt_basis_card_eq_dim
and basis_exists["consumes" - 1, "case_names" "1"] = lt_basis_exists
and dim_eq_card_independent = lt_dim_eq_card_independent
and dim_span = lt_dim_span
and dim_span_eq_card_independent = lt_dim_span_eq_card_independent
and dim_le_card = lt_dim_le_card
and span_eq_dim = lt_span_eq_dim
and dim_le_card' = lt_dim_le_card'
and span_card_ge_dim = lt_span_card_ge_dim
and dim_with = lt_dim_with

end

subsubsection \<open>Finite Dimensional Vector Spaces\<close>

context finite_dimensional_vector_space_on begin

context includes lifting_syntax assumes "\<exists>(Rep::'s \<Rightarrow> 'a) (Abs::'a \<Rightarrow> 's). type_definition Rep Abs S" begin

interpretation local_typedef_finite_dimensional_vector_space_on S scale basis "TYPE('s)" by unfold_locales fact

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'd,
    OF type.ab_group_add_axioms type_finite_dimensional_vector_space_on_with,
    folded dim_S_def,
    untransferred,
    var_simplified implicit_ab_group_add]:
     lt_finiteI_independent = finite_dimensional_vector_space.finiteI_independent
and  lt_dim_empty = finite_dimensional_vector_space.dim_empty
and  lt_dim_insert = finite_dimensional_vector_space.dim_insert
and  lt_dim_singleton = finite_dimensional_vector_space.dim_singleton
and  lt_choose_subspace_of_subspace["consumes" - 1, "case_names" "1"] = finite_dimensional_vector_space.choose_subspace_of_subspace
and  lt_basis_subspace_exists["consumes" - 1, "case_names" "1"] = finite_dimensional_vector_space.basis_subspace_exists
and  lt_dim_mono = finite_dimensional_vector_space.dim_mono
and  lt_dim_subset = finite_dimensional_vector_space.dim_subset
and  lt_dim_eq_0 = finite_dimensional_vector_space.dim_eq_0
and  lt_dim_UNIV = finite_dimensional_vector_space.dim_UNIV
and  lt_independent_card_le_dim = finite_dimensional_vector_space.independent_card_le_dim
and  lt_card_ge_dim_independent = finite_dimensional_vector_space.card_ge_dim_independent
and  lt_card_le_dim_spanning = finite_dimensional_vector_space.card_le_dim_spanning
and  lt_card_eq_dim = finite_dimensional_vector_space.card_eq_dim
and  lt_subspace_dim_equal = finite_dimensional_vector_space.subspace_dim_equal
and  lt_dim_eq_span = finite_dimensional_vector_space.dim_eq_span
and  lt_dim_psubset = finite_dimensional_vector_space.dim_psubset
and  lt_indep_card_eq_dim_span = finite_dimensional_vector_space.indep_card_eq_dim_span
and  lt_independent_bound_general = finite_dimensional_vector_space.independent_bound_general
and  lt_independent_explicit = finite_dimensional_vector_space.independent_explicit
and  lt_dim_sums_Int = finite_dimensional_vector_space.dim_sums_Int
and  lt_dependent_biggerset_general = finite_dimensional_vector_space.dependent_biggerset_general
and  lt_subset_le_dim = finite_dimensional_vector_space.subset_le_dim
and  lt_linear_inj_imp_surj = finite_dimensional_vector_space.linear_inj_imp_surj
and  lt_linear_surj_imp_inj = finite_dimensional_vector_space.linear_surj_imp_inj
and  lt_linear_inverse_left = finite_dimensional_vector_space.linear_inverse_left
and  lt_left_inverse_linear = finite_dimensional_vector_space.left_inverse_linear
and  lt_right_inverse_linear = finite_dimensional_vector_space.right_inverse_linear
(* not expected to work:
     lt_dimension_def = finite_dimensional_vector_space.dimension_def
and  lt_dim_subset_UNIV = finite_dimensional_vector_space.dim_subset_UNIV
and  lt_dim_eq_full = finite_dimensional_vector_space.dim_eq_full
and  lt_inj_linear_imp_inv_linear = finite_dimensional_vector_space.inj_linear_imp_inv_linear
*)

end

lemmas_with [cancel_type_definition,
    OF S_ne,
    folded subset_iff',
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
     finiteI_independent = lt_finiteI_independent
and  dim_empty = lt_dim_empty
and  dim_insert = lt_dim_insert
and  dim_singleton = lt_dim_singleton
and  choose_subspace_of_subspace["consumes" - 1, "case_names" "1"] = lt_choose_subspace_of_subspace
and  basis_subspace_exists["consumes" - 1, "case_names" "1"] = lt_basis_subspace_exists
and  dim_mono = lt_dim_mono
and  dim_subset = lt_dim_subset
and  dim_eq_0 = lt_dim_eq_0
and  dim_UNIV = lt_dim_UNIV
and  independent_card_le_dim = lt_independent_card_le_dim
and  card_ge_dim_independent = lt_card_ge_dim_independent
and  card_le_dim_spanning = lt_card_le_dim_spanning
and  card_eq_dim = lt_card_eq_dim
and  subspace_dim_equal = lt_subspace_dim_equal
and  dim_eq_span = lt_dim_eq_span
and  dim_psubset = lt_dim_psubset
and  indep_card_eq_dim_span = lt_indep_card_eq_dim_span
and  independent_bound_general = lt_independent_bound_general
and  independent_explicit = lt_independent_explicit
and  dim_sums_Int = lt_dim_sums_Int
and  dependent_biggerset_general = lt_dependent_biggerset_general
and  subset_le_dim = lt_subset_le_dim
and  linear_inj_imp_surj = lt_linear_inj_imp_surj
and  linear_surj_imp_inj = lt_linear_surj_imp_inj
and  linear_inverse_left = lt_linear_inverse_left
and  left_inverse_linear = lt_left_inverse_linear
and  right_inverse_linear = lt_right_inverse_linear

end

context module_pair_on begin

context includes lifting_syntax
  assumes
    "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S1"
    "\<exists>(Rep::'t \<Rightarrow> 'c) (Abs::'c \<Rightarrow> 't). type_definition Rep Abs S2" begin

interpretation local_typedef_module_pair S1 scale1 "TYPE('s)" S2 scale2 "TYPE('t)" by unfold_locales fact+

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'e 'f,
  OF lt2.type.ab_group_add_axioms lt1.type.ab_group_add_axioms type_module_pair_on_with,
  untransferred,
  var_simplified implicit_ab_group_add]:
  lt_module_hom_zero = module_pair.module_hom_zero
and lt_module_hom_add = module_pair.module_hom_add
and lt_module_hom_sub = module_pair.module_hom_sub
and lt_module_hom_neg = module_pair.module_hom_neg
and lt_module_hom_scale = module_pair.module_hom_scale
and lt_module_hom_compose_scale = module_pair.module_hom_compose_scale
and lt_module_hom_sum = module_pair.module_hom_sum
and lt_module_hom_eq_on_span = module_pair.module_hom_eq_on_span
(* should work, but doesnt
and lt_bij_module_hom_imp_inv_module_hom = module_pair.bij_module_hom_imp_inv_module_hom[of scale1 scale2]
*)

end

lemmas_with [cancel_type_definition, OF m1.S_ne,
  cancel_type_definition, OF m2.S_ne,
    folded subset_iff' top_set_def,
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
  module_hom_zero = lt_module_hom_zero
and module_hom_add = lt_module_hom_add
and module_hom_sub = lt_module_hom_sub
and module_hom_neg = lt_module_hom_neg
and module_hom_scale = lt_module_hom_scale
and module_hom_compose_scale = lt_module_hom_compose_scale
and module_hom_sum = lt_module_hom_sum
and module_hom_eq_on_span = lt_module_hom_eq_on_span

end

context vector_space_pair_on begin

context includes lifting_syntax
  notes [transfer_rule del] = Collect_transfer
  assumes
    "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S1"
    "\<exists>(Rep::'t \<Rightarrow> 'c) (Abs::'c \<Rightarrow> 't). type_definition Rep Abs S2" begin

interpretation local_typedef_vector_space_pair S1 scale1 "TYPE('s)" S2 scale2 "TYPE('t)" by unfold_locales fact+

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'e 'f,
  OF lt2.type.ab_group_add_axioms lt1.type.ab_group_add_axioms type_vector_space_pair_on_with,
  folded lt1.dim_S_def lt2.dim_S_def,
  untransferred,
  var_simplified implicit_ab_group_add]:
  lt_linear_0 = vector_space_pair.linear_0
and lt_linear_add = vector_space_pair.linear_add
and lt_linear_scale = vector_space_pair.linear_scale
and lt_linear_neg = vector_space_pair.linear_neg
and lt_linear_diff = vector_space_pair.linear_diff
and lt_linear_sum = vector_space_pair.linear_sum
and lt_linear_inj_on_iff_eq_0 = vector_space_pair.linear_inj_on_iff_eq_0
and lt_linear_inj_iff_eq_0 = vector_space_pair.linear_inj_iff_eq_0
and lt_linear_subspace_image = vector_space_pair.linear_subspace_image
and lt_linear_subspace_vimage = vector_space_pair.linear_subspace_vimage
and lt_linear_subspace_kernel = vector_space_pair.linear_subspace_kernel
and lt_linear_span_image = vector_space_pair.linear_span_image
and lt_linear_dependent_inj_imageD = vector_space_pair.linear_dependent_inj_imageD
and lt_linear_eq_0_on_span = vector_space_pair.linear_eq_0_on_span
and lt_linear_independent_injective_image = vector_space_pair.linear_independent_injective_image
and lt_linear_inj_on_span_independent_image = vector_space_pair.linear_inj_on_span_independent_image
and lt_linear_inj_on_span_iff_independent_image = vector_space_pair.linear_inj_on_span_iff_independent_image
and lt_linear_subspace_linear_preimage = vector_space_pair.linear_subspace_linear_preimage
and lt_linear_spans_image = vector_space_pair.linear_spans_image
and lt_linear_spanning_surjective_image = vector_space_pair.linear_spanning_surjective_image
and lt_linear_eq_on_span = vector_space_pair.linear_eq_on_span
and lt_linear_compose_scale_right = vector_space_pair.linear_compose_scale_right
and lt_linear_compose_add = vector_space_pair.linear_compose_add
and lt_linear_zero = vector_space_pair.linear_zero
and lt_linear_compose_sub = vector_space_pair.linear_compose_sub
and lt_linear_compose_neg = vector_space_pair.linear_compose_neg
and lt_linear_compose_scale = vector_space_pair.linear_compose_scale
and lt_linear_indep_image_lemma = vector_space_pair.linear_indep_image_lemma
and lt_linear_eq_on = vector_space_pair.linear_eq_on
and lt_linear_compose_sum = vector_space_pair.linear_compose_sum
and lt_linear_independent_extend_subspace = vector_space_pair.linear_independent_extend_subspace
and lt_linear_independent_extend = vector_space_pair.linear_independent_extend
and lt_linear_exists_left_inverse_on = vector_space_pair.linear_exists_left_inverse_on
and lt_linear_exists_right_inverse_on = vector_space_pair.linear_exists_right_inverse_on
and lt_linear_inj_on_left_inverse = vector_space_pair.linear_inj_on_left_inverse
and lt_linear_injective_left_inverse = vector_space_pair.linear_injective_left_inverse
and lt_linear_surj_right_inverse = vector_space_pair.linear_surj_right_inverse
and lt_linear_surjective_right_inverse = vector_space_pair.linear_surjective_right_inverse
and lt_finite_basis_to_basis_subspace_isomorphism = vector_space_pair.finite_basis_to_basis_subspace_isomorphism
(* should work, but doesnt
*)
(* not expected to work:
  lt_construct_def = vector_space_pair.construct_def
  lt_construct_cong = vector_space_pair.construct_cong
  lt_linear_construct = vector_space_pair.linear_construct
  lt_construct_basis = vector_space_pair.construct_basis
  lt_construct_outside = vector_space_pair.construct_outside
  lt_construct_add = vector_space_pair.construct_add
  lt_construct_scale = vector_space_pair.construct_scale
  lt_construct_in_span = vector_space_pair.construct_in_span
  lt_in_span_in_range_construct = vector_space_pair.in_span_in_range_construct
  lt_range_construct_eq_span = vector_space_pair.range_construct_eq_span
*)
end

lemmas_with [cancel_type_definition, OF m1.S_ne,
    cancel_type_definition, OF m2.S_ne,
    folded subset_iff' top_set_def,
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
  linear_0 = lt_linear_0
  and linear_add = lt_linear_add
  and linear_scale = lt_linear_scale
  and linear_neg = lt_linear_neg
  and linear_diff = lt_linear_diff
  and linear_sum = lt_linear_sum
  and linear_inj_on_iff_eq_0 = lt_linear_inj_on_iff_eq_0
  and linear_inj_iff_eq_0 = lt_linear_inj_iff_eq_0
  and linear_subspace_image = lt_linear_subspace_image
  and linear_subspace_vimage = lt_linear_subspace_vimage
  and linear_subspace_kernel = lt_linear_subspace_kernel
  and linear_span_image = lt_linear_span_image
  and linear_dependent_inj_imageD = lt_linear_dependent_inj_imageD
  and linear_eq_0_on_span = lt_linear_eq_0_on_span
  and linear_independent_injective_image = lt_linear_independent_injective_image
  and linear_inj_on_span_independent_image = lt_linear_inj_on_span_independent_image
  and linear_inj_on_span_iff_independent_image = lt_linear_inj_on_span_iff_independent_image
  and linear_subspace_linear_preimage = lt_linear_subspace_linear_preimage
  and linear_spans_image = lt_linear_spans_image
  and linear_spanning_surjective_image = lt_linear_spanning_surjective_image
  and linear_eq_on_span = lt_linear_eq_on_span
  and linear_compose_scale_right = lt_linear_compose_scale_right
  and linear_compose_add = lt_linear_compose_add
  and linear_zero = lt_linear_zero
  and linear_compose_sub = lt_linear_compose_sub
  and linear_compose_neg = lt_linear_compose_neg
  and linear_compose_scale = lt_linear_compose_scale
  and linear_indep_image_lemma = lt_linear_indep_image_lemma
  and linear_eq_on = lt_linear_eq_on
  and linear_compose_sum = lt_linear_compose_sum
  and linear_independent_extend_subspace = lt_linear_independent_extend_subspace
  and linear_independent_extend = lt_linear_independent_extend
  and linear_exists_left_inverse_on = lt_linear_exists_left_inverse_on
  and linear_exists_right_inverse_on = lt_linear_exists_right_inverse_on
  and linear_inj_on_left_inverse = lt_linear_inj_on_left_inverse
  and linear_injective_left_inverse = lt_linear_injective_left_inverse
  and linear_surj_right_inverse = lt_linear_surj_right_inverse
  and linear_surjective_right_inverse = lt_linear_surjective_right_inverse
  and finite_basis_to_basis_subspace_isomorphism = lt_finite_basis_to_basis_subspace_isomorphism

end

context finite_dimensional_vector_space_pair_1_on begin

context includes lifting_syntax
  notes [transfer_rule del] = Collect_transfer
  assumes
    "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S1"
    "\<exists>(Rep::'t \<Rightarrow> 'c) (Abs::'c \<Rightarrow> 't). type_definition Rep Abs S2" begin

interpretation local_typedef_finite_dimensional_vector_space_pair_1 S1 scale1 Basis1 "TYPE('s)" S2 scale2 "TYPE('t)" by unfold_locales fact+

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'e 'f,
  OF lt2.type.ab_group_add_axioms lt1.type.ab_group_add_axioms type_finite_dimensional_vector_space_pair_1_on_with,
  folded lt1.dim_S_def lt2.dim_S_def,
  untransferred,
  var_simplified implicit_ab_group_add]:
   lt_dim_image_eq = finite_dimensional_vector_space_pair_1.dim_image_eq
and lt_dim_image_le = finite_dimensional_vector_space_pair_1.dim_image_le

end

lemmas_with [cancel_type_definition, OF vs1.S_ne,
    cancel_type_definition, OF vs2.S_ne,
    folded subset_iff' top_set_def,
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
  dim_image_eq = lt_dim_image_eq
and dim_image_le = lt_dim_image_le

end


context finite_dimensional_vector_space_pair_on begin

context includes lifting_syntax
  notes [transfer_rule del] = Collect_transfer
  assumes
    "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S1"
    "\<exists>(Rep::'t \<Rightarrow> 'c) (Abs::'c \<Rightarrow> 't). type_definition Rep Abs S2" begin

interpretation local_typedef_finite_dimensional_vector_space_pair S1 scale1 Basis1 "TYPE('s)" S2 scale2 Basis2 "TYPE('t)" by unfold_locales fact+

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'e 'f,
  OF lt2.type.ab_group_add_axioms lt1.type.ab_group_add_axioms type_finite_dimensional_vector_space_pair_on_with,
  folded lt1.dim_S_def lt2.dim_S_def,
  untransferred,
  var_simplified implicit_ab_group_add]:
lt_linear_surjective_imp_injective = finite_dimensional_vector_space_pair.linear_surjective_imp_injective
and lt_linear_injective_imp_surjective = finite_dimensional_vector_space_pair.linear_injective_imp_surjective
and lt_linear_injective_isomorphism = finite_dimensional_vector_space_pair.linear_injective_isomorphism
and lt_linear_surjective_isomorphism = finite_dimensional_vector_space_pair.linear_surjective_isomorphism
and lt_basis_to_basis_subspace_isomorphism = finite_dimensional_vector_space_pair.basis_to_basis_subspace_isomorphism
and lt_subspace_isomorphism = finite_dimensional_vector_space_pair.subspace_isomorphism

end

lemmas_with [cancel_type_definition, OF vs1.S_ne,
    cancel_type_definition, OF vs2.S_ne,
    folded subset_iff' top_set_def,
    simplified pred_fun_def,
    simplified\<comment>\<open>too much?\<close>]:
linear_surjective_imp_injective = lt_linear_surjective_imp_injective
and linear_injective_imp_surjective = lt_linear_injective_imp_surjective
and linear_injective_isomorphism = lt_linear_injective_isomorphism
and linear_surjective_isomorphism = lt_linear_surjective_isomorphism
and basis_to_basis_subspace_isomorphism = lt_basis_to_basis_subspace_isomorphism
and subspace_isomorphism = lt_subspace_isomorphism

end

end
