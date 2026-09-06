section \<open>A field extension as a vector space over a subfield\<close>

theory Extension_Vector_Space
  imports Steinitz Field_Typeclass Subfield
begin

text \<open>We feed the type-class field operations into
  the abstract @{locale Vector_Space}.  For subfields @{term "K \<subseteq> L"} of a type-class field, @{term L}
  is a vector space over @{term K}: the vectors are the elements of @{term L}, addition and the zero
  are the field's, and scalar multiplication is field multiplication (restricted to scalars from
  @{term K}).  This is the linchpin that carries the Steinitz results --- @{const Vector_Space.span},
  @{const Vector_Space.basis}, @{const Vector_Space.dimension} and
  @{thm [source] Vector_Space.basis_card_unique} --- over to field extensions, giving a general
  @{text "[L:K]"} and its tower law.\<close>

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

subsection \<open>A subfield is a locale-based field\<close>

text \<open>The carrier @{term K} of a @{locale Subfield} satisfies the locale-based @{locale Field} axioms
  under the ambient type-class operations.  Built bottom-up exactly as in
  \<open>Field_Typeclass\<close>, but with carrier @{term K} in place of the whole type.\<close>
context Subfield
begin

lemma sf_add_group: "Group K (+) 0"
  using zero_closed add_closed uminus_closed
  by (intro GroupI; force simp: algebra_simps)

lemma sf_add_abelian: "Abelian_Group K (+) 0"
proof (rule Abelian_Group.intro[OF sf_add_group])
  show "commutative_monoid K (+) 0"
    by unfold_locales (auto intro: add_closed simp: ac_simps)
qed

lemma sf_mult_cmonoid: "commutative_monoid K (*) 1"
  by unfold_locales (auto intro: mult_closed simp: ac_simps)

lemma sf_ring: "Ring K (+) (*) 0 1"
  by (simp add: Ring_axioms.intro Ring_def commutative_monoid.axioms(1) distrib_left
      mult.commute sf_add_abelian sf_mult_cmonoid)

lemma sf_commutative_ring: "commutative_ring K (+) (*) 0 1"
  by (rule commutative_ring.intro[OF sf_ring sf_mult_cmonoid])

lemma sf_field: "Field K (+) (*) 0 1"
proof -
  interpret R: commutative_ring K "(+)" "(*)" "0" "1" by (rule sf_commutative_ring)
  show "Field K (+) (*) 0 1"
  proof qed (use R.multiplicative.invertible_def inverse_closed in fastforce)+
qed

end (* subfield *)

subsection \<open>The extension as a vector space\<close>

text \<open>Two nested subfields @{term "K \<subseteq> L"}.  The larger field @{term L} is the space of vectors, the
  smaller field @{term K} supplies the scalars.\<close>
locale subfield_tower = base: Subfield K + ext: Subfield L
  for K L :: "'a :: field set" +
  assumes base_subset: "K \<subseteq> L"
begin

text \<open>@{term L} is a @{term K}-vector space under the ambient field operations.  (The locale name is
  qualified: @{theory HOL.Vector_Spaces} is imported transitively and also defines a @{text
  vector_space} locale.)\<close>
sublocale vs: Vector_Space K "(+)" "(*)" "0" "1" "(+)" "0" L "(*)"
proof (intro Vector_Space.intro Vector_Space.Vector_Space_axioms.intro)
  show "Field K (+) (*) 0 1" by (rule base.sf_field)
  show "Abelian_Group L (+) 0" by (rule ext.sf_add_abelian)
next
  fix a v assume "a \<in> K" "v \<in> L"
  then show "a * v \<in> L" using base_subset by (auto intro: ext.mult_closed)
qed (auto simp: algebra_simps)

end (* subfield_tower *)

context subfield_tower
begin

text \<open>Over the extension, the abstract additive @{const commutative_monoid.fincomp} of the vector
  group is just the ordinary finite sum @{const sum}, since @{term "vadd = (+)"} and the summands lie
  in @{term L}.\<close>
lemma vadd_fincomp_eq_sum:
  assumes "finite B" and "f \<in> B \<rightarrow> L"
  shows "vs.vadd.fincomp f B = sum f B"
  using assms by (induct B rule: finite_induct) auto

text \<open>Hence a @{const Vector_Space.lincomb} over a finite index set of vectors is the field sum of the
  scaled vectors.\<close>
lemma vs_lincomb_eq_sum:
  assumes "finite B" and "B \<subseteq> L" and "\<And>v. v \<in> B \<Longrightarrow> c v \<in> K"
  shows "vs.lincomb c B = (\<Sum>v\<in>B. c v * v)"
proof -
  have "(\<lambda>v. c v * v) \<in> B \<rightarrow> L"
    using assms base_subset by (auto intro: ext.mult_closed)
  then show ?thesis
    unfolding vs.lincomb_def by (rule vadd_fincomp_eq_sum[OF assms(1)])
qed

text \<open>A finite K-scaled sum of vectors in L lies in the span of those vectors.\<close>
lemma sum_scale_in_span:
  assumes "finite A" and "\<And>x. x \<in> A \<Longrightarrow> g x \<in> L" and "\<And>x. x \<in> A \<Longrightarrow> f x \<in> K"
  shows "(\<Sum>x\<in>A. f x * g x) \<in> vs.span (g ` A)"
  using assms
proof (induct A rule: finite_induct)
  case empty
  show ?case by (simp add: vs.span_zero)
next
  case (insert x A)
  have gFL: "g ` A \<subseteq> L" using insert.prems by auto
  \<comment> \<open>The new term is a scalar multiple of g x in the span of the enlarged set.\<close>
  have term_span: "f x * g x \<in> vs.span (g ` insert x A)"
    by (simp add: image_subset_iff insert.prems vs.span_incl vs.span_scale)
  \<comment> \<open>The rest lies in the span of the smaller set, hence of the enlarged one.\<close>
  have rest_span: "(\<Sum>x\<in>A. f x * g x) \<in> vs.span (g ` insert x A)"
    using insert vs.span_mono[of "g ` A" "g ` insert x A"] by auto
  then show ?case
    using gFL insert term_span vs.span_vadd by auto
qed

text \<open>Specialise the finite vector-space cardinality bridge to a finite field extension.  The
  carrier of the larger field is the vector-space carrier, while @{term vs.dimension} is the
  extension degree in the existing tower interpretation.\<close>
corollary finite_subfield_tower_cardinality:
  assumes finL: "finite L"
  shows "card L = card K ^ vs.dimension"
  by (rule vs.card_eq_card_base_pow_dimension[OF finL])

text \<open>Basis extension is part of the field-extension API as well: a finite independent set of
vectors can be completed inside its union with an existing basis.\<close>
corollary subfield_tower_basis_extension:
  assumes ind: "vs.lin_indep A" and B: "vs.basis B"
  shows "\<exists>C. A \<subseteq> C \<and> C \<subseteq> A \<union> B \<and> vs.basis C"
  using vs.basis_extension[OF ind B] .

text \<open>A finite extension has a basis in the same interpretation used for its dimension.  This
  re-exports the basis-extraction theorem at the field-extension boundary, so clients do not have
  to reconstruct the finite spanning argument through the module implementation.\<close>
corollary finite_subfield_tower_basis_exists:
  assumes finL: "finite L"
  shows "\<exists>B. vs.basis B"
proof -
  have spanL: "vs.spanning L"
    by (rule iffD2[OF vs.spanning_iff_mod_spanning[OF finL subset_refl]])
      (rule vs.mod.spanning_whole)
  then show ?thesis
    using vs.basis_exists_from_spanning[OF spanL] by blast
qed

text \<open>More generally, a finite spanning set for the larger field can be reduced to a basis.  This
  is the reusable bridge for extensions presented by generators rather than by a finite carrier.\<close>
corollary subfield_tower_basis_exists_of_finite_spanning:
  assumes finB: "finite B" and BL: "B \<subseteq> L" and span: "L \<subseteq> vs.span B"
  shows "\<exists>C. C \<subseteq> B \<and> vs.basis C"
proof -
  have mod_span: "vs.mod.spanning B"
    by (rule vs.mod.spanningI[OF BL]) (use span in blast)
  have spanB: "vs.spanning B"
    by (rule iffD2[OF vs.spanning_iff_mod_spanning[OF finB BL] mod_span])
  obtain C where "C \<subseteq> B" and "vs.basis C"
    using vs.basis_exists_from_spanning[OF spanB] by blast
  then show ?thesis by blast
qed

text \<open>The dimension of a nontrivial finite field extension is positive.  Stating this once avoids
  repeated cardinality arguments when a client needs a genuine extension degree.\<close>
corollary finite_subfield_tower_dimension_pos:
  assumes finL: "finite L"
  shows "vs.dimension > 0"
proof -
  have cardL: "card L = card K ^ vs.dimension"
    by (rule finite_subfield_tower_cardinality[OF finL])
  have pairL: "{0, 1} \<subseteq> L" by auto
  have cardL_ge2: "2 \<le> card L"
    using card_mono[OF finL pairL] by simp
  show ?thesis
  proof (rule ccontr)
    assume "\<not> vs.dimension > 0"
    then have "vs.dimension = 0" by simp
    then have "card L = 1" using cardL by simp
    then show False using cardL_ge2 by simp
  qed
qed

end (* subfield_tower *)

text \<open>Every subfield sits in the trivial tower over itself, and every pair of nested subfields forms a
  tower; the sublocale then equips it with the full Steinitz vocabulary.\<close>
lemma subfield_tower_refl:
  assumes "Subfield K" shows "subfield_tower K K"
  by (rule subfield_tower.intro[OF assms assms]) (unfold_locales, rule subset_refl)

end
