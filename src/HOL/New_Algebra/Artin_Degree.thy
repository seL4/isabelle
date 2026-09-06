section \<open>Artin's degree bound: the fixed field of a finite group has small index\<close>

theory Artin_Degree
  imports Artin Algebraic_Transitivity
begin

text \<open>The results of \<open>Artin\<close> are phrased with explicit sums over an index set.
  Here they are transported into the vector-space language of
  \<open>Extension_Vector_Space\<close>, where @{term "fixed_field K H \<subseteq> K"} is a
  @{locale subfield_tower} and the size of the extension is measured by
  @{const Vector_Space.lin_indep} and @{const Vector_Space.dimension}.  The bridge in both directions
  is @{thm [source] subfield_tower.vs_lincomb_eq_sum}: an abstract linear combination over a finite
  set of vectors is an ordinary field sum.

  The conclusion is \<^emph>\<open>Artin's bound\<close>: over the fixed field of a finite group @{term H} of
  automorphisms, no more than @{term "card H"} elements of @{term K} can be linearly independent.
  Together with Dedekind's lemma --- which gives the matching lower bound --- this is what pins the
  order of the Galois group of @{term "fixed_field K H"} to exactly @{term "card H"}.\<close>

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

subsection \<open>The fixed field sits below \<open>K\<close> as a tower\<close>

text \<open>Both fields are subfields of \<^typ>\<open>complex\<close> and one contains the other, so they form a
  @{locale subfield_tower} --- the scalars being the fixed field and the vectors @{term K}.  Note the
  translation between the two subfield notions: @{const complex_subfield} is what the Galois
  development uses, the type class @{locale Subfield} is what the vector-space layer needs.\<close>
lemma fixed_field_tower:
  assumes K: "complex_subfield K" and HG: "H \<subseteq> field_auto K F"
  shows "subfield_tower (fixed_field K H) K"
proof (rule subfield_tower.intro)
  have K': "Subfield K" using K by (simp add: complex_subfield_iff_subfield)
  show "Subfield (fixed_field K H)"
    by (rule fixed_field_subfield[OF K' HG])
  show "Subfield K" by (rule K')
  show "subfield_tower_axioms (fixed_field K H) K"
    by unfold_locales (rule fixed_field_subset)
qed


subsection \<open>Artin's bound\<close>

text \<open>No set of more than @{term "card H"} elements of @{term K} is linearly independent over the
  fixed field.  The argument is the one sketched in \<open>Artin\<close>, now assembled:
  @{thm [source] artin_lemma} produces a simultaneous dependence with coefficients in @{term K}, and
  @{thm [source] artin_solution_over_fixed_field} pushes those coefficients down into the fixed field.
  The simultaneous system is the key correction: no assumption that the vectors themselves are fixed
  by @{term H} is needed.

  Care is needed about which set indexes what.  A \<open>lin_indep\<close> set is a set \<^emph>\<open>of vectors\<close>, and the
  dependence lemmas index by an arbitrary type; we index the vectors by themselves, taking
  @{term "J = B"} and @{term "x = id"}.

  The statements live in a \<^emph>\<open>context\<close> fixing @{term K} and @{term H} and interpreting the tower.  The
  @{locale Vector_Space} locale has nine parameters, so spelling \<open>lin_indep\<close> out at the top level
  would mean writing all of them; inside the context the interpretation supplies them and the
  qualified \<open>T.vs.\<close> prefix works.\<close>

context
  fixes K F :: "complex set" and H :: "(complex \<Rightarrow> complex) set"
  assumes K: "complex_subfield K" and Hsub: "H \<in> galois_subgroups K F"
begin

lemma H_auto: "H \<subseteq> field_auto K F" using Hsub by (rule galois_subgroups_subset)

interpretation T: subfield_tower "fixed_field K H" K by (rule fixed_field_tower[OF K H_auto])

theorem artin_bound:
  assumes finH: "finite H" and BK: "B \<subseteq> K"
    and finB: "finite B" and lt: "card H < card B"
  shows "\<not> T.vs.lin_indep B"
proof
  assume indep: "T.vs.lin_indep B"
  have idH: "identity K \<in> H"
  proof -
    interpret S: Subgroup H "field_auto K F" "compose K" "identity K"
      using Hsub by (simp add: galois_subgroups_iff)
    show ?thesis by (rule S.sub_unit_closed)
  qed
  \<comment> \<open>A simultaneous nontrivial dependence with coefficients in @{term K}, indexed by the vectors themselves.\<close>
  have xK: "\<And>j. j \<in> B \<Longrightarrow> id j \<in> K"
  proof -
    fix j assume jB: "j \<in> B"
    have "j \<in> K" using BK jB by blast
    then show "id j \<in> K" by simp
  qed
  have dep: "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> B. c j \<noteq> 0) \<and>
      (\<forall>\<sigma> \<in> H. (\<Sum>j \<in> B. \<sigma> (id j) * c j) = 0)"
    using artin_lemma[where x = id and J = B, OF K finH H_auto finB lt xK] .
  have descended:
      "\<exists>c. (\<forall>j \<in> B. c j \<in> fixed_field K H) \<and>
        (\<exists>j \<in> B. c j \<noteq> 0) \<and>
        (\<forall>\<sigma> \<in> H. (\<Sum>j \<in> B. \<sigma> (id j) * c j) = 0)"
  proof (rule artin_solution_over_fixed_field[where x = id and J = B and F = F])
    show "complex_subfield K" by (rule K)
    show "H \<in> galois_subgroups K F" by (rule Hsub)
    show "finite B" by (rule finB)
    show "\<And>j. j \<in> B \<Longrightarrow> id j \<in> K" by (rule xK)
    show "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> B. c j \<noteq> 0) \<and>
        (\<forall>\<sigma> \<in> H. (\<Sum>j \<in> B. \<sigma> (id j) * c j) = 0)" by (rule dep)
  qed
  then obtain c where cfix: "\<And>j. j \<in> B \<Longrightarrow> c j \<in> fixed_field K H"
    and cnz: "\<exists>j \<in> B. c j \<noteq> 0"
    and ceq_all: "\<forall>\<sigma> \<in> H. (\<Sum>j \<in> B. \<sigma> (id j) * c j) = 0" by blast
  have ceq: "(\<Sum>j \<in> B. j * c j) = 0"
  proof -
    have row: "(\<Sum>j \<in> B. identity K (id j) * c j) = 0"
      using ceq_all idH by blast
    moreover have "(\<Sum>j \<in> B. identity K (id j) * c j) =
        (\<Sum>j \<in> B. j * c j)"
    proof (intro sum.cong refl)
      fix j assume jB: "j \<in> B"
      have jK: "j \<in> K" using BK jB by blast
      have "identity K (id j) = j" by (simp add: identity_apply jK)
      then show "identity K (id j) * c j = j * c j" by simp
    qed
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Re-read the sum as an abstract linear combination.  @{const Vector_Space.lin_indep} demands a
    coefficient function that is \<^emph>\<open>extensional\<close> on @{term B}, so restrict @{term c}.\<close>
  define e where "e = restrict c B"
  have eF: "e \<in> B \<rightarrow>\<^sub>E fixed_field K H" using cfix by (simp add: e_def)
  have "T.vs.lincomb e B = (\<Sum>j \<in> B. e j * j)"
    using finB BK eF by (intro T.vs_lincomb_eq_sum) auto
  also have "\<dots> = (\<Sum>j \<in> B. j * c j)"
    by (intro sum.cong refl) (simp add: e_def mult.commute)
  also have "\<dots> = 0" by (rule ceq)
  finally have lc0: "T.vs.lincomb e B = 0" .
  \<comment> \<open>Independence would force every coefficient to vanish, contradicting nontriviality.\<close>
  have "\<forall>v \<in> B. e v = 0" using indep eF lc0 by (simp add: T.vs.lin_indep_def)
  then show False using cnz by (auto simp: e_def)
qed

text \<open>Consequently a basis of @{term K} over the fixed field --- if there is one --- has at most
  @{term "card H"} elements, so the degree is bounded by the group order.\<close>
corollary artin_dimension_le:
  assumes finH: "finite H" and basis: "T.vs.basis B"
  shows "card B \<le> card H"
proof (rule ccontr)
  assume "\<not> card B \<le> card H"
  then have lt: "card H < card B" by simp
  have finB: "finite B" and BK: "B \<subseteq> K" using basis by (auto simp: T.vs.basis_def)
  have "T.vs.lin_indep B" using basis by (rule T.vs.basis_lin_indep)
  moreover have "\<not> T.vs.lin_indep B"
    by (rule artin_bound[where B = B, OF finH BK finB lt])
  ultimately show False by simp
qed

text \<open>And the same bound on the degree itself, since the dimension is the size of any basis
  (@{thm [source] Vector_Space.dimension_eq_any_field} --- no finiteness of the base field needed).\<close>
corollary artin_degree_le:
  assumes finH: "finite H" and basis: "T.vs.basis B"
  shows "T.vs.dimension \<le> card H"
  using artin_dimension_le[where B = B, OF finH basis]
    T.vs.dimension_eq_any_field[OF basis] by simp

end


subsection \<open>The reverse bound: the Galois group is no larger than the degree\<close>

text \<open>Now the other inequality, and the one that needs Dedekind's lemma.  Let @{term E} be an
  intermediate field and @{term B} a basis of @{term K} over @{term E}.  Then
  @{term "field_auto K E"} has at most @{term "card B"} elements.

  The argument is again the linear pigeonhole, with the roles of the two index sets exchanged.
  Suppose there were more than @{term "card B"} automorphisms, and take a finite set @{term S} of
  them of size @{term "card B + 1"}.  Consider the system with \<^emph>\<open>one equation per basis vector\<close>
  @{term "v \<in> B"} and one unknown per automorphism:
  @{text "\<Sum>\<^sub>\<sigma> a\<^sub>\<sigma> \<sigma>(v) = 0"}.  It has more unknowns than equations, so
  @{thm [source] Subfield.underdetermined_solution} gives a nontrivial solution.

  A solution of those finitely many equations already satisfies the corresponding relation at
  \<^emph>\<open>every\<close> point of @{term K}: an arbitrary @{term "z \<in> K"} is an @{term E}-combination of @{term B},
  and each automorphism is @{term E}-linear (it is additive, multiplicative, and fixes @{term E}), so
  the relation propagates from the basis to all of @{term K} by linearity.  But then Dedekind's lemma
  forces every coefficient to vanish --- contradicting nontriviality.

  The propagation step is the only real work, and it is where the basis hypothesis is used.\<close>

text \<open>As before the statements sit inside a context, so that the tower's interpretation supplies the
  nine parameters of @{locale Vector_Space} and \<open>basis\<close> can be written qualified.  The tower is
  \<^emph>\<open>interpreted\<close> here rather than passed as an assumption: a hypothesis @{text "subfield_tower E K"}
  would not bring \<open>T.vs.basis\<close> into scope for the statement itself.\<close>

context
  fixes K E :: "complex set"
  assumes K: "complex_subfield K" and Ebase: "subfield_tower E K"
begin

interpretation T: subfield_tower E K by (rule Ebase)

text \<open>@{term K} as a type-class @{locale Subfield}, which is where
  @{thm [source] Subfield.underdetermined_solution} lives.

  A plain fact, cited as @{text "subfield.underdetermined_solution[OF Ksf]"}.  Replacing it by
  @{command interpretation} --- the obvious move, to get the theorem unqualified --- does not work
  inside a @{command context} carrying assumptions: the interpretation is accepted but its theorems
  are not available under the prefix, giving \<open>Undefined fact: KS.underdetermined_solution\<close>.\<close>
lemma Ksf: "Subfield K" using K by (simp add: complex_subfield_iff_subfield)

text \<open>The base field lies inside the extension --- the tower's own axiom.\<close>
lemma EK: "E \<subseteq> K" by (rule T.base_subset)

text \<open>An automorphism fixing @{term E} is @{term E}-linear on linear combinations of a finite set of
  vectors: it commutes with the sum, with the scalar products, and fixes the scalars.\<close>
lemma field_auto_lincomb:
  assumes s: "\<sigma> \<in> field_auto K E" and finB: "finite B" and BK: "B \<subseteq> K"
    and c: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> E"
  shows "\<sigma> (\<Sum>v \<in> B. c v * v) = (\<Sum>v \<in> B. c v * \<sigma> v)"
proof -
  interpret K: complex_subfield K by (rule K)
  have cK: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> K" using c EK by blast
  have "\<sigma> (\<Sum>v \<in> B. c v * v) = (\<Sum>v \<in> B. \<sigma> (c v * v))"
    using cK BK by (intro field_auto_sum[OF K s]) (blast intro: K.mult_closed)
  also have "\<dots> = (\<Sum>v \<in> B. c v * \<sigma> v)"
  proof (intro sum.cong refl)
    fix v assume v: "v \<in> B"
    have "\<sigma> (c v * v) = \<sigma> (c v) * \<sigma> v"
      using s cK[OF v] BK v by (blast intro: field_auto_mult)
    also have "\<sigma> (c v) = c v" using s c[OF v] by (simp add: field_auto_mem_iff)
    finally show "\<sigma> (c v * v) = c v * \<sigma> v" by simp
  qed
  finally show ?thesis .
qed

text \<open>Hence a relation among automorphisms that holds on a basis holds throughout @{term K}.\<close>
lemma character_relation_from_basis:
  assumes finS: "finite S" and SG: "S \<subseteq> field_auto K E"
    and basis: "T.vs.basis B"
    and rel: "\<forall>v \<in> B. (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> v) = 0"
    and z: "z \<in> K"
  shows "(\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> z) = 0"
proof -
  have finB: "finite B" and BK: "B \<subseteq> K" using basis by (auto simp: T.vs.basis_def)
  \<comment> \<open>Coordinates of @{term z} with respect to the basis.\<close>
  have "T.vs.spanning B" using basis by (rule T.vs.basis_spanning)
  then obtain c where cE: "c \<in> B \<rightarrow>\<^sub>E E" and zeq: "z = T.vs.lincomb c B"
    using z by (auto simp: T.vs.spanning_def)
  have cEv: "\<And>v. v \<in> B \<Longrightarrow> c v \<in> E" using cE by auto
  have zsum: "z = (\<Sum>v \<in> B. c v * v)"
    using zeq T.vs_lincomb_eq_sum[OF finB BK cEv] by simp
  \<comment> \<open>Expand each @{term "\<sigma> z"} by linearity and exchange the two sums.\<close>
  have "(\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> z) = (\<Sum>\<sigma> \<in> S. a \<sigma> * (\<Sum>v \<in> B. c v * \<sigma> v))"
    using SG finB BK cEv by (intro sum.cong refl) (simp add: zsum field_auto_lincomb subset_iff)
  \<comment> \<open>Exchanging the two sums, done in two explicit steps: distribute each product over the inner
    sum, then @{thm [source] sum.swap}.  One @{method simp} with both facts does not close it.\<close>
  also have "\<dots> = (\<Sum>\<sigma> \<in> S. \<Sum>v \<in> B. c v * (a \<sigma> * \<sigma> v))"
    by (intro sum.cong refl) (simp add: sum_distrib_left mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>v \<in> B. \<Sum>\<sigma> \<in> S. c v * (a \<sigma> * \<sigma> v))" by (rule sum.swap)
  also have "\<dots> = (\<Sum>v \<in> B. c v * (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> v))"
    by (intro sum.cong refl) (simp add: sum_distrib_left)
  also have "\<dots> = 0" using rel by simp
  finally show ?thesis .
qed

text \<open>\<^emph>\<open>The reverse bound.\<close>  With a basis of size @{term "card B"}, there cannot be more than
  @{term "card B"} distinct automorphisms of @{term K} fixing @{term E}.\<close>
theorem galois_group_card_le:
  assumes basis: "T.vs.basis B"
    and finS: "finite S" and SG: "S \<subseteq> field_auto K E"
  shows "card S \<le> card B"
proof (rule ccontr)
  assume "\<not> card S \<le> card B"
  then have lt: "card B < card S" by simp
  have finB: "finite B" and BK: "B \<subseteq> K" using basis by (auto simp: T.vs.basis_def)
  \<comment> \<open>One equation per basis vector, one unknown per automorphism: more unknowns than equations.
    The coefficient matrix @{term "\<lambda>v \<sigma>. \<sigma> v"} is indexed by vectors then automorphisms.\<close>
  have entries: "\<forall>v \<in> B. \<forall>\<sigma> \<in> S. \<sigma> v \<in> K"
    using SG BK by (blast intro: field_auto_closed)
  have "\<exists>a. (\<forall>\<sigma>. a \<sigma> \<in> K) \<and> (\<exists>\<sigma> \<in> S. a \<sigma> \<noteq> 0) \<and> (\<forall>v \<in> B. (\<Sum>\<sigma> \<in> S. \<sigma> v * a \<sigma>) = 0)"
    using Subfield.underdetermined_solution[OF Ksf, where A = "\<lambda>v \<sigma>. \<sigma> v" and I = B and J = S]
    using entries finB finS lt by blast
  then obtain a where anz: "\<exists>\<sigma> \<in> S. a \<sigma> \<noteq> 0" and arel: "\<forall>v \<in> B. (\<Sum>\<sigma> \<in> S. \<sigma> v * a \<sigma>) = 0"
    by fastforce
  \<comment> \<open>Rewrite into the orientation Dedekind's lemma expects.\<close>
  have arel': "\<forall>v \<in> B. (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> v) = 0"
    using arel by (simp add: mult.commute)
  \<comment> \<open>The relation extends from the basis to all of @{term K}, so Dedekind applies.\<close>
  have "\<And>z. z \<in> K \<Longrightarrow> (\<Sum>\<sigma> \<in> S. a \<sigma> * \<sigma> z) = 0"
    by (rule character_relation_from_basis[OF finS SG basis arel'])
  then have "\<forall>\<sigma> \<in> S. a \<sigma> = 0"
    using dedekind_independence[OF K, where S = S and a = a and F = E] finS SG by blast
  then show False using anz by blast
qed

end


subsection \<open>Artin's theorem\<close>

text \<open>The two bounds now meet.  Let @{term H} be a finite group of automorphisms of @{term K}.
  The uniform bound first extracts a basis @{term B} of @{term K} over @{term "fixed_field K H"}; write
  \<open>G = field_auto K (fixed_field K H)\<close> for the Galois group of the fixed field.

    \<^item> @{thm [source] artin_dimension_le} gives @{term "card B \<le> card H"}: were there more basis
      vectors than automorphisms, Artin's bound would make them dependent;
    \<^item> @{thm [source] galois_group_card_le} gives @{term "card G \<le> card B"}: were there more
      automorphisms than basis vectors, Dedekind's lemma would be contradicted;
    \<^item> @{thm [source] galois_extension.le_galois_group_fixed_field} --- the unit of the adjunction, and
      the one part needing no hypotheses --- gives @{term "H \<subseteq> G"}.

  Chaining the first two bounds gives @{term "card G \<le> card H"}, and an inclusion between finite sets
  of equal cardinality is an equality.  So the kernel operator of the Galois correspondence is the
  identity on finite subgroups: \<^emph>\<open>every\<close> automorphism fixing the fixed field of @{term H} already
  belongs to @{term H}.

  This is the converse half of the correspondence, and the hypothesis that does the work is
  \<^emph>\<open>finiteness of @{term H}\<close>; no basis, separability, or normality is assumed by the public theorem.\<close>

text \<open>Again a context, for the same reason as before: the locally extracted \<open>basis\<close> is a
  @{locale Vector_Space} constant and can only be written qualified where an interpretation of the tower
  is in scope.  Here the tower is the one built from @{term H} itself.\<close>

context
  fixes K F :: "complex set" and H :: "(complex \<Rightarrow> complex) set"
  assumes K: "complex_subfield K" and Fsub: "complex_subfield F" and FK: "F \<subseteq> K"
    and Hsub: "H \<in> galois_subgroups K F"
begin

lemma HG: "H \<subseteq> field_auto K F" using Hsub by (rule galois_subgroups_subset)

interpretation T: subfield_tower "fixed_field K H" K
  by (rule fixed_field_tower[OF K HG])

theorem artin_theorem:
  assumes finH: "finite H"
  shows "field_auto K (fixed_field K H) = H"
proof -
  \<comment> \<open>Via the locale's own intro rule: @{method unfold_locales} would descend through
    @{locale complex_subfield} to its six closure axioms for each of @{term K} and @{term F}.\<close>
  have K': "Subfield K" using K by (simp add: complex_subfield_iff_subfield)
  have F': "Subfield F" using Fsub by (simp add: complex_subfield_iff_subfield)
  interpret GE: galois_extension K F
    by (rule galois_extension.intro[OF K' F' FK])
  have tower: "subfield_tower (fixed_field K H) K" by (rule fixed_field_tower[OF K HG])
  \<comment> \<open>First obtain a basis from the uniform Artin bound.  The bound applies to every independent
    set, so the maximum-cardinality extraction in @{thm [source] Vector_Space.basis_exists_of_independent_card_bound}
    supplies a basis without assuming one in the theorem statement.\<close>
  have indep_bound: "\<And>A. T.vs.lin_indep A \<Longrightarrow> card A \<le> card H"
  proof -
    fix A assume indA: "T.vs.lin_indep A"
    have finA: "finite A" and AK: "A \<subseteq> K"
      using indA by (auto simp: T.vs.lin_indep_def)
    show "card A \<le> card H"
    proof (rule ccontr)
      assume "\<not> card A \<le> card H"
      then have lt: "card H < card A" by simp
      have "\<not> T.vs.lin_indep A"
        by (rule artin_bound[where B = A, OF K Hsub finH AK finA lt])
      then show False using indA by blast
    qed
  qed
  obtain B where basis: "T.vs.basis B"
    using T.vs.basis_exists_of_independent_card_bound[where n = "card H"] indep_bound by blast
  \<comment> \<open>Upper bound: the extracted basis is no larger than the group.\<close>
  have le1: "card B \<le> card H"
    by (rule artin_dimension_le[OF K Hsub finH basis])
  \<comment> \<open>Lower bound: the Galois group of the fixed field is no larger than the basis.  Its finiteness
    comes from the same bound, since a set exceeding @{term "card B"} could not inject.\<close>
  have finG: "finite (field_auto K (fixed_field K H))"
  proof (rule ccontr)
    assume inf: "infinite (field_auto K (fixed_field K H))"
    \<comment> \<open>An infinite set has a finite subset larger than @{term "card B"}, which the bound forbids.\<close>
    then obtain S where S: "S \<subseteq> field_auto K (fixed_field K H)"
      and finS: "finite S" and cardS: "card S = card B + 1"
      by (meson infinite_arbitrarily_large)
    have "card S \<le> card B" by (rule galois_group_card_le[OF K tower basis finS S])
    then show False using cardS by simp
  qed
  have le2: "card (field_auto K (fixed_field K H)) \<le> card B"
    by (rule galois_group_card_le[OF K tower basis finG subset_refl])
  \<comment> \<open>So the group of the fixed field is no bigger than @{term H}, which it contains.\<close>
  have HsubG: "H \<subseteq> field_auto K (fixed_field K H)"
    using Hsub by (rule GE.le_galois_group_fixed_field)
  have card_le: "card (field_auto K (fixed_field K H)) \<le> card H" using le1 le2 by simp
  \<comment> \<open>@{thm [source] card_seteq} concludes @{text "A = B"} from @{text "finite A"},
    @{text "B \<subseteq> A"} and @{text "card A \<le> card B"} --- so here @{term H} plays the \<^emph>\<open>subset\<close> and the
    Galois group the finite superset.\<close>
  show ?thesis by (rule card_seteq[OF finG HsubG card_le, symmetric])
qed

end

text \<open>\<^bold>\<open>What this completes.\<close>  With @{thm [source] artin_theorem} the kernel operator of the Galois
  correspondence is the identity on finite subgroups.  Together with the semi-inverse laws already in
  \<open>Galois_Correspondence\<close>, the correspondence restricts to a \<^emph>\<open>bijection\<close> between the finite subgroups
  of the Galois group and those intermediate fields that arise as fixed fields.

  The remaining step for the classical statement --- that \<^emph>\<open>every\<close> intermediate field of a finite
  Galois extension is such a fixed field, so that the closure operator is the identity too --- is
  where separability and normality enter, and it is not attempted here.  For the simple normal case
  \<open>galois_simple_normal_degree\<close> of \<open>Galois_Degree\<close> supplies the matching degree count.

  The theorem now obtains the needed basis internally from the uniform Artin bound, so no basis or
  vector-fixing hypothesis is exposed at the public interface.\<close>

end
