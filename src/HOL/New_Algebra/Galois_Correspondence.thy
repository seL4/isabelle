section \<open>The Galois correspondence between intermediate fields and subgroups\<close>

theory Galois_Correspondence
  imports Galois_Automorphism Order_Theory
begin

text \<open>Let \<open>F \<subseteq> K\<close> be subfields of an ambient type-class field.  There are two natural operations between the
  \<^emph>\<open>intermediate fields\<close> of the extension and the \<^emph>\<open>subgroups\<close> of its Galois group
  @{term "field_auto K F"}:

    \<^item> \<^emph>\<open>fixing\<close> a set of automorphisms, @{text "H \<mapsto> K\<^sup>H"}, the subfield of @{term K} on which every
      element of @{term H} acts as the identity;

    \<^item> \<^emph>\<open>the relative Galois group\<close> of an intermediate field, @{text "E \<mapsto> field_auto K E"}, the
      automorphisms of @{term K} fixing @{term E} pointwise.

  Both are \<^emph>\<open>inclusion-reversing\<close>: a bigger group of automorphisms fixes fewer points, and a bigger
  intermediate field admits fewer automorphisms fixing it.  So this is an \<^emph>\<open>antitone\<close> adjoint pair,
  and the way to see it as a @{locale Galois_Connection} --- which is defined for \<^emph>\<open>monotone\<close>
  adjoints --- is to order one of the two lattices by reverse inclusion.  We order the subgroups by
  \<open>\<supseteq>\<close>; then both maps become isotone and the adjunction reads
  @{text "K\<^sup>H \<subseteq> E \<longleftrightarrow> H \<supseteq> field_auto K E"}.

  This is the general half of the Galois correspondence, and it needs no separability, normality or
  finiteness hypotheses at all: it is a formal consequence of the definitions, exactly as for the
  extension/contraction pair on ideals in \<open>Ideal_Extension\<close>.  What genuinely \<^emph>\<open>does\<close> need those
  hypotheses is the statement that the two maps are mutually inverse \<^emph>\<open>bijections\<close>; the closure
  operator @{text "E \<mapsto> K\<^bsup>field_auto K E\<^esup>"} is the identity precisely on the intermediate fields over
  which @{term K} is normal.  That refinement is not attempted here --- see the note at the end.\<close>


subsection \<open>The fixed field of a set of automorphisms\<close>

text \<open>The subfield of @{term K} fixed pointwise by every automorphism in @{term H}.  We do not
  require @{term H} to be a subgroup: the definition and its basic properties make sense for an
  arbitrary set of maps, and the extra generality costs nothing.\<close>
text \<open>The fixed field is a subfield by the generic closure theorem
  @{thm [source] field_auto_fixed_field_subfield}; the empty case is @{term K} itself.\<close>
theorem fixed_field_subfield:
  assumes Ksub: "Subfield K" and H: "H \<subseteq> field_auto K F"
  shows "Subfield (fixed_field K H)"
  by (rule field_auto_fixed_field_subfield[OF Ksub H])

text \<open>The base field lies inside every fixed field: by definition each automorphism in the Galois
  group fixes @{term F} pointwise.\<close>
lemma base_subset_fixed_field:
  assumes H: "H \<subseteq> field_auto K F" and FK: "F \<subseteq> K"
  shows "F \<subseteq> fixed_field K H"
  using field_auto_base_subset_fixed_field[OF H FK] .


subsection \<open>Intermediate fields and the relative Galois group\<close>

text \<open>The intermediate fields of the extension \<open>F \<subseteq> K\<close>: the subfields lying between the two.\<close>
definition inter_fields :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> 'a set set"
  where "inter_fields K F = {E. Subfield E \<and> F \<subseteq> E \<and> E \<subseteq> K}"

lemma inter_fields_iff:
  "E \<in> inter_fields K F \<longleftrightarrow> Subfield E \<and> F \<subseteq> E \<and> E \<subseteq> K"
  by (simp add: inter_fields_def)

text \<open>The two ends of the extension are intermediate fields.\<close>
lemma base_in_inter_fields:
  "\<lbrakk> Subfield F; F \<subseteq> K \<rbrakk> \<Longrightarrow> F \<in> inter_fields K F"
  by (simp add: inter_fields_iff)

lemma top_in_inter_fields:
  "\<lbrakk> Subfield K; F \<subseteq> K \<rbrakk> \<Longrightarrow> K \<in> inter_fields K F"
  by (simp add: inter_fields_iff)

text \<open>Taking the relative Galois group is inclusion-reversing: a bigger intermediate field imposes
  more conditions, so fewer automorphisms survive.\<close>
lemma field_auto_antitone: "E \<subseteq> E' \<Longrightarrow> field_auto K E' \<subseteq> field_auto K E"
  by (auto simp: field_auto_def)

text \<open>The relative Galois group of an intermediate field is a subgroup of the whole Galois group:
  it consists of automorphisms of @{term K}, and fixing @{term E} pointwise implies fixing the
  smaller @{term F} pointwise.\<close>
theorem field_auto_subgroup_of_Galois_group:
  assumes Ksub: "Subfield K" and FK: "F \<subseteq> K" and E: "E \<in> inter_fields K F"
  shows "Subgroup (field_auto K E) (field_auto K F) (compose K) (identity K)"
proof -
  from E have Esub: "Subfield E" and FE: "F \<subseteq> E" and EK: "E \<subseteq> K"
    by (auto simp: inter_fields_iff)
  \<comment> \<open>Work inside the whole Galois group as the ambient group, so that \<open>subgroupI\<close> applies.\<close>
  interpret W: Group "field_auto K F" "compose K" "identity K"
    using Ksub FK by (rule field_auto_group)
  \<comment> \<open>The relative group is also a subgroup of the symmetric group, which supplies inverses.\<close>
  interpret S: Subgroup "field_auto K E" "transformations.Sym K" "compose K" "identity K"
    using Ksub EK by (rule field_auto_subgroup)
  have EF: "field_auto K E \<subseteq> field_auto K F" using FE by (rule field_auto_antitone)
  show ?thesis
  proof (rule W.subgroupI [OF EF])
    show "identity K \<in> field_auto K E" using Ksub EK by (rule field_auto_identity)
    show "\<And>g h. \<lbrakk> g \<in> field_auto K E; h \<in> field_auto K E \<rbrakk> \<Longrightarrow> compose K g h \<in> field_auto K E"
      using Ksub EK by (blast intro: field_auto_compose)
    \<comment> \<open>Invertibility and the inverse are computed in the symmetric group; because
      @{term "field_auto K E"} is a subgroup there, the inverse stays inside it, and the two
      ambient groups agree on inverses by @{thm [source] Subgroup.subgroup_inverse_equality}.\<close>
    show "\<And>g. g \<in> field_auto K E \<Longrightarrow> W.invertible g"
      using EF by (blast intro: W.invertible)
    show "\<And>g. g \<in> field_auto K E \<Longrightarrow> W.inverse g \<in> field_auto K E"
    proof -
      fix g assume g: "g \<in> field_auto K E"
      then have gW: "g \<in> field_auto K F" using EF by blast
      have inv_in: "S.sub.inverse g \<in> field_auto K E"
        using g by (simp add: S.sub.invertible_inverse_closed)
      \<comment> \<open>The symmetric-group inverse is a two-sided inverse of \<open>g\<close> in the ambient Galois group
        too, so the two notions of inverse agree.\<close>
      have "W.inverse g = S.sub.inverse g"
      proof (rule W.inverse_equality)
        show "g \<in> field_auto K F" by (rule gW)
        show "S.sub.inverse g \<in> field_auto K F" using inv_in EF by blast
        show "compose K g (S.sub.inverse g) = identity K"
          using g by simp
        show "compose K (S.sub.inverse g) g = identity K"
          using g by simp
      qed
      then show "W.inverse g \<in> field_auto K E" using inv_in by simp
    qed
  qed
qed

text \<open>The set of subgroups of the Galois group, as the second of the two lattices.\<close>
definition galois_subgroups :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) set set"
  where "galois_subgroups K F =
    {H. Subgroup H (field_auto K F) (compose K) (identity K)}"

lemma galois_subgroups_iff:
  "H \<in> galois_subgroups K F \<longleftrightarrow> Subgroup H (field_auto K F) (compose K) (identity K)"
  by (simp add: galois_subgroups_def)

lemma galois_subgroups_subset:
  assumes "H \<in> galois_subgroups K F" shows "H \<subseteq> field_auto K F"
proof -
  interpret Subgroup H "field_auto K F" "compose K" "identity K"
    using assms by (simp add: galois_subgroups_iff)
  show ?thesis by (rule subset)
qed


subsection \<open>The adjunction\<close>

locale galois_extension =
  fixes K F :: "'a :: field set"
  assumes Ksub: "Subfield K" and Fsub: "Subfield F" and FK: "F \<subseteq> K"
begin

text \<open>Fixing lands in the intermediate fields: the fixed field of a subgroup is a subfield lying
  between @{term F} and @{term K}.\<close>
lemma fixed_field_in_inter_fields:
  assumes H: "H \<in> galois_subgroups K F"
  shows "fixed_field K H \<in> inter_fields K F"
proof -
  have HG: "H \<subseteq> field_auto K F" using H by (rule galois_subgroups_subset)
  show ?thesis
    unfolding inter_fields_iff
  proof (intro conjI)
    show "Subfield (fixed_field K H)" using Ksub HG by (rule fixed_field_subfield)
    show "F \<subseteq> fixed_field K H" using HG FK by (rule base_subset_fixed_field)
    show "fixed_field K H \<subseteq> K" by (rule fixed_field_subset)
  qed
qed

text \<open>\<^emph>\<open>The adjunction.\<close>  Both sides of the biconditional say the same thing --- \<^emph>\<open>every\<close>
  automorphism in @{term H} fixes \<^emph>\<open>every\<close> point of @{term E} --- so the proof is a matter of
  unfolding.  This is the antitone (or \<^emph>\<open>polarity\<close>) form of an adjunction: both maps reverse
  inclusion, and each side bounds one argument by the image of the other.

  It is worth being precise about which biconditional is formal, because the other one is a deep
  theorem.  The statement proved here bounds @{term E} \<^emph>\<open>above\<close> by a fixed field and @{term H}
  \<^emph>\<open>above\<close> by a Galois group.  The reverse reading --- @{text "fixed_field K H \<subseteq> E \<longleftrightarrow>
  field_auto K E \<subseteq> H"} --- is \<^emph>\<open>not\<close> a formal consequence: its left-to-right direction asserts that
  every automorphism fixing @{term E} already lies in @{term H}, which is Artin's theorem and needs
  @{term H} finite.\<close>
theorem fixed_field_galois:
  assumes E: "E \<in> inter_fields K F" and H: "H \<in> galois_subgroups K F"
  shows "E \<subseteq> fixed_field K H \<longleftrightarrow> H \<subseteq> field_auto K E"
proof
  assume "E \<subseteq> fixed_field K H"
  then have fixes_E: "\<And>\<sigma> x. \<lbrakk> \<sigma> \<in> H; x \<in> E \<rbrakk> \<Longrightarrow> \<sigma> x = x"
    by (auto dest: fixed_field_memD)
  show "H \<subseteq> field_auto K E"
  proof
    fix \<sigma> assume s: "\<sigma> \<in> H"
    then have "\<sigma> \<in> field_auto K F" using H galois_subgroups_subset by blast
    then show "\<sigma> \<in> field_auto K E" using s fixes_E by (auto simp: field_auto_def)
  qed
next
  assume "H \<subseteq> field_auto K E"
  then have "\<And>\<sigma> x. \<lbrakk> \<sigma> \<in> H; x \<in> E \<rbrakk> \<Longrightarrow> \<sigma> x = x" by (auto simp: field_auto_def)
  moreover have "E \<subseteq> K" using E by (simp add: inter_fields_iff)
  ultimately show "E \<subseteq> fixed_field K H" by (blast intro: fixed_field_memI)
qed

text \<open>The two \<^emph>\<open>unit\<close> inequalities, which hold unconditionally and in both directions.  These are
  the parts of the correspondence that need no hypotheses; it is their \<^emph>\<open>converses\<close> that require
  normality and separability.\<close>
lemma le_fixed_field_galois_group:
  assumes E: "E \<in> inter_fields K F"
  shows "E \<subseteq> fixed_field K (field_auto K E)"
  using E by (auto simp: inter_fields_iff fixed_field_def field_auto_def)

lemma le_galois_group_fixed_field:
  assumes H: "H \<in> galois_subgroups K F"
  shows "H \<subseteq> field_auto K (fixed_field K H)"
proof
  fix \<sigma> assume s: "\<sigma> \<in> H"
  then have "\<sigma> \<in> field_auto K F" using H galois_subgroups_subset by blast
  then show "\<sigma> \<in> field_auto K (fixed_field K H)"
    using s by (auto simp: field_auto_def fixed_field_def)
qed


subsection \<open>The Galois connection\<close>

text \<open>Both maps reverse inclusion, so to view the pair as a @{locale Galois_Connection} --- whose
  adjoints are \<^emph>\<open>isotone\<close> --- we order the subgroup lattice by \<^emph>\<open>reverse\<close> inclusion.  Then the
  adjunction @{thm [source] fixed_field_galois} is literally the @{text galois} axiom, with
  @{term "field_auto K"} as the lower adjoint out of the intermediate fields and
  @{term "fixed_field K"} as the upper adjoint back.

  Note the direction: @{term "field_auto K"} is the \<^emph>\<open>lower\<close> adjoint here, even though it is the map
  \<^emph>\<open>into\<close> the groups, because the group side carries the reversed order.  Inclusion is a partial order
  on any set of sets, and so is its converse.\<close>

text \<open>Inclusion and reverse inclusion are partial orders on the two lattices.\<close>
lemma partial_order_inter_fields: "Partial_Order (inter_fields K F) (\<subseteq>)"
  by unfold_locales auto

lemma partial_order_galois_subgroups: "Partial_Order (galois_subgroups K F) (\<lambda>H H'. H' \<subseteq> H)"
  by unfold_locales auto

theorem galois_correspondence:
  "Galois_Connection
     (inter_fields K F) (\<subseteq>)
     (galois_subgroups K F) (\<lambda>H H'. H' \<subseteq> H)
     (field_auto K) (fixed_field K)"
proof (rule Galois_Connection.intro)
  show "Partial_Order (inter_fields K F) (\<subseteq>)" by (rule partial_order_inter_fields)
  show "Partial_Order (galois_subgroups K F) (\<lambda>H H'. H' \<subseteq> H)"
    by (rule partial_order_galois_subgroups)
  show "Galois_Connection_axioms
          (inter_fields K F) (\<subseteq>) (galois_subgroups K F) (\<lambda>H H'. H' \<subseteq> H)
          (field_auto K) (fixed_field K)"
  proof
    show "field_auto K \<in> inter_fields K F \<rightarrow> galois_subgroups K F"
      using Ksub FK field_auto_subgroup_of_Galois_group by (auto simp: galois_subgroups_iff)
    show "fixed_field K \<in> galois_subgroups K F \<rightarrow> inter_fields K F"
      using fixed_field_in_inter_fields by auto
    fix E H assume "E \<in> inter_fields K F" and "H \<in> galois_subgroups K F"
    then show "H \<subseteq> field_auto K E \<longleftrightarrow> E \<subseteq> fixed_field K H"
      using fixed_field_galois by blast
  qed
qed

text \<open>The consequences, specialised to the correspondence.  As in \<open>Ideal_Extension\<close> these come from a
  local @{command interpretation} of the theorem rather than a @{command sublocale} declaration.\<close>

context
begin

interpretation GC: Galois_Connection
  "inter_fields K F" "(\<subseteq>)" "galois_subgroups K F" "\<lambda>H H'. H' \<subseteq> H"
  "field_auto K" "fixed_field K"
  by (rule galois_correspondence)

text \<open>Both maps are inclusion-reversing on their lattices --- the isotonicity of the connection,
  read back through the reversed order on subgroups.\<close>
corollary field_auto_mono:
  "\<lbrakk> E \<in> inter_fields K F; E' \<in> inter_fields K F; E \<subseteq> E' \<rbrakk>
   \<Longrightarrow> field_auto K E' \<subseteq> field_auto K E"
  using isotone_le[OF GC.lower_isotone] by simp

corollary fixed_field_mono:
  "\<lbrakk> H \<in> galois_subgroups K F; H' \<in> galois_subgroups K F; H' \<subseteq> H \<rbrakk>
   \<Longrightarrow> fixed_field K H \<subseteq> fixed_field K H'"
  using isotone_le[OF GC.upper_isotone] by simp

text \<open>The \<^emph>\<open>semi-inverse\<close> laws: one round trip and back is the identity.  These are the strongest
  fixed-point statements available without finiteness --- they say the closure and kernel operators
  are idempotent, \<^emph>\<open>not\<close> that either is the identity.\<close>
corollary field_auto_fixed_field_field_auto:
  "E \<in> inter_fields K F \<Longrightarrow> field_auto K (fixed_field K (field_auto K E)) = field_auto K E"
  using GC.lower_semi_inverse by simp

corollary fixed_field_field_auto_fixed_field:
  "H \<in> galois_subgroups K F \<Longrightarrow> fixed_field K (field_auto K (fixed_field K H)) = fixed_field K H"
  using GC.upper_semi_inverse by simp

end

end (* galois_extension *)


text \<open>\<^bold>\<open>Scope and downstream completion.\<close>  This theory deliberately stops at the
  representation-independent, inclusion-reversing adjunction, packaged as a
  @{locale Galois_Connection}.  No separability, normality or finiteness hypothesis belongs in this
  layer: the unit, counit and semi-inverse laws are the reusable order-theoretic API.

  The two fixed-point statements are assembled in downstream theories:

    \<^item> \<open>Artin_Degree\<close> supplies the finite-subgroup kernel identity,
      \<open>field_auto K (fixed_field K H) = H\<close>, through \<open>artin_theorem\<close>.  Its public theorem
      now derives the required basis from the uniform Artin bound and does not expose the old
      fixed-vector premise;

    \<^item> \<open>Galois_Finite_Extension\<close> supplies the closure identity for complex splitting fields,
      with algebraicity discharged by the generated-field API.

  Thus the complex-specific correspondence is complete in both directions at the downstream layer.
  A future abstract version over the \<open>subfield\<close> type class is separate work rather than a gap in
  this adjunction theory.\<close>

end
