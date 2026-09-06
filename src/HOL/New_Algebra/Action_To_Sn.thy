section \<open>Embedding a Faithful Finite Action into a Concrete Symmetric Group\<close>

theory Action_To_Sn
  imports Symmetric_Relabel Group_Operations
begin

context Group_Action
begin

text \<open>Transport a faithful finite action into the concrete symmetric group Sn (card S),
  via an enumeration e of S.\<close>

lemma action_pull_hom:
  assumes ebij: "bij_betw e {0..<n} S"
  shows "group_homomorphism (restrict (\<lambda>g. pull n e (\<phi> g)) G) G (\<cdot>) \<one> (Sn n) (\<circ>) id"
proof -
  interpret T: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  have phiSym: "\<phi> g \<in> transformations.Sym S" if "g \<in> G" for g
    using that by (rule hom_closed)
  show ?thesis
  proof 
    show "restrict (\<lambda>g. pull n e (\<phi> g)) G \<in> G \<rightarrow>\<^sub>E Sn n"
      using phiSym ebij by (simp add: pull_in_Sn)
  next
    fix g h assume g: "g \<in> G" and h: "h \<in> G"
    have "pull n e (\<phi> (g \<cdot> h)) = pull n e (\<phi> g) \<circ> pull n e (\<phi> h)"
      by (simp add: ebij g h hom_compose pull_compose)
    then show "restrict (\<lambda>g. pull n e (\<phi> g)) G (g \<cdot> h)
                = restrict (\<lambda>g. pull n e (\<phi> g)) G g \<circ> restrict (\<lambda>g. pull n e (\<phi> g)) G h"
      using g h by (simp add: grp.composition_closed)
  next
    show "restrict (\<lambda>g. pull n e (\<phi> g)) G \<one> = id"
      using ebij grp.unit_closed by (simp add: hom_unit pull_unit)
  qed
qed

text \<open>Under faithfulness the transported homomorphism has trivial kernel, hence is injective.\<close>
lemma action_pull_inj:
  assumes ebij: "bij_betw e {0..<n} S" and faith: faithful
  shows "inj_on (restrict (\<lambda>g. pull n e (\<phi> g)) G) G"
proof (rule inj_onI)
  fix g h assume g: "g \<in> G" and h: "h \<in> G"
    and eq: "restrict (\<lambda>g. pull n e (\<phi> g)) G g = restrict (\<lambda>g. pull n e (\<phi> g)) G h"
  have pgh: "pull n e (\<phi> g) = pull n e (\<phi> h)" using eq g h by simp
  have agree: "\<phi> g s = \<phi> h s" if s: "s \<in> S" for s
  proof -
    define i where "i = inv_into {0..<n} e s"
    have iln: "i < n" using ebij s unfolding i_def by (metis atLeastLessThan_iff bij_betw_def inv_into_into)
    have ei: "e i = s" using ebij s unfolding i_def by (simp add: bij_betw_inv_into_right)
    have "inv_into {0..<n} e (\<phi> g s) = inv_into {0..<n} e (\<phi> h s)"
      by (metis ei iln pgh pull_def)
    then show "\<phi> g s = \<phi> h s"
      by (metis action_closed bij_betw_inv_into_right ebij g h that)  
  qed
  have ginvg: "grp.inverse g \<in> G" using g by (simp add: grp.invertible_inverse_closed grp.invertible)
  have ghG: "grp.inverse g \<cdot> h \<in> G" using ginvg h by (rule grp.composition_closed)
  have triv: "\<phi> (grp.inverse g \<cdot> h) s = s" if s: "s \<in> S" for s
    by (metis action_mult agree g ginvg group_inv_rel h that)
  have invgh: "grp.inverse g \<cdot> h = \<one>"
    using faith ghG triv unfolding faithful_def by blast
  show "g = h"
    using g grp.inverse_unique h invgh by auto 
qed

text \<open>Hence a faithful finite action embeds @{term G} as a subgroup of @{term "Sn n"}: the
  transported map is a group isomorphism onto its image.\<close>
theorem action_embeds_Sn:
  assumes ebij: "bij_betw e {0..<n} S" and faith: faithful
  shows "group_isomorphism (restrict (\<lambda>g. pull n e (\<phi> g)) G) G (\<cdot>) \<one>
           ((\<lambda>g. pull n e (\<phi> g)) ` G) (\<circ>) id"
proof -
  interpret H: group_homomorphism "restrict (\<lambda>g. pull n e (\<phi> g)) G" G "(\<cdot>)" \<one> "Sn n" "(\<circ>)" id
    by (rule action_pull_hom[OF ebij])
  have img: "restrict (\<lambda>g. pull n e (\<phi> g)) G ` G = (\<lambda>g. pull n e (\<phi> g)) ` G" by auto
  interpret Img: Subgroup "(\<lambda>g. pull n e (\<phi> g)) ` G" "Sn n" "(\<circ>)" id
    using H.image.Subgroup_axioms img by simp
  show ?thesis
  proof 
    have inj: "inj_on (restrict (\<lambda>g. pull n e (\<phi> g)) G) G" 
      by (rule action_pull_inj[OF ebij faith])
    with img show "bij_betw (restrict (\<lambda>g. pull n e (\<phi> g)) G) G ((\<lambda>g. pull n e (\<phi> g)) ` G)"
      by (simp add: bij_betw_def)
  qed (use H.commutes_with_unit H.commutes_with_composition in auto)
qed

end

end
