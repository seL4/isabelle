section \<open>The Symmetric Group on the Roots and Non-Solvability\<close>

theory Abel_Ruffini
  imports Galois_Action Symmetric_Group Group_Operations
begin

section \<open>Embedding a Faithful Finite Action into a Concrete Symmetric Group\<close>

subsection \<open>Relabelling Symmetric Groups along a Bijection\<close>

text \<open>Relabelling along a bijection @{term e} from @{term "{0..<n}"} to a finite set @{term X}
  transports the symmetric group on @{term X} to @{term "Sn n"}.\<close>

definition pull :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> nat)"
  where "pull n e a = (\<lambda>i. if i < n then inv_into {0..<n} e (a (e i)) else i)"

context
  fixes n :: nat and e :: "nat \<Rightarrow> 'a" and X :: "'a set"
  assumes ebij: "bij_betw e {0..<n} X"
begin

lemma e_in_X: "i < n \<Longrightarrow> e i \<in> X"
  using ebij by (auto simp: bij_betw_def)

lemma inv_e_lt: "x \<in> X \<Longrightarrow> inv_into {0..<n} e x < n"
  using ebij by (metis atLeastLessThan_iff bij_betw_def inv_into_into)

lemma inv_e_e: "i < n \<Longrightarrow> inv_into {0..<n} e (e i) = i"
  using ebij by (simp add: bij_betw_inv_into_left)

lemma e_inv_e: "x \<in> X \<Longrightarrow> e (inv_into {0..<n} e x) = x"
  using ebij by (simp add: bij_betw_inv_into_right)

lemma pull_permutes:
  assumes a: "a \<in> transformations.Sym X"
  shows "pull n e a permutes {0..<n}"
proof (rule bij_imp_permutes)
  have abij: "bij_betw a X X" using a by (simp add: transformations.Units_bijective)
  show "bij_betw (pull n e a) {0..<n} {0..<n}"
  proof (rule bij_betwI)
    show "pull n e a \<in> {0..<n} \<rightarrow> {0..<n}"
      using abij by (auto simp: pull_def e_in_X inv_e_lt bij_betwE)
    show "(\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) \<in> {0..<n} \<rightarrow> {0..<n}"
      using abij by (simp add: bij_betw_def e_in_X inv_e_lt inv_into_into)
  next
    fix i assume "i \<in> {0..<n}"
    then have iln: "i < n" by simp
    have eiX: "e i \<in> X" using iln by (rule e_in_X)
    have aeiX: "a (e i) \<in> X" using abij eiX by (auto simp: bij_betwE)
    have "(\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) (pull n e a i)
            = inv_into {0..<n} e (inv_into X a (e (inv_into {0..<n} e (a (e i)))))"
      using iln by (simp add: pull_def)
    also have "inv_into X a (e (inv_into {0..<n} e (a (e i)))) = e i"
      using abij eiX by (simp add: aeiX bij_betw_inv_into_left e_inv_e)
    finally show "(\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) (pull n e a i) = i"
      by (simp add: iln inv_e_e)
    have inv_in: "inv_into X a (e i) \<in> X"
      using abij eiX by (metis bij_betw_inv_into bij_betwE)
    have "pull n e a ((\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) i)
            = inv_into {0..<n} e (a (e (inv_into {0..<n} e (inv_into X a (e i)))))"
      using iln inv_in by (simp add: pull_def inv_e_lt)
    also have "a (e (inv_into {0..<n} e (inv_into X a (e i)))) = e i"
      by (metis abij bij_betw_inv_into_right e_inv_e eiX inv_in)
    finally show "pull n e a ((\<lambda>i. inv_into {0..<n} e (inv_into X a (e i))) i) = i"
      using iln inv_e_e by presburger
  qed
qed (simp add: pull_def)


lemma pull_compose:
  assumes a: "a \<in> transformations.Sym X" and b: "b \<in> transformations.Sym X"
  shows "pull n e (compose X a b) = pull n e a \<circ> pull n e b"
proof (rule ext)
  fix i
  show "pull n e (compose X a b) i = (pull n e a \<circ> pull n e b) i"
  proof (cases "i < n")
    case True
    then have beiX: "b (e i) \<in> X"
      by (meson b bij_betwE e_in_X transformations.Units_bij_betwI)
    then show ?thesis
      using True inv_e_lt beiX by (simp add: True compose_eq e_in_X pull_def e_inv_e)
  next
    case False
    then show ?thesis by (simp add: pull_def compose_def)
  qed
qed

lemma pull_unit: "pull n e (identity X) = id"
  using e_in_X by (auto simp: pull_def inv_e_e)

lemma pull_in_Sn: "a \<in> transformations.Sym X \<Longrightarrow> pull n e a \<in> Sn n"
  by (simp add: Sn_def pull_permutes)

end

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
    define i where "i \<equiv> inv_into {0..<n} e s"
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

section \<open>The Symmetric Group on the Roots and Non-Solvability\<close>


text \<open>A subgroup of Sn p containing some p-cycle (conjugate to ncycle p) and some
  transposition is the whole group.\<close>
lemma subgroup_with_cycle_transpose_eq_Sn:
  fixes p :: nat and q :: "nat \<Rightarrow> nat" and i j :: nat
  assumes p: "prime p" and H: "Subgroup H (Sn p) (\<circ>) id"
    and q: "q \<in> Sn p"
    and c_in: "q \<circ> ncycle p \<circ> inv q \<in> H"
    and t_in: "Transposition.transpose i j \<in> H"
    and i: "i < p" and jj: "j < p" and ij: "i \<noteq> j"
  shows "H = Sn p"
proof -
  interpret G: Group "Sn p" "(\<circ>)" id by (rule Group_Sn)
  interpret H: Subgroup H "Sn p" "(\<circ>)" id by (rule H)
  have bq: "bij q" using q by (simp add: Sn_def permutes_bij)
  \<comment> \<open>Write the transposition as the same-conjugator form.\<close>
  define a where "a = inv q i"
  define b where "b = inv q j"
  have qa: "q a = i" unfolding a_def using bq by (simp add: surj_f_inv_f bij_is_surj)
  have qb: "q b = j" unfolding b_def using bq by (simp add: surj_f_inv_f bij_is_surj)
  have qperm: "q permutes {0..<p}" using q by (simp add: Sn_iff)
  have ap: "a < p"
    using a_def i permutes_nat_inv_less qperm by presburger
  have bp: "b < p"
    using b_def jj permutes_nat_less permutes_nat_inv_less qperm by blast
  have ab: "a \<noteq> b" using ij qa qb by auto
  have t_eq: "Transposition.transpose i j = q \<circ> Transposition.transpose a b \<circ> inv q"
    using bq qa qb by (simp add: transpose_conjug)
  \<comment> \<open>Both generators lie in H, so the generated subgroup (= Sn p) is contained in H.\<close>
  have gens_sub: "{q \<circ> ncycle p \<circ> inv q, q \<circ> Transposition.transpose a b \<circ> inv q} \<subseteq> H"
    using c_in t_in t_eq by auto
  have "Sn p = G.generate {q \<circ> ncycle p \<circ> inv q, q \<circ> Transposition.transpose a b \<circ> inv q}"
    using Sn_generated_conj_cycle_transpose[OF p q ap bp ab] by simp
  also have "\<dots> \<subseteq> H"
    using G.generate_mono G.generate_subgroup_eq H gens_sub by blast
  finally show ?thesis by blast
qed


text \<open>The abstract group-theoretic heart of Abel--Ruffini: a finite group acting faithfully
  and transitively on a set of prime cardinality @{term "p \<ge> 5"}, whose image in @{term "Sn p"}
  contains a transposition, is not solvable, because that image is then all of @{term "Sn p"},
  which is not solvable.\<close>
theorem (in Group_Action) not_solvable_of_transitive_with_transposition:
  fixes e :: "nat \<Rightarrow> 'b" and p :: nat
  assumes ebij: "bij_betw e {0..<p} S"
    and p: "prime p" and p5: "5 \<le> p" and finG: "finite G"
    and faith: faithful
    and trans: "\<exists>s\<in>S. orbit s = S"
    and transp: "\<exists>i j. i < p \<and> j < p \<and> i \<noteq> j
                   \<and> Transposition.transpose i j \<in> (\<lambda>g. pull p e (\<phi> g)) ` G"
  shows "\<not> Group.solvable G (\<cdot>) \<one>"
proof
  assume solv: "Group.solvable G (\<cdot>) \<one>"
  define \<Psi> where "\<Psi> = restrict (\<lambda>g. pull p e (\<phi> g)) G"
  define I where "I = (\<lambda>g. pull p e (\<phi> g)) ` G"
  \<comment> \<open>The transported action is an isomorphism of G onto the subgroup I of Sn p.\<close>
  have iso: "group_isomorphism \<Psi> G (\<cdot>) \<one> I (\<circ>) id"
    unfolding \<Psi>_def I_def by (rule action_embeds_Sn[OF ebij faith])
  interpret Iso: group_isomorphism \<Psi> G "(\<cdot>)" \<one> I "(\<circ>)" id by (rule iso)
  interpret Hom: group_homomorphism \<Psi> G "(\<cdot>)" \<one> "Sn p" "(\<circ>)" id
    unfolding \<Psi>_def by (rule action_pull_hom[OF ebij])
  interpret G5: Group "Sn p" "(\<circ>)" id by (rule Group_Sn)
  have finS: "finite S" using ebij bij_betw_finite by blast
  have cardS: "card S = p" using ebij bij_betw_same_card by (metis card_atLeastLessThan diff_zero)
  \<comment> \<open>p divides card G, by orbit-stabilizer with a full orbit.\<close>
  obtain s0 where s0: "s0 \<in> S" and orb: "orbit s0 = S" using trans by blast
  have "card G = card (orbit s0) * card (stabilizer s0)"
    using s0 finG by (rule orbit_stabilizer_card)
  then have pdvd: "p dvd card G" using orb cardS by (metis dvd_triv_left)
  \<comment> \<open>Cauchy: an order-p element of G.\<close>
  obtain g0 where g0: "g0 \<in> G" and g0ord: "grp.element_order g0 = p"
    using grp.Cauchy[OF p finG pdvd] by blast
  \<comment> \<open>Its image has the same order @{term p}, computed via the isomorphism (using the raw
    @{const Monoid.element_order} bridge so the orders match by name), and so is a p-cycle.\<close>
  have psg0_in: "\<Psi> g0 \<in> I" unfolding I_def \<Psi>_def using g0 by auto
  have I_sub_Sn: "I \<subseteq> Sn p"
    using hom_closed ebij by (simp add: I_def image_subset_iff pull_in_Sn)
  have finI: "finite I" using I_sub_Sn finite_Sn finite_subset by blast
  have psg0_Sn: "\<Psi> g0 \<in> Sn p" using psg0_in I_sub_Sn by blast
  have img_ord: "Monoid.element_order (\<circ>) id (\<Psi> g0) = p"
    using Iso.element_order_preserved'[OF finG finI g0] g0ord by simp
  obtain q where q: "q \<in> Sn p" and cyc: "\<Psi> g0 = q \<circ> ncycle p \<circ> inv q"
    using order_p_elt_conj_ncycle_order[OF p psg0_Sn img_ord] by blast
  \<comment> \<open>I is a subgroup of Sn p containing this p-cycle and (by hypothesis) a transposition.\<close>
  have I_sub: "Subgroup I (Sn p) (\<circ>) id"
    using Hom.image.Subgroup_axioms unfolding \<Psi>_def I_def by simp
  obtain i j where ij: "i < p" "j < p" "i \<noteq> j" and t_in: "Transposition.transpose i j \<in> I"
    using transp I_def by blast
  have c_in: "q \<circ> ncycle p \<circ> inv q \<in> I" using psg0_in cyc by simp
  have "I = Sn p"
    using subgroup_with_cycle_transpose_eq_Sn[OF p I_sub q c_in t_in ij] .
  \<comment> \<open>So G is isomorphic onto Sn p, which would make Sn p solvable --- contradiction.\<close>
  then have "Group.solvable (Sn p) (\<circ>) id"
    using Iso.solvable_image_epi[OF solv] by simp
  with Sn_not_solvable p5 show False by blast
qed

end
