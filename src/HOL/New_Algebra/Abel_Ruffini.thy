section \<open>The Symmetric Group on the Roots and Non-Solvability\<close>

theory Abel_Ruffini
  imports Galois_Action Action_To_Sn
begin

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
