section \<open>Finite p-groups\<close>

theory P_Group
  imports Sylow_Theorems
begin

context Group
begin

text \<open>The class equation makes the center of a nontrivial finite \<open>p\<close>-group visible
  arithmetically: every noncentral conjugacy orbit has cardinality divisible by \<open>p\<close>.\<close>
theorem p_group_prime_dvd_card_center:
  fixes p n :: nat
  assumes prime: "prime p" and fin: "finite G" and npos: "n > 0"
    and cardG: "card G = p ^ n"
  shows "p dvd card center"
proof -
  interpret conj: Group_Action G "(\<cdot>)" \<one> \<phi>_conj G
    by (rule conjugation_action)
  have orbit_p: "p dvd card (conj.orbit y)" if yG: "y \<in> G" and ynz: "y \<notin> center" for y
  proof -
    have orbit_dvd: "card (conj.orbit y) dvd p ^ n"
      using conj.orbit_stabilizer_card[OF yG fin] cardG by (metis dvd_triv_left)
    have orbit_ne: "conj.orbit y \<noteq> {y}"
      using conj.fixed_point_iff_orbit_singleton[OF yG] ynz center_eq_fixed_points by blast
    have orbit_card_ne: "card (conj.orbit y) \<noteq> 1"
    proof
      assume "card (conj.orbit y) = 1"
      then obtain z where orbit_z: "conj.orbit y = {z}"
        by (metis card_1_singletonE)
      have "y \<in> conj.orbit y" by (rule conj.orbit_self[OF yG])
      then have "z = y" using orbit_z by simp
      then show False using orbit_ne orbit_z by simp
    qed
    show ?thesis
    proof (rule ccontr)
      assume "\<not> p dvd card (conj.orbit y)"
      then have "card (conj.orbit y) = 1"
        by (rule prime_power_dvd_not_prime_dvd[OF prime orbit_dvd])
      then show False using orbit_card_ne by contradiction
    qed
  qed
  have p_nonfixed: "p dvd card (G - conj.fixed_points)"
    by (rule conj.dvd_card_nonfixed_points[OF fin])
      (simp add: center_eq_fixed_points orbit_p)
  have p_diff: "p dvd card (G - center)"
    using p_nonfixed by (simp add: center_eq_fixed_points)
  have pG: "p dvd card G"
  proof -
    have "p dvd p ^ n" using npos by (cases n) simp_all
    then show ?thesis using cardG by simp
  qed
  have center_le: "card center \<le> card G"
    by (rule card_mono[OF fin center_subset])
  have fin_center: "finite center"
    by (rule finite_subset[OF center_subset fin])
  have diff_card: "card (G - center) = card G - card center"
    by (rule card_Diff_subset[OF fin_center center_subset])
  have "p dvd card G - card center" using p_diff diff_card by simp
  then show ?thesis by (rule dvd_diffD1[OF _ pG center_le])
qed

corollary p_group_center_nontrivial:
  fixes p n :: nat
  assumes prime: "prime p" and fin: "finite G" and npos: "n > 0"
    and cardG: "card G = p ^ n"
  shows "\<exists>z\<in>center. z \<noteq> \<one>"
proof -
  have pdvd: "p dvd card center"
    by (rule p_group_prime_dvd_card_center[OF prime fin npos cardG])
  have unit_center: "\<one> \<in> center"
    by (rule Submonoid.sub_unit_closed[OF Subgroup.axioms(1)[OF center_subgroup]])
  have card_ne: "card center \<noteq> 1"
  proof
    assume "card center = 1"
    then have "p dvd 1" using pdvd by simp
    then show False using prime by simp
  qed
  have "center \<noteq> {\<one>}"
  proof
    assume "center = {\<one>}"
    then show False using card_ne by simp
  qed
  then show ?thesis using unit_center by blast
qed

text \<open>A group of order \<open>p\<^sup>2\<close> is abelian.  A hypothetical noncentral
  element has a centralizer strictly larger than the center; Lagrange then forces that
  centralizer to have the full group cardinality.\<close>
theorem card_prime_square_imp_abelian:
  fixes p :: nat
  assumes prime: "prime p" and fin: "finite G" and cardG: "card G = p ^ 2"
  shows "Abelian_Group G (\<cdot>) \<one>"
proof -
  have pcenter: "p dvd card center"
    by (rule p_group_prime_dvd_card_center[OF prime fin, of 2]) (simp_all add: cardG)
  have unit_center: "\<one> \<in> center"
    by (rule Submonoid.sub_unit_closed[OF Subgroup.axioms(1)[OF center_subgroup]])
  have fin_center: "finite center" by (rule finite_subset[OF center_subset fin])
  have center_ne: "center \<noteq> {}" using unit_center by blast
  have center_pos: "0 < card center"
    by (rule iffD2[OF card_gt_0_iff]) (rule conjI[OF center_ne fin_center])
  have p_le_center: "p \<le> card center"
    by (rule dvd_imp_le[OF pcenter center_pos])
  have all_center: "x \<in> center" if xG: "x \<in> G" for x
  proof (rule ccontr)
    assume xnot: "x \<notin> center"
    interpret C: subgroup_of_group "centralizer x" G "(\<cdot>)" \<one>
      using centralizer_subgroup[OF xG]
      by (simp add: Group_axioms subgroup_of_group_def)
    have center_C: "center \<subseteq> centralizer x"
    proof
      fix z assume z: "z \<in> center"
      have zG: "z \<in> G" using center_subset z by blast
      have "z \<cdot> x = x \<cdot> z" using center_mem_iff[OF zG] z xG by blast
      then show "z \<in> centralizer x" using centralizer_mem_iff[OF zG xG] by simp
    qed
    have xC: "x \<in> centralizer x"
      using centralizer_mem_iff[OF xG xG] by simp
    have center_ne_C: "center \<noteq> centralizer x"
    proof
      assume "center = centralizer x"
      then have "x \<in> center" using xC by simp
      then show False using xnot by contradiction
    qed
    have proper: "center \<subset> centralizer x"
      by (rule psubsetI[OF center_C center_ne_C])
    have finC: "finite (centralizer x)"
      by (rule finite_subset[OF centralizer_subset fin])
    have center_lt_C: "card center < card (centralizer x)"
      by (rule psubset_card_mono[OF finC proper])
    have lagrange: "card G = card (centralizer x) * C.index"
      by (rule C.lagrange[OF fin])
    have C_dvd: "card (centralizer x) dvd p ^ 2"
      using lagrange cardG by (metis dvd_triv_left)
    obtain j where jle: "j \<le> 2" and cardC: "card (centralizer x) = p ^ j"
      using divides_primepow_nat[OF prime, of "card (centralizer x)" 2] C_dvd by blast
    have p_lt_C: "p < card (centralizer x)"
      using p_le_center center_lt_C by linarith
    have j2: "j = 2"
    proof -
      have "j = 0 \<or> j = 1 \<or> j = 2" using jle by presburger
      then show ?thesis
      proof (elim disjE)
        assume "j = 0"
        then show ?thesis using cardC p_lt_C prime by (simp add: prime_ge_2_nat)
      next
        assume "j = 1"
        then show ?thesis using cardC p_lt_C by simp
      next
        assume "j = 2"
        then show ?thesis .
      qed
    qed
    have cardC_G: "card (centralizer x) = card G" using cardC cardG j2 by simp
    have C_eq: "centralizer x = G"
      by (rule card_subset_eq[OF fin centralizer_subset cardC_G])
    have commute: "x \<cdot> g = g \<cdot> x" if gG: "g \<in> G" for g
    proof -
      have "g \<in> centralizer x" using C_eq gG by simp
      then have "g \<cdot> x = x \<cdot> g"
        using centralizer_mem_iff[OF gG xG] by simp
      then show ?thesis by (rule sym)
    qed
    have "x \<in> center" using center_mem_iff[OF xG] commute by blast
    then show False using xnot by contradiction
  qed
  show ?thesis
  proof
    fix x y
    assume xG: "x \<in> G" and yG: "y \<in> G"
    have "x \<in> center" by (rule all_center[OF xG])
    then show "x \<cdot> y = y \<cdot> x" using center_mem_iff[OF xG] yG by blast
  qed
qed

end

end
