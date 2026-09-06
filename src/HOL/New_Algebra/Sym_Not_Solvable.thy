section \<open>Insolvability of the Symmetric Group\<close>

theory Sym_Not_Solvable
  imports Symmetric_Group Solvable_Transfer
begin

text \<open>
  For @{text "n \<ge> 5"} the symmetric group @{term "Sn n"} is not solvable.  The argument
  is the classical one: every three-cycle is a commutator of two three-cycles (using two
  ``spare'' points, which exist when @{text "n \<ge> 5"}), so the three-cycles survive in
  every term of the derived series, which therefore never reaches the trivial subgroup.
\<close>

subsection \<open>Three-cycles as commutators\<close>

text \<open>The inverse of a three-cycle is the reversed three-cycle.\<close>
lemma rev_inv_3cycle:
  assumes "distinct [a,b,(c::nat)]"
  shows "inv (cycle_of_list [a,b,c]) = cycle_of_list [c,b,a]"
  using assms by (auto simp add: o_inv_distrib inv_unique_comp transpose_def)

text \<open>Inside @{term "Sn n"} the group inverse coincides with the functional inverse.\<close>
lemma Sn_inverse:
  assumes "p \<in> Sn n"
  shows "Monoid.inverse (Sn n) (\<circ>) id p = inv p"
proof -
  interpret S: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  show ?thesis
    by (metis S.invertible S.invertible_left_inverse S.invertible_right_inverse assms inv_unique_comp)
qed

text \<open>The defining pointwise identity: a three-cycle factors as a product of four
  three-cycles (which is, up to inverses, a commutator).  Verified by a six-way case
  split on the argument.\<close>
lemma three_cycle_commutator_core:
  assumes dist: "distinct [a,b,c,d,(e::nat)]"
  shows "cycle_of_list [a,b,c]
           = cycle_of_list [a,b,d] \<circ> cycle_of_list [c,e,a] \<circ> cycle_of_list [d,b,a] \<circ> cycle_of_list [a,e,c]"
proof (rule ext)
  fix x
  have ne: "a\<noteq>b" "a\<noteq>c" "a\<noteq>d" "a\<noteq>e" "b\<noteq>c" "b\<noteq>d" "b\<noteq>e" "c\<noteq>d" "c\<noteq>e" "d\<noteq>e"
    using dist by auto
  then show "cycle_of_list [a,b,c] x
               = (cycle_of_list [a,b,d] \<circ> cycle_of_list [c,e,a] \<circ> cycle_of_list [d,b,a] \<circ> cycle_of_list [a,e,c]) x"
    by (cases "x \<in> {a,b,c,d,e}") (auto simp: ne ne[symmetric])+
qed

text \<open>Hence a three-cycle is a commutator of two three-cycles in @{term "Sn n"}.\<close>
theorem three_cycle_commutator:
  assumes dist: "distinct [a,b,c,d,(e::nat)]" and lt: "a<n" "b<n" "c<n" "d<n" "e<n"
  shows "cycle_of_list [a,b,c]
           = Group.commutator_elt (Sn n) (\<circ>) id (cycle_of_list [a,b,d]) (cycle_of_list [c,e,a])"
proof -
  interpret S: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  have ip: "inv (cycle_of_list [a,b,d]) = cycle_of_list [d,b,a]"
    using dist by (intro rev_inv_3cycle) auto
  have iq: "inv (cycle_of_list [c,e,a]) = cycle_of_list [a,e,c]"
    using dist by (intro rev_inv_3cycle) auto
  have p_in: "cycle_of_list [a,b,d] \<in> Sn n" using dist lt by (intro three_cycle_in_Sn) auto
  have q_in: "cycle_of_list [c,e,a] \<in> Sn n" using dist lt by (intro three_cycle_in_Sn) auto
  have "Group.commutator_elt (Sn n) (\<circ>) id (cycle_of_list [a,b,d]) (cycle_of_list [c,e,a])
      = cycle_of_list [a,b,d] \<circ> cycle_of_list [c,e,a] \<circ> cycle_of_list [d,b,a] \<circ> cycle_of_list [a,e,c]"
    using p_in q_in ip iq by (simp add: S.commutator_elt_def Sn_inverse)
  also have "\<dots> = cycle_of_list [a,b,c]"
    using three_cycle_commutator_core[OF dist] by simp
  finally show ?thesis ..
qed


subsection \<open>Persistence of three-cycles in the derived series\<close>

text \<open>A set of cardinality at least two contains two distinct elements.  (A direct
  consequence of the library lemma @{thm [source] card_le_Suc_iff}.)\<close>
lemma card_ge2_two_elems:
  assumes "2 \<le> card R"
  shows "\<exists>d e. d \<in> R \<and> e \<in> R \<and> d \<noteq> e"
  using card_le_Suc_iff[of 1 R] assms not_less_eq_eq by fastforce 

text \<open>For @{text "n \<ge> 5"} there are two further points distinct from any three.\<close>
lemma two_spare_points:
  assumes n5: "5 \<le> n" and dist: "distinct [a,b,(c::nat)]" and lt: "a<n" "b<n" "c<n"
  shows "\<exists>d e. distinct [a,b,c,d,e] \<and> d<n \<and> e<n"
proof -
  let ?R = "{0..<n} - {a,b,c}"
  have "{a,b,c} \<subseteq> {0..<n}" using lt by auto
  then have "card ?R = card {0..<n} - card {a,b,c}" by (simp add: card_Diff_subset)
  moreover have "card {a,b,c} = 3" using dist by auto
  ultimately have "2 \<le> card ?R" using n5 by simp
  then obtain d e where "d \<in> ?R" "e \<in> ?R" "d \<noteq> e" using card_ge2_two_elems by blast
  then show ?thesis using dist by auto
qed

text \<open>If a subgroup of @{term "Sn n"} contains all three-cycles, so does its commutator
  subgroup.\<close>
lemma three_cycle_in_commutator_subgroup:
  assumes n5: "5 \<le> n"
    and H: "Subgroup H (Sn n) (\<circ>) id"
    and Hcyc: "\<And>x y z. distinct [x,y,z] \<Longrightarrow> x<n \<Longrightarrow> y<n \<Longrightarrow> z<n \<Longrightarrow> cycle_of_list [x,y,z] \<in> H"
    and dist: "distinct [a,b,c]" and lt: "a<n" "b<n" "c<n"
  shows "cycle_of_list [a,b,c] \<in> Group.commutator_subgroup (Sn n) (\<circ>) id H H"
proof -
  interpret HS: Subgroup H "Sn n" "(\<circ>)" id
    using H by blast
  obtain d e where de: "distinct [a,b,c,d,e]" "d<n" "e<n"
    using two_spare_points[OF n5 dist lt] by blast
  have hd: "cycle_of_list [a,b,d] \<in> H" using de dist lt by (intro Hcyc) auto
  have he: "cycle_of_list [c,e,a] \<in> H" using de dist lt by (intro Hcyc) auto
  have "cycle_of_list [a,b,c]
      = Group.commutator_elt (Sn n) (\<circ>) id (cycle_of_list [a,b,d]) (cycle_of_list [c,e,a])"
    using de dist lt by (intro three_cycle_commutator) auto
  then show ?thesis
    by (metis Group.commutator_gen_mem Group_Sn HS.subset hd he)
qed

text \<open>Every three-cycle survives in every term of the derived series of @{term "Sn n"}.\<close>
lemma three_cycles_in_derivedSeries:
  assumes n5: "5 \<le> n" and dist: "distinct [a,b,c]" and lt: "a<n" "b<n" "c<n"
  shows "cycle_of_list [a,b,c] \<in> Group.derivedSeries (Sn n) (\<circ>) id m"
proof -
  interpret S: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  have "\<forall>x y z. distinct [x,y,z] \<longrightarrow> x<n \<longrightarrow> y<n \<longrightarrow> z<n
           \<longrightarrow> cycle_of_list [x,y,z] \<in> S.derivedSeries m"
  proof (induction m)
    case 0
    show ?case
      using S.derivedSeries.simps(1) three_cycle_in_Sn by blast
  next
    case (Suc m)
    then show ?case
      using S.derivedSeries.simps(2) S.derivedSeries_subgroup n5 three_cycle_in_commutator_subgroup
      by blast
  qed
  then show ?thesis using dist lt by blast
qed


subsection \<open>The main theorem\<close>

lemma three_cycle_012_neq_id: "cycle_of_list [0,1,2] \<noteq> (id :: nat \<Rightarrow> nat)"
proof
  assume "cycle_of_list [0,1,2] = (id :: nat \<Rightarrow> nat)"
  then have "cycle_of_list [(0::nat),1,2] 0 = 0" by simp
  moreover have "cycle_of_list [(0::nat),1,2] 0 = 1" by (simp add: transpose_def)
  ultimately show False by simp
qed

theorem Sn_not_solvable:
  assumes n5: "5 \<le> n"
  shows "\<not> Group.solvable (Sn n) (\<circ>) id"
proof
  interpret S: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  assume "S.solvable"
  then obtain m where m: "S.derivedSeries m = {id}" unfolding S.solvable_def by blast
  have "cycle_of_list [0,1,2] \<in> S.derivedSeries m"
    using n5 by (intro three_cycles_in_derivedSeries) auto
  with m have "cycle_of_list [0,1,2] = (id :: nat \<Rightarrow> nat)" by simp
  then show False using three_cycle_012_neq_id by simp
qed


subsection \<open>The alternating group\<close>

text \<open>The same argument runs inside the alternating group: every three-cycle is even,
  so it lies in @{term "An n"}, and the commutator-of-three-cycles identity stays inside
  @{term "An n"}.  The key reuse is @{thm [source] Group.commutator_elt_subgroup_eq}: the
  commutator computed in the subgroup @{term "An n"} agrees with the one in @{term "Sn n"}.\<close>

lemma An_is_subgroup_of_Sn: "Subgroup (An n) (Sn n) (\<circ>) id"
  using An_normal by (simp add: normal_subgroup_def subgroup_of_group_def)

lemma Group_An: "Group (An n) (\<circ>) id"
  by (rule subgroup_imp_Group[OF An_is_subgroup_of_Sn])

lemma three_cycle_in_An_commutator_subgroup:
  assumes n5: "5 \<le> n"
    and H: "Subgroup H (An n) (\<circ>) id"
    and Hcyc: "\<And>x y z. distinct [x,y,z] \<Longrightarrow> x<n \<Longrightarrow> y<n \<Longrightarrow> z<n \<Longrightarrow> cycle_of_list [x,y,z] \<in> H"
    and dist: "distinct [a,b,c]" and lt: "a<n" "b<n" "c<n"
  shows "cycle_of_list [a,b,c] \<in> Group.commutator_subgroup (An n) (\<circ>) id H H"
proof -
  interpret S: Group "Sn n" "(\<circ>)" id by (rule Group_Sn)
  interpret HA: Subgroup H "An n" "(\<circ>)" id by (rule H)
  obtain d e where de: "distinct [a,b,c,d,e]" "d<n" "e<n"
    using two_spare_points[OF n5 dist lt] by blast
  have hd: "cycle_of_list [a,b,d] \<in> H" using de dist lt by (intro Hcyc) auto
  have he: "cycle_of_list [c,e,a] \<in> H" using de dist lt by (intro Hcyc) auto
  have hd_A: "cycle_of_list [a,b,d] \<in> An n" using de dist lt by (intro three_cycle_in_An) auto
  \<comment> \<open>the commutator in @{term "An n"} agrees with the one in @{term "Sn n"}\<close>
  have "cycle_of_list [a,b,c]
      = Group.commutator_elt (An n) (\<circ>) id (cycle_of_list [a,b,d]) (cycle_of_list [c,e,a])"
    using An_is_subgroup_of_Sn HA.sub S.commutator_elt_subgroup_eq de hd_A he lt
          three_cycle_commutator by presburger 
  with HA.subset show ?thesis
    by (metis Group.commutator_gen_mem Group_An hd he)
qed

lemma three_cycles_in_An_derivedSeries:
  assumes n5: "5 \<le> n" and dist: "distinct [a,b,c]" and lt: "a<n" "b<n" "c<n"
  shows "cycle_of_list [a,b,c] \<in> Group.derivedSeries (An n) (\<circ>) id m"
proof -
  interpret A: Group "An n" "(\<circ>)" id by (rule Group_An)
  have ?thesis 
    using dist lt
  proof (induction m arbitrary: a b c)
    case 0
    then show ?case
      using A.derivedSeries.simps(1) three_cycle_in_An by blast
  next
    case (Suc m)
    with A.derivedSeries.simps(2) A.derivedSeries_subgroup n5
          three_cycle_in_An_commutator_subgroup show ?case by blast 
  qed
  then show ?thesis using dist lt by blast
qed

theorem An_not_solvable:
  assumes n5: "5 \<le> n"
  shows "\<not> Group.solvable (An n) (\<circ>) id"
proof
  interpret A: Group "An n" "(\<circ>)" id by (rule Group_An)
  assume "A.solvable"
  then obtain m where m: "A.derivedSeries m = {id}" unfolding A.solvable_def by blast
  have "cycle_of_list [0,1,2] \<in> A.derivedSeries m"
    using n5 by (intro three_cycles_in_An_derivedSeries) auto
  with m show False using three_cycle_012_neq_id by simp
qed

end
