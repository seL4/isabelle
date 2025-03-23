(*  Author:  LCP, ported from HOL Light
*)

section\<open>Euclidean space and n-spheres, as subtopologies of n-dimensional space\<close>

theory Abstract_Euclidean_Space
imports Homotopy Locally
begin

subsection \<open>Euclidean spaces as abstract topologies\<close>

definition Euclidean_space :: "nat \<Rightarrow> (nat \<Rightarrow> real) topology"
  where "Euclidean_space n \<equiv> subtopology (powertop_real UNIV) {x. \<forall>i\<ge>n. x i = 0}"

lemma topspace_Euclidean_space:
   "topspace(Euclidean_space n) = {x. \<forall>i\<ge>n. x i = 0}"
  by (simp add: Euclidean_space_def)

lemma nontrivial_Euclidean_space: "Euclidean_space n \<noteq> trivial_topology"
  using topspace_Euclidean_space [of n] by force

lemma subset_Euclidean_space [simp]:
   "topspace(Euclidean_space m) \<subseteq> topspace(Euclidean_space n) \<longleftrightarrow> m \<le> n"
  apply (simp add: topspace_Euclidean_space subset_iff, safe)
   apply (drule_tac x="(\<lambda>i. if i < m then 1 else 0)" in spec)
   apply auto
  using not_less by fastforce

lemma topspace_Euclidean_space_alt:
  "topspace(Euclidean_space n) = (\<Inter>i \<in> {n..}. {x. x \<in> topspace(powertop_real UNIV) \<and> x i \<in> {0}})"
  by (auto simp: topspace_Euclidean_space)

lemma closedin_Euclidean_space:
  "closedin (powertop_real UNIV) (topspace(Euclidean_space n))"
proof -
  have "closedin (powertop_real UNIV) {x. x i = 0}" if "n \<le> i" for i
  proof -
    have "closedin (powertop_real UNIV) {x \<in> topspace (powertop_real UNIV). x i \<in> {0}}"
    proof (rule closedin_continuous_map_preimage)
      show "continuous_map (powertop_real UNIV) euclideanreal (\<lambda>x. x i)"
        by (metis UNIV_I continuous_map_product_coordinates)
      show "closedin euclideanreal {0}"
        by simp
    qed
    then show ?thesis
      by auto
  qed
  then show ?thesis
    unfolding topspace_Euclidean_space_alt
    by force
qed

lemma closedin_Euclidean_imp_closed: "closedin (Euclidean_space m) S \<Longrightarrow> closed S"
  by (metis Euclidean_space_def closed_closedin closedin_Euclidean_space closedin_closed_subtopology euclidean_product_topology topspace_Euclidean_space)

lemma closedin_Euclidean_space_iff:
  "closedin (Euclidean_space m) S \<longleftrightarrow> closed S \<and> S \<subseteq> topspace (Euclidean_space m)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using closedin_closed_subtopology topspace_Euclidean_space
    by (fastforce simp: topspace_Euclidean_space_alt closedin_Euclidean_imp_closed)
  show "?rhs \<Longrightarrow> ?lhs"
  apply (simp add: closedin_subtopology Euclidean_space_def)
    by (metis (no_types) closed_closedin euclidean_product_topology inf.orderE)
qed

lemma continuous_map_componentwise_Euclidean_space:
  "continuous_map X (Euclidean_space n) (\<lambda>x i. if i < n then f x i else 0) \<longleftrightarrow>
   (\<forall>i < n. continuous_map X euclideanreal (\<lambda>x. f x i))"
proof -
  have *: "continuous_map X euclideanreal (\<lambda>x. if k < n then f x k else 0)"
    if "\<And>i. i<n \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x i)" for k
    by (intro continuous_intros that)
  show ?thesis
    unfolding Euclidean_space_def continuous_map_in_subtopology
    by (fastforce simp: continuous_map_componentwise_UNIV * elim: continuous_map_eq)
qed

lemma continuous_map_Euclidean_space_add [continuous_intros]:
   "\<lbrakk>continuous_map X (Euclidean_space n) f; continuous_map X (Euclidean_space n) g\<rbrakk>
    \<Longrightarrow> continuous_map X (Euclidean_space n) (\<lambda>x i. f x i + g x i)"
  unfolding Euclidean_space_def continuous_map_in_subtopology
  by (auto simp: continuous_map_componentwise_UNIV Pi_iff continuous_map_add)

lemma continuous_map_Euclidean_space_diff [continuous_intros]:
   "\<lbrakk>continuous_map X (Euclidean_space n) f; continuous_map X (Euclidean_space n) g\<rbrakk>
    \<Longrightarrow> continuous_map X (Euclidean_space n) (\<lambda>x i. f x i - g x i)"
  unfolding Euclidean_space_def continuous_map_in_subtopology 
  by (auto simp: continuous_map_componentwise_UNIV Pi_iff continuous_map_diff)

lemma continuous_map_Euclidean_space_iff:
  "continuous_map (Euclidean_space m) euclidean g
   = continuous_on (topspace (Euclidean_space m)) g"
proof
  assume "continuous_map (Euclidean_space m) euclidean g"
  then have "continuous_map (top_of_set {f. \<forall>n\<ge>m. f n = 0}) euclidean g"
    by (simp add: Euclidean_space_def euclidean_product_topology)
  then show "continuous_on (topspace (Euclidean_space m)) g"
    by (metis continuous_map_subtopology_eu subtopology_topspace topspace_Euclidean_space)
next
  assume "continuous_on (topspace (Euclidean_space m)) g"
  then have "continuous_map (top_of_set {f. \<forall>n\<ge>m. f n = 0}) euclidean g"
    by (simp add: topspace_Euclidean_space)
  then show "continuous_map (Euclidean_space m) euclidean g"
    by (simp add: Euclidean_space_def euclidean_product_topology)
qed

lemma cm_Euclidean_space_iff_continuous_on:
  "continuous_map (subtopology (Euclidean_space m) S) (Euclidean_space n) f
   \<longleftrightarrow> continuous_on (topspace (subtopology (Euclidean_space m) S)) f \<and>
       f \<in> (topspace (subtopology (Euclidean_space m) S)) \<rightarrow> topspace (Euclidean_space n)"
  (is "?P \<longleftrightarrow> ?Q \<and> ?R")
proof -
  have ?Q if ?P
  proof -
    have "\<And>n. Euclidean_space n = top_of_set {f. \<forall>m\<ge>n. f m = 0}"
      by (simp add: Euclidean_space_def euclidean_product_topology)
    with that show ?thesis
      by (simp add: subtopology_subtopology)
  qed
  moreover
  have ?R if ?P
    using that by (simp add: image_subset_iff continuous_map_def)
  moreover
  have ?P if ?Q ?R
  proof -
    have "continuous_map (top_of_set (topspace (subtopology (subtopology (powertop_real UNIV) {f. \<forall>n\<ge>m. f n = 0}) S))) (top_of_set (topspace (subtopology (powertop_real UNIV) {f. \<forall>na\<ge>n. f na = 0}))) f"
      using Euclidean_space_def that by auto
    then show ?thesis
      by (simp add: Euclidean_space_def euclidean_product_topology subtopology_subtopology)
  qed
  ultimately show ?thesis
    by auto
qed

lemma homeomorphic_Euclidean_space_product_topology:
  "Euclidean_space n homeomorphic_space product_topology (\<lambda>i. euclideanreal) {..<n}"
proof -
  have cm: "continuous_map (product_topology (\<lambda>i. euclideanreal) {..<n})
          euclideanreal (\<lambda>x. if k < n then x k else 0)" for k
    by (auto intro: continuous_map_if continuous_map_product_projection)
  show ?thesis
    unfolding homeomorphic_space_def homeomorphic_maps_def
    apply (rule_tac x="\<lambda>f. restrict f {..<n}" in exI)
    apply (rule_tac x="\<lambda>f i. if i < n then f i else 0" in exI)
    apply (simp add: Euclidean_space_def continuous_map_in_subtopology)
    apply (intro conjI continuous_map_from_subtopology)
       apply (force simp: continuous_map_componentwise cm intro: continuous_map_product_projection)+
    done
qed

lemma contractible_Euclidean_space [simp]: "contractible_space (Euclidean_space n)"
  using homeomorphic_Euclidean_space_product_topology contractible_space_euclideanreal
    contractible_space_product_topology homeomorphic_space_contractibility by blast

lemma path_connected_Euclidean_space: "path_connected_space (Euclidean_space n)"
  by (simp add: contractible_imp_path_connected_space)

lemma connected_Euclidean_space: "connected_space (Euclidean_space n)"
  by (simp add: contractible_imp_connected_space)

lemma locally_path_connected_Euclidean_space:
   "locally_path_connected_space (Euclidean_space n)"
  apply (simp add: homeomorphic_locally_path_connected_space [OF homeomorphic_Euclidean_space_product_topology [of n]]
                   locally_path_connected_space_product_topology)
  using locally_path_connected_space_euclideanreal by auto

lemma compact_Euclidean_space [simp]:
   "compact_space (Euclidean_space n) \<longleftrightarrow> n = 0"
  using homeomorphic_compact_space [OF homeomorphic_Euclidean_space_product_topology] 
  by (auto simp: product_topology_trivial_iff compact_space_product_topology)


subsection\<open>n-dimensional spheres\<close>

definition nsphere where
 "nsphere n \<equiv> subtopology (Euclidean_space (Suc n)) { x. (\<Sum>i\<le>n. x i ^ 2) = 1 }"

lemma nsphere:
   "nsphere n = subtopology (powertop_real UNIV)
                            {x. (\<Sum>i\<le>n. x i ^ 2) = 1 \<and> (\<forall>i>n. x i = 0)}"
  by (simp add: nsphere_def Euclidean_space_def subtopology_subtopology Suc_le_eq Collect_conj_eq Int_commute)

lemma continuous_map_nsphere_projection: "continuous_map (nsphere n) euclideanreal (\<lambda>x. x k)"
  unfolding nsphere
  by (blast intro: continuous_map_from_subtopology [OF continuous_map_product_projection])

lemma in_topspace_nsphere: "(\<lambda>n. if n = 0 then 1 else 0) \<in> topspace (nsphere n)"
  by (simp add: nsphere_def topspace_Euclidean_space power2_eq_square if_distrib [where f = "\<lambda>x. x * _"] cong: if_cong)

lemma nonempty_nsphere [simp]: "(nsphere n) \<noteq> trivial_topology"
  by (metis discrete_topology_unique empty_iff in_topspace_nsphere)

lemma subtopology_nsphere_equator:
  "subtopology (nsphere (Suc n)) {x. x(Suc n) = 0} = nsphere n"
proof -
  have "({x. (\<Sum>i\<le>n. (x i)\<^sup>2) + (x (Suc n))\<^sup>2 = 1 \<and> (\<forall>i>Suc n. x i = 0)} \<inter> {x. x (Suc n) = 0})
      = {x. (\<Sum>i\<le>n. (x i)\<^sup>2) = 1 \<and> (\<forall>i>n. x i = (0::real))}"
    using Suc_lessI [of n] by (fastforce simp: set_eq_iff)
  then show ?thesis
    by (simp add: nsphere subtopology_subtopology)
qed

lemma topspace_nsphere_minus1:
  assumes x: "x \<in> topspace (nsphere n)" and "x n = 0"
  shows "x \<in> topspace (nsphere (n - Suc 0))"
proof (cases "n = 0")
  case True
  then show ?thesis
    using x by auto
next
  case False
  have subt_eq: "nsphere (n - Suc 0) = subtopology (nsphere n) {x. x n = 0}"
    by (metis False Suc_pred le_zero_eq not_le subtopology_nsphere_equator)
  with x show ?thesis
    by (simp add: assms)
qed

lemma continuous_map_nsphere_reflection:
  "continuous_map (nsphere n) (nsphere n) (\<lambda>x i. if i = k then -x i else x i)"
proof -
  have cm: "continuous_map (powertop_real UNIV) euclideanreal (\<lambda>x. if j = k then - x j else x j)" for j
  proof (cases "j=k")
    case True
    then show ?thesis
      by simp (metis UNIV_I continuous_map_product_projection)
  next
    case False
    then show ?thesis
      by (auto intro: continuous_map_product_projection)
  qed
  have eq: "(if i = k then x k * x k else x i * x i) = x i * x i" for i and x :: "nat \<Rightarrow> real"
    by simp
  show ?thesis
    apply (simp add: nsphere continuous_map_in_subtopology continuous_map_componentwise_UNIV
                     continuous_map_from_subtopology cm)
    apply (intro conjI allI impI continuous_intros continuous_map_from_subtopology continuous_map_product_projection)
      apply (auto simp: power2_eq_square if_distrib [where f = "\<lambda>x. x * _"] eq cong: if_cong)
    done
qed


proposition contractible_space_upper_hemisphere:
  assumes "k \<le> n"
  shows "contractible_space(subtopology (nsphere n) {x. x k \<ge> 0})"
proof -
  define p:: "nat \<Rightarrow> real" where "p \<equiv> \<lambda>i. if i = k then 1 else 0"
  have "p \<in> topspace(nsphere n)"
    using assms
    by (simp add: nsphere p_def power2_eq_square if_distrib [where f = "\<lambda>x. x * _"] cong: if_cong)
  let ?g = "\<lambda>x i. x i / sqrt(\<Sum>j\<le>n. x j ^ 2)"
  let ?h = "\<lambda>(t,q) i. (1 - t) * q i + t * p i"
  let ?Y = "subtopology (Euclidean_space (Suc n)) {x. 0 \<le> x k \<and> (\<exists>i\<le>n. x i \<noteq> 0)}"
  have "continuous_map (prod_topology (top_of_set {0..1}) (subtopology (nsphere n) {x. 0 \<le> x k}))
                       (subtopology (nsphere n) {x. 0 \<le> x k}) (?g \<circ> ?h)"
  proof (rule continuous_map_compose)
    have *: "\<lbrakk>0 \<le> b k; (\<Sum>i\<le>n. (b i)\<^sup>2) = 1; \<forall>i>n. b i = 0; 0 \<le> a; a \<le> 1\<rbrakk>
           \<Longrightarrow> \<exists>i. (i = k \<longrightarrow> (1 - a) * b k + a \<noteq> 0) \<and>
                   (i \<noteq> k \<longrightarrow> i \<le> n \<and> a \<noteq> 1 \<and> b i \<noteq> 0)" for a::real and b
      apply (cases "a \<noteq> 1 \<and> b k = 0"; simp)
       apply (metis (no_types, lifting) atMost_iff sum.neutral zero_power2)
      by (metis add.commute add_le_same_cancel2 diff_ge_0_iff_ge diff_zero less_eq_real_def mult_eq_0_iff mult_nonneg_nonneg not_le numeral_One zero_neq_numeral)
    show "continuous_map (prod_topology (top_of_set {0..1}) (subtopology (nsphere n) {x. 0 \<le> x k})) ?Y ?h"
      using assms
      apply (auto simp: * nsphere continuous_map_componentwise_UNIV
               prod_topology_subtopology subtopology_subtopology case_prod_unfold
               continuous_map_in_subtopology Euclidean_space_def p_def if_distrib [where f = "\<lambda>x. _ * x"] cong: if_cong)
      apply (intro continuous_map_prod_snd continuous_intros continuous_map_from_subtopology)
        apply auto
      done
  next
    have 1: "\<And>x i. \<lbrakk> i \<le> n; x i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<le>n. (x i / sqrt (\<Sum>j\<le>n. (x j)\<^sup>2))\<^sup>2) = 1"
      by (force simp: sum_nonneg sum_nonneg_eq_0_iff field_split_simps simp flip: sum_divide_distrib)
    have cm: "continuous_map ?Y (nsphere n) (\<lambda>x i. x i / sqrt (\<Sum>j\<le>n. (x j)\<^sup>2))"
      unfolding Euclidean_space_def nsphere subtopology_subtopology continuous_map_in_subtopology
    proof (intro continuous_intros conjI)
      show "continuous_map
               (subtopology (powertop_real UNIV) ({x. \<forall>i\<ge>Suc n. x i = 0} \<inter> {x. 0 \<le> x k \<and> (\<exists>i\<le>n. x i \<noteq> 0)}))
               (powertop_real UNIV) (\<lambda>x i. x i / sqrt (\<Sum>j\<le>n. (x j)\<^sup>2))"
        unfolding continuous_map_componentwise
        by (intro continuous_intros conjI ballI) (auto simp: sum_nonneg_eq_0_iff)
    qed (auto simp: 1)
    show "continuous_map ?Y (subtopology (nsphere n) {x. 0 \<le> x k}) (\<lambda>x i. x i / sqrt (\<Sum>j\<le>n. (x j)\<^sup>2))"
      by (force simp: cm sum_nonneg continuous_map_in_subtopology if_distrib [where f = "\<lambda>x. _ * x"] cong: if_cong)
  qed
  moreover have "(?g \<circ> ?h) (0, x) = x"
    if "x \<in> topspace (subtopology (nsphere n) {x. 0 \<le> x k})" for x
    using that
    by (simp add: assms nsphere)
  moreover
  have "(?g \<circ> ?h) (1, x) = p"
    if "x \<in> topspace (subtopology (nsphere n) {x. 0 \<le> x k})" for x
    by (force simp: assms p_def power2_eq_square if_distrib [where f = "\<lambda>x. x * _"] cong: if_cong)
  ultimately
  show ?thesis
    apply (simp add: contractible_space_def homotopic_with)
    apply (rule_tac x=p in exI)
    apply (rule_tac x="?g \<circ> ?h" in exI, force)
    done
qed


corollary contractible_space_lower_hemisphere:
  assumes "k \<le> n"
  shows "contractible_space(subtopology (nsphere n) {x. x k \<le> 0})"
proof -
  have "contractible_space (subtopology (nsphere n) {x. 0 \<le> x k}) = ?thesis"
  proof (rule homeomorphic_space_contractibility)
    show "subtopology (nsphere n) {x. 0 \<le> x k} homeomorphic_space subtopology (nsphere n) {x. x k \<le> 0}"
      unfolding homeomorphic_space_def homeomorphic_maps_def
      apply (rule_tac x="\<lambda>x i. if i = k then -(x i) else x i" in exI)+
      apply (auto simp: continuous_map_in_subtopology continuous_map_from_subtopology
                  continuous_map_nsphere_reflection)
      done
  qed
  then show ?thesis
    using contractible_space_upper_hemisphere [OF assms] by metis
qed


proposition nullhomotopic_nonsurjective_sphere_map:
  assumes f: "continuous_map (nsphere p) (nsphere p) f"
    and fim: "f ` (topspace(nsphere p)) \<noteq> topspace(nsphere p)"
  obtains a where "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) f (\<lambda>x. a)"
proof -
  obtain a where a: "a \<in> topspace(nsphere p)" "a \<notin> f ` (topspace(nsphere p))"
    using fim continuous_map_image_subset_topspace f by blast
  then have a1: "(\<Sum>i\<le>p. (a i)\<^sup>2) = 1" and a0: "\<And>i. i > p \<Longrightarrow> a i = 0"
    by (simp_all add: nsphere)
  have f1: "(\<Sum>j\<le>p. (f x j)\<^sup>2) = 1" if "x \<in> topspace (nsphere p)" for x
  proof -
    have "f x \<in> topspace (nsphere p)"
      using continuous_map_image_subset_topspace f that by blast
    then show ?thesis
      by (simp add: nsphere)
  qed
  show thesis
  proof
    let ?g = "\<lambda>x i. x i / sqrt(\<Sum>j\<le>p. x j ^ 2)"
    let ?h = "\<lambda>(t,x) i. (1 - t) * f x i - t * a i"
    let ?Y = "subtopology (Euclidean_space(Suc p)) (- {\<lambda>i. 0})"
    let ?T01 = "top_of_set {0..1::real}"
    have 1: "continuous_map (prod_topology ?T01 (nsphere p)) (nsphere p) (?g \<circ> ?h)"
    proof (rule continuous_map_compose)
      have "continuous_map (prod_topology ?T01 (nsphere p)) euclideanreal ((\<lambda>x. f x k) \<circ> snd)" for k
        unfolding nsphere
        apply (simp add: continuous_map_of_snd flip: null_topspace_iff_trivial)
        apply (rule continuous_map_compose [of _ "nsphere p" f, unfolded o_def])
        using f apply (simp add: nsphere)
        by (simp add: continuous_map_nsphere_projection)
      then have "continuous_map (prod_topology ?T01 (nsphere p)) euclideanreal (\<lambda>r. ?h r k)"
        for k
        unfolding case_prod_unfold o_def
        by (intro continuous_map_into_fulltopology [OF continuous_map_fst] continuous_intros) auto
      moreover have "?h \<in> ({0..1} \<times> topspace (nsphere p)) \<rightarrow> {x. \<forall>i\<ge>Suc p. x i = 0}"
        using continuous_map_image_subset_topspace [OF f]
        by (auto simp: nsphere image_subset_iff a0)
      moreover have "(\<lambda>i. 0) \<notin> ?h ` ({0..1} \<times> topspace (nsphere p))"
      proof clarify
        fix t b
        assume eq: "(\<lambda>i. 0) = (\<lambda>i. (1 - t) * f b i - t * a i)" and "t \<in> {0..1}" and b: "b \<in> topspace (nsphere p)"
        have "(1 - t)\<^sup>2 = (\<Sum>i\<le>p. ((1 - t) * f b i)^2)"
          using f1 [OF b] by (simp add: power_mult_distrib flip: sum_distrib_left)
        also have "\<dots> = (\<Sum>i\<le>p. (t * a i)^2)"
          using eq by (simp add: fun_eq_iff)
        also have "\<dots> = t\<^sup>2"
          using a1 by (simp add: power_mult_distrib flip: sum_distrib_left)
        finally have "1 - t = t"
          by (simp add: power2_eq_iff)
        then have *: "t = 1/2"
          by simp
        have fba: "f b \<noteq> a"
          using a(2) b by blast
        then show False
          using eq unfolding * by (simp add: fun_eq_iff)
      qed
      ultimately show "continuous_map (prod_topology ?T01 (nsphere p)) ?Y ?h"
        unfolding Euclidean_space_def continuous_map_in_subtopology continuous_map_componentwise_UNIV 
        by (force simp flip: image_subset_iff_funcset)
    next
      have *: "\<lbrakk>\<forall>i\<ge>Suc p. x i = 0; x \<noteq> (\<lambda>i. 0)\<rbrakk> \<Longrightarrow> (\<Sum>j\<le>p. (x j)\<^sup>2) \<noteq> 0" for x :: "nat \<Rightarrow> real"
        by (force simp: fun_eq_iff not_less_eq_eq sum_nonneg_eq_0_iff)
      show "continuous_map ?Y (nsphere p) ?g"
        apply (simp add: Euclidean_space_def continuous_map_in_subtopology continuous_map_componentwise_UNIV
                         nsphere continuous_map_componentwise subtopology_subtopology)
        apply (intro conjI allI continuous_intros continuous_map_from_subtopology [OF continuous_map_product_projection])
            apply (simp_all add: *)
         apply (force simp: sum_nonneg fun_eq_iff not_less_eq_eq sum_nonneg_eq_0_iff power_divide simp flip: sum_divide_distrib)
        done
    qed
    have 2: "(?g \<circ> ?h) (0, x) = f x" if "x \<in> topspace (nsphere p)" for x
      using that f1 by simp
    have 3: "(?g \<circ> ?h) (1, x) = (\<lambda>i. - a i)" for x
      using a by (force simp: field_split_simps nsphere)
    then show "homotopic_with (\<lambda>x. True) (nsphere p) (nsphere p) f (\<lambda>x. (\<lambda>i. - a i))"
      by (force simp: homotopic_with intro: 1 2 3)
  qed
qed

lemma Hausdorff_Euclidean_space:
   "Hausdorff_space (Euclidean_space n)"
  unfolding Euclidean_space_def
  by (rule Hausdorff_space_subtopology) (metis Hausdorff_space_euclidean Hausdorff_space_product_topology)

end

