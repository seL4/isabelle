section\<open>The binary product topology\<close>

theory Product_Topology
imports Function_Topology Abstract_Limits
begin

section \<open>Product Topology\<close> 

subsection\<open>Definition\<close>

definition prod_topology :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<times> 'b) topology" where
 "prod_topology X Y \<equiv> topology (arbitrary union_of (\<lambda>U. U \<in> {S \<times> T |S T. openin X S \<and> openin Y T}))"

lemma open_product_open:
  assumes "open A"
  shows "\<exists>\<U>. \<U> \<subseteq> {S \<times> T |S T. open S \<and> open T} \<and> \<Union> \<U> = A"
proof -
  obtain f g where *: "\<And>u. u \<in> A \<Longrightarrow> open (f u) \<and> open (g u) \<and> u \<in> (f u) \<times> (g u) \<and> (f u) \<times> (g u) \<subseteq> A"
    using open_prod_def [of A] assms by metis
  let ?\<U> = "(\<lambda>u. f u \<times> g u) ` A"
  show ?thesis
    by (rule_tac x="?\<U>" in exI) (auto simp: dest: *)
qed

lemma open_product_open_eq: "(arbitrary union_of (\<lambda>U. \<exists>S T. U = S \<times> T \<and> open S \<and> open T)) = open"
  by (force simp: union_of_def arbitrary_def intro: open_product_open open_Times)

lemma openin_prod_topology:
   "openin (prod_topology X Y) = arbitrary union_of (\<lambda>U. U \<in> {S \<times> T |S T. openin X S \<and> openin Y T})"
  unfolding prod_topology_def
proof (rule topology_inverse')
  show "istopology (arbitrary union_of (\<lambda>U. U \<in> {S \<times> T |S T. openin X S \<and> openin Y T}))"
    apply (rule istopology_base, simp)
    by (metis openin_Int Times_Int_Times)
qed

lemma topspace_prod_topology [simp]:
   "topspace (prod_topology X Y) = topspace X \<times> topspace Y"
proof -
  have "topspace(prod_topology X Y) = \<Union> (Collect (openin (prod_topology X Y)))" (is "_ = ?Z")
    unfolding topspace_def ..
  also have "\<dots> = topspace X \<times> topspace Y"
  proof
    show "?Z \<subseteq> topspace X \<times> topspace Y"
      apply (auto simp: openin_prod_topology union_of_def arbitrary_def)
      using openin_subset by force+
  next
    have *: "\<exists>A B. topspace X \<times> topspace Y = A \<times> B \<and> openin X A \<and> openin Y B"
      by blast
    show "topspace X \<times> topspace Y \<subseteq> ?Z"
      apply (rule Union_upper)
      using * by (simp add: openin_prod_topology arbitrary_union_of_inc)
  qed
  finally show ?thesis .
qed

lemma subtopology_Times:
  shows "subtopology (prod_topology X Y) (S \<times> T) = prod_topology (subtopology X S) (subtopology Y T)"
proof -
  have "((\<lambda>U. \<exists>S T. U = S \<times> T \<and> openin X S \<and> openin Y T) relative_to S \<times> T) =
        (\<lambda>U. \<exists>S' T'. U = S' \<times> T' \<and> (openin X relative_to S) S' \<and> (openin Y relative_to T) T')"
    by (auto simp: relative_to_def Times_Int_Times fun_eq_iff) metis
  then show ?thesis
    by (simp add: topology_eq openin_prod_topology arbitrary_union_of_relative_to flip: openin_relative_to)
qed

lemma prod_topology_subtopology:
    "prod_topology (subtopology X S) Y = subtopology (prod_topology X Y) (S \<times> topspace Y)"
    "prod_topology X (subtopology Y T) = subtopology (prod_topology X Y) (topspace X \<times> T)"
by (auto simp: subtopology_Times)

lemma prod_topology_discrete_topology:
     "discrete_topology (S \<times> T) = prod_topology (discrete_topology S) (discrete_topology T)"
  by (auto simp: discrete_topology_unique openin_prod_topology intro: arbitrary_union_of_inc)

lemma prod_topology_euclidean [simp]: "prod_topology euclidean euclidean = euclidean"
  by (simp add: prod_topology_def open_product_open_eq)

lemma prod_topology_subtopology_eu [simp]:
  "prod_topology (subtopology euclidean S) (subtopology euclidean T) = subtopology euclidean (S \<times> T)"
  by (simp add: prod_topology_subtopology subtopology_subtopology Times_Int_Times)

lemma continuous_map_subtopology_eu [simp]:
  "continuous_map (subtopology euclidean S) (subtopology euclidean T) h \<longleftrightarrow> continuous_on S h \<and> h ` S \<subseteq> T"
  apply safe
  apply (metis continuous_map_closedin_preimage_eq continuous_map_in_subtopology continuous_on_closed order_refl topspace_euclidean_subtopology)
  apply (simp add: continuous_map_closedin_preimage_eq image_subset_iff)
  by (metis (no_types, hide_lams) continuous_map_closedin_preimage_eq continuous_map_in_subtopology continuous_on_closed order_refl topspace_euclidean_subtopology)

lemma openin_prod_topology_alt:
     "openin (prod_topology X Y) S \<longleftrightarrow>
      (\<forall>x y. (x,y) \<in> S \<longrightarrow> (\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> S))"
  apply (auto simp: openin_prod_topology arbitrary_union_of_alt, fastforce)
  by (metis mem_Sigma_iff)

lemma open_map_fst: "open_map (prod_topology X Y) X fst"
  unfolding open_map_def openin_prod_topology_alt
  by (force simp: openin_subopen [of X "fst ` _"] intro: subset_fst_imageI)

lemma open_map_snd: "open_map (prod_topology X Y) Y snd"
  unfolding open_map_def openin_prod_topology_alt
  by (force simp: openin_subopen [of Y "snd ` _"] intro: subset_snd_imageI)

lemma openin_Times:
     "openin (prod_topology X Y) (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> openin X S \<and> openin Y T"
proof (cases "S = {} \<or> T = {}")
  case False
  then show ?thesis
    apply (simp add: openin_prod_topology_alt openin_subopen [of X S] openin_subopen [of Y T] times_subset_iff, safe)
      apply (meson|force)+
    done
qed force


lemma closure_of_Times:
   "(prod_topology X Y) closure_of (S \<times> T) = (X closure_of S) \<times> (Y closure_of T)"  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: closure_of_def openin_prod_topology_alt) blast
  show "?rhs \<subseteq> ?lhs"
    by (clarsimp simp: closure_of_def openin_prod_topology_alt) (meson SigmaI subsetD)
qed

lemma closedin_Times:
   "closedin (prod_topology X Y) (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> closedin X S \<and> closedin Y T"
  by (auto simp: closure_of_Times times_eq_iff simp flip: closure_of_eq)

lemma interior_of_Times: "(prod_topology X Y) interior_of (S \<times> T) = (X interior_of S) \<times> (Y interior_of T)"
proof (rule interior_of_unique)
  show "(X interior_of S) \<times> Y interior_of T \<subseteq> S \<times> T"
    by (simp add: Sigma_mono interior_of_subset)
  show "openin (prod_topology X Y) ((X interior_of S) \<times> Y interior_of T)"
    by (simp add: openin_Times)
next
  show "T' \<subseteq> (X interior_of S) \<times> Y interior_of T" if "T' \<subseteq> S \<times> T" "openin (prod_topology X Y) T'" for T'
  proof (clarsimp; intro conjI)
    fix a :: "'a" and b :: "'b"
    assume "(a, b) \<in> T'"
    with that obtain U V where UV: "openin X U" "openin Y V" "a \<in> U" "b \<in> V" "U \<times> V \<subseteq> T'"
      by (metis openin_prod_topology_alt)
    then show "a \<in> X interior_of S"
      using interior_of_maximal_eq that(1) by fastforce
    show "b \<in> Y interior_of T"
      using UV interior_of_maximal_eq that(1)
      by (metis SigmaI mem_Sigma_iff subset_eq)
  qed
qed

subsection \<open>Continuity\<close>

lemma continuous_map_pairwise:
   "continuous_map Z (prod_topology X Y) f \<longleftrightarrow> continuous_map Z X (fst \<circ> f) \<and> continuous_map Z Y (snd \<circ> f)"
   (is "?lhs = ?rhs")
proof -
  let ?g = "fst \<circ> f" and ?h = "snd \<circ> f"
  have f: "f x = (?g x, ?h x)" for x
    by auto
  show ?thesis
  proof (cases "(\<forall>x \<in> topspace Z. ?g x \<in> topspace X) \<and> (\<forall>x \<in> topspace Z. ?h x \<in> topspace Y)")
    case True
    show ?thesis
    proof safe
      assume "continuous_map Z (prod_topology X Y) f"
      then have "openin Z {x \<in> topspace Z. fst (f x) \<in> U}" if "openin X U" for U
        unfolding continuous_map_def using True that
        apply clarify
        apply (drule_tac x="U \<times> topspace Y" in spec)
        by (simp add: openin_Times mem_Times_iff cong: conj_cong)
      with True show "continuous_map Z X (fst \<circ> f)"
        by (auto simp: continuous_map_def)
    next
      assume "continuous_map Z (prod_topology X Y) f"
      then have "openin Z {x \<in> topspace Z. snd (f x) \<in> V}" if "openin Y V" for V
        unfolding continuous_map_def using True that
        apply clarify
        apply (drule_tac x="topspace X \<times> V" in spec)
        by (simp add: openin_Times mem_Times_iff cong: conj_cong)
      with True show "continuous_map Z Y (snd \<circ> f)"
        by (auto simp: continuous_map_def)
    next
      assume Z: "continuous_map Z X (fst \<circ> f)" "continuous_map Z Y (snd \<circ> f)"
      have *: "openin Z {x \<in> topspace Z. f x \<in> W}"
        if "\<And>w. w \<in> W \<Longrightarrow> \<exists>U V. openin X U \<and> openin Y V \<and> w \<in> U \<times> V \<and> U \<times> V \<subseteq> W" for W
      proof (subst openin_subopen, clarify)
        fix x :: "'a"
        assume "x \<in> topspace Z" and "f x \<in> W"
        with that [OF \<open>f x \<in> W\<close>]
        obtain U V where UV: "openin X U" "openin Y V" "f x \<in> U \<times> V" "U \<times> V \<subseteq> W"
          by auto
        with Z  UV show "\<exists>T. openin Z T \<and> x \<in> T \<and> T \<subseteq> {x \<in> topspace Z. f x \<in> W}"
          apply (rule_tac x="{x \<in> topspace Z. ?g x \<in> U} \<inter> {x \<in> topspace Z. ?h x \<in> V}" in exI)
          apply (auto simp: \<open>x \<in> topspace Z\<close> continuous_map_def)
          done
      qed
      show "continuous_map Z (prod_topology X Y) f"
        using True by (simp add: continuous_map_def openin_prod_topology_alt mem_Times_iff *)
    qed
  qed (auto simp: continuous_map_def)
qed

lemma continuous_map_paired:
   "continuous_map Z (prod_topology X Y) (\<lambda>x. (f x,g x)) \<longleftrightarrow> continuous_map Z X f \<and> continuous_map Z Y g"
  by (simp add: continuous_map_pairwise o_def)

lemma continuous_map_pairedI [continuous_intros]:
   "\<lbrakk>continuous_map Z X f; continuous_map Z Y g\<rbrakk> \<Longrightarrow> continuous_map Z (prod_topology X Y) (\<lambda>x. (f x,g x))"
  by (simp add: continuous_map_pairwise o_def)

lemma continuous_map_fst [continuous_intros]: "continuous_map (prod_topology X Y) X fst"
  using continuous_map_pairwise [of "prod_topology X Y" X Y id]
  by (simp add: continuous_map_pairwise)

lemma continuous_map_snd [continuous_intros]: "continuous_map (prod_topology X Y) Y snd"
  using continuous_map_pairwise [of "prod_topology X Y" X Y id]
  by (simp add: continuous_map_pairwise)

lemma continuous_map_fst_of [continuous_intros]:
   "continuous_map Z (prod_topology X Y) f \<Longrightarrow> continuous_map Z X (fst \<circ> f)"
  by (simp add: continuous_map_pairwise)

lemma continuous_map_snd_of [continuous_intros]:
   "continuous_map Z (prod_topology X Y) f \<Longrightarrow> continuous_map Z Y (snd \<circ> f)"
  by (simp add: continuous_map_pairwise)

lemma continuous_map_if_iff [simp]: "continuous_map X Y (\<lambda>x. if P then f x else g x) \<longleftrightarrow> continuous_map X Y (if P then f else g)"
  by simp

lemma continuous_map_if [continuous_intros]: "\<lbrakk>P \<Longrightarrow> continuous_map X Y f; ~P \<Longrightarrow> continuous_map X Y g\<rbrakk>
      \<Longrightarrow> continuous_map X Y (\<lambda>x. if P then f x else g x)"
  by simp

lemma continuous_map_subtopology_fst [continuous_intros]: "continuous_map (subtopology (prod_topology X Y) Z) X fst"
      using continuous_map_from_subtopology continuous_map_fst by force

lemma continuous_map_subtopology_snd [continuous_intros]: "continuous_map (subtopology (prod_topology X Y) Z) Y snd"
      using continuous_map_from_subtopology continuous_map_snd by force

lemma quotient_map_fst [simp]:
   "quotient_map(prod_topology X Y) X fst \<longleftrightarrow> (topspace Y = {} \<longrightarrow> topspace X = {})"
  by (auto simp: continuous_open_quotient_map open_map_fst continuous_map_fst)

lemma quotient_map_snd [simp]:
   "quotient_map(prod_topology X Y) Y snd \<longleftrightarrow> (topspace X = {} \<longrightarrow> topspace Y = {})"
  by (auto simp: continuous_open_quotient_map open_map_snd continuous_map_snd)

lemma retraction_map_fst:
   "retraction_map (prod_topology X Y) X fst \<longleftrightarrow> (topspace Y = {} \<longrightarrow> topspace X = {})"
proof (cases "topspace Y = {}")
  case True
  then show ?thesis
    using continuous_map_image_subset_topspace
    by (fastforce simp: retraction_map_def retraction_maps_def continuous_map_fst continuous_map_on_empty)
next
  case False
  have "\<exists>g. continuous_map X (prod_topology X Y) g \<and> (\<forall>x\<in>topspace X. fst (g x) = x)"
    if y: "y \<in> topspace Y" for y
    by (rule_tac x="\<lambda>x. (x,y)" in exI) (auto simp: y continuous_map_paired)
  with False have "retraction_map (prod_topology X Y) X fst"
    by (fastforce simp: retraction_map_def retraction_maps_def continuous_map_fst)
  with False show ?thesis
    by simp
qed

lemma retraction_map_snd:
   "retraction_map (prod_topology X Y) Y snd \<longleftrightarrow> (topspace X = {} \<longrightarrow> topspace Y = {})"
proof (cases "topspace X = {}")
  case True
  then show ?thesis
    using continuous_map_image_subset_topspace
    by (fastforce simp: retraction_map_def retraction_maps_def continuous_map_fst continuous_map_on_empty)
next
  case False
  have "\<exists>g. continuous_map Y (prod_topology X Y) g \<and> (\<forall>y\<in>topspace Y. snd (g y) = y)"
    if x: "x \<in> topspace X" for x
    by (rule_tac x="\<lambda>y. (x,y)" in exI) (auto simp: x continuous_map_paired)
  with False have "retraction_map (prod_topology X Y) Y snd"
    by (fastforce simp: retraction_map_def retraction_maps_def continuous_map_snd)
  with False show ?thesis
    by simp
qed


lemma continuous_map_of_fst:
   "continuous_map (prod_topology X Y) Z (f \<circ> fst) \<longleftrightarrow> topspace Y = {} \<or> continuous_map X Z f"
proof (cases "topspace Y = {}")
  case True
  then show ?thesis
    by (simp add: continuous_map_on_empty)
next
  case False
  then show ?thesis
    by (simp add: continuous_compose_quotient_map_eq quotient_map_fst)
qed

lemma continuous_map_of_snd:
   "continuous_map (prod_topology X Y) Z (f \<circ> snd) \<longleftrightarrow> topspace X = {} \<or> continuous_map Y Z f"
proof (cases "topspace X = {}")
  case True
  then show ?thesis
    by (simp add: continuous_map_on_empty)
next
  case False
  then show ?thesis
    by (simp add: continuous_compose_quotient_map_eq quotient_map_snd)
qed

lemma continuous_map_prod_top:
   "continuous_map (prod_topology X Y) (prod_topology X' Y') (\<lambda>(x,y). (f x, g y)) \<longleftrightarrow>
    topspace (prod_topology X Y) = {} \<or> continuous_map X X' f \<and> continuous_map Y Y' g"
proof (cases "topspace (prod_topology X Y) = {}")
  case True
  then show ?thesis
    by (simp add: continuous_map_on_empty)
next
  case False
  then show ?thesis
    by (simp add: continuous_map_paired case_prod_unfold continuous_map_of_fst [unfolded o_def] continuous_map_of_snd [unfolded o_def])
qed

lemma in_prod_topology_closure_of:
  assumes  "z \<in> (prod_topology X Y) closure_of S"
  shows "fst z \<in> X closure_of (fst ` S)" "snd z \<in> Y closure_of (snd ` S)"
  using assms continuous_map_eq_image_closure_subset continuous_map_fst apply fastforce
  using assms continuous_map_eq_image_closure_subset continuous_map_snd apply fastforce
  done


proposition compact_space_prod_topology:
   "compact_space(prod_topology X Y) \<longleftrightarrow> topspace(prod_topology X Y) = {} \<or> compact_space X \<and> compact_space Y"
proof (cases "topspace(prod_topology X Y) = {}")
  case True
  then show ?thesis
    using compact_space_topspace_empty by blast
next
  case False
  then have non_mt: "topspace X \<noteq> {}" "topspace Y \<noteq> {}"
    by auto
  have "compact_space X" "compact_space Y" if "compact_space(prod_topology X Y)"
  proof -
    have "compactin X (fst ` (topspace X \<times> topspace Y))"
      by (metis compact_space_def continuous_map_fst image_compactin that topspace_prod_topology)
    moreover
    have "compactin Y (snd ` (topspace X \<times> topspace Y))"
      by (metis compact_space_def continuous_map_snd image_compactin that topspace_prod_topology)
    ultimately show "compact_space X" "compact_space Y"
      by (simp_all add: non_mt compact_space_def)
  qed
  moreover
  define \<X> where "\<X> \<equiv> (\<lambda>V. topspace X \<times> V) ` Collect (openin Y)"
  define \<Y> where "\<Y> \<equiv> (\<lambda>U. U \<times> topspace Y) ` Collect (openin X)"
  have "compact_space(prod_topology X Y)" if "compact_space X" "compact_space Y"
  proof (rule Alexander_subbase_alt)
    show toptop: "topspace X \<times> topspace Y \<subseteq> \<Union>(\<X> \<union> \<Y>)"
      unfolding \<X>_def \<Y>_def by auto
    fix \<C> :: "('a \<times> 'b) set set"
    assume \<C>: "\<C> \<subseteq> \<X> \<union> \<Y>" "topspace X \<times> topspace Y \<subseteq> \<Union>\<C>"
    then obtain \<X>' \<Y>' where XY: "\<X>' \<subseteq> \<X>" "\<Y>' \<subseteq> \<Y>" and \<C>eq: "\<C> = \<X>' \<union> \<Y>'"
      using subset_UnE by metis
    then have sub: "topspace X \<times> topspace Y \<subseteq> \<Union>(\<X>' \<union> \<Y>')"
      using \<C> by simp
    obtain \<U> \<V> where \<U>: "\<And>U. U \<in> \<U> \<Longrightarrow> openin X U" "\<Y>' = (\<lambda>U. U \<times> topspace Y) ` \<U>"
      and \<V>: "\<And>V. V \<in> \<V> \<Longrightarrow> openin Y V" "\<X>' = (\<lambda>V. topspace X \<times> V) ` \<V>"
      using XY by (clarsimp simp add: \<X>_def \<Y>_def subset_image_iff) (force simp add: subset_iff)
    have "\<exists>\<D>. finite \<D> \<and> \<D> \<subseteq> \<X>' \<union> \<Y>' \<and> topspace X \<times> topspace Y \<subseteq> \<Union> \<D>"
    proof -
      have "topspace X \<subseteq> \<Union>\<U> \<or> topspace Y \<subseteq> \<Union>\<V>"
        using \<U> \<V> \<C> \<C>eq by auto
      then have *: "\<exists>\<D>. finite \<D> \<and>
               (\<forall>x \<in> \<D>. x \<in> (\<lambda>V. topspace X \<times> V) ` \<V> \<or> x \<in> (\<lambda>U. U \<times> topspace Y) ` \<U>) \<and>
               (topspace X \<times> topspace Y \<subseteq> \<Union>\<D>)"
      proof
        assume "topspace X \<subseteq> \<Union>\<U>"
        with \<open>compact_space X\<close> \<U> obtain \<F> where "finite \<F>" "\<F> \<subseteq> \<U>" "topspace X \<subseteq> \<Union>\<F>"
          by (meson compact_space_alt)
        with that show ?thesis
          by (rule_tac x="(\<lambda>D. D \<times> topspace Y) ` \<F>" in exI) auto
      next
        assume "topspace Y \<subseteq> \<Union>\<V>"
        with \<open>compact_space Y\<close> \<V> obtain \<F> where "finite \<F>" "\<F> \<subseteq> \<V>" "topspace Y \<subseteq> \<Union>\<F>"
          by (meson compact_space_alt)
        with that show ?thesis
          by (rule_tac x="(\<lambda>C. topspace X \<times> C) ` \<F>" in exI) auto
      qed
      then show ?thesis
        using that \<U> \<V> by blast
    qed
    then show "\<exists>\<D>. finite \<D> \<and> \<D> \<subseteq> \<C> \<and> topspace X \<times> topspace Y \<subseteq> \<Union> \<D>"
      using \<C> \<C>eq by blast
  next
    have "(finite intersection_of (\<lambda>x. x \<in> \<X> \<or> x \<in> \<Y>) relative_to topspace X \<times> topspace Y)
           = (\<lambda>U. \<exists>S T. U = S \<times> T \<and> openin X S \<and> openin Y T)"
      (is "?lhs = ?rhs")
    proof -
      have "?rhs U" if "?lhs U" for U
      proof -
        have "topspace X \<times> topspace Y \<inter> \<Inter> T \<in> {A \<times> B |A B. A \<in> Collect (openin X) \<and> B \<in> Collect (openin Y)}"
          if "finite T" "T \<subseteq> \<X> \<union> \<Y>" for T
          using that
        proof induction
          case (insert B \<B>)
          then show ?case
            unfolding \<X>_def \<Y>_def
            apply (simp add: Int_ac subset_eq image_def)
            apply (metis (no_types) openin_Int openin_topspace Times_Int_Times)
            done
        qed auto
        then show ?thesis
          using that
          by (auto simp: subset_eq  elim!: relative_toE intersection_ofE)
      qed
      moreover
      have "?lhs Z" if Z: "?rhs Z" for Z
      proof -
        obtain U V where "Z = U \<times> V" "openin X U" "openin Y V"
          using Z by blast
        then have UV: "U \<times> V = (topspace X \<times> topspace Y) \<inter> (U \<times> V)"
          by (simp add: Sigma_mono inf_absorb2 openin_subset)
        moreover
        have "?lhs ((topspace X \<times> topspace Y) \<inter> (U \<times> V))"
        proof (rule relative_to_inc)
          show "(finite intersection_of (\<lambda>x. x \<in> \<X> \<or> x \<in> \<Y>)) (U \<times> V)"
            apply (simp add: intersection_of_def \<X>_def \<Y>_def)
            apply (rule_tac x="{(U \<times> topspace Y),(topspace X \<times> V)}" in exI)
            using \<open>openin X U\<close> \<open>openin Y V\<close> openin_subset UV apply (fastforce simp add:)
            done
        qed
        ultimately show ?thesis
          using \<open>Z = U \<times> V\<close> by auto
      qed
      ultimately show ?thesis
        by meson
    qed
    then show "topology (arbitrary union_of (finite intersection_of (\<lambda>x. x \<in> \<X> \<union> \<Y>)
           relative_to (topspace X \<times> topspace Y))) =
        prod_topology X Y"
      by (simp add: prod_topology_def)
  qed
  ultimately show ?thesis
    using False by blast
qed

lemma compactin_Times:
   "compactin (prod_topology X Y) (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> compactin X S \<and> compactin Y T"
  by (auto simp: compactin_subspace subtopology_Times compact_space_prod_topology)

subsection\<open>Homeomorphic maps\<close>

lemma homeomorphic_maps_prod:
   "homeomorphic_maps (prod_topology X Y) (prod_topology X' Y') (\<lambda>(x,y). (f x, g y)) (\<lambda>(x,y). (f' x, g' y)) \<longleftrightarrow>
        topspace(prod_topology X Y) = {} \<and>
        topspace(prod_topology X' Y') = {} \<or>
        homeomorphic_maps X X' f f' \<and>
        homeomorphic_maps Y Y' g g'"
  unfolding homeomorphic_maps_def continuous_map_prod_top
  by (auto simp: continuous_map_def homeomorphic_maps_def continuous_map_prod_top)

lemma embedding_map_graph:
   "embedding_map X (prod_topology X Y) (\<lambda>x. (x, f x)) \<longleftrightarrow> continuous_map X Y f"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have "snd \<circ> (\<lambda>x. (x, f x)) = f"
    by force
  moreover have "continuous_map X Y (snd \<circ> (\<lambda>x. (x, f x)))"
    using L
    unfolding embedding_map_def
    by (meson continuous_map_in_subtopology continuous_map_snd_of homeomorphic_imp_continuous_map)
  ultimately show ?rhs
    by simp
next
  assume R: ?rhs
  then show ?lhs
    unfolding homeomorphic_map_maps embedding_map_def homeomorphic_maps_def
    by (rule_tac x=fst in exI)
       (auto simp: continuous_map_in_subtopology continuous_map_paired continuous_map_from_subtopology
                   continuous_map_fst topspace_subtopology)
qed

lemma homeomorphic_space_prod_topology:
   "\<lbrakk>X homeomorphic_space X''; Y homeomorphic_space Y'\<rbrakk>
        \<Longrightarrow> prod_topology X Y homeomorphic_space prod_topology X'' Y'"
using homeomorphic_maps_prod unfolding homeomorphic_space_def by blast

lemma prod_topology_homeomorphic_space_left:
   "topspace Y = {b} \<Longrightarrow> prod_topology X Y homeomorphic_space X"
  unfolding homeomorphic_space_def
  by (rule_tac x=fst in exI) (simp add: homeomorphic_map_def inj_on_def flip: homeomorphic_map_maps)

lemma prod_topology_homeomorphic_space_right:
   "topspace X = {a} \<Longrightarrow> prod_topology X Y homeomorphic_space Y"
  unfolding homeomorphic_space_def
  by (rule_tac x=snd in exI) (simp add: homeomorphic_map_def inj_on_def flip: homeomorphic_map_maps)


lemma homeomorphic_space_prod_topology_sing1:
     "b \<in> topspace Y \<Longrightarrow> X homeomorphic_space (prod_topology X (subtopology Y {b}))"
  by (metis empty_subsetI homeomorphic_space_sym inf.absorb_iff2 insert_subset prod_topology_homeomorphic_space_left topspace_subtopology)

lemma homeomorphic_space_prod_topology_sing2:
     "a \<in> topspace X \<Longrightarrow> Y homeomorphic_space (prod_topology (subtopology X {a}) Y)"
  by (metis empty_subsetI homeomorphic_space_sym inf.absorb_iff2 insert_subset prod_topology_homeomorphic_space_right topspace_subtopology)

lemma topological_property_of_prod_component:
  assumes major: "P(prod_topology X Y)"
    and X: "\<And>x. \<lbrakk>x \<in> topspace X; P(prod_topology X Y)\<rbrakk> \<Longrightarrow> P(subtopology (prod_topology X Y) ({x} \<times> topspace Y))"
    and Y: "\<And>y. \<lbrakk>y \<in> topspace Y; P(prod_topology X Y)\<rbrakk> \<Longrightarrow> P(subtopology (prod_topology X Y) (topspace X \<times> {y}))"
    and PQ:  "\<And>X X'. X homeomorphic_space X' \<Longrightarrow> (P X \<longleftrightarrow> Q X')"
    and PR: "\<And>X X'. X homeomorphic_space X' \<Longrightarrow> (P X \<longleftrightarrow> R X')"
  shows "topspace(prod_topology X Y) = {} \<or> Q X \<and> R Y"
proof -
  have "Q X \<and> R Y" if "topspace(prod_topology X Y) \<noteq> {}"
  proof -
    from that obtain a b where a: "a \<in> topspace X" and b: "b \<in> topspace Y"
      by force
    show ?thesis
      using X [OF a major] and Y [OF b major] homeomorphic_space_prod_topology_sing1 [OF b, of X] homeomorphic_space_prod_topology_sing2 [OF a, of Y]
      by (simp add: subtopology_Times) (meson PQ PR homeomorphic_space_prod_topology_sing2 homeomorphic_space_sym)
  qed
  then show ?thesis by metis
qed

lemma limitin_pairwise:
   "limitin (prod_topology X Y) f l F \<longleftrightarrow> limitin X (fst \<circ> f) (fst l) F \<and> limitin Y (snd \<circ> f) (snd l) F"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain a b where ev: "\<And>U. \<lbrakk>(a,b) \<in> U; openin (prod_topology X Y) U\<rbrakk> \<Longrightarrow> \<forall>\<^sub>F x in F. f x \<in> U"
                        and a: "a \<in> topspace X" and b: "b \<in> topspace Y" and l: "l = (a,b)"
    by (auto simp: limitin_def)
  moreover have "\<forall>\<^sub>F x in F. fst (f x) \<in> U" if "openin X U" "a \<in> U" for U
  proof -
    have "\<forall>\<^sub>F c in F. f c \<in> U \<times> topspace Y"
      using b that ev [of "U \<times> topspace Y"] by (auto simp: openin_prod_topology_alt)
    then show ?thesis
      by (rule eventually_mono) (metis (mono_tags, lifting) SigmaE2 prod.collapse)
  qed
  moreover have "\<forall>\<^sub>F x in F. snd (f x) \<in> U" if "openin Y U" "b \<in> U" for U
  proof -
    have "\<forall>\<^sub>F c in F. f c \<in> topspace X \<times> U"
      using a that ev [of "topspace X \<times> U"] by (auto simp: openin_prod_topology_alt)
    then show ?thesis
      by (rule eventually_mono) (metis (mono_tags, lifting) SigmaE2 prod.collapse)
  qed
  ultimately show ?rhs
    by (simp add: limitin_def)
next
  have "limitin (prod_topology X Y) f (a,b) F"
    if "limitin X (fst \<circ> f) a F" "limitin Y (snd \<circ> f) b F" for a b
    using that
  proof (clarsimp simp: limitin_def)
    fix Z :: "('a \<times> 'b) set"
    assume a: "a \<in> topspace X" "\<forall>U. openin X U \<and> a \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. fst (f x) \<in> U)"
      and b: "b \<in> topspace Y" "\<forall>U. openin Y U \<and> b \<in> U \<longrightarrow> (\<forall>\<^sub>F x in F. snd (f x) \<in> U)"
      and Z: "openin (prod_topology X Y) Z" "(a, b) \<in> Z"
    then obtain U V where "openin X U" "openin Y V" "a \<in> U" "b \<in> V" "U \<times> V \<subseteq> Z"
      using Z by (force simp: openin_prod_topology_alt)
    then have "\<forall>\<^sub>F x in F. fst (f x) \<in> U" "\<forall>\<^sub>F x in F. snd (f x) \<in> V"
      by (simp_all add: a b)
    then show "\<forall>\<^sub>F x in F. f x \<in> Z"
      by (rule eventually_elim2) (use \<open>U \<times> V \<subseteq> Z\<close> subsetD in auto)
  qed
  then show "?rhs \<Longrightarrow> ?lhs"
    by (metis prod.collapse)
qed

end

