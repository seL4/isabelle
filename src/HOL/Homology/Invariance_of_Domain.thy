section\<open>Invariance of Domain\<close>

theory Invariance_of_Domain
  imports Brouwer_Degree "HOL-Analysis.Continuous_Extension" "HOL-Analysis.Homeomorphism"

begin

subsection\<open>Degree invariance mod 2 for map between pairs\<close>

theorem Borsuk_odd_mapping_degree_step:
  assumes cmf: "continuous_map (nsphere n) (nsphere n) f"
    and f: "\<And>x. x \<in> topspace(nsphere n) \<Longrightarrow> (f \<circ> (\<lambda>x i. -x i)) x = ((\<lambda>x i. -x i) \<circ> f) x"
    and fim: "f ` (topspace(nsphere(n - Suc 0))) \<subseteq> topspace(nsphere(n - Suc 0))"
  shows "even (Brouwer_degree2 n f - Brouwer_degree2 (n - Suc 0) f)"
proof (cases "n = 0")
  case False
  define neg where "neg \<equiv> \<lambda>x::nat\<Rightarrow>real. \<lambda>i. -x i"
  define upper where "upper \<equiv> \<lambda>n. {x::nat\<Rightarrow>real. x n \<ge> 0}"
  define lower where "lower \<equiv> \<lambda>n. {x::nat\<Rightarrow>real. x n \<le> 0}"
  define equator where "equator \<equiv> \<lambda>n. {x::nat\<Rightarrow>real. x n = 0}"
  define usphere where "usphere \<equiv> \<lambda>n. subtopology (nsphere n) (upper n)"
  define lsphere where "lsphere \<equiv> \<lambda>n. subtopology (nsphere n) (lower n)"
  have [simp]: "neg x i = -x i" for x i
    by (force simp: neg_def)
  have equator_upper: "equator n \<subseteq> upper n"
    by (force simp: equator_def upper_def)
  have upper_usphere: "subtopology (nsphere n) (upper n) = usphere n"
    by (simp add: usphere_def)
  let ?rhgn = "relative_homology_group n (nsphere n)"
  let ?hi_ee = "hom_induced n (nsphere n) (equator n) (nsphere n) (equator n)"
  interpret GE: comm_group "?rhgn (equator n)"
    by simp
  interpret HB: group_hom "?rhgn (equator n)"
                          "homology_group (int n - 1) (subtopology (nsphere n) (equator n))"
                          "hom_boundary n (nsphere n) (equator n)"
    by (simp add: group_hom_axioms_def group_hom_def hom_boundary_hom)
  interpret HIU: group_hom "?rhgn (equator n)"
                           "?rhgn (upper n)"
                           "hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id"
    by (simp add: group_hom_axioms_def group_hom_def hom_induced_hom)
  have subt_eq: "subtopology (nsphere n) {x. x n = 0} = nsphere (n - Suc 0)"
    by (metis False Suc_pred le_zero_eq not_le subtopology_nsphere_equator)
  then have equ: "subtopology (nsphere n) (equator n) = nsphere(n - Suc 0)"
    "subtopology (lsphere n) (equator n) = nsphere(n - Suc 0)"
    "subtopology (usphere n) (equator n) = nsphere(n - Suc 0)"
    using False by (auto simp: lsphere_def usphere_def equator_def lower_def upper_def subtopology_subtopology simp flip: Collect_conj_eq cong: rev_conj_cong)
  have cmr: "continuous_map (nsphere(n - Suc 0)) (nsphere(n - Suc 0)) f"
    by (metis (no_types, lifting) IntE cmf fim continuous_map_from_subtopology continuous_map_in_subtopology equ(1) image_subset_iff topspace_subtopology)

  have "f x n = 0" if "x \<in> topspace (nsphere n)" "x n = 0" for x
  proof -
    have "x \<in> topspace (nsphere (n - Suc 0))"
      by (simp add: that topspace_nsphere_minus1)
    moreover have "topspace (nsphere n) \<inter> {f. f n = 0} = topspace (nsphere (n - Suc 0))"
      by (metis subt_eq topspace_subtopology)
    ultimately show ?thesis
      using cmr continuous_map_def by fastforce
  qed
  then have fimeq: "f ` (topspace (nsphere n) \<inter> equator n) \<subseteq> topspace (nsphere n) \<inter> equator n"
    using fim cmf by (auto simp: equator_def continuous_map_def image_subset_iff)
  have "\<And>k. continuous_map (powertop_real UNIV) euclideanreal (\<lambda>x. - x k)"
    by (metis UNIV_I continuous_map_product_projection continuous_map_minus)
  then have cm_neg: "continuous_map (nsphere m) (nsphere m) neg" for m
    by (force simp: nsphere continuous_map_in_subtopology neg_def continuous_map_componentwise_UNIV intro: continuous_map_from_subtopology)
  then have cm_neg_lu: "continuous_map (lsphere n) (usphere n) neg"
      by (auto simp: lsphere_def usphere_def lower_def upper_def continuous_map_from_subtopology continuous_map_in_subtopology)
  have neg_in_top_iff: "neg x \<in> topspace(nsphere m) \<longleftrightarrow> x \<in> topspace(nsphere m)" for m x
    by (simp add: nsphere_def neg_def topspace_Euclidean_space)
  obtain z where zcarr: "z \<in> carrier (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))"
    and zeq: "subgroup_generated (reduced_homology_group (int n - 1) (nsphere (n - Suc 0))) {z}
              = reduced_homology_group (int n - 1) (nsphere (n - Suc 0))"
    using cyclic_reduced_homology_group_nsphere [of "int n - 1" "n - Suc 0"] by (auto simp: cyclic_group_def)
  have "hom_boundary n (subtopology (nsphere n) {x. x n \<le> 0}) {x. x n = 0}
      \<in> Group.iso (relative_homology_group n
                     (subtopology (nsphere n) {x. x n \<le> 0}) {x. x n = 0})
                  (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))"
    using iso_lower_hemisphere_reduced_homology_group [of "int n - 1" "n - Suc 0"] False by simp
  then obtain gp where g: "group_isomorphisms
                          (relative_homology_group n (subtopology (nsphere n) {x. x n \<le> 0}) {x. x n = 0})
                          (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))
                          (hom_boundary n (subtopology (nsphere n) {x. x n \<le> 0}) {x. x n = 0})
                          gp"
    by (auto simp: group.iso_iff_group_isomorphisms)
  then interpret gp: group_hom "reduced_homology_group (int n - 1) (nsphere (n - Suc 0))"
    "relative_homology_group n (subtopology (nsphere n) {x. x n \<le> 0}) {x. x n = 0}" gp
    by (simp add: group_hom_axioms_def group_hom_def group_isomorphisms_def)
  obtain zp where zpcarr: "zp \<in> carrier(relative_homology_group n (lsphere n) (equator n))"
    and zp_z: "hom_boundary n (lsphere n) (equator n) zp = z"
    and zp_sg: "subgroup_generated (relative_homology_group n (lsphere n) (equator n)) {zp}
                = relative_homology_group n (lsphere n) (equator n)"
  proof
    show "gp z \<in> carrier (relative_homology_group n (lsphere n) (equator n))"
      "hom_boundary n (lsphere n) (equator n) (gp z) = z"
      using g zcarr by (auto simp: lsphere_def equator_def lower_def group_isomorphisms_def)
    have giso: "gp \<in> Group.iso (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))
                     (relative_homology_group n (subtopology (nsphere n) {x. x n \<le> 0}) {x. x n = 0})"
      by (metis (mono_tags, lifting) g group_isomorphisms_imp_iso group_isomorphisms_sym)
    show "subgroup_generated (relative_homology_group n (lsphere n) (equator n)) {gp z} =
        relative_homology_group n (lsphere n) (equator n)"
      apply (rule monoid.equality)
      using giso gp.subgroup_generated_by_image [of "{z}"] zcarr
      by (auto simp: lsphere_def equator_def lower_def zeq gp.iso_iff)
  qed
  have hb_iso: "hom_boundary n (subtopology (nsphere n) {x. x n \<ge> 0}) {x. x n = 0}
            \<in> iso (relative_homology_group n (subtopology (nsphere n) {x. x n \<ge> 0}) {x. x n = 0})
                  (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))"
    using iso_upper_hemisphere_reduced_homology_group [of "int n - 1" "n - Suc 0"] False by simp
  then obtain gn where g: "group_isomorphisms
                          (relative_homology_group n (subtopology (nsphere n) {x. x n \<ge> 0}) {x. x n = 0})
                          (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))
                          (hom_boundary n (subtopology (nsphere n) {x. x n \<ge> 0}) {x. x n = 0})
                          gn"
    by (auto simp: group.iso_iff_group_isomorphisms)
  then interpret gn: group_hom "reduced_homology_group (int n - 1) (nsphere (n - Suc 0))"
    "relative_homology_group n (subtopology (nsphere n) {x. x n \<ge> 0}) {x. x n = 0}" gn
    by (simp add: group_hom_axioms_def group_hom_def group_isomorphisms_def)
  obtain zn where zncarr: "zn \<in> carrier(relative_homology_group n (usphere n) (equator n))"
    and zn_z: "hom_boundary n (usphere n) (equator n) zn = z"
    and zn_sg: "subgroup_generated (relative_homology_group n (usphere n) (equator n)) {zn}
                 = relative_homology_group n (usphere n) (equator n)"
  proof
    show "gn z \<in> carrier (relative_homology_group n (usphere n) (equator n))"
      "hom_boundary n (usphere n) (equator n) (gn z) = z"
      using g zcarr by (auto simp: usphere_def equator_def upper_def group_isomorphisms_def)
    have giso: "gn \<in> Group.iso (reduced_homology_group (int n - 1) (nsphere (n - Suc 0)))
                     (relative_homology_group n (subtopology (nsphere n) {x. x n \<ge> 0}) {x. x n = 0})"
      by (metis (mono_tags, lifting) g group_isomorphisms_imp_iso group_isomorphisms_sym)
    show "subgroup_generated (relative_homology_group n (usphere n) (equator n)) {gn z} =
        relative_homology_group n (usphere n) (equator n)"
      apply (rule monoid.equality)
      using giso gn.subgroup_generated_by_image [of "{z}"] zcarr
      by (auto simp: usphere_def equator_def upper_def zeq gn.iso_iff)
  qed
  let ?hi_lu = "hom_induced n (lsphere n) (equator n) (nsphere n) (upper n) id"
  interpret gh_lu: group_hom "relative_homology_group n (lsphere n) (equator n)" "?rhgn (upper n)" ?hi_lu
    by (simp add: group_hom_axioms_def group_hom_def hom_induced_hom)
  interpret gh_eef: group_hom "?rhgn (equator n)" "?rhgn (equator n)" "?hi_ee f"
    by (simp add: group_hom_axioms_def group_hom_def hom_induced_hom)
  define wp where "wp \<equiv> ?hi_lu zp"
  then have wpcarr: "wp \<in> carrier(?rhgn (upper n))"
    by (simp add: hom_induced_carrier)
  have "hom_induced n (nsphere n) {} (nsphere n) {x. x n \<ge> 0} id
      \<in> iso (reduced_homology_group n (nsphere n))
            (?rhgn {x. x n \<ge> 0})"
    using iso_reduced_homology_group_upper_hemisphere [of n n n] by auto
  then have "carrier(?rhgn {x. x n \<ge> 0})
          \<subseteq> (hom_induced n (nsphere n) {} (nsphere n) {x. x n \<ge> 0} id)
                         ` carrier(reduced_homology_group n (nsphere n))"
    by (simp add: iso_iff)
  then obtain vp where vpcarr: "vp \<in> carrier(reduced_homology_group n (nsphere n))"
    and eqwp: "hom_induced n (nsphere n) {} (nsphere n) (upper n) id vp = wp"
    using wpcarr by (auto simp: upper_def)
  define wn where "wn \<equiv> hom_induced n (usphere n) (equator n) (nsphere n) (lower n) id zn"
  then have wncarr: "wn \<in> carrier(?rhgn (lower n))"
    by (simp add: hom_induced_carrier)
  have "hom_induced n (nsphere n) {} (nsphere n) {x. x n \<le> 0} id
      \<in> iso (reduced_homology_group n (nsphere n))
            (?rhgn {x. x n \<le> 0})"
    using iso_reduced_homology_group_lower_hemisphere [of n n n] by auto
  then have "carrier(?rhgn {x. x n \<le> 0})
          \<subseteq> (hom_induced n (nsphere n) {} (nsphere n) {x. x n \<le> 0} id)
                         ` carrier(reduced_homology_group n (nsphere n))"
    by (simp add: iso_iff)
  then obtain vn where vpcarr: "vn \<in> carrier(reduced_homology_group n (nsphere n))"
    and eqwp: "hom_induced n (nsphere n) {} (nsphere n) (lower n) id vn = wn"
    using wncarr by (auto simp: lower_def)
  define up where "up \<equiv> hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id zp"
  then have upcarr: "up \<in> carrier(?rhgn (equator n))"
    by (simp add: hom_induced_carrier)
  define un where "un \<equiv> hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id zn"
  then have uncarr: "un \<in> carrier(?rhgn (equator n))"
    by (simp add: hom_induced_carrier)
  have *: "(\<lambda>(x, y).
            hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id x
          \<otimes>\<^bsub>?rhgn (equator n)\<^esub>
            hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id y)
        \<in> Group.iso
            (relative_homology_group n (lsphere n) (equator n) \<times>\<times>
             relative_homology_group n (usphere n) (equator n))
            (?rhgn (equator n))"
  proof (rule conjunct1 [OF exact_sequence_sum_lemma [OF abelian_relative_homology_group]])
    show "hom_induced n (lsphere n) (equator n) (nsphere n) (upper n) id
        \<in> Group.iso (relative_homology_group n (lsphere n) (equator n))
            (?rhgn (upper n))"
      apply (simp add: lsphere_def usphere_def equator_def lower_def upper_def)
      using iso_relative_homology_group_lower_hemisphere by blast
    show "hom_induced n (usphere n) (equator n) (nsphere n) (lower n) id
        \<in> Group.iso (relative_homology_group n (usphere n) (equator n))
            (?rhgn (lower n))"
      apply (simp_all add: lsphere_def usphere_def equator_def lower_def upper_def)
      using iso_relative_homology_group_upper_hemisphere by blast+
    show "exact_seq
         ([?rhgn (lower n),
           ?rhgn (equator n),
           relative_homology_group n (lsphere n) (equator n)],
          [hom_induced n (nsphere n) (equator n) (nsphere n) (lower n) id,
           hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id])"
      unfolding lsphere_def usphere_def equator_def lower_def upper_def
      by (rule homology_exactness_triple_3) force
    show "exact_seq
         ([?rhgn (upper n),
           ?rhgn (equator n),
           relative_homology_group n (usphere n) (equator n)],
          [hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id,
           hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id])"
      unfolding lsphere_def usphere_def equator_def lower_def upper_def
      by (rule homology_exactness_triple_3) force
  next
    fix x
    assume "x \<in> carrier (relative_homology_group n (lsphere n) (equator n))"
    show "hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id
         (hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id x) =
        hom_induced n (lsphere n) (equator n) (nsphere n) (upper n) id x"
      by (simp add: hom_induced_compose' subset_iff lsphere_def usphere_def equator_def lower_def upper_def)
  next
    fix x
    assume "x \<in> carrier (relative_homology_group n (usphere n) (equator n))"
    show "hom_induced n (nsphere n) (equator n) (nsphere n) (lower n) id
         (hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id x) =
        hom_induced n (usphere n) (equator n) (nsphere n) (lower n) id x"
      by (simp add: hom_induced_compose' subset_iff lsphere_def usphere_def equator_def lower_def upper_def)
  qed
  then have sb: "carrier (?rhgn (equator n))
             \<subseteq> (\<lambda>(x, y).
            hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id x
          \<otimes>\<^bsub>?rhgn (equator n)\<^esub>
            hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id y)
               ` carrier (relative_homology_group n (lsphere n) (equator n) \<times>\<times>
             relative_homology_group n (usphere n) (equator n))"
    by (simp add: iso_iff)
  obtain a b::int
    where up_ab: "?hi_ee f up
             = up [^]\<^bsub>?rhgn (equator n)\<^esub> a\<otimes>\<^bsub>?rhgn (equator n)\<^esub> un [^]\<^bsub>?rhgn (equator n)\<^esub> b"
  proof -
    have hiupcarr: "?hi_ee f up \<in> carrier(?rhgn (equator n))"
      by (simp add: hom_induced_carrier)
    obtain u v where u: "u \<in> carrier (relative_homology_group n (lsphere n) (equator n))"
      and v: "v \<in> carrier (relative_homology_group n (usphere n) (equator n))"
      and eq: "?hi_ee f up =
                hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id u
                \<otimes>\<^bsub>?rhgn (equator n)\<^esub>
                hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id v"
      using subsetD [OF sb hiupcarr] by auto
    have "u \<in> carrier (subgroup_generated (relative_homology_group n (lsphere n) (equator n)) {zp})"
      by (simp_all add: u zp_sg)
    then obtain a::int where a: "u = zp [^]\<^bsub>relative_homology_group n (lsphere n) (equator n)\<^esub> a"
      by (metis group.carrier_subgroup_generated_by_singleton group_relative_homology_group rangeE zpcarr)
    have ae: "hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id
            (pow (relative_homology_group n (lsphere n) (equator n)) zp a)
          = pow (?rhgn (equator n)) (hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id zp) a"
      by (meson group_hom.hom_int_pow group_hom_axioms_def group_hom_def group_relative_homology_group hom_induced zpcarr)
    have "v \<in> carrier (subgroup_generated (relative_homology_group n (usphere n) (equator n)) {zn})"
      by (simp_all add: v zn_sg)
    then obtain b::int where b: "v = zn [^]\<^bsub>relative_homology_group n (usphere n) (equator n)\<^esub> b"
      by (metis group.carrier_subgroup_generated_by_singleton group_relative_homology_group rangeE zncarr)
    have be: "hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id
           (zn [^]\<^bsub>relative_homology_group n (usphere n) (equator n)\<^esub> b)
        = hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id
           zn [^]\<^bsub>relative_homology_group n (nsphere n) (equator n)\<^esub> b"
      by (meson group_hom.hom_int_pow group_hom_axioms_def group_hom_def group_relative_homology_group hom_induced zncarr)
    show thesis
    proof
      show "?hi_ee f up
         = up [^]\<^bsub>?rhgn (equator n)\<^esub> a \<otimes>\<^bsub>?rhgn (equator n)\<^esub> un [^]\<^bsub>?rhgn (equator n)\<^esub> b"
        using a ae b be eq local.up_def un_def by auto
    qed
  qed
  have "(hom_boundary n (nsphere n) (equator n)
       \<circ> hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id) zp = z"
    using zp_z equ apply (simp add: lsphere_def naturality_hom_induced)
    by (metis hom_boundary_carrier hom_induced_id)
  then have up_z: "hom_boundary n (nsphere n) (equator n) up = z"
    by (simp add: up_def)
  have "(hom_boundary n (nsphere n) (equator n)
       \<circ> hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id) zn = z"
    using zn_z equ apply (simp add: usphere_def naturality_hom_induced)
    by (metis hom_boundary_carrier hom_induced_id)
  then have un_z: "hom_boundary n (nsphere n) (equator n) un = z"
    by (simp add: un_def)
  have Bd_ab: "Brouwer_degree2 (n - Suc 0) f = a + b"
  proof (rule Brouwer_degree2_unique_generator; use False int_ops in simp_all)
    show "continuous_map (nsphere (n - Suc 0)) (nsphere (n - Suc 0)) f"
      using cmr by auto
    show "subgroup_generated (reduced_homology_group (int n - 1) (nsphere (n - Suc 0))) {z} =
        reduced_homology_group (int n - 1) (nsphere (n - Suc 0))"
      using zeq by blast
    have "(hom_induced (int n - 1) (nsphere (n - Suc 0)) {} (nsphere (n - Suc 0)) {} f
           \<circ> hom_boundary n (nsphere n) (equator n)) up
        = (hom_boundary n (nsphere n) (equator n) \<circ>
           ?hi_ee f) up"
      using naturality_hom_induced [OF cmf fimeq, of n, symmetric]
      by (simp add: subtopology_restrict equ fun_eq_iff)
    also have "\<dots> = hom_boundary n (nsphere n) (equator n)
                       (up [^]\<^bsub>relative_homology_group n (nsphere n) (equator n)\<^esub>
                        a \<otimes>\<^bsub>relative_homology_group n (nsphere n) (equator n)\<^esub>
                        un [^]\<^bsub>relative_homology_group n (nsphere n) (equator n)\<^esub> b)"
      by (simp add: o_def up_ab)
    also have "\<dots> = z [^]\<^bsub>reduced_homology_group (int n - 1) (nsphere (n - Suc 0))\<^esub> (a + b)"
      using zcarr
      apply (simp add: HB.hom_int_pow reduced_homology_group_def group.int_pow_subgroup_generated upcarr uncarr)
      by (metis equ(1) group.int_pow_mult group_relative_homology_group hom_boundary_carrier un_z up_z)
  finally show "hom_induced (int n - 1) (nsphere (n - Suc 0)) {} (nsphere (n - Suc 0)) {} f z =
        z [^]\<^bsub>reduced_homology_group (int n - 1) (nsphere (n - Suc 0))\<^esub> (a + b)"
      by (simp add: up_z)
  qed
  define u where "u \<equiv> up \<otimes>\<^bsub>?rhgn (equator n)\<^esub> inv\<^bsub>?rhgn (equator n)\<^esub> un"
  have ucarr: "u \<in> carrier (?rhgn (equator n))"
    by (simp add: u_def uncarr upcarr)
  then have "u [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 n f = u [^]\<^bsub>?rhgn (equator n)\<^esub> (a - b)
             \<longleftrightarrow> (GE.ord u) dvd a - b - Brouwer_degree2 n f"
    by (simp add: GE.int_pow_eq)
  moreover
  have "GE.ord u = 0"
  proof (clarsimp simp add: GE.ord_eq_0 ucarr)
    fix d :: nat
    assume "0 < d"
      and "u [^]\<^bsub>?rhgn (equator n)\<^esub> d = singular_relboundary_set n (nsphere n) (equator n)"
    then have "hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id u [^]\<^bsub>?rhgn (upper n)\<^esub> d
               = \<one>\<^bsub>?rhgn (upper n)\<^esub>"
      by (metis HIU.hom_one HIU.hom_nat_pow one_relative_homology_group ucarr)
    moreover
    have "?hi_lu
        = hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id \<circ>
          hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id"
      by (simp add: lsphere_def image_subset_iff equator_upper flip: hom_induced_compose)
    then have p: "wp = hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id up"
      by (simp add: local.up_def wp_def)
    have n: "hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id un = \<one>\<^bsub>?rhgn (upper n)\<^esub>"
      using homology_exactness_triple_3 [OF equator_upper, of n "nsphere n"]
      using un_def zncarr by (auto simp: upper_usphere kernel_def)
    have "hom_induced n (nsphere n) (equator n) (nsphere n) (upper n) id u = wp"
      unfolding u_def
      using p n HIU.inv_one HIU.r_one uncarr upcarr by auto
    ultimately have "(wp [^]\<^bsub>?rhgn (upper n)\<^esub> d) = \<one>\<^bsub>?rhgn (upper n)\<^esub>"
      by simp
    moreover have "infinite (carrier (subgroup_generated (?rhgn (upper n)) {wp}))"
    proof -
      have "?rhgn (upper n) \<cong> reduced_homology_group n (nsphere n)"
        unfolding upper_def
        using iso_reduced_homology_group_upper_hemisphere [of n n n]
        by (blast intro: group.iso_sym group_reduced_homology_group is_isoI)
      also have "\<dots> \<cong> integer_group"
        by (simp add: reduced_homology_group_nsphere)
      finally have iso: "?rhgn (upper n) \<cong> integer_group" .
      have "carrier (subgroup_generated (?rhgn (upper n)) {wp}) = carrier (?rhgn (upper n))"
        using gh_lu.subgroup_generated_by_image [of "{zp}"] zpcarr HIU.carrier_subgroup_generated_subset
          gh_lu.iso_iff iso_relative_homology_group_lower_hemisphere zp_sg
        by (auto simp: lower_def lsphere_def upper_def equator_def wp_def)
      then show ?thesis
        using infinite_UNIV_int iso_finite [OF iso] by simp
    qed
    ultimately show False
      using HIU.finite_cyclic_subgroup \<open>0 < d\<close> wpcarr by blast
  qed
  ultimately have iff: "u [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 n f = u [^]\<^bsub>?rhgn (equator n)\<^esub> (a - b)
                   \<longleftrightarrow> Brouwer_degree2 n f = a - b"
    by auto
  have "u [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 n f = ?hi_ee f u"
  proof -
    have ne: "topspace (nsphere n) \<inter> equator n \<noteq> {}"
      by (metis equ(1) nonempty_nsphere topspace_subtopology)
    have eq1: "hom_boundary n (nsphere n) (equator n) u
               = \<one>\<^bsub>reduced_homology_group (int n - 1) (subtopology (nsphere n) (equator n))\<^esub>"
      using one_reduced_homology_group u_def un_z uncarr up_z upcarr by force
    then have uhom: "u \<in> hom_induced n (nsphere n) {} (nsphere n) (equator n) id `
                         carrier (reduced_homology_group (int n) (nsphere n))"
      using homology_exactness_reduced_1 [OF ne, of n] eq1 ucarr by (auto simp: kernel_def)
    then obtain v where vcarr: "v \<in> carrier (reduced_homology_group (int n) (nsphere n))"
                  and ueq: "u = hom_induced n (nsphere n) {} (nsphere n) (equator n) id v"
      by blast
    interpret GH_hi: group_hom "homology_group n (nsphere n)"
                        "?rhgn (equator n)"
                        "hom_induced n (nsphere n) {} (nsphere n) (equator n) id"
      by (simp add: group_hom_axioms_def group_hom_def hom_induced_hom)
    have poweq: "pow (homology_group n (nsphere n)) x i = pow (reduced_homology_group n (nsphere n)) x i"
      for x and i::int
      by (simp add: False un_reduced_homology_group)
    have vcarr': "v \<in> carrier (homology_group n (nsphere n))"
      using carrier_reduced_homology_group_subset vcarr by blast
    have "u [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 n f
          = hom_induced n (nsphere n) {} (nsphere n) (equator n) f v"
      using vcarr vcarr'
      by (simp add: ueq poweq hom_induced_compose' cmf flip: GH_hi.hom_int_pow Brouwer_degree2)
    also have "\<dots> = hom_induced n (nsphere n) (topspace(nsphere n) \<inter> equator n) (nsphere n) (equator n) f
                     (hom_induced n (nsphere n) {} (nsphere n) (topspace(nsphere n) \<inter> equator n) id v)"
      using fimeq by (simp add: hom_induced_compose' cmf)
    also have "\<dots> = ?hi_ee f u"
      by (metis hom_induced inf.left_idem ueq)
    finally show ?thesis .
  qed
  moreover
  interpret gh_een: group_hom "?rhgn (equator n)" "?rhgn (equator n)" "?hi_ee neg"
    by (simp add: group_hom_axioms_def group_hom_def hom_induced_hom)
  have hi_up_eq_un: "?hi_ee neg up = un [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - Suc 0) neg"
  proof -
    have "?hi_ee neg (hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) id zp)
         = hom_induced n (lsphere n) (equator n) (nsphere n) (equator n) (neg \<circ> id) zp"
      by (intro hom_induced_compose') (auto simp: lsphere_def equator_def cm_neg)
    also have "\<dots> = hom_induced n (usphere n) (equator n) (nsphere n) (equator n) id
            (hom_induced n (lsphere n) (equator n) (usphere n) (equator n) neg zp)"
      by (subst hom_induced_compose' [OF cm_neg_lu]) (auto simp: usphere_def equator_def)
    also have "hom_induced n (lsphere n) (equator n) (usphere n) (equator n) neg zp
             = zn [^]\<^bsub>relative_homology_group n (usphere n) (equator n)\<^esub> Brouwer_degree2 (n - Suc 0) neg"
    proof -
      let ?hb = "hom_boundary n (usphere n) (equator n)"
      have eq: "subtopology (nsphere n) {x. x n \<ge> 0} = usphere n \<and> {x. x n = 0} = equator n"
        by (auto simp: usphere_def upper_def equator_def)
      with hb_iso have inj: "inj_on (?hb) (carrier (relative_homology_group n (usphere n) (equator n)))"
        by (simp add: iso_iff)
      interpret hb_hom: group_hom "relative_homology_group n (usphere n) (equator n)"
                                  "reduced_homology_group (int n - 1) (nsphere (n - Suc 0))"
                                  "?hb"
        using hb_iso iso_iff eq group_hom_axioms_def group_hom_def by fastforce
      show ?thesis
      proof (rule inj_onD [OF inj])
        have *: "hom_induced (int n - 1) (nsphere (n - Suc 0)) {} (nsphere (n - Suc 0)) {} neg z
                 = z [^]\<^bsub>homology_group (int n - 1) (nsphere (n - Suc 0))\<^esub> Brouwer_degree2 (n - Suc 0) neg"
          using Brouwer_degree2 [of z "n - Suc 0" neg] False zcarr
          by (simp add: int_ops group.int_pow_subgroup_generated reduced_homology_group_def)
        have "?hb \<circ>
              hom_induced n (lsphere n) (equator n) (usphere n) (equator n) neg
            = hom_induced (int n - 1) (nsphere (n - Suc 0)) {} (nsphere (n - Suc 0)) {} neg \<circ>
              hom_boundary n (lsphere n) (equator n)"
          apply (subst naturality_hom_induced [OF cm_neg_lu])
           apply (force simp: equator_def neg_def)
          by (simp add: equ)
        then have "?hb
                    (hom_induced n (lsphere n) (equator n) (usphere n) (equator n) neg zp)
            = (z [^]\<^bsub>homology_group (int n - 1) (nsphere (n - Suc 0))\<^esub> Brouwer_degree2 (n - Suc 0) neg)"
          by (metis "*" comp_apply zp_z)
        also have "\<dots> = ?hb (zn [^]\<^bsub>relative_homology_group n (usphere n) (equator n)\<^esub>
          Brouwer_degree2 (n - Suc 0) neg)"
          by (metis group.int_pow_subgroup_generated group_relative_homology_group hb_hom.hom_int_pow reduced_homology_group_def zcarr zn_z zncarr)
        finally show "?hb (hom_induced n (lsphere n) (equator n) (usphere n) (equator n) neg zp) =
        ?hb (zn [^]\<^bsub>relative_homology_group n (usphere n) (equator n)\<^esub>
          Brouwer_degree2 (n - Suc 0) neg)" by simp
      qed (auto simp: hom_induced_carrier group.int_pow_closed zncarr)
    qed
    finally show ?thesis
      by (metis (no_types, lifting) group_hom.hom_int_pow group_hom_axioms_def group_hom_def group_relative_homology_group hom_induced local.up_def un_def zncarr)
  qed
  have "continuous_map (nsphere (n - Suc 0)) (nsphere (n - Suc 0)) neg"
    using cm_neg by blast
  then have "homeomorphic_map (nsphere (n - Suc 0)) (nsphere (n - Suc 0)) neg"
    apply (auto simp: homeomorphic_map_maps homeomorphic_maps_def)
    apply (rule_tac x=neg in exI, auto)
    done
  then have Brouwer_degree2_21: "Brouwer_degree2 (n - Suc 0) neg ^ 2 = 1"
    using Brouwer_degree2_homeomorphic_map power2_eq_1_iff by force
  have hi_un_eq_up: "?hi_ee neg un = up [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - Suc 0) neg" (is "?f un = ?y")
  proof -
    have [simp]: "neg \<circ> neg = id"
      by force
    have "?f (?f ?y) = ?y"
      apply (subst hom_induced_compose' [OF cm_neg _ cm_neg])
       apply(force simp: equator_def)
      apply (simp add: upcarr hom_induced_id_gen)
      done
    moreover have "?f ?y = un"
      using upcarr apply (simp only: gh_een.hom_int_pow hi_up_eq_un)
      by (metis (no_types, lifting) Brouwer_degree2_21 GE.group_l_invI GE.l_inv_ex group.int_pow_1 group.int_pow_pow power2_eq_1_iff uncarr zmult_eq_1_iff)
    ultimately show "?f un = ?y"
      by simp
  qed
  have "?hi_ee f un = un [^]\<^bsub>?rhgn (equator n)\<^esub> a \<otimes>\<^bsub>?rhgn (equator n)\<^esub> up [^]\<^bsub>?rhgn (equator n)\<^esub> b"
  proof -
    let ?TE = "topspace (nsphere n) \<inter> equator n"
    have fneg: "(f \<circ> neg) x = (neg \<circ> f) x" if "x \<in> topspace (nsphere n)" for x
      using f [OF that] by (force simp: neg_def)
    have neg_im: "neg ` (topspace (nsphere n) \<inter> equator n) \<subseteq> topspace (nsphere n) \<inter> equator n"
      by (metis cm_neg continuous_map_image_subset_topspace equ(1) topspace_subtopology)
    have 1: "hom_induced n (nsphere n) ?TE (nsphere n) ?TE f \<circ> hom_induced n (nsphere n) ?TE (nsphere n) ?TE neg
           = hom_induced n (nsphere n) ?TE (nsphere n) ?TE neg \<circ> hom_induced n (nsphere n) ?TE (nsphere n) ?TE f"
      using neg_im fimeq cm_neg cmf
      apply (simp add: flip: hom_induced_compose del: hom_induced_restrict)
      using fneg by (auto intro: hom_induced_eq)
    have "(un [^]\<^bsub>?rhgn (equator n)\<^esub> a) \<otimes>\<^bsub>?rhgn (equator n)\<^esub> (up [^]\<^bsub>?rhgn (equator n)\<^esub> b)
        = un [^]\<^bsub>?rhgn (equator n)\<^esub> (Brouwer_degree2 (n - 1) neg * a * Brouwer_degree2 (n - 1) neg)
          \<otimes>\<^bsub>?rhgn (equator n)\<^esub>
          up [^]\<^bsub>?rhgn (equator n)\<^esub> (Brouwer_degree2 (n - 1) neg * b * Brouwer_degree2 (n - 1) neg)"
    proof -
      have "Brouwer_degree2 (n - Suc 0) neg = 1 \<or> Brouwer_degree2 (n - Suc 0) neg = - 1"
        using Brouwer_degree2_21 power2_eq_1_iff by blast
      then show ?thesis
        by fastforce
    qed
    also have "\<dots> = ((un [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - 1) neg) [^]\<^bsub>?rhgn (equator n)\<^esub> a \<otimes>\<^bsub>?rhgn (equator n)\<^esub>
           (up [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - 1) neg) [^]\<^bsub>?rhgn (equator n)\<^esub> b) [^]\<^bsub>?rhgn (equator n)\<^esub>
          Brouwer_degree2 (n - 1) neg"
      by (simp add: GE.int_pow_distrib GE.int_pow_pow uncarr upcarr)
    also have "\<dots> = ?hi_ee neg (?hi_ee f up) [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - Suc 0) neg"
      by (simp add: gh_een.hom_int_pow hi_un_eq_up hi_up_eq_un uncarr up_ab upcarr)
    finally have 2: "(un [^]\<^bsub>?rhgn (equator n)\<^esub> a) \<otimes>\<^bsub>?rhgn (equator n)\<^esub> (up [^]\<^bsub>?rhgn (equator n)\<^esub> b)
             = ?hi_ee neg (?hi_ee f up) [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - Suc 0) neg" .
    have "un = ?hi_ee neg up [^]\<^bsub>?rhgn (equator n)\<^esub> Brouwer_degree2 (n - Suc 0) neg"
      by (metis (no_types, opaque_lifting) Brouwer_degree2_21 GE.int_pow_1 GE.int_pow_pow hi_up_eq_un power2_eq_1_iff uncarr zmult_eq_1_iff)
    moreover have "?hi_ee f ((?hi_ee neg up) [^]\<^bsub>?rhgn (equator n)\<^esub> (Brouwer_degree2 (n - Suc 0) neg))
                 = un [^]\<^bsub>?rhgn (equator n)\<^esub> a \<otimes>\<^bsub>?rhgn (equator n)\<^esub> up [^]\<^bsub>?rhgn (equator n)\<^esub> b"
      using 1 2 by (simp add: hom_induced_carrier gh_eef.hom_int_pow fun_eq_iff)
    ultimately show ?thesis
      by blast
  qed
  then have "?hi_ee f u = u [^]\<^bsub>?rhgn (equator n)\<^esub> (a - b)"
    by (simp add: u_def upcarr uncarr up_ab GE.int_pow_diff GE.m_ac GE.int_pow_distrib GE.int_pow_inv GE.inv_mult_group)
  ultimately
  have "Brouwer_degree2 n f = a - b"
    using iff by blast
  with Bd_ab show ?thesis
    by simp
qed simp


subsection \<open>General Jordan-Brouwer separation theorem and invariance of dimension\<close>

proposition relative_homology_group_Euclidean_complement_step:
  assumes "closedin (Euclidean_space n) S"
  shows "relative_homology_group p (Euclidean_space n) (topspace(Euclidean_space n) - S)
      \<cong> relative_homology_group (p + k) (Euclidean_space (n+k)) (topspace(Euclidean_space (n+k)) - S)"
proof -
  have *: "relative_homology_group p (Euclidean_space n) (topspace(Euclidean_space n) - S)
           \<cong> relative_homology_group (p + 1) (Euclidean_space (Suc n)) (topspace(Euclidean_space (Suc n)) - {x \<in> S. x n = 0})"
    (is "?lhs \<cong> ?rhs")
    if clo: "closedin (Euclidean_space (Suc n)) S" and cong: "\<And>x y. \<lbrakk>x \<in> S; \<And>i. i \<noteq> n \<Longrightarrow> x i = y i\<rbrakk> \<Longrightarrow> y \<in> S"
      for p n S
  proof -
    have Ssub: "S \<subseteq> topspace (Euclidean_space (Suc n))"
      by (meson clo closedin_def)
    define lo where "lo \<equiv> {x \<in> topspace(Euclidean_space (Suc n)). x n < (if x \<in> S then 0 else 1)}"
    define hi where "hi = {x \<in> topspace(Euclidean_space (Suc n)). x n > (if x \<in> S then 0 else -1)}"
    have lo_hi_Int: "lo \<inter> hi = {x \<in> topspace(Euclidean_space (Suc n)) - S. x n \<in> {-1<..<1}}"
      by (auto simp: hi_def lo_def)
    have lo_hi_Un: "lo \<union> hi = topspace(Euclidean_space (Suc n)) - {x \<in> S. x n = 0}"
      by (auto simp: hi_def lo_def)
    define ret where "ret \<equiv> \<lambda>c::real. \<lambda>x i. if i = n then c else x i"
    have cm_ret: "continuous_map (powertop_real UNIV) (powertop_real UNIV) (ret t)" for t
      by (auto simp: ret_def continuous_map_componentwise_UNIV intro: continuous_map_product_projection)
    let ?ST = "\<lambda>t. subtopology (Euclidean_space (Suc n)) {x. x n = t}"
    define squashable where
      "squashable \<equiv> \<lambda>t S. \<forall>x t'. x \<in> S \<and> (x n \<le> t' \<and> t' \<le> t \<or> t \<le> t' \<and> t' \<le> x n) \<longrightarrow> ret t' x \<in> S"
    have squashable: "squashable t (topspace(Euclidean_space(Suc n)))" for t
      by (simp add: squashable_def topspace_Euclidean_space ret_def)
    have squashableD: "\<lbrakk>squashable t S; x \<in> S; x n \<le> t' \<and> t' \<le> t \<or> t \<le> t' \<and> t' \<le> x n\<rbrakk> \<Longrightarrow> ret t' x \<in> S" for x t' t S
      by (auto simp: squashable_def)
    have "squashable 1 hi"
      by (force simp: squashable_def hi_def ret_def topspace_Euclidean_space intro: cong)
    have "squashable t UNIV" for t
      by (force simp: squashable_def hi_def ret_def topspace_Euclidean_space intro: cong)
    have squashable_0_lohi: "squashable 0 (lo \<inter> hi)"
      using Ssub
      by (auto simp: squashable_def hi_def lo_def ret_def topspace_Euclidean_space intro: cong)
    have rm_ret: "retraction_maps (subtopology (Euclidean_space (Suc n)) U)
                                  (subtopology (Euclidean_space (Suc n)) {x. x \<in> U \<and> x n = t})
                                  (ret t) id"
      if "squashable t U" for t U
      unfolding retraction_maps_def
    proof (intro conjI ballI)
      show "continuous_map (subtopology (Euclidean_space (Suc n)) U)
             (subtopology (Euclidean_space (Suc n)) {x \<in> U. x n = t}) (ret t)"
        apply (simp add: cm_ret continuous_map_in_subtopology continuous_map_from_subtopology Euclidean_space_def)
        using that by (fastforce simp: squashable_def ret_def)
    next
      show "continuous_map (subtopology (Euclidean_space (Suc n)) {x \<in> U. x n = t})
                           (subtopology (Euclidean_space (Suc n)) U) id"
        using continuous_map_in_subtopology by fastforce
      show "ret t (id x) = x"
        if "x \<in> topspace (subtopology (Euclidean_space (Suc n)) {x \<in> U. x n = t})" for x
        using that by (simp add: topspace_Euclidean_space ret_def fun_eq_iff)
    qed
    have cm_snd: "continuous_map (prod_topology (top_of_set {0..1}) (subtopology (powertop_real UNIV) S))
                              euclideanreal (\<lambda>x. snd x k)" for k::nat and S
      using continuous_map_componentwise_UNIV continuous_map_into_fulltopology continuous_map_snd by fastforce
    have cm_fstsnd: "continuous_map (prod_topology (top_of_set {0..1}) (subtopology (powertop_real UNIV) S))
                              euclideanreal (\<lambda>x. fst x * snd x k)" for k::nat and S
      by (intro continuous_intros continuous_map_into_fulltopology [OF continuous_map_fst] cm_snd)
    have hw_sub: "homotopic_with (\<lambda>k. k ` V \<subseteq> V) (subtopology (Euclidean_space (Suc n)) U)
                                 (subtopology (Euclidean_space (Suc n)) U) (ret t) id"
      if "squashable t U" "squashable t V" for U V t
      unfolding homotopic_with_def
    proof (intro exI conjI allI ballI)
      let ?h = "\<lambda>(z,x). ret ((1 - z) * t + z * x n) x"
      show "(\<lambda>x. ?h (u, x)) ` V \<subseteq> V" if "u \<in> {0..1}" for u
        using that
        by clarsimp (metis squashableD [OF \<open>squashable t V\<close>] convex_bound_le diff_ge_0_iff_ge eq_diff_eq' le_cases less_eq_real_def segment_bound_lemma)
      have 1: "?h ` ({0..1} \<times> ({x. \<forall>i\<ge>Suc n. x i = 0} \<inter> U)) \<subseteq> U"
        by clarsimp (metis squashableD [OF \<open>squashable t U\<close>] convex_bound_le diff_ge_0_iff_ge eq_diff_eq' le_cases less_eq_real_def segment_bound_lemma)
      show "continuous_map (prod_topology (top_of_set {0..1}) (subtopology (Euclidean_space (Suc n)) U))
                           (subtopology (Euclidean_space (Suc n)) U) ?h"
        apply (simp add: continuous_map_in_subtopology Euclidean_space_def subtopology_subtopology 1)
        apply (auto simp: case_prod_unfold ret_def continuous_map_componentwise_UNIV)
         apply (intro continuous_map_into_fulltopology [OF continuous_map_fst] cm_snd continuous_intros)
        by (auto simp: cm_snd)
    qed (auto simp: ret_def)
    have cs_hi: "contractible_space(subtopology (Euclidean_space(Suc n)) hi)"
    proof -
      have "homotopic_with (\<lambda>x. True) (?ST 1) (?ST 1) id (\<lambda>x. (\<lambda>i. if i = n then 1 else 0))"
        apply (subst homotopic_with_sym)
        apply (simp add: homotopic_with)
        apply (rule_tac x="(\<lambda>(z,x) i. if i=n then 1 else z * x i)" in exI)
        apply (auto simp: Euclidean_space_def subtopology_subtopology continuous_map_in_subtopology case_prod_unfold continuous_map_componentwise_UNIV cm_fstsnd)
        done
      then have "contractible_space (?ST 1)"
        unfolding contractible_space_def by metis
      moreover have "?thesis = contractible_space (?ST 1)"
      proof (intro deformation_retract_imp_homotopy_equivalent_space homotopy_equivalent_space_contractibility)
        have "{x. \<forall>i\<ge>Suc n. x i = 0} \<inter> {x \<in> hi. x n = 1} = {x. \<forall>i\<ge>Suc n. x i = 0} \<inter> {x. x n = 1}"
          by (auto simp: hi_def topspace_Euclidean_space)
        then have eq: "subtopology (Euclidean_space (Suc n)) {x. x \<in> hi \<and> x n = 1} = ?ST 1"
          by (simp add: Euclidean_space_def subtopology_subtopology)
        show "homotopic_with (\<lambda>x. True) (subtopology (Euclidean_space (Suc n)) hi) (subtopology (Euclidean_space (Suc n)) hi) (ret 1) id"
          using hw_sub [OF \<open>squashable 1 hi\<close> \<open>squashable 1 UNIV\<close>] eq by simp
        show "retraction_maps (subtopology (Euclidean_space (Suc n)) hi) (?ST 1) (ret 1) id"
          using rm_ret [OF \<open>squashable 1 hi\<close>] eq by simp
      qed
      ultimately show ?thesis by metis
    qed
    have "?lhs \<cong> relative_homology_group p (Euclidean_space (Suc n)) (lo \<inter> hi)"
    proof (rule group.iso_sym [OF _ deformation_retract_imp_isomorphic_relative_homology_groups])
      have "{x. \<forall>i\<ge>Suc n. x i = 0} \<inter> {x. x n = 0} = {x. \<forall>i\<ge>n. x i = (0::real)}"
        by auto (metis le_less_Suc_eq not_le)
      then have "?ST 0 = Euclidean_space n"
        by (simp add: Euclidean_space_def subtopology_subtopology)
      then show "retraction_maps (Euclidean_space (Suc n)) (Euclidean_space n) (ret 0) id"
        using rm_ret [OF \<open>squashable 0 UNIV\<close>] by auto
      then have "ret 0 x \<in> topspace (Euclidean_space n)"
        if "x \<in> topspace (Euclidean_space (Suc n))" "-1 < x n" "x n < 1" for x
        using that by (simp add: continuous_map_def retraction_maps_def)
      then show "(ret 0) ` (lo \<inter> hi) \<subseteq> topspace (Euclidean_space n) - S"
        by (auto simp: local.cong ret_def hi_def lo_def)
      show "homotopic_with (\<lambda>h. h ` (lo \<inter> hi) \<subseteq> lo \<inter> hi) (Euclidean_space (Suc n)) (Euclidean_space (Suc n)) (ret 0) id"
        using hw_sub [OF squashable squashable_0_lohi] by simp
    qed (auto simp: lo_def hi_def Euclidean_space_def)
    also have "\<dots> \<cong> relative_homology_group p (subtopology (Euclidean_space (Suc n)) hi) (lo \<inter> hi)"
    proof (rule group.iso_sym [OF _ isomorphic_relative_homology_groups_inclusion_contractible])
      show "contractible_space (subtopology (Euclidean_space (Suc n)) hi)"
        by (simp add: cs_hi)
      show "topspace (Euclidean_space (Suc n)) \<inter> hi \<noteq> {}"
        apply (simp add: hi_def topspace_Euclidean_space set_eq_iff)
        apply (rule_tac x="\<lambda>i. if i = n then 1 else 0" in exI, auto)
        done
    qed auto
    also have "\<dots> \<cong> relative_homology_group p (subtopology (Euclidean_space (Suc n)) (lo \<union> hi)) lo"
    proof -
      have oo: "openin (Euclidean_space (Suc n)) {x \<in> topspace (Euclidean_space (Suc n)). x n \<in> A}"
        if "open A" for A
      proof (rule openin_continuous_map_preimage)
        show "continuous_map (Euclidean_space (Suc n)) euclideanreal (\<lambda>x. x n)"
        proof -
          have "\<forall>n f. continuous_map (product_topology f UNIV) (f (n::nat)) (\<lambda>f. f n::real)"
            by (simp add: continuous_map_product_projection)
          then show ?thesis
            using Euclidean_space_def continuous_map_from_subtopology
            by (metis (mono_tags))
        qed
      qed (auto intro: that)
      have "openin (Euclidean_space(Suc n)) lo"
        apply (simp add: openin_subopen [of _ lo])
        apply (simp add: lo_def, safe)
         apply (force intro: oo [of "lessThan 0", simplified] open_Collect_less)
        apply (rule_tac x="{x \<in> topspace(Euclidean_space(Suc n)). x n < 1}
                            \<inter> (topspace(Euclidean_space(Suc n)) - S)" in exI)
        using clo apply (force intro: oo [of "lessThan 1", simplified] open_Collect_less)
        done
      moreover have "openin (Euclidean_space(Suc n)) hi"
        apply (simp add: openin_subopen [of _ hi])
        apply (simp add: hi_def, safe)
         apply (force intro: oo [of "greaterThan 0", simplified] open_Collect_less)
        apply (rule_tac x="{x \<in> topspace(Euclidean_space(Suc n)). x n > -1}
                                \<inter> (topspace(Euclidean_space(Suc n)) - S)" in exI)
        using clo apply (force intro: oo [of "greaterThan (-1)", simplified] open_Collect_less)
        done
      ultimately
      have *: "subtopology (Euclidean_space (Suc n)) (lo \<union> hi) closure_of
                   (topspace (subtopology (Euclidean_space (Suc n)) (lo \<union> hi)) - hi)
                   \<subseteq> subtopology (Euclidean_space (Suc n)) (lo \<union> hi) interior_of lo"
        by (metis (no_types, lifting) Diff_idemp Diff_subset_conv Un_commute Un_upper2 closure_of_interior_of interior_of_closure_of interior_of_complement interior_of_eq lo_hi_Un openin_Un openin_open_subtopology topspace_subtopology_subset)
      have eq: "((lo \<union> hi) \<inter> (lo \<union> hi - (topspace (Euclidean_space (Suc n)) \<inter> (lo \<union> hi) - hi))) = hi"
        "(lo - (topspace (Euclidean_space (Suc n)) \<inter> (lo \<union> hi) - hi)) = lo \<inter> hi"
        by (auto simp: lo_def hi_def Euclidean_space_def)
      show ?thesis
        using homology_excision_axiom [OF *, of "lo \<union> hi" p]
        by (force simp: subtopology_subtopology eq is_iso_def)
    qed
    also have "\<dots> \<cong> relative_homology_group (p + 1 - 1) (subtopology (Euclidean_space (Suc n)) (lo \<union> hi)) lo"
      by simp
    also have "\<dots> \<cong> relative_homology_group (p + 1) (Euclidean_space (Suc n)) (lo \<union> hi)"
    proof (rule group.iso_sym [OF _ isomorphic_relative_homology_groups_relboundary_contractible])
      have proj: "continuous_map (powertop_real UNIV) euclideanreal (\<lambda>f. f n)"
        by (metis UNIV_I continuous_map_product_projection)
      have hilo: "\<And>x. x \<in> hi \<Longrightarrow> (\<lambda>i. if i = n then - x i else x i) \<in> lo"
                 "\<And>x. x \<in> lo \<Longrightarrow> (\<lambda>i. if i = n then - x i else x i) \<in> hi"
        using local.cong
        by (auto simp: hi_def lo_def topspace_Euclidean_space split: if_split_asm)
      have "subtopology (Euclidean_space (Suc n)) hi homeomorphic_space subtopology (Euclidean_space (Suc n)) lo"
        unfolding homeomorphic_space_def
        apply (rule_tac x="\<lambda>x i. if i = n then -(x i) else x i" in exI)+
        using proj
        apply (auto simp: homeomorphic_maps_def Euclidean_space_def continuous_map_in_subtopology
                          hilo continuous_map_componentwise_UNIV continuous_map_from_subtopology continuous_map_minus
                    intro: continuous_map_from_subtopology continuous_map_product_projection)
        done
      then have "contractible_space(subtopology (Euclidean_space(Suc n)) hi)
             \<longleftrightarrow> contractible_space (subtopology (Euclidean_space (Suc n)) lo)"
        by (rule homeomorphic_space_contractibility)
      then show "contractible_space (subtopology (Euclidean_space (Suc n)) lo)"
        using cs_hi by auto
      show "topspace (Euclidean_space (Suc n)) \<inter> lo \<noteq> {}"
        apply (simp add: lo_def Euclidean_space_def set_eq_iff)
        apply (rule_tac x="\<lambda>i. if i = n then -1 else 0" in exI, auto)
        done
    qed auto
    also have "\<dots> \<cong> ?rhs"
      by (simp flip: lo_hi_Un)
    finally show ?thesis .
  qed
  show ?thesis
  proof (induction k)
    case (Suc m)
    with assms obtain T where cloT: "closedin (powertop_real UNIV) T"
                         and SeqT: "S = T \<inter> {x. \<forall>i\<ge>n. x i = 0}"
      by (auto simp: Euclidean_space_def closedin_subtopology)
    then have "closedin (Euclidean_space (m + n)) S"
      apply (simp add: Euclidean_space_def closedin_subtopology)
      apply (rule_tac x="T \<inter> topspace(Euclidean_space n)" in exI)
      using closedin_Euclidean_space topspace_Euclidean_space by force
    moreover have "relative_homology_group p (Euclidean_space n) (topspace (Euclidean_space n) - S)
                \<cong> relative_homology_group (p + 1) (Euclidean_space (Suc n)) (topspace (Euclidean_space (Suc n)) - S)"
      if "closedin (Euclidean_space n) S" for p n
    proof -
      define S' where "S' \<equiv> {x \<in> topspace(Euclidean_space(Suc n)). (\<lambda>i. if i < n then x i else 0) \<in> S}"
      have Ssub_n: "S \<subseteq> topspace (Euclidean_space n)"
        by (meson that closedin_def)
      have "relative_homology_group p (Euclidean_space n) (topspace(Euclidean_space n) - S')
           \<cong> relative_homology_group (p + 1) (Euclidean_space (Suc n)) (topspace(Euclidean_space (Suc n)) - {x \<in> S'. x n = 0})"
      proof (rule *)
        have cm: "continuous_map (powertop_real UNIV) euclideanreal (\<lambda>f. f u)" for u
          by (metis UNIV_I continuous_map_product_projection)
        have "continuous_map (subtopology (powertop_real UNIV) {x. \<forall>i>n. x i = 0}) euclideanreal
                (\<lambda>x. if k \<le> n then x k else 0)" for k
          by (simp add: continuous_map_from_subtopology [OF cm])
        moreover have "\<forall>i\<ge>n. (if i < n then x i else 0) = 0"
          if "x \<in> topspace (subtopology (powertop_real UNIV) {x. \<forall>i>n. x i = 0})" for x
          using that by simp
        ultimately have "continuous_map (Euclidean_space (Suc n)) (Euclidean_space n) (\<lambda>x i. if i < n then x i else 0)"
          by (simp add: Euclidean_space_def continuous_map_in_subtopology continuous_map_componentwise_UNIV
                        continuous_map_from_subtopology [OF cm] image_subset_iff)
        then show "closedin (Euclidean_space (Suc n)) S'"
          unfolding S'_def using that by (rule closedin_continuous_map_preimage)
      next
        fix x y
        assume xy: "\<And>i. i \<noteq> n \<Longrightarrow> x i = y i" "x \<in> S'"
        then have "(\<lambda>i. if i < n then x i else 0) = (\<lambda>i. if i < n then y i else 0)"
          by (simp add: S'_def Euclidean_space_def fun_eq_iff)
        with xy show "y \<in> S'"
          by (simp add: S'_def Euclidean_space_def)
      qed
      moreover
      have abs_eq: "(\<lambda>i. if i < n then x i else 0) = x" if "\<And>i. i \<ge> n \<Longrightarrow> x i = 0" for x :: "nat \<Rightarrow> real" and n
        using that by auto
      then have "topspace (Euclidean_space n) - S' = topspace (Euclidean_space n) - S"
        by (simp add: S'_def Euclidean_space_def set_eq_iff cong: conj_cong)
      moreover
      have "topspace (Euclidean_space (Suc n)) - {x \<in> S'. x n = 0} = topspace (Euclidean_space (Suc n)) - S"
        using Ssub_n
        apply (auto simp: S'_def subset_iff Euclidean_space_def set_eq_iff abs_eq  cong: conj_cong)
        by (metis abs_eq le_antisym not_less_eq_eq)
      ultimately show ?thesis
        by simp
    qed
    ultimately have "relative_homology_group (p + m)(Euclidean_space (m + n))(topspace (Euclidean_space (m + n)) - S)
            \<cong> relative_homology_group (p + m + 1) (Euclidean_space (Suc (m + n))) (topspace (Euclidean_space (Suc (m + n))) - S)"
      by (metis \<open>closedin (Euclidean_space (m + n)) S\<close>)
    then show ?case
      using Suc.IH iso_trans by (force simp: algebra_simps)
  qed (simp add: iso_refl)
qed

lemma iso_Euclidean_complements_lemma1:
  assumes S: "closedin (Euclidean_space m) S" and cmf: "continuous_map(subtopology (Euclidean_space m) S) (Euclidean_space n) f"
  obtains g where "continuous_map (Euclidean_space m) (Euclidean_space n) g"
                  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  have cont: "continuous_on (topspace (Euclidean_space m) \<inter> S) (\<lambda>x. f x i)" for i
    by (metis (no_types) continuous_on_product_then_coordinatewise
            cm_Euclidean_space_iff_continuous_on cmf topspace_subtopology)
  have "f ` (topspace (Euclidean_space m) \<inter> S) \<subseteq> topspace (Euclidean_space n)"
    using cmf continuous_map_image_subset_topspace by fastforce
  then
  have "\<exists>g. continuous_on (topspace (Euclidean_space m)) g \<and> (\<forall>x \<in> S. g x = f x i)" for i
    using S Tietze_unbounded [OF cont [of i]]
    by (metis closedin_Euclidean_space_iff closedin_closed_Int topspace_subtopology topspace_subtopology_subset)
  then obtain g where cmg: "\<And>i. continuous_map (Euclidean_space m) euclideanreal (g i)"
    and gf: "\<And>i x. x \<in> S \<Longrightarrow> g i x = f x i"
    unfolding continuous_map_Euclidean_space_iff by metis
  let ?GG = "\<lambda>x i. if i < n then g i x else 0"
  show thesis
  proof
    show "continuous_map (Euclidean_space m) (Euclidean_space n) ?GG"
      unfolding Euclidean_space_def [of n]
      by (auto simp: continuous_map_in_subtopology continuous_map_componentwise cmg)
    show "?GG x = f x" if "x \<in> S" for x
    proof -
      have "S \<subseteq> topspace (Euclidean_space m)"
        by (meson S closedin_def)
      then have "f x \<in> topspace (Euclidean_space n)"
        using cmf that unfolding continuous_map_def topspace_subtopology by blast
      then show ?thesis
        by (force simp: topspace_Euclidean_space gf that)
    qed
  qed
qed


lemma iso_Euclidean_complements_lemma2:
  assumes S: "closedin (Euclidean_space m) S"
      and T: "closedin (Euclidean_space n) T"
      and hom: "homeomorphic_map (subtopology (Euclidean_space m) S) (subtopology (Euclidean_space n) T) f"
  obtains g where "homeomorphic_map (prod_topology (Euclidean_space m) (Euclidean_space n))
                                    (prod_topology (Euclidean_space n) (Euclidean_space m)) g"
                  "\<And>x. x \<in> S \<Longrightarrow> g(x,(\<lambda>i. 0)) = (f x,(\<lambda>i. 0))"
proof -
  obtain g where cmf: "continuous_map (subtopology (Euclidean_space m) S) (subtopology (Euclidean_space n) T) f"
           and cmg: "continuous_map (subtopology (Euclidean_space n) T) (subtopology (Euclidean_space m) S) g"
           and gf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
           and fg: "\<And>y. y \<in> T \<Longrightarrow> f (g y) = y"
    using hom S T closedin_subset unfolding homeomorphic_map_maps homeomorphic_maps_def
    by fastforce
  obtain f' where cmf': "continuous_map (Euclidean_space m) (Euclidean_space n) f'"
             and f'f: "\<And>x. x \<in> S \<Longrightarrow> f' x = f x"
    using iso_Euclidean_complements_lemma1 S cmf continuous_map_into_fulltopology by metis
  obtain g' where cmg': "continuous_map (Euclidean_space n) (Euclidean_space m) g'"
             and g'g: "\<And>x. x \<in> T \<Longrightarrow> g' x = g x"
    using iso_Euclidean_complements_lemma1 T cmg continuous_map_into_fulltopology by metis
  define p  where "p \<equiv> \<lambda>(x,y). (x,(\<lambda>i. y i + f' x i))"
  define p' where "p' \<equiv> \<lambda>(x,y). (x,(\<lambda>i. y i - f' x i))"
  define q  where "q \<equiv> \<lambda>(x,y). (x,(\<lambda>i. y i + g' x i))"
  define q' where "q' \<equiv> \<lambda>(x,y). (x,(\<lambda>i. y i - g' x i))"
  have "homeomorphic_maps (prod_topology (Euclidean_space m) (Euclidean_space n))
                          (prod_topology (Euclidean_space m) (Euclidean_space n))
                          p p'"
       "homeomorphic_maps (prod_topology (Euclidean_space n) (Euclidean_space m))
                          (prod_topology (Euclidean_space n) (Euclidean_space m))
                          q q'"
       "homeomorphic_maps (prod_topology (Euclidean_space m) (Euclidean_space n))
                          (prod_topology (Euclidean_space n) (Euclidean_space m)) (\<lambda>(x,y). (y,x)) (\<lambda>(x,y). (y,x))"
    apply (simp_all add: p_def p'_def q_def q'_def homeomorphic_maps_def continuous_map_pairwise)
    apply (force simp: case_prod_unfold continuous_map_of_fst [unfolded o_def] cmf' cmg' intro: continuous_intros)+
    done
  then have "homeomorphic_maps (prod_topology (Euclidean_space m) (Euclidean_space n))
                          (prod_topology (Euclidean_space n) (Euclidean_space m))
                          (q' \<circ> (\<lambda>(x,y). (y,x)) \<circ> p) (p' \<circ> ((\<lambda>(x,y). (y,x)) \<circ> q))"
    using homeomorphic_maps_compose homeomorphic_maps_sym by (metis (no_types, lifting))
  moreover
  have "\<And>x. x \<in> S \<Longrightarrow> (q' \<circ> (\<lambda>(x,y). (y,x)) \<circ> p) (x, \<lambda>i. 0) = (f x, \<lambda>i. 0)"
    apply (simp add: q'_def p_def f'f)
    apply (simp add: fun_eq_iff)
    by (metis S T closedin_subset g'g gf hom homeomorphic_imp_surjective_map image_eqI topspace_subtopology_subset)
  ultimately
  show thesis
    using homeomorphic_map_maps that by blast
qed


proposition isomorphic_relative_homology_groups_Euclidean_complements:
  assumes S: "closedin (Euclidean_space n) S" and T: "closedin (Euclidean_space n) T"
   and hom: "(subtopology (Euclidean_space n) S) homeomorphic_space (subtopology (Euclidean_space n) T)"
   shows "relative_homology_group p (Euclidean_space n) (topspace(Euclidean_space n) - S)
          \<cong> relative_homology_group p (Euclidean_space n) (topspace(Euclidean_space n) - T)"
proof -
  have subST: "S \<subseteq> topspace(Euclidean_space n)" "T \<subseteq> topspace(Euclidean_space n)"
    by (meson S T closedin_def)+
  have "relative_homology_group p (Euclidean_space n) (topspace (Euclidean_space n) - S)
        \<cong> relative_homology_group (p + int n) (Euclidean_space (n + n)) (topspace (Euclidean_space (n + n)) - S)"
    using relative_homology_group_Euclidean_complement_step [OF S] by blast
  moreover have "relative_homology_group p (Euclidean_space n) (topspace (Euclidean_space n) - T)
        \<cong> relative_homology_group (p + int n) (Euclidean_space (n + n)) (topspace (Euclidean_space (n + n)) - T)"
    using relative_homology_group_Euclidean_complement_step [OF T] by blast
  moreover have "relative_homology_group (p + int n) (Euclidean_space (n + n)) (topspace (Euclidean_space (n + n)) - S)
               \<cong> relative_homology_group (p + int n) (Euclidean_space (n + n)) (topspace (Euclidean_space (n + n)) - T)"
  proof -
    obtain f where f: "homeomorphic_map (subtopology (Euclidean_space n) S)
                                        (subtopology (Euclidean_space n) T) f"
      using hom unfolding homeomorphic_space by blast
    obtain g where g: "homeomorphic_map (prod_topology (Euclidean_space n) (Euclidean_space n))
                                        (prod_topology (Euclidean_space n) (Euclidean_space n)) g"
              and gf: "\<And>x. x \<in> S \<Longrightarrow> g(x,(\<lambda>i. 0)) = (f x,(\<lambda>i. 0))"
      using S T f iso_Euclidean_complements_lemma2 by blast
    define h where "h \<equiv> \<lambda>x::nat \<Rightarrow>real. ((\<lambda>i. if i < n then x i else 0), (\<lambda>j. if j < n then x(n + j) else 0))"
    define k where "k \<equiv> \<lambda>(x,y) i. if i < 2 * n then if i < n then x i else y(i - n) else (0::real)"
    have hk: "homeomorphic_maps (Euclidean_space(2 * n)) (prod_topology (Euclidean_space n) (Euclidean_space n)) h k"
      unfolding homeomorphic_maps_def
    proof safe
      show "continuous_map (Euclidean_space (2 * n))
                           (prod_topology (Euclidean_space n) (Euclidean_space n)) h"
        apply (simp add: h_def continuous_map_pairwise o_def continuous_map_componentwise_Euclidean_space)
        unfolding Euclidean_space_def
        by (metis (mono_tags) UNIV_I continuous_map_from_subtopology continuous_map_product_projection)
      have "continuous_map (prod_topology (Euclidean_space n) (Euclidean_space n)) euclideanreal (\<lambda>p. fst p i)" for i
        using Euclidean_space_def continuous_map_into_fulltopology continuous_map_fst by fastforce
      moreover
      have "continuous_map (prod_topology (Euclidean_space n) (Euclidean_space n)) euclideanreal (\<lambda>p. snd p (i - n))" for i
        using Euclidean_space_def continuous_map_into_fulltopology continuous_map_snd by fastforce
      ultimately
      show "continuous_map (prod_topology (Euclidean_space n) (Euclidean_space n))
                           (Euclidean_space (2 * n)) k"
        by (simp add: k_def continuous_map_pairwise o_def continuous_map_componentwise_Euclidean_space case_prod_unfold)
    qed (auto simp: k_def h_def fun_eq_iff topspace_Euclidean_space)
    define kgh where "kgh \<equiv> k \<circ> g \<circ> h"
    let ?i = "hom_induced (p + n) (Euclidean_space(2 * n)) (topspace(Euclidean_space(2 * n)) - S)
                                 (Euclidean_space(2 * n)) (topspace(Euclidean_space(2 * n)) - T) kgh"
    have "?i \<in> iso (relative_homology_group (p + int n) (Euclidean_space (2 * n))
                    (topspace (Euclidean_space (2 * n)) - S))
                   (relative_homology_group (p + int n) (Euclidean_space (2 * n))
                    (topspace (Euclidean_space (2 * n)) - T))"
    proof (rule homeomorphic_map_relative_homology_iso)
      show hm: "homeomorphic_map (Euclidean_space (2 * n)) (Euclidean_space (2 * n)) kgh"
        unfolding kgh_def by (meson hk g homeomorphic_map_maps homeomorphic_maps_compose homeomorphic_maps_sym)
      have Teq: "T = f ` S"
        using f homeomorphic_imp_surjective_map subST(1) subST(2) topspace_subtopology_subset by blast
      have khf: "\<And>x. x \<in> S \<Longrightarrow> k(h(f x)) = f x"
        by (metis (no_types, lifting) Teq hk homeomorphic_maps_def image_subset_iff le_add1 mult_2 subST(2) subsetD subset_Euclidean_space)
      have gh: "g(h x) = h(f x)" if "x \<in> S" for x
      proof -
        have [simp]: "(\<lambda>i. if i < n then x i else 0) = x"
          using subST(1) that topspace_Euclidean_space by (auto simp: fun_eq_iff)
        have "f x \<in> topspace(Euclidean_space n)"
          using Teq subST(2) that by blast
        moreover have "(\<lambda>j. if j < n then x (n + j) else 0) = (\<lambda>j. 0::real)"
          using Euclidean_space_def subST(1) that by force
        ultimately show ?thesis
          by (simp add: topspace_Euclidean_space h_def gf \<open>x \<in> S\<close> fun_eq_iff)
      qed
      have *: "\<lbrakk>S \<subseteq> U; T \<subseteq> U; kgh ` U = U; inj_on kgh U; kgh ` S = T\<rbrakk> \<Longrightarrow> kgh ` (U - S) = U - T" for U
        unfolding inj_on_def set_eq_iff by blast
      show "kgh ` (topspace (Euclidean_space (2 * n)) - S) = topspace (Euclidean_space (2 * n)) - T"
      proof (rule *)
        show "kgh ` topspace (Euclidean_space (2 * n)) = topspace (Euclidean_space (2 * n))"
          by (simp add: hm homeomorphic_imp_surjective_map)
        show "inj_on kgh (topspace (Euclidean_space (2 * n)))"
          using hm homeomorphic_map_def by auto
        show "kgh ` S = T"
          by (simp add: Teq kgh_def gh khf)
      qed (use subST topspace_Euclidean_space in \<open>fastforce+\<close>)
    qed auto
    then show ?thesis
      by (simp add: is_isoI mult_2)
  qed
  ultimately show ?thesis
    by (meson group.iso_sym iso_trans group_relative_homology_group)
qed

lemma lemma_iod:
  assumes "S \<subseteq> T" "S \<noteq> {}" and Tsub: "T \<subseteq> topspace(Euclidean_space n)"
      and S: "\<And>a b u. \<lbrakk>a \<in> S; b \<in> T; 0 < u; u < 1\<rbrakk> \<Longrightarrow> (\<lambda>i. (1 - u) * a i + u * b i) \<in> S"
    shows "path_connectedin (Euclidean_space n) T"
proof -
  obtain a where "a \<in> S"
    using assms by blast
  have "path_component_of (subtopology (Euclidean_space n) T) a b" if "b \<in> T" for b
    unfolding path_component_of_def
  proof (intro exI conjI)
    have [simp]: "\<forall>i\<ge>n. a i = 0"
      using Tsub \<open>a \<in> S\<close> assms(1) topspace_Euclidean_space by auto
    have [simp]: "\<forall>i\<ge>n. b i = 0"
      using Tsub that topspace_Euclidean_space by auto
    have inT: "(\<lambda>i. (1 - x) * a i + x * b i) \<in> T" if "0 \<le> x" "x \<le> 1" for x
    proof (cases "x = 0 \<or> x = 1")
      case True
      with \<open>a \<in> S\<close> \<open>b \<in> T\<close> \<open>S \<subseteq> T\<close> show ?thesis
        by force
    next
      case False
      then show ?thesis
        using subsetD [OF \<open>S \<subseteq> T\<close> S] \<open>a \<in> S\<close> \<open>b \<in> T\<close> that by auto
    qed
    have "continuous_on {0..1} (\<lambda>x. (1 - x) * a k + x * b k)" for k
      by (intro continuous_intros)
    then show "pathin (subtopology (Euclidean_space n) T) (\<lambda>t i. (1 - t) * a i + t * b i)"
      apply (simp add: Euclidean_space_def subtopology_subtopology pathin_subtopology)
      apply (simp add: pathin_def continuous_map_componentwise_UNIV inT)
      done
  qed auto
  then have "path_connected_space (subtopology (Euclidean_space n) T)"
    by (metis Tsub path_component_of_equiv path_connected_space_iff_path_component topspace_subtopology_subset)
  then show ?thesis
    by (simp add: Tsub path_connectedin_def)
qed


lemma invariance_of_dimension_closedin_Euclidean_space:
  assumes "closedin (Euclidean_space n) S"
  shows "subtopology (Euclidean_space n) S homeomorphic_space Euclidean_space n
         \<longleftrightarrow> S = topspace(Euclidean_space n)"
         (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have Ssub: "S \<subseteq> topspace (Euclidean_space n)"
    by (meson assms closedin_def)
  moreover have False if "a \<notin> S" and "a \<in> topspace (Euclidean_space n)" for a
  proof -
    have cl_n: "closedin (Euclidean_space (Suc n)) (topspace(Euclidean_space n))"
      using Euclidean_space_def closedin_Euclidean_space closedin_subtopology by fastforce
    then have sub: "subtopology (Euclidean_space(Suc n)) (topspace(Euclidean_space n)) = Euclidean_space n"
      by (metis (no_types, lifting) Euclidean_space_def closedin_subset subtopology_subtopology topspace_Euclidean_space topspace_subtopology topspace_subtopology_subset)
    then have cl_S: "closedin (Euclidean_space(Suc n)) S"
      using cl_n assms closedin_closed_subtopology by fastforce
    have sub_SucS: "subtopology (Euclidean_space (Suc n)) S = subtopology (Euclidean_space n) S"
      by (metis Ssub sub subtopology_subtopology topspace_subtopology topspace_subtopology_subset)
    have non0: "{y. \<exists>x::nat\<Rightarrow>real. (\<forall>i\<ge>Suc n. x i = 0) \<and> (\<exists>i\<ge>n. x i \<noteq> 0) \<and> y = x n} = -{0}"
    proof safe
      show "False" if "\<forall>i\<ge>Suc n. f i = 0" "0 = f n" "n \<le> i" "f i \<noteq> 0" for f::"nat\<Rightarrow>real" and i
        by (metis that le_antisym not_less_eq_eq)
      show "\<exists>f::nat\<Rightarrow>real. (\<forall>i\<ge>Suc n. f i = 0) \<and> (\<exists>i\<ge>n. f i \<noteq> 0) \<and> a = f n" if "a \<noteq> 0" for a
        by (rule_tac x="(\<lambda>i. 0)(n:= a)" in exI) (force simp: that)
    qed
    have "homology_group 0 (subtopology (Euclidean_space (Suc n)) (topspace (Euclidean_space (Suc n)) - S))
          \<cong> homology_group 0 (subtopology (Euclidean_space (Suc n)) (topspace (Euclidean_space (Suc n)) - topspace (Euclidean_space n)))"
    proof (rule isomorphic_relative_contractible_space_imp_homology_groups)
      show "(topspace (Euclidean_space (Suc n)) - S = {}) =
            (topspace (Euclidean_space (Suc n)) - topspace (Euclidean_space n) = {})"
        using cl_n closedin_subset that by auto
    next
      fix p
      show "relative_homology_group p (Euclidean_space (Suc n))
         (topspace (Euclidean_space (Suc n)) - S) \<cong>
        relative_homology_group p (Euclidean_space (Suc n))
         (topspace (Euclidean_space (Suc n)) - topspace (Euclidean_space n))"
        by (simp add: L sub_SucS cl_S cl_n isomorphic_relative_homology_groups_Euclidean_complements sub)
    qed (auto simp: L)
    moreover
    have "continuous_map (powertop_real UNIV) euclideanreal (\<lambda>x. x n)"
      by (metis (no_types) UNIV_I continuous_map_product_projection)
    then have cm: "continuous_map (subtopology (Euclidean_space (Suc n)) (topspace (Euclidean_space (Suc n)) - topspace (Euclidean_space n)))
                                  euclideanreal (\<lambda>x. x n)"
      by (simp add: Euclidean_space_def continuous_map_from_subtopology)
    have False if "path_connected_space
                      (subtopology (Euclidean_space (Suc n))
                       (topspace (Euclidean_space (Suc n)) - topspace (Euclidean_space n)))"
      using path_connectedin_continuous_map_image [OF cm that [unfolded path_connectedin_topspace [symmetric]]]
            bounded_path_connected_Compl_real [of "{0}"]
      by (simp add: topspace_Euclidean_space image_def Bex_def non0 flip: path_connectedin_topspace)
    moreover
    have eq: "T = T \<inter> {x. x n \<le> 0} \<union> T \<inter> {x. x n \<ge> 0}" for T :: "(nat \<Rightarrow> real) set"
      by auto
    have "path_connectedin (Euclidean_space (Suc n)) (topspace (Euclidean_space (Suc n)) - S)"
    proof (subst eq, rule path_connectedin_Un)
      have "topspace(Euclidean_space(Suc n)) \<inter> {x. x n = 0} = topspace(Euclidean_space n)"
        apply (auto simp: topspace_Euclidean_space)
        by (metis Suc_leI inf.absorb_iff2 inf.orderE leI)
      let ?S = "topspace(Euclidean_space(Suc n)) \<inter> {x. x n < 0}"
      show "path_connectedin (Euclidean_space (Suc n))
              ((topspace (Euclidean_space (Suc n)) - S) \<inter> {x. x n \<le> 0})"
      proof (rule lemma_iod)
        show "?S \<subseteq> (topspace (Euclidean_space (Suc n)) - S) \<inter> {x. x n \<le> 0}"
          using Ssub topspace_Euclidean_space by auto
        show "?S \<noteq> {}"
          apply (simp add: topspace_Euclidean_space set_eq_iff)
          apply (rule_tac x="(\<lambda>i. 0)(n:= -1)" in exI)
          apply auto
          done
        fix a b and u::real
        assume
          "a \<in> ?S" "0 < u" "u < 1"
          "b \<in> (topspace (Euclidean_space (Suc n)) - S) \<inter> {x. x n \<le> 0}"
        then show "(\<lambda>i. (1 - u) * a i + u * b i) \<in> ?S"
          by (simp add: topspace_Euclidean_space add_neg_nonpos less_eq_real_def mult_less_0_iff)
      qed (simp add: topspace_Euclidean_space subset_iff)
      let ?T = "topspace(Euclidean_space(Suc n)) \<inter> {x. x n > 0}"
      show "path_connectedin (Euclidean_space (Suc n))
              ((topspace (Euclidean_space (Suc n)) - S) \<inter> {x. 0 \<le> x n})"
      proof (rule lemma_iod)
        show "?T \<subseteq> (topspace (Euclidean_space (Suc n)) - S) \<inter> {x. 0 \<le> x n}"
          using Ssub topspace_Euclidean_space by auto
        show "?T \<noteq> {}"
          apply (simp add: topspace_Euclidean_space set_eq_iff)
          apply (rule_tac x="(\<lambda>i. 0)(n:= 1)" in exI)
          apply auto
          done
        fix a b and u::real
        assume  "a \<in> ?T" "0 < u" "u < 1" "b \<in> (topspace (Euclidean_space (Suc n)) - S) \<inter> {x. 0 \<le> x n}"
        then show "(\<lambda>i. (1 - u) * a i + u * b i) \<in> ?T"
          by (simp add: topspace_Euclidean_space add_pos_nonneg)
      qed (simp add: topspace_Euclidean_space subset_iff)
      show "(topspace (Euclidean_space (Suc n)) - S) \<inter> {x. x n \<le> 0} \<inter>
            ((topspace (Euclidean_space (Suc n)) - S) \<inter> {x. 0 \<le> x n}) \<noteq> {}"
        using that
        apply (auto simp: Set.set_eq_iff topspace_Euclidean_space)
        by (metis Suc_leD order_refl)
    qed
    then have "path_connected_space (subtopology (Euclidean_space (Suc n))
                                         (topspace (Euclidean_space (Suc n)) - S))"
      apply (simp add: path_connectedin_subtopology flip: path_connectedin_topspace)
      by (metis Int_Diff inf_idem)
    ultimately
    show ?thesis
      using isomorphic_homology_imp_path_connectedness by blast
  qed
  ultimately show ?rhs
    by blast
qed (simp add: homeomorphic_space_refl)



lemma isomorphic_homology_groups_Euclidean_complements:
  assumes "closedin (Euclidean_space n) S" "closedin (Euclidean_space n) T"
           "(subtopology (Euclidean_space n) S) homeomorphic_space (subtopology (Euclidean_space n) T)"
  shows "homology_group p (subtopology (Euclidean_space n) (topspace(Euclidean_space n) - S))
         \<cong> homology_group p (subtopology (Euclidean_space n) (topspace(Euclidean_space n) - T))"
proof (rule isomorphic_relative_contractible_space_imp_homology_groups)
  show "topspace (Euclidean_space n) - S \<subseteq> topspace (Euclidean_space n)"
    using assms homeomorphic_space_sym invariance_of_dimension_closedin_Euclidean_space subtopology_superset by fastforce
  show "topspace (Euclidean_space n) - T \<subseteq> topspace (Euclidean_space n)"
    using assms invariance_of_dimension_closedin_Euclidean_space subtopology_superset by force
  show "(topspace (Euclidean_space n) - S = {}) = (topspace (Euclidean_space n) - T = {})"
    by (metis Diff_eq_empty_iff assms closedin_subset homeomorphic_space_sym invariance_of_dimension_closedin_Euclidean_space subset_antisym subtopology_topspace)
  show "relative_homology_group p (Euclidean_space n) (topspace (Euclidean_space n) - S) \<cong>
        relative_homology_group p (Euclidean_space n) (topspace (Euclidean_space n) - T)" for p
    using assms isomorphic_relative_homology_groups_Euclidean_complements by blast
qed auto

lemma eqpoll_path_components_Euclidean_complements:
  assumes "closedin (Euclidean_space n) S" "closedin (Euclidean_space n) T"
          "(subtopology (Euclidean_space n) S) homeomorphic_space (subtopology (Euclidean_space n) T)"
 shows "path_components_of
             (subtopology (Euclidean_space n)
                          (topspace(Euclidean_space n) - S))
      \<approx> path_components_of
             (subtopology (Euclidean_space n)
                          (topspace(Euclidean_space n) - T))"
  by (simp add: assms isomorphic_homology_groups_Euclidean_complements isomorphic_homology_imp_path_components)

lemma path_connectedin_Euclidean_complements:
  assumes "closedin (Euclidean_space n) S" "closedin (Euclidean_space n) T"
          "(subtopology (Euclidean_space n) S) homeomorphic_space (subtopology (Euclidean_space n) T)"
  shows "path_connectedin (Euclidean_space n) (topspace(Euclidean_space n) - S)
         \<longleftrightarrow> path_connectedin (Euclidean_space n) (topspace(Euclidean_space n) - T)"
  by (meson Diff_subset assms isomorphic_homology_groups_Euclidean_complements isomorphic_homology_imp_path_connectedness path_connectedin_def)

lemma eqpoll_connected_components_Euclidean_complements:
  assumes S: "closedin (Euclidean_space n) S" and T: "closedin (Euclidean_space n) T"
     and ST: "(subtopology (Euclidean_space n) S) homeomorphic_space (subtopology (Euclidean_space n) T)"
  shows "connected_components_of
             (subtopology (Euclidean_space n)
                          (topspace(Euclidean_space n) - S))
        \<approx> connected_components_of
             (subtopology (Euclidean_space n)
                          (topspace(Euclidean_space n) - T))"
  using eqpoll_path_components_Euclidean_complements [OF assms]
  by (metis S T closedin_def locally_path_connected_Euclidean_space locally_path_connected_space_open_subset path_components_eq_connected_components_of)

lemma connected_in_Euclidean_complements:
  assumes "closedin (Euclidean_space n) S" "closedin (Euclidean_space n) T"
          "(subtopology (Euclidean_space n) S) homeomorphic_space (subtopology (Euclidean_space n) T)"
  shows "connectedin (Euclidean_space n) (topspace(Euclidean_space n) - S)
     \<longleftrightarrow> connectedin (Euclidean_space n) (topspace(Euclidean_space n) - T)"
  apply (simp add: connectedin_def connected_space_iff_components_subset_singleton subset_singleton_iff_lepoll)
  using eqpoll_connected_components_Euclidean_complements [OF assms]
  by (meson eqpoll_sym lepoll_trans1)


theorem invariance_of_dimension_Euclidean_space:
   "Euclidean_space m homeomorphic_space Euclidean_space n \<longleftrightarrow> m = n"
proof (cases m n rule: linorder_cases)
  case less
  then have *: "topspace (Euclidean_space m) \<subseteq> topspace (Euclidean_space n)"
    by (meson le_cases not_le subset_Euclidean_space)
  then have "Euclidean_space m = subtopology (Euclidean_space n) (topspace(Euclidean_space m))"
    by (simp add: Euclidean_space_def inf.absorb_iff2 subtopology_subtopology)
  then show ?thesis
    by (metis (no_types, lifting) * Euclidean_space_def closedin_Euclidean_space closedin_closed_subtopology eq_iff invariance_of_dimension_closedin_Euclidean_space subset_Euclidean_space topspace_Euclidean_space)
next
  case equal
  then show ?thesis
    by (simp add: homeomorphic_space_refl)
next
  case greater
  then have *: "topspace (Euclidean_space n) \<subseteq> topspace (Euclidean_space m)"
    by (meson le_cases not_le subset_Euclidean_space)
  then have "Euclidean_space n = subtopology (Euclidean_space m) (topspace(Euclidean_space n))"
    by (simp add: Euclidean_space_def inf.absorb_iff2 subtopology_subtopology)
  then show ?thesis
    by (metis (no_types, lifting) "*" Euclidean_space_def closedin_Euclidean_space closedin_closed_subtopology eq_iff homeomorphic_space_sym invariance_of_dimension_closedin_Euclidean_space subset_Euclidean_space topspace_Euclidean_space)
qed



lemma biglemma:
  assumes "n \<noteq> 0" and S: "compactin (Euclidean_space n) S"
      and cmh: "continuous_map (subtopology (Euclidean_space n) S) (Euclidean_space n) h"
      and "inj_on h S"
    shows "path_connectedin (Euclidean_space n) (topspace(Euclidean_space n) - h ` S)
       \<longleftrightarrow> path_connectedin (Euclidean_space n) (topspace(Euclidean_space n) - S)"
proof (rule path_connectedin_Euclidean_complements)
  have hS_sub: "h ` S \<subseteq> topspace(Euclidean_space n)"
    by (metis (no_types) S cmh compactin_subspace continuous_map_image_subset_topspace topspace_subtopology_subset)
  show clo_S: "closedin (Euclidean_space n) S"
    using assms by (simp add: continuous_map_in_subtopology Hausdorff_Euclidean_space compactin_imp_closedin)
  show clo_hS: "closedin (Euclidean_space n) (h ` S)"
    using Hausdorff_Euclidean_space S cmh compactin_absolute compactin_imp_closedin image_compactin by blast
  have "homeomorphic_map (subtopology (Euclidean_space n) S) (subtopology (Euclidean_space n) (h ` S)) h"
  proof (rule continuous_imp_homeomorphic_map)
    show "compact_space (subtopology (Euclidean_space n) S)"
      by (simp add: S compact_space_subtopology)
    show "Hausdorff_space (subtopology (Euclidean_space n) (h ` S))"
      using hS_sub
      by (simp add: Hausdorff_Euclidean_space Hausdorff_space_subtopology)
    show "continuous_map (subtopology (Euclidean_space n) S) (subtopology (Euclidean_space n) (h ` S)) h"
      using cmh continuous_map_in_subtopology by fastforce
    show "h ` topspace (subtopology (Euclidean_space n) S) = topspace (subtopology (Euclidean_space n) (h ` S))"
      using clo_hS clo_S closedin_subset by auto
    show "inj_on h (topspace (subtopology (Euclidean_space n) S))"
      by (metis \<open>inj_on h S\<close> clo_S closedin_def topspace_subtopology_subset)
  qed
  then show "subtopology (Euclidean_space n) (h ` S) homeomorphic_space subtopology (Euclidean_space n) S"
    using homeomorphic_space homeomorphic_space_sym by blast
qed


lemma lemmaIOD:
  assumes
    "\<exists>T. T \<in> U \<and> c \<subseteq> T" "\<exists>T. T \<in> U \<and> d \<subseteq> T" "\<Union>U = c \<union> d" "\<And>T. T \<in> U \<Longrightarrow> T \<noteq> {}"
    "pairwise disjnt U" "~(\<exists>T. U \<subseteq> {T})"
  shows "c \<in> U"
  using assms
  apply safe
  subgoal for C' D'
  proof (cases "C'=D'")
    show "c \<in> U"
      if UU: "\<Union> U = c \<union> d"
        and U: "\<And>T. T \<in> U \<Longrightarrow> T \<noteq> {}" "disjoint U" and "\<nexists>T. U \<subseteq> {T}" "c \<subseteq> C'" "D' \<in> U" "d \<subseteq> D'" "C' = D'"
    proof -
      have "c \<union> d = D'"
        using Union_upper sup_mono UU that(5) that(6) that(7) that(8) by auto
      then have "\<Union>U = D'"
        by (simp add: UU)
      with U have "U = {D'}"
        by (metis (no_types, lifting) disjnt_Union1 disjnt_self_iff_empty insertCI pairwiseD subset_iff that(4) that(6))
      then show ?thesis
        using that(4) by auto
    qed
    show "c \<in> U"
      if "\<Union> U = c \<union> d""disjoint U" "C' \<in> U" "c \<subseteq> C'""D' \<in> U" "d \<subseteq> D'" "C' \<noteq> D'"
    proof -
      have "C' \<inter> D' = {}"
        using \<open>disjoint U\<close> \<open>C' \<in> U\<close> \<open>D' \<in> U\<close> \<open>C' \<noteq> D'\<close>unfolding disjnt_iff pairwise_def
        by blast
      then show ?thesis
        using subset_antisym that(1) \<open>C' \<in> U\<close> \<open>c \<subseteq> C'\<close> \<open>d \<subseteq> D'\<close> by fastforce
    qed
  qed
  done




theorem invariance_of_domain_Euclidean_space:
  assumes U: "openin (Euclidean_space n) U"
    and cmf: "continuous_map (subtopology (Euclidean_space n) U) (Euclidean_space n) f"
    and "inj_on f U"
  shows "openin (Euclidean_space n) (f ` U)"   (is "openin ?E (f ` U)")
proof (cases "n = 0")
  case True
  have [simp]: "Euclidean_space 0 = discrete_topology {\<lambda>i. 0}"
    by (auto simp: subtopology_eq_discrete_topology_sing topspace_Euclidean_space)
  show ?thesis
    using cmf True U by auto
next
  case False
  define enorm where "enorm \<equiv> \<lambda>x. sqrt(\<Sum>i<n. x i ^ 2)"
  have enorm_if [simp]: "enorm (\<lambda>i. if i = k then d else 0) = (if k < n then \<bar>d\<bar> else 0)" for k d
    using \<open>n \<noteq> 0\<close> by (auto simp:  enorm_def power2_eq_square if_distrib [of "\<lambda>x. x * _"] cong: if_cong)
  define zero::"nat\<Rightarrow>real" where "zero \<equiv> \<lambda>i. 0"
  have zero_in [simp]: "zero \<in> topspace ?E"
    using False by (simp add: zero_def topspace_Euclidean_space)
  have enorm_eq_0 [simp]: "enorm x = 0 \<longleftrightarrow> x = zero"
    if "x \<in> topspace(Euclidean_space n)" for x
    using that unfolding zero_def enorm_def
    apply (simp add: sum_nonneg_eq_0_iff fun_eq_iff topspace_Euclidean_space)
    using le_less_linear by blast
  have [simp]: "enorm zero = 0"
    by (simp add: zero_def enorm_def)
  have cm_enorm: "continuous_map ?E euclideanreal enorm"
    unfolding enorm_def
  proof (intro continuous_intros)
    show "continuous_map ?E euclideanreal (\<lambda>x. x i)"
      if "i \<in> {..<n}" for i
      using that by (auto simp: Euclidean_space_def intro: continuous_map_product_projection continuous_map_from_subtopology)
  qed auto
  have enorm_ge0: "0 \<le> enorm x" for x
    by (auto simp: enorm_def sum_nonneg)
  have le_enorm: "\<bar>x i\<bar> \<le> enorm x" if "i < n" for i x
  proof -
    have "\<bar>x i\<bar> \<le> sqrt (\<Sum>k\<in>{i}. (x k)\<^sup>2)"
      by auto
    also have "\<dots> \<le> sqrt (\<Sum>k<n. (x k)\<^sup>2)"
      by (rule real_sqrt_le_mono [OF sum_mono2]) (use that in auto)
    finally show ?thesis
      by (simp add: enorm_def)
  qed
  define B where "B \<equiv> \<lambda>r. {x \<in> topspace ?E. enorm x < r}"
  define C where "C \<equiv> \<lambda>r. {x \<in> topspace ?E. enorm x \<le> r}"
  define S where "S \<equiv> \<lambda>r. {x \<in> topspace ?E. enorm x = r}"
  have BC: "B r \<subseteq> C r" and SC: "S r \<subseteq> C r" and disjSB: "disjnt (S r) (B r)" and eqC: "B r \<union> S r = C r" for r
    by (auto simp: B_def C_def S_def disjnt_def)
  consider "n = 1" | "n \<ge> 2"
    using False by linarith
  then have **: "openin ?E (h ` (B r))"
    if "r > 0" and cmh: "continuous_map(subtopology ?E (C r)) ?E h" and injh: "inj_on h (C r)" for r h
  proof cases
    case 1
    define e :: "[real,nat]\<Rightarrow>real" where "e \<equiv> \<lambda>x i. if i = 0 then x else 0"
    define e' :: "(nat\<Rightarrow>real)\<Rightarrow>real" where "e' \<equiv> \<lambda>x. x 0"
    have "continuous_map euclidean euclideanreal (\<lambda>f. f (0::nat))"
      by auto
    then have "continuous_map (subtopology (powertop_real UNIV) {f. \<forall>n\<ge>Suc 0. f n = 0}) euclideanreal (\<lambda>f. f 0)"
      by (metis (mono_tags) continuous_map_from_subtopology euclidean_product_topology)
    then have hom_ee': "homeomorphic_maps euclideanreal (Euclidean_space 1) e e'"
      by (auto simp: homeomorphic_maps_def e_def e'_def continuous_map_in_subtopology Euclidean_space_def)
    have eBr: "e ` {-r<..<r} = B r"
      unfolding B_def e_def C_def
      by(force simp: "1" topspace_Euclidean_space enorm_def power2_eq_square if_distrib [of "\<lambda>x. x * _"] cong: if_cong)
    have in_Cr: "\<And>x. \<lbrakk>-r < x; x < r\<rbrakk> \<Longrightarrow> (\<lambda>i. if i = 0 then x else 0) \<in> C r"
      using \<open>n \<noteq> 0\<close> by (auto simp: C_def topspace_Euclidean_space)
    have inj: "inj_on (e' \<circ> h \<circ> e) {- r<..<r}"
    proof (clarsimp simp: inj_on_def e_def e'_def)
      show "(x::real) = y"
        if f: "h (\<lambda>i. if i = 0 then x else 0) 0 = h (\<lambda>i. if i = 0 then y else 0) 0"
          and "-r < x" "x < r" "-r < y" "y < r"
        for x y :: real
      proof -
        have x: "(\<lambda>i. if i = 0 then x else 0) \<in> C r" and y: "(\<lambda>i. if i = 0 then y else 0) \<in> C r"
          by (blast intro: inj_onD [OF \<open>inj_on h (C r)\<close>] that in_Cr)+
        have "continuous_map (subtopology (Euclidean_space (Suc 0)) (C r)) (Euclidean_space (Suc 0)) h"
          using cmh by (simp add: 1)
        then have "h ` ({x. \<forall>i\<ge>Suc 0. x i = 0} \<inter> C r) \<subseteq> {x. \<forall>i\<ge>Suc 0. x i = 0}"
          by (force simp: Euclidean_space_def subtopology_subtopology continuous_map_def)
        have "h (\<lambda>i. if i = 0 then x else 0) j = h (\<lambda>i. if i = 0 then y else 0) j" for j
        proof (cases j)
          case (Suc j')
          have "h ` ({x. \<forall>i\<ge>Suc 0. x i = 0} \<inter> C r) \<subseteq> {x. \<forall>i\<ge>Suc 0. x i = 0}"
            using continuous_map_image_subset_topspace [OF cmh]
            by (simp add: 1 Euclidean_space_def subtopology_subtopology)
          with Suc f x y show ?thesis
            by (simp add: "1" image_subset_iff)
        qed (use f in blast)
        then have "(\<lambda>i. if i = 0 then x else 0) = (\<lambda>i::nat. if i = 0 then y else 0)"
          by (blast intro: inj_onD [OF \<open>inj_on h (C r)\<close>] that in_Cr)
        then show ?thesis
          by (simp add: fun_eq_iff) presburger
      qed
    qed
    have hom_e': "homeomorphic_map (Euclidean_space 1) euclideanreal e'"
      using hom_ee' homeomorphic_maps_map by blast
    have "openin (Euclidean_space n) (h ` e ` {- r<..<r})"
      unfolding 1
    proof (subst homeomorphic_map_openness [OF hom_e', symmetric])
      show "h ` e ` {- r<..<r} \<subseteq> topspace (Euclidean_space 1)"
        using "1" C_def \<open>\<And>r. B r \<subseteq> C r\<close> cmh continuous_map_image_subset_topspace eBr by fastforce
      have cont: "continuous_on {- r<..<r} (e' \<circ> h \<circ> e)"
      proof (intro continuous_on_compose)
        have "\<And>i. continuous_on {- r<..<r} (\<lambda>x. if i = 0 then x else 0)"
          by (auto simp: continuous_on_topological)
        then show "continuous_on {- r<..<r} e"
          by (force simp: e_def intro: continuous_on_coordinatewise_then_product)
        have subCr: "e ` {- r<..<r} \<subseteq> topspace (subtopology ?E (C r))"
          by (auto simp: eBr \<open>\<And>r. B r \<subseteq> C r\<close>) (auto simp: B_def)
        with cmh show "continuous_on (e ` {- r<..<r}) h"
          by (meson cm_Euclidean_space_iff_continuous_on continuous_on_subset)
        have "h ` (e ` {- r<..<r}) \<subseteq> topspace ?E"
          using subCr cmh by (simp add: continuous_map_def image_subset_iff)
        moreover have "continuous_on (topspace ?E) e'"
          by (metis "1" continuous_map_Euclidean_space_iff hom_ee' homeomorphic_maps_def)
        ultimately show "continuous_on (h ` e ` {- r<..<r}) e'"
          by (simp add: e'_def continuous_on_subset)
      qed
      show "openin euclideanreal (e' ` h ` e ` {- r<..<r})"
        using injective_eq_1d_open_map_UNIV [OF cont] inj by (simp add: image_image is_interval_1)
    qed
    then show ?thesis
      by (simp flip: eBr)
  next
    case 2
    have cloC: "\<And>r. closedin (Euclidean_space n) (C r)"
      unfolding C_def
      by (rule closedin_continuous_map_preimage [OF cm_enorm, of concl:  "{.._}", simplified])
    have cloS: "\<And>r. closedin (Euclidean_space n) (S r)"
      unfolding S_def
      by (rule closedin_continuous_map_preimage [OF cm_enorm, of concl:  "{_}", simplified])
    have C_subset: "C r \<subseteq> UNIV \<rightarrow>\<^sub>E {- \<bar>r\<bar>..\<bar>r\<bar>}"
      using le_enorm \<open>r > 0\<close>
      apply (auto simp: C_def topspace_Euclidean_space abs_le_iff)
       apply (metis add.inverse_neutral le_cases less_minus_iff not_le order_trans)
      by (metis enorm_ge0 not_le order.trans)
    have compactinC: "compactin (Euclidean_space n) (C r)"
      unfolding Euclidean_space_def compactin_subtopology
    proof
      show "compactin (powertop_real UNIV) (C r)"
      proof (rule closed_compactin [OF _ C_subset])
        show "closedin (powertop_real UNIV) (C r)"
          by (metis Euclidean_space_def cloC closedin_Euclidean_space closedin_closed_subtopology topspace_Euclidean_space)
      qed (simp add: compactin_PiE)
    qed (auto simp: C_def topspace_Euclidean_space)
    have compactinS: "compactin (Euclidean_space n) (S r)"
      unfolding Euclidean_space_def compactin_subtopology
    proof
      show "compactin (powertop_real UNIV) (S r)"
      proof (rule closed_compactin)
        show "S r \<subseteq> UNIV \<rightarrow>\<^sub>E {- \<bar>r\<bar>..\<bar>r\<bar>}"
          using C_subset \<open>\<And>r. S r \<subseteq> C r\<close> by blast
        show "closedin (powertop_real UNIV) (S r)"
          by (metis Euclidean_space_def cloS closedin_Euclidean_space closedin_closed_subtopology topspace_Euclidean_space)
      qed (simp add: compactin_PiE)
    qed (auto simp: S_def topspace_Euclidean_space)
    have h_if_B: "\<And>y. y \<in> B r \<Longrightarrow> h y \<in> topspace ?E"
      using B_def \<open>\<And>r. B r \<union> S r = C r\<close> cmh continuous_map_image_subset_topspace by fastforce
    have com_hSr: "compactin (Euclidean_space n) (h ` S r)"
      by (meson \<open>\<And>r. S r \<subseteq> C r\<close> cmh compactinS compactin_subtopology image_compactin)
    have ope_comp_hSr: "openin (Euclidean_space n) (topspace (Euclidean_space n) - h ` S r)"
    proof (rule openin_diff)
      show "closedin (Euclidean_space n) (h ` S r)"
        using Hausdorff_Euclidean_space com_hSr compactin_imp_closedin by blast
    qed auto
    have h_pcs: "h ` (B r) \<in> path_components_of (subtopology ?E (topspace ?E - h ` (S r)))"
    proof (rule lemmaIOD)
      have pc_interval: "path_connectedin (Euclidean_space n) {x \<in> topspace(Euclidean_space n). enorm x \<in> T}"
        if T: "is_interval T" for T
      proof -
        define mul :: "[real, nat \<Rightarrow> real, nat] \<Rightarrow> real" where "mul \<equiv> \<lambda>a x i. a * x i"
        let ?neg = "mul (-1)"
        have neg_neg [simp]: "?neg (?neg x) = x" for x
          by (simp add: mul_def)
        have enorm_mul [simp]: "enorm(mul a x) = abs a * enorm x" for a x
          by (simp add: enorm_def mul_def power_mult_distrib) (metis real_sqrt_abs real_sqrt_mult sum_distrib_left)
        have mul_in_top: "mul a x \<in> topspace ?E"
            if "x \<in> topspace ?E" for a x
          using mul_def that topspace_Euclidean_space by auto
        have neg_in_S: "?neg x \<in> S r"
            if "x \<in> S r" for x r
          using that topspace_Euclidean_space S_def by simp (simp add: mul_def)
        have *: "path_connectedin ?E (S d)"
          if "d \<ge> 0" for d
        proof (cases "d = 0")
          let ?ES = "subtopology ?E (S d)"
          case False
          then have "d > 0"
            using that by linarith
          moreover have "path_connected_space ?ES"
            unfolding path_connected_space_iff_path_component
          proof clarify
            have **: "path_component_of ?ES x y"
              if x: "x \<in> topspace ?ES" and y: "y \<in> topspace ?ES" "x \<noteq> ?neg y" for x y
            proof -
              show ?thesis
                unfolding path_component_of_def pathin_def S_def
              proof (intro exI conjI)
                let ?g = "(\<lambda>x. mul (d / enorm x) x) \<circ> (\<lambda>t i. (1 - t) * x i + t * y i)"
                show "continuous_map (top_of_set {0::real..1}) (subtopology ?E {x \<in> topspace ?E. enorm x = d}) ?g"
                proof (rule continuous_map_compose)
                  let ?Y = "subtopology ?E (- {zero})"
                  have **: False
                    if eq0: "\<And>j. (1 - r) * x j + r * y j = 0"
                      and ne: "x i \<noteq> - y i"
                      and d: "enorm x = d" "enorm y = d"
                      and r: "0 \<le> r" "r \<le> 1"
                    for i r
                  proof -
                    have "mul (1-r) x = ?neg (mul r y)"
                      using eq0 by (simp add: mul_def fun_eq_iff algebra_simps)
                    then have "enorm (mul (1-r) x) = enorm (?neg (mul r y))"
                      by metis
                    with r have "(1-r) * enorm x = r * enorm y"
                      by simp
                    then have r12: "r = 1/2"
                      using \<open>d \<noteq> 0\<close> d by auto
                    show ?thesis
                      using ne eq0 [of i] unfolding r12 by (simp add: algebra_simps)
                  qed
                  show "continuous_map (top_of_set {0..1}) ?Y (\<lambda>t i. (1 - t) * x i + t * y i)"
                    using x y
                    unfolding continuous_map_componentwise_UNIV Euclidean_space_def continuous_map_in_subtopology
                    apply (intro conjI allI continuous_intros)
                          apply (auto simp: zero_def mul_def S_def Euclidean_space_def fun_eq_iff)
                    using ** by blast
                  have cm_enorm': "continuous_map (subtopology (powertop_real UNIV) A) euclideanreal enorm" for A
                    unfolding enorm_def by (intro continuous_intros) auto
                  have "continuous_map ?Y (subtopology ?E {x. enorm x = d}) (\<lambda>x. mul (d / enorm x) x)"
                    unfolding continuous_map_in_subtopology
                  proof (intro conjI)
                    show "continuous_map ?Y (Euclidean_space n) (\<lambda>x. mul (d / enorm x) x)"
                      unfolding continuous_map_in_subtopology Euclidean_space_def mul_def zero_def subtopology_subtopology continuous_map_componentwise_UNIV
                    proof (intro conjI allI cm_enorm' continuous_intros)
                      show "enorm x \<noteq> 0"
                        if "x \<in> topspace (subtopology (powertop_real UNIV) ({x. \<forall>i\<ge>n. x i = 0} \<inter> - {\<lambda>i. 0}))" for x
                        using that by simp (metis abs_le_zero_iff le_enorm not_less)
                    qed auto
                  qed (use \<open>d > 0\<close> enorm_ge0 in auto)
                  moreover have "subtopology ?E {x \<in> topspace ?E. enorm x = d} = subtopology ?E {x. enorm x = d}"
                    by (simp add: subtopology_restrict Collect_conj_eq)
                  ultimately show "continuous_map ?Y (subtopology (Euclidean_space n) {x \<in> topspace (Euclidean_space n). enorm x = d}) (\<lambda>x. mul (d / enorm x) x)"
                    by metis
                qed
                show "?g (0::real) = x" "?g (1::real) = y"
                  using that by (auto simp: S_def zero_def mul_def fun_eq_iff)
              qed
            qed
            obtain a b where a: "a \<in> topspace ?ES" and b: "b \<in> topspace ?ES"
              and "a \<noteq> b" and negab: "?neg a \<noteq> b"
            proof
              let ?v = "\<lambda>j i::nat. if i = j then d else 0"
              show "?v 0 \<in> topspace (subtopology ?E (S d))" "?v 1 \<in> topspace (subtopology ?E (S d))"
                using \<open>n \<ge> 2\<close> \<open>d \<ge> 0\<close> by (auto simp: S_def topspace_Euclidean_space)
              show "?v 0 \<noteq> ?v 1" "?neg (?v 0) \<noteq> (?v 1)"
                using \<open>d > 0\<close> by (auto simp: mul_def fun_eq_iff)
            qed
            show "path_component_of ?ES x y"
              if x: "x \<in> topspace ?ES" and y: "y \<in> topspace ?ES"
              for x y
            proof -
              have "path_component_of ?ES x (?neg x)"
              proof -
                have "path_component_of ?ES x a"
                  by (metis (no_types, opaque_lifting) ** a b \<open>a \<noteq> b\<close> negab path_component_of_trans path_component_of_sym x)
                moreover
                have pa_ab: "path_component_of ?ES a b" using "**" a b negab neg_neg by blast
                then have "path_component_of ?ES a (?neg x)"
                  by (metis "**" \<open>a \<noteq> b\<close> cloS closedin_def neg_in_S path_component_of_equiv topspace_subtopology_subset x)
                ultimately show ?thesis
                  by (meson path_component_of_trans)
              qed
              then show ?thesis
                using "**" x y by force
            qed
          qed
          ultimately show ?thesis
            by (simp add: cloS closedin_subset path_connectedin_def)
        qed (simp add: S_def cong: conj_cong)
        have "path_component_of (subtopology ?E {x \<in> topspace ?E. enorm x \<in> T}) x y"
          if "enorm x = a" "x \<in> topspace ?E" "enorm x \<in> T" "enorm y = b" "y \<in> topspace ?E" "enorm y \<in> T"
          for x y a b
          using that
          proof (induction a b arbitrary: x y rule: linorder_less_wlog)
            case (less a b)
            then have "a \<ge> 0"
              using enorm_ge0 by blast
            with less.hyps have "b > 0"
              by linarith
            show ?case
            proof (rule path_component_of_trans)
              have y'_ts: "mul (a / b) y \<in> topspace ?E"
                using \<open>y \<in> topspace ?E\<close> mul_in_top by blast
              moreover have "enorm (mul (a / b) y) = a"
                unfolding enorm_mul using \<open>0 < b\<close> \<open>0 \<le> a\<close> less.prems by simp
              ultimately have y'_S: "mul (a / b) y \<in> S a"
                using S_def by blast
              have "x \<in> S a"
                using S_def less.prems by blast
              with \<open>x \<in> topspace ?E\<close> y'_ts y'_S
              have "path_component_of (subtopology ?E (S a)) x (mul (a / b) y)"
                by (metis * [OF \<open>a \<ge> 0\<close>] path_connected_space_iff_path_component path_connectedin_def topspace_subtopology_subset)
              moreover
              have "{f \<in> topspace ?E. enorm f = a} \<subseteq> {f \<in> topspace ?E. enorm f \<in> T}"
                using \<open>enorm x = a\<close> \<open>enorm x \<in> T\<close> by force
              ultimately
              show "path_component_of (subtopology ?E {x. x \<in> topspace ?E \<and> enorm x \<in> T}) x (mul (a / b) y)"
                by (simp add: S_def path_component_of_mono)
              have "pathin ?E (\<lambda>t. mul (((1 - t) * b + t * a) / b) y)"
                using \<open>b > 0\<close> \<open>y \<in> topspace ?E\<close>
                unfolding pathin_def Euclidean_space_def mul_def continuous_map_in_subtopology continuous_map_componentwise_UNIV
                by (intro allI conjI continuous_intros) auto
              moreover have "mul (((1 - t) * b + t * a) / b) y \<in> topspace ?E"
                if "t \<in> {0..1}" for t
                using \<open>y \<in> topspace ?E\<close> mul_in_top by blast
                moreover have "enorm (mul (((1 - t) * b + t * a) / b) y) \<in> T"
                  if "t \<in> {0..1}" for t
                proof -
                  have "a \<in> T" "b \<in> T"
                    using less.prems by auto
                  then have "\<bar>(1 - t) * b + t * a\<bar> \<in> T"
                  proof (rule mem_is_interval_1_I [OF T])
                    show "a \<le> \<bar>(1 - t) * b + t * a\<bar>"
                      using that \<open>a \<ge> 0\<close> less.hyps segment_bound_lemma by auto
                    show "\<bar>(1 - t) * b + t * a\<bar> \<le> b"
                      using that \<open>a \<ge> 0\<close> less.hyps by (auto intro: convex_bound_le)
                  qed
                then show ?thesis
                  unfolding enorm_mul \<open>enorm y = b\<close> using that \<open>b > 0\<close> by simp
              qed
              ultimately have pa: "pathin (subtopology ?E {x \<in> topspace ?E. enorm x \<in> T})
                                          (\<lambda>t. mul (((1 - t) * b + t * a) / b) y)"
                by (auto simp: pathin_subtopology)
              have ex_pathin: "\<exists>g. pathin (subtopology ?E {x \<in> topspace ?E. enorm x \<in> T}) g \<and>
                                   g 0 = y \<and> g 1 = mul (a / b) y"
                apply (rule_tac x="\<lambda>t. mul (((1 - t) * b + t * a) / b) y" in exI)
                using \<open>b > 0\<close> pa by (auto simp: mul_def)
              show "path_component_of (subtopology ?E {x. x \<in> topspace ?E \<and> enorm x \<in> T}) (mul (a / b) y) y"
                by (rule path_component_of_sym) (simp add: path_component_of_def ex_pathin)
            qed
          next
            case (refl a)
            then have pc: "path_component_of (subtopology ?E (S (enorm u))) u v"
              if "u \<in> topspace ?E \<inter> S (enorm x)" "v \<in> topspace ?E \<inter> S (enorm u)" for u v
              using * [of a] enorm_ge0 that
              by (auto simp: path_connectedin_def path_connected_space_iff_path_component S_def)
            have sub: "{u \<in> topspace ?E. enorm u = enorm x} \<subseteq> {u \<in> topspace ?E. enorm u \<in> T}"
              using \<open>enorm x \<in> T\<close> by auto
            show ?case
              using pc [of x y] refl by (auto simp: S_def path_component_of_mono [OF _ sub])
          next
            case (sym a b)
            then show ?case
              by (blast intro: path_component_of_sym)
          qed
        then show ?thesis
          by (simp add: path_connectedin_def path_connected_space_iff_path_component)
      qed
      have "h ` S r \<subseteq> topspace ?E"
        by (meson SC cmh compact_imp_compactin_subtopology compactinS compactin_subset_topspace image_compactin)
      moreover
      have "\<not> compact_space ?E "
        by (metis compact_Euclidean_space \<open>n \<noteq> 0\<close>)
      then have "\<not> compactin ?E (topspace ?E)"
        by (simp add: compact_space_def topspace_Euclidean_space)
      then have "h ` S r \<noteq> topspace ?E"
        using com_hSr by auto
      ultimately have top_hSr_ne: "topspace (subtopology ?E (topspace ?E - h ` S r)) \<noteq> {}"
        by auto
      show pc1: "\<exists>T. T \<in> path_components_of (subtopology ?E (topspace ?E - h ` S r)) \<and> h ` B r \<subseteq> T"
      proof (rule exists_path_component_of_superset [OF _ top_hSr_ne])
        have "path_connectedin ?E (h ` B r)"
        proof (rule path_connectedin_continuous_map_image)
          show "continuous_map (subtopology ?E (C r)) ?E h"
            by (simp add: cmh)
          have "path_connectedin ?E (B r)"
            using pc_interval[of "{..<r}"] is_interval_convex_1 unfolding B_def by auto
            then show "path_connectedin (subtopology ?E (C r)) (B r)"
              by (simp add: path_connectedin_subtopology BC)
          qed
          moreover have "h ` B r \<subseteq> topspace ?E - h ` S r"
            apply (auto simp: h_if_B)
            by (metis BC SC disjSB disjnt_iff inj_onD [OF injh] subsetD)
        ultimately show "path_connectedin (subtopology ?E (topspace ?E - h ` S r)) (h ` B r)"
          by (simp add: path_connectedin_subtopology)
      qed metis
      show "\<exists>T. T \<in> path_components_of (subtopology ?E (topspace ?E - h ` S r)) \<and> topspace ?E - h ` (C r) \<subseteq> T"
      proof (rule exists_path_component_of_superset [OF _ top_hSr_ne])
        have eq: "topspace ?E - {x \<in> topspace ?E. enorm x \<le> r} = {x \<in> topspace ?E. r < enorm x}"
          by auto
        have "path_connectedin ?E (topspace ?E - C r)"
          using pc_interval[of "{r<..}"] is_interval_convex_1 unfolding C_def eq by auto
        then have "path_connectedin ?E (topspace ?E - h ` C r)"
          by (metis biglemma [OF \<open>n \<noteq> 0\<close> compactinC cmh injh])
        then show "path_connectedin (subtopology ?E (topspace ?E - h ` S r)) (topspace ?E - h ` C r)"
          by (simp add: Diff_mono SC image_mono path_connectedin_subtopology)
      qed metis
      have "topspace ?E \<inter> (topspace ?E - h ` S r) = h ` B r \<union> (topspace ?E - h ` C r)"         (is "?lhs = ?rhs")
      proof
        show "?lhs \<subseteq> ?rhs"
          using \<open>\<And>r. B r \<union> S r = C r\<close> by auto
        have "h ` B r \<inter> h ` S r = {}"
          by (metis Diff_triv \<open>\<And>r. B r \<union> S r = C r\<close> \<open>\<And>r. disjnt (S r) (B r)\<close> disjnt_def inf_commute inj_on_Un injh)
        then show "?rhs \<subseteq> ?lhs"
          using path_components_of_subset pc1 \<open>\<And>r. B r \<union> S r = C r\<close>
          by (fastforce simp add: h_if_B)
      qed
      then show "\<Union> (path_components_of (subtopology ?E (topspace ?E - h ` S r))) = h ` B r \<union> (topspace ?E - h ` (C r))"
        by (simp add: Union_path_components_of)
      show "T \<noteq> {}"
        if "T \<in> path_components_of (subtopology ?E (topspace ?E - h ` S r))" for T
        using that by (simp add: nonempty_path_components_of)
      show "disjoint (path_components_of (subtopology ?E (topspace ?E - h ` S r)))"
        by (simp add: pairwise_disjoint_path_components_of)
      have "\<not> path_connectedin ?E (topspace ?E - h ` S r)"
      proof (subst biglemma [OF \<open>n \<noteq> 0\<close> compactinS])
        show "continuous_map (subtopology ?E (S r)) ?E h"
          by (metis Un_commute Un_upper1 cmh continuous_map_from_subtopology_mono eqC)
        show "inj_on h (S r)"
          using SC inj_on_subset injh by blast
        show "\<not> path_connectedin ?E (topspace ?E - S r)"
        proof
          have "topspace ?E - S r = {x \<in> topspace ?E. enorm x \<noteq> r}"
            by (auto simp: S_def)
          moreover have "enorm ` {x \<in> topspace ?E. enorm x \<noteq> r} = {0..} - {r}"
          proof
            have "\<exists>x. x \<in> topspace ?E \<and> enorm x \<noteq> r \<and> d = enorm x"
              if "d \<noteq> r" "d \<ge> 0" for d
            proof (intro exI conjI)
              show "(\<lambda>i. if i = 0 then d else 0) \<in> topspace ?E"
                using \<open>n \<noteq> 0\<close> by (auto simp: Euclidean_space_def)
              show "enorm (\<lambda>i. if i = 0 then d else 0) \<noteq> r"  "d = enorm (\<lambda>i. if i = 0 then d else 0)"
                using \<open>n \<noteq> 0\<close> that by simp_all
            qed
            then show "{0..} - {r} \<subseteq> enorm ` {x \<in> topspace ?E. enorm x \<noteq> r}"
              by (auto simp: image_def)
          qed (auto simp: enorm_ge0)
          ultimately have non_r: "enorm ` (topspace ?E - S r) = {0..} - {r}"
            by simp
          have "\<exists>x\<ge>0. x \<noteq> r \<and> r \<le> x"
            by (metis gt_ex le_cases not_le order_trans)
          then have "\<not> is_interval ({0..} - {r})"
            unfolding is_interval_1
            using  \<open>r > 0\<close> by (auto simp: Bex_def)
          then show False
            if "path_connectedin ?E (topspace ?E - S r)"
            using path_connectedin_continuous_map_image [OF cm_enorm that] by (simp add: is_interval_path_connected_1 non_r)
        qed
      qed
      then have "\<not> path_connected_space (subtopology ?E (topspace ?E - h ` S r))"
        by (simp add: path_connectedin_def)
      then show "\<nexists>T. path_components_of (subtopology ?E (topspace ?E - h ` S r)) \<subseteq> {T}"
        by (simp add: path_components_of_subset_singleton)
    qed
    moreover have "openin ?E A"
      if "A \<in> path_components_of (subtopology ?E (topspace ?E - h ` (S r)))" for A
      using locally_path_connected_Euclidean_space [of n] that ope_comp_hSr
      by (simp add: locally_path_connected_space_open_path_components)
    ultimately show ?thesis by metis
  qed
  have "\<exists>T. openin ?E T \<and> f x \<in> T \<and> T \<subseteq> f ` U"
    if "x \<in> U" for x
  proof -
    have x: "x \<in> topspace ?E"
      by (meson U in_mono openin_subset that)
    obtain V where V: "openin (powertop_real UNIV) V" and Ueq: "U = V \<inter> {x. \<forall>i\<ge>n. x i = 0}"
      using U by (auto simp: openin_subtopology Euclidean_space_def)
    with \<open>x \<in> U\<close> have "x \<in> V" by blast
    then obtain T where Tfin: "finite {i. T i \<noteq> UNIV}" and Topen: "\<And>i. open (T i)"
      and Tx: "x \<in> Pi\<^sub>E UNIV T" and TV: "Pi\<^sub>E UNIV T \<subseteq> V"
      using V by (force simp: openin_product_topology_alt)
    have "\<exists>e>0. \<forall>x'. \<bar>x' - x i\<bar> < e \<longrightarrow> x' \<in> T i" for i
      using Topen [of i] Tx by (auto simp: open_real)
    then obtain \<beta> where B0: "\<And>i. \<beta> i > 0" and BT: "\<And>i x'. \<bar>x' - x i\<bar> < \<beta> i \<Longrightarrow> x' \<in> T i"
      by metis
    define r where "r \<equiv> Min (insert 1 (\<beta> ` {i. T i \<noteq> UNIV}))"
    have "r > 0"
      by (simp add: B0 Tfin r_def)
    have inU: "y \<in> U"
      if y: "y \<in> topspace ?E" and yxr: "\<And>i. i<n \<Longrightarrow> \<bar>y i - x i\<bar> < r" for y
    proof -
      have "y i \<in> T i" for i
      proof (cases "T i = UNIV")
        show "y i \<in> T i" if "T i \<noteq> UNIV"
        proof (cases "i < n")
          case True
          then show ?thesis
            using yxr [OF True] that by (simp add: r_def BT Tfin)
        next
          case False
          then show ?thesis
            using B0 Ueq \<open>x \<in> U\<close> topspace_Euclidean_space y by (force intro: BT)
        qed
      qed auto
      with TV have "y \<in> V" by auto
      then show ?thesis
        using that by (auto simp: Ueq topspace_Euclidean_space)
    qed
    have xinU: "(\<lambda>i. x i + y i) \<in> U" if "y \<in> C(r/2)" for y
    proof (rule inU)
      have y: "y \<in> topspace ?E"
        using C_def that by blast
      show "(\<lambda>i. x i + y i) \<in> topspace ?E"
        using x y by (simp add: topspace_Euclidean_space)
      have "enorm y \<le> r/2"
        using that by (simp add: C_def)
      then show "\<bar>x i + y i - x i\<bar> < r" if "i < n" for i
        using le_enorm enorm_ge0 that \<open>0 < r\<close> leI order_trans by fastforce
    qed
    show ?thesis
    proof (intro exI conjI)
      show "openin ?E ((f \<circ> (\<lambda>y i. x i + y i)) ` B (r/2))"
      proof (rule **)
        have "continuous_map (subtopology ?E (C(r/2))) (subtopology ?E U) (\<lambda>y i. x i + y i)"
          by (auto simp: xinU continuous_map_in_subtopology
              intro!: continuous_intros continuous_map_Euclidean_space_add x)
        then show "continuous_map (subtopology ?E (C(r/2))) ?E (f \<circ> (\<lambda>y i. x i + y i))"
          by (rule continuous_map_compose) (simp add: cmf)
        show "inj_on (f \<circ> (\<lambda>y i. x i + y i)) (C(r/2))"
        proof (clarsimp simp add: inj_on_def C_def topspace_Euclidean_space simp del: divide_const_simps)
          show "y' = y"
            if ey: "enorm y \<le> r / 2" and ey': "enorm y' \<le> r / 2"
              and y0: "\<forall>i\<ge>n. y i = 0" and y'0: "\<forall>i\<ge>n. y' i = 0"
              and feq: "f (\<lambda>i. x i + y' i) = f (\<lambda>i. x i + y i)"
            for y' y :: "nat \<Rightarrow> real"
          proof -
            have "(\<lambda>i. x i + y i) \<in> U"
            proof (rule inU)
              show "(\<lambda>i. x i + y i) \<in> topspace ?E"
                using topspace_Euclidean_space x y0 by auto
              show "\<bar>x i + y i - x i\<bar> < r" if "i < n" for i
                using ey le_enorm [of _ y] \<open>r > 0\<close> that by fastforce
            qed
            moreover have "(\<lambda>i. x i + y' i) \<in> U"
            proof (rule inU)
              show "(\<lambda>i. x i + y' i) \<in> topspace ?E"
                using topspace_Euclidean_space x y'0 by auto
              show "\<bar>x i + y' i - x i\<bar> < r" if "i < n" for i
                using ey' le_enorm [of _ y'] \<open>r > 0\<close> that by fastforce
            qed
            ultimately have "(\<lambda>i. x i + y' i) = (\<lambda>i. x i + y i)"
              using feq by (meson \<open>inj_on f U\<close> inj_on_def)
            then show ?thesis
              by (auto simp: fun_eq_iff)
          qed
        qed
      qed (simp add: \<open>0 < r\<close>)
      have "x \<in> (\<lambda>y i. x i + y i) ` B (r / 2)"
      proof
        show "x = (\<lambda>i. x i + zero i)"
          by (simp add: zero_def)
      qed (auto simp: B_def \<open>r > 0\<close>)
      then show "f x \<in> (f \<circ> (\<lambda>y i. x i + y i)) ` B (r/2)"
        by (metis image_comp image_eqI)
      show "(f \<circ> (\<lambda>y i. x i + y i)) ` B (r/2) \<subseteq> f ` U"
        using \<open>\<And>r. B r \<subseteq> C r\<close> xinU by fastforce
    qed
  qed
  then show ?thesis
    using openin_subopen by force
qed


corollary invariance_of_domain_Euclidean_space_embedding_map:
  assumes "openin (Euclidean_space n) U"
    and cmf: "continuous_map(subtopology (Euclidean_space n) U) (Euclidean_space n) f"
    and "inj_on f U"
  shows "embedding_map(subtopology (Euclidean_space n) U) (Euclidean_space n) f"
proof (rule injective_open_imp_embedding_map [OF cmf])
  show "open_map (subtopology (Euclidean_space n) U) (Euclidean_space n) f"
    unfolding open_map_def
    by (meson assms continuous_map_from_subtopology_mono inj_on_subset invariance_of_domain_Euclidean_space openin_imp_subset openin_trans_full)
  show "inj_on f (topspace (subtopology (Euclidean_space n) U))"
    using assms openin_subset topspace_subtopology_subset by fastforce
qed

corollary invariance_of_domain_Euclidean_space_gen:
  assumes "n \<le> m" and U: "openin (Euclidean_space m) U"
    and cmf: "continuous_map(subtopology (Euclidean_space m) U) (Euclidean_space n) f"
    and "inj_on f U"
  shows "openin (Euclidean_space n) (f ` U)"
proof -
  have *: "Euclidean_space n = subtopology (Euclidean_space m) (topspace(Euclidean_space n))"
    by (metis Euclidean_space_def \<open>n \<le> m\<close> inf.absorb_iff2 subset_Euclidean_space subtopology_subtopology topspace_Euclidean_space)
  moreover have "U \<subseteq> topspace (subtopology (Euclidean_space m) U)"
    by (metis U inf.absorb_iff2 openin_subset openin_subtopology openin_topspace)
  ultimately show ?thesis
    by (metis (no_types) U \<open>inj_on f U\<close> cmf continuous_map_in_subtopology inf.absorb_iff2
        inf.orderE invariance_of_domain_Euclidean_space openin_imp_subset openin_subtopology openin_topspace)
qed

corollary invariance_of_domain_Euclidean_space_embedding_map_gen:
  assumes "n \<le> m" and U: "openin (Euclidean_space m) U"
    and cmf: "continuous_map(subtopology (Euclidean_space m) U) (Euclidean_space n) f"
    and "inj_on f U"
  shows "embedding_map(subtopology (Euclidean_space m) U) (Euclidean_space n) f"
  proof (rule injective_open_imp_embedding_map [OF cmf])
  show "open_map (subtopology (Euclidean_space m) U) (Euclidean_space n) f"
    by (meson U \<open>n \<le> m\<close> \<open>inj_on f U\<close> cmf continuous_map_from_subtopology_mono invariance_of_domain_Euclidean_space_gen open_map_def openin_open_subtopology subset_inj_on)
  show "inj_on f (topspace (subtopology (Euclidean_space m) U))"
    using assms openin_subset topspace_subtopology_subset by fastforce
qed


subsection\<open>Relating two variants of Euclidean space, one within product topology.    \<close>

proposition homeomorphic_maps_Euclidean_space_euclidean_gen_OLD:
  fixes B :: "'n::euclidean_space set"
  assumes "finite B" "independent B" and orth: "pairwise orthogonal B" and n: "card B = n"
  obtains f g where "homeomorphic_maps (Euclidean_space n) (top_of_set (span B)) f g"
proof -
  note representation_basis [OF \<open>independent B\<close>, simp]
  obtain b where injb: "inj_on b {..<n}" and beq: "b ` {..<n} = B"
    using finite_imp_nat_seg_image_inj_on [OF \<open>finite B\<close>]
    by (metis n card_Collect_less_nat card_image lessThan_def)
  then have biB: "\<And>i. i < n \<Longrightarrow> b i \<in> B"
    by force
  have repr: "\<And>v. v \<in> span B \<Longrightarrow> (\<Sum>i<n. representation B v (b i) *\<^sub>R b i) = v"
    using real_vector.sum_representation_eq [OF \<open>independent B\<close> _ \<open>finite B\<close>]
    by (metis (no_types, lifting) injb beq order_refl sum.reindex_cong)
  let ?f = "\<lambda>x. \<Sum>i<n. x i *\<^sub>R b i"
  let ?g = "\<lambda>v i. if i < n then representation B v (b i) else 0"
  show thesis
  proof
    show "homeomorphic_maps (Euclidean_space n) (top_of_set (span B)) ?f ?g"
      unfolding homeomorphic_maps_def
    proof (intro conjI)
      have *: "continuous_map euclidean (top_of_set (span B)) ?f"
        by (metis (mono_tags) biB continuous_map_span_sum lessThan_iff)
      show "continuous_map (Euclidean_space n) (top_of_set (span B)) ?f"
        unfolding Euclidean_space_def
        by (rule continuous_map_from_subtopology) (simp add: euclidean_product_topology *)
      show "continuous_map (top_of_set (span B)) (Euclidean_space n) ?g"
        unfolding Euclidean_space_def
        by (auto simp: continuous_map_in_subtopology continuous_map_componentwise_UNIV continuous_on_representation \<open>independent B\<close> biB orth pairwise_orthogonal_imp_finite)
      have [simp]: "\<And>x i. i<n \<Longrightarrow> x i *\<^sub>R b i \<in> span B"
        by (simp add: biB span_base span_scale)
      have "representation B (?f x) (b j) = x j"
        if 0: "\<forall>i\<ge>n. x i = (0::real)" and "j < n" for x j
      proof -
        have "representation B (?f x) (b j) = (\<Sum>i<n. representation B (x i *\<^sub>R b i) (b j))"
          by (subst real_vector.representation_sum) (auto simp add: \<open>independent B\<close>)
        also have "... = (\<Sum>i<n. x i * representation B (b i) (b j))"
          by (simp add: assms(2) biB representation_scale span_base)
        also have "... = (\<Sum>i<n. if b j = b i then x i else 0)"
          by (simp add: biB if_distrib cong: if_cong)
        also have "... = x j"
          using that inj_on_eq_iff [OF injb] by auto
        finally show ?thesis .
      qed
      then show "\<forall>x\<in>topspace (Euclidean_space n). ?g (?f x) = x"
        by (auto simp: Euclidean_space_def)
      show "\<forall>y\<in>topspace (top_of_set (span B)). ?f (?g y) = y"
        using repr by (auto simp: Euclidean_space_def)
    qed
  qed
qed

proposition homeomorphic_maps_Euclidean_space_euclidean_gen:
  fixes B :: "'n::euclidean_space set"
  assumes "independent B" and orth: "pairwise orthogonal B" and n: "card B = n"
    and 1: "\<And>u. u \<in> B \<Longrightarrow> norm u = 1"
  obtains f g where "homeomorphic_maps (Euclidean_space n) (top_of_set (span B)) f g"
    and "\<And>x. x \<in> topspace (Euclidean_space n) \<Longrightarrow> (norm (f x))\<^sup>2 = (\<Sum>i<n. (x i)\<^sup>2)"
proof -
  note representation_basis [OF \<open>independent B\<close>, simp]
  have "finite B"
    using \<open>independent B\<close> finiteI_independent by metis
  obtain b where injb: "inj_on b {..<n}" and beq: "b ` {..<n} = B"
    using finite_imp_nat_seg_image_inj_on [OF \<open>finite B\<close>]
    by (metis n card_Collect_less_nat card_image lessThan_def)
  then have biB: "\<And>i. i < n \<Longrightarrow> b i \<in> B"
    by force
  have "0 \<notin> B"
    using \<open>independent B\<close> dependent_zero by blast
  have [simp]: "b i \<bullet> b j = (if j = i then 1 else 0)"
    if "i < n" "j < n" for i j
  proof (cases "i = j")
    case True
    with 1 that show ?thesis
      by (auto simp: norm_eq_sqrt_inner biB)
  next
    case False
    then have "b i \<noteq> b j"
      by (meson inj_onD injb lessThan_iff that)
    then show ?thesis
      using orth by (auto simp: orthogonal_def pairwise_def norm_eq_sqrt_inner that biB)
  qed
  have [simp]: "\<And>x i. i<n \<Longrightarrow> x i *\<^sub>R b i \<in> span B"
    by (simp add: biB span_base span_scale)
  have repr: "\<And>v. v \<in> span B \<Longrightarrow> (\<Sum>i<n. representation B v (b i) *\<^sub>R b i) = v"
    using real_vector.sum_representation_eq [OF \<open>independent B\<close> _ \<open>finite B\<close>]
    by (metis (no_types, lifting) injb beq order_refl sum.reindex_cong)
    define f where "f \<equiv> \<lambda>x. \<Sum>i<n. x i *\<^sub>R b i"
    define g where "g \<equiv> \<lambda>v i. if i < n then representation B v (b i) else 0"
  show thesis
  proof
    show "homeomorphic_maps (Euclidean_space n) (top_of_set (span B)) f g"
      unfolding homeomorphic_maps_def
    proof (intro conjI)
      have *: "continuous_map euclidean (top_of_set (span B)) f"
        unfolding f_def
        by (rule continuous_map_span_sum) (use biB \<open>0 \<notin> B\<close> in auto)
      show "continuous_map (Euclidean_space n) (top_of_set (span B)) f"
        unfolding Euclidean_space_def
        by (rule continuous_map_from_subtopology) (simp add: euclidean_product_topology *)
      show "continuous_map (top_of_set (span B)) (Euclidean_space n) g"
        unfolding Euclidean_space_def g_def
        by (auto simp: continuous_map_in_subtopology continuous_map_componentwise_UNIV continuous_on_representation \<open>independent B\<close> biB orth pairwise_orthogonal_imp_finite)
      have "representation B (f x) (b j) = x j"
        if 0: "\<forall>i\<ge>n. x i = (0::real)" and "j < n" for x j
      proof -
        have "representation B (f x) (b j) = (\<Sum>i<n. representation B (x i *\<^sub>R b i) (b j))"
          unfolding f_def
          by (subst real_vector.representation_sum) (auto simp add: \<open>independent B\<close>)
        also have "... = (\<Sum>i<n. x i * representation B (b i) (b j))"
          by (simp add: \<open>independent B\<close> biB representation_scale span_base)
        also have "... = (\<Sum>i<n. if b j = b i then x i else 0)"
          by (simp add: biB if_distrib cong: if_cong)
        also have "... = x j"
          using that inj_on_eq_iff [OF injb] by auto
        finally show ?thesis .
      qed
      then show "\<forall>x\<in>topspace (Euclidean_space n). g (f x) = x"
        by (auto simp: Euclidean_space_def f_def g_def)
      show "\<forall>y\<in>topspace (top_of_set (span B)). f (g y) = y"
        using repr by (auto simp: Euclidean_space_def f_def g_def)
    qed
    show normeq: "(norm (f x))\<^sup>2 = (\<Sum>i<n. (x i)\<^sup>2)" if "x \<in> topspace (Euclidean_space n)" for x
      unfolding f_def  dot_square_norm [symmetric]
      by (simp add: power2_eq_square inner_sum_left inner_sum_right if_distrib biB cong: if_cong)
  qed
qed

corollary homeomorphic_maps_Euclidean_space_euclidean:
  obtains f :: "(nat \<Rightarrow> real) \<Rightarrow> 'n::euclidean_space" and g
  where "homeomorphic_maps (Euclidean_space (DIM('n))) euclidean f g"
  by (force intro: homeomorphic_maps_Euclidean_space_euclidean_gen [OF independent_Basis orthogonal_Basis refl norm_Basis])

lemma homeomorphic_maps_nsphere_euclidean_sphere:
  fixes B :: "'n::euclidean_space set"
  assumes B: "independent B" and orth: "pairwise orthogonal B" and n: "card B = n" and "n \<noteq> 0"
    and 1: "\<And>u. u \<in> B \<Longrightarrow> norm u = 1"
  obtains f :: "(nat \<Rightarrow> real) \<Rightarrow> 'n::euclidean_space" and g
  where "homeomorphic_maps (nsphere(n - 1)) (top_of_set (sphere 0 1 \<inter> span B)) f g"
proof -
  have "finite B"
    using \<open>independent B\<close> finiteI_independent by metis
  obtain f g where fg: "homeomorphic_maps (Euclidean_space n) (top_of_set (span B)) f g"
    and normf: "\<And>x. x \<in> topspace (Euclidean_space n) \<Longrightarrow> (norm (f x))\<^sup>2 = (\<Sum>i<n. (x i)\<^sup>2)"
    using homeomorphic_maps_Euclidean_space_euclidean_gen [OF B orth n 1]
    by blast
  obtain b where injb: "inj_on b {..<n}" and beq: "b ` {..<n} = B"
    using finite_imp_nat_seg_image_inj_on [OF \<open>finite B\<close>]
    by (metis n card_Collect_less_nat card_image lessThan_def)
  then have biB: "\<And>i. i < n \<Longrightarrow> b i \<in> B"
    by force
  have [simp]: "\<And>i. i < n \<Longrightarrow> b i \<noteq> 0"
    using \<open>independent B\<close> biB dependent_zero by fastforce
  have [simp]: "b i \<bullet> b j = (if j = i then (norm (b i))\<^sup>2 else 0)"
    if "i < n" "j < n" for i j
  proof (cases "i = j")
    case False
    then have "b i \<noteq> b j"
      by (meson inj_onD injb lessThan_iff that)
    then show ?thesis
      using orth by (auto simp: orthogonal_def pairwise_def norm_eq_sqrt_inner that biB)
  qed (auto simp: norm_eq_sqrt_inner)
  have [simp]: "Suc (n - Suc 0) = n"
    using Suc_pred \<open>n \<noteq> 0\<close> by blast
  then have [simp]: "{..card B - Suc 0} = {..<card B}"
    using n by fastforce
  show thesis
  proof
    have 1: "norm (f x) = 1"
      if "(\<Sum>i<card B. (x i)\<^sup>2) = (1::real)" "x \<in> topspace (Euclidean_space n)" for x
    proof -
      have "norm (f x)^2 = 1"
        using normf that by (simp add: n)
      with that show ?thesis
        by (simp add: power2_eq_imp_eq)
    qed
    have "homeomorphic_maps (nsphere (n - 1)) (top_of_set (span B \<inter> sphere 0 1)) f g"
      unfolding nsphere_def subtopology_subtopology [symmetric]
      proof (rule homeomorphic_maps_subtopologies_alt)
  show "homeomorphic_maps (Euclidean_space (Suc (n - 1))) (top_of_set (span B)) f g"
      using fg by (force simp add: )
    show "f ` (topspace (Euclidean_space (Suc (n - 1))) \<inter> {x. (\<Sum>i\<le>n - 1. (x i)\<^sup>2) = 1}) \<subseteq> sphere 0 1"
      using n by (auto simp: image_subset_iff Euclidean_space_def 1)
    have "(\<Sum>i\<le>n - Suc 0. (g u i)\<^sup>2) = 1"
      if "u \<in> span B" and "norm (u::'n) = 1" for u
    proof -
      obtain v where [simp]: "u = f v" "v \<in> topspace (Euclidean_space n)"
        using fg unfolding homeomorphic_maps_map subset_iff
        by (metis \<open>u \<in> span B\<close> homeomorphic_imp_surjective_map image_eqI topspace_euclidean_subtopology)
      then have [simp]: "g (f v) = v"
        by (meson fg homeomorphic_maps_map)
      have fv21: "norm (f v) ^ 2 = 1"
        using that by simp
      show ?thesis
        using that normf fv21 \<open>v \<in> topspace (Euclidean_space n)\<close> n by force
    qed
    then show "g ` (topspace (top_of_set (span B)) \<inter> sphere 0 1) \<subseteq> {x. (\<Sum>i\<le>n - 1. (x i)\<^sup>2) = 1}"
      by auto
  qed
  then show "homeomorphic_maps (nsphere(n - 1)) (top_of_set (sphere 0 1 \<inter> span B)) f g"
    by (simp add: inf_commute)
  qed
qed


subsection\<open> Invariance of dimension and domain\<close>

lemma homeomorphic_maps_iff_homeomorphism [simp]:
   "homeomorphic_maps (top_of_set S) (top_of_set T) f g \<longleftrightarrow> homeomorphism S T f g"
  unfolding homeomorphic_maps_def homeomorphism_def by force

lemma homeomorphic_space_iff_homeomorphic [simp]:
   "(top_of_set S) homeomorphic_space (top_of_set T) \<longleftrightarrow> S homeomorphic T"
  by (simp add: homeomorphic_def homeomorphic_space_def)

lemma homeomorphic_subspace_Euclidean_space:
  fixes S :: "'a::euclidean_space set"
  assumes "subspace S"
  shows "top_of_set S homeomorphic_space Euclidean_space n \<longleftrightarrow> dim S = n"
proof -
  obtain B where B: "B \<subseteq> S" "independent B" "span B = S" "card B = dim S"
           and orth: "pairwise orthogonal B" and 1: "\<And>x. x \<in> B \<Longrightarrow> norm x = 1"
    by (metis assms orthonormal_basis_subspace)
  then have "finite B"
    by (simp add: pairwise_orthogonal_imp_finite)
  have "top_of_set S homeomorphic_space top_of_set (span B)"
    unfolding homeomorphic_space_iff_homeomorphic
    by (auto simp: assms B intro: homeomorphic_subspaces)
  also have "\<dots> homeomorphic_space Euclidean_space (dim S)"
    unfolding homeomorphic_space_def
    using homeomorphic_maps_Euclidean_space_euclidean_gen [OF \<open>independent B\<close> orth] homeomorphic_maps_sym 1 B
    by metis
  finally have "top_of_set S homeomorphic_space Euclidean_space (dim S)" .
  then show ?thesis
    using homeomorphic_space_sym homeomorphic_space_trans invariance_of_dimension_Euclidean_space by blast
qed

lemma homeomorphic_subspace_Euclidean_space_dim:
  fixes S :: "'a::euclidean_space set"
  assumes "subspace S"
  shows "top_of_set S homeomorphic_space Euclidean_space (dim S)"
  by (simp add: homeomorphic_subspace_Euclidean_space assms)

lemma homeomorphic_subspaces_eq:
  fixes S T:: "'a::euclidean_space set"
  assumes "subspace S" "subspace T"
  shows "S homeomorphic T \<longleftrightarrow> dim S = dim T"
proof
  show "dim S = dim T"
    if "S homeomorphic T"
  proof -
    have "Euclidean_space (dim S) homeomorphic_space top_of_set S"
      using \<open>subspace S\<close> homeomorphic_space_sym homeomorphic_subspace_Euclidean_space_dim by blast
    also have "\<dots> homeomorphic_space top_of_set T"
      by (simp add: that)
    also have "\<dots> homeomorphic_space Euclidean_space (dim T)"
      by (simp add: homeomorphic_subspace_Euclidean_space assms)
    finally have "Euclidean_space (dim S) homeomorphic_space Euclidean_space (dim T)" .
    then show ?thesis
      by (simp add: invariance_of_dimension_Euclidean_space)
  qed
next
  show "S homeomorphic T"
    if "dim S = dim T"
    by (metis that assms homeomorphic_subspaces)
qed

lemma homeomorphic_affine_Euclidean_space:
  assumes "affine S"
  shows "top_of_set S homeomorphic_space Euclidean_space n \<longleftrightarrow> aff_dim S = n"
   (is "?X homeomorphic_space ?E \<longleftrightarrow> aff_dim S = n")
proof (cases "S = {}")
  case True
  with assms show ?thesis
    using homeomorphic_empty_space nonempty_Euclidean_space by fastforce
next
  case False
  then obtain a where "a \<in> S"
    by force
  have "(?X homeomorphic_space ?E)
       = (top_of_set (image (\<lambda>x. -a + x) S) homeomorphic_space ?E)"
  proof
    show "top_of_set ((+) (- a) ` S) homeomorphic_space ?E"
      if "?X homeomorphic_space ?E"
      using that
      by (meson homeomorphic_space_iff_homeomorphic homeomorphic_space_sym homeomorphic_space_trans homeomorphic_translation)
    show "?X homeomorphic_space ?E"
      if "top_of_set ((+) (- a) ` S) homeomorphic_space ?E"
      using that
      by (meson homeomorphic_space_iff_homeomorphic homeomorphic_space_trans homeomorphic_translation)
  qed
  also have "\<dots> \<longleftrightarrow> aff_dim S = n"
    by (metis \<open>a \<in> S\<close> aff_dim_eq_dim affine_diffs_subspace affine_hull_eq assms homeomorphic_subspace_Euclidean_space of_nat_eq_iff)
  finally show ?thesis .
qed


corollary invariance_of_domain_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and "subspace U" "subspace V" and VU: "dim V \<le> dim U"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S"
    shows "openin (top_of_set V) (f ` S)"
proof -
  have "S \<subseteq> U"
    using openin_imp_subset [OF ope] .
  have Uhom: "top_of_set U homeomorphic_space Euclidean_space (dim U)"
   and Vhom: "top_of_set V homeomorphic_space Euclidean_space (dim V)"
    by (simp_all add: assms homeomorphic_subspace_Euclidean_space_dim)
  then obtain \<phi> \<phi>' where hom: "homeomorphic_maps (top_of_set U) (Euclidean_space (dim U)) \<phi> \<phi>'"
    by (auto simp: homeomorphic_space_def)
  obtain \<psi> \<psi>' where \<psi>: "homeomorphic_map (top_of_set V) (Euclidean_space (dim V)) \<psi>"
              and \<psi>'\<psi>: "\<forall>x\<in>V. \<psi>' (\<psi> x) = x"
    using Vhom by (auto simp: homeomorphic_space_def homeomorphic_maps_map)
  have "((\<psi> \<circ> f \<circ> \<phi>') o \<phi>) ` S = (\<psi> o f) ` S"
  proof (rule image_cong [OF refl])
    show "(\<psi> \<circ> f \<circ> \<phi>' \<circ> \<phi>) x = (\<psi> \<circ> f) x" if "x \<in> S" for x
      using that unfolding o_def
      by (metis \<open>S \<subseteq> U\<close> hom homeomorphic_maps_map in_mono topspace_euclidean_subtopology)
  qed
  moreover
  have "openin (Euclidean_space (dim V)) ((\<psi> \<circ> f \<circ> \<phi>') ` \<phi> ` S)"
  proof (rule invariance_of_domain_Euclidean_space_gen [OF VU])
    show "openin (Euclidean_space (dim U)) (\<phi> ` S)"
      using homeomorphic_map_openness_eq hom homeomorphic_maps_map ope by blast
    show "continuous_map (subtopology (Euclidean_space (dim U)) (\<phi> ` S)) (Euclidean_space (dim V)) (\<psi> \<circ> f \<circ> \<phi>')"
    proof (intro continuous_map_compose)
      have "continuous_on ({x. \<forall>i\<ge>dim U. x i = 0} \<inter> \<phi> ` S) \<phi>'"
        if "continuous_on {x. \<forall>i\<ge>dim U. x i = 0} \<phi>'"
        using that by (force elim: continuous_on_subset)
      moreover have "\<phi>' ` ({x. \<forall>i\<ge>dim U. x i = 0} \<inter> \<phi> ` S) \<subseteq> S"
        if "\<forall>x\<in>U. \<phi>' (\<phi> x) = x"
        using that \<open>S \<subseteq> U\<close> by fastforce
      ultimately show "continuous_map (subtopology (Euclidean_space (dim U)) (\<phi> ` S)) (top_of_set S) \<phi>'"
        using hom unfolding homeomorphic_maps_def
        by (simp add:  Euclidean_space_def subtopology_subtopology euclidean_product_topology)
      show "continuous_map (top_of_set S) (top_of_set V) f"
        by (simp add: contf fim)
      show "continuous_map (top_of_set V) (Euclidean_space (dim V)) \<psi>"
        by (simp add: \<psi> homeomorphic_imp_continuous_map)
    qed
    show "inj_on (\<psi> \<circ> f \<circ> \<phi>') (\<phi> ` S)"
      using injf hom
      unfolding inj_on_def homeomorphic_maps_map
      by simp (metis \<open>S \<subseteq> U\<close> \<psi>'\<psi> fim imageI subsetD)
  qed
  ultimately have "openin (Euclidean_space (dim V)) (\<psi> ` f ` S)"
    by (simp add: image_comp)
  then show ?thesis
    by (simp add: fim homeomorphic_map_openness_eq [OF \<psi>])
qed

lemma invariance_of_domain:
  fixes f :: "'a \<Rightarrow> 'a::euclidean_space"
  assumes "continuous_on S f" "open S" "inj_on f S" shows "open(f ` S)"
  using invariance_of_domain_subspaces [of UNIV S UNIV] assms by (force simp add: )

corollary invariance_of_dimension_subspaces:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and "subspace U" "subspace V"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "dim U \<le> dim V"
proof -
  have "False" if "dim V < dim U"
  proof -
    obtain T where "subspace T" "T \<subseteq> U" "dim T = dim V"
      using choose_subspace_of_subspace [of "dim V" U]
      by (metis \<open>dim V < dim U\<close> assms(2) order.strict_implies_order span_eq_iff)
    then have "V homeomorphic T"
      by (simp add: \<open>subspace V\<close> homeomorphic_subspaces)
    then obtain h k where homhk: "homeomorphism V T h k"
      using homeomorphic_def  by blast
    have "continuous_on S (h \<circ> f)"
      by (meson contf continuous_on_compose continuous_on_subset fim homeomorphism_cont1 homhk)
    moreover have "(h \<circ> f) ` S \<subseteq> U"
      using \<open>T \<subseteq> U\<close> fim homeomorphism_image1 homhk by fastforce
    moreover have "inj_on (h \<circ> f) S"
      apply (clarsimp simp: inj_on_def)
      by (metis fim homeomorphism_apply1 homhk image_subset_iff inj_onD injf)
    ultimately have ope_hf: "openin (top_of_set U) ((h \<circ> f) ` S)"
      using invariance_of_domain_subspaces [OF ope \<open>subspace U\<close> \<open>subspace U\<close>] by blast
    have "(h \<circ> f) ` S \<subseteq> T"
      using fim homeomorphism_image1 homhk by fastforce
    then have "dim ((h \<circ> f) ` S) \<le> dim T"
      by (rule dim_subset)
    also have "dim ((h \<circ> f) ` S) = dim U"
      using \<open>S \<noteq> {}\<close> \<open>subspace U\<close>
      by (blast intro: dim_openin ope_hf)
    finally show False
      using \<open>dim V < dim U\<close> \<open>dim T = dim V\<close> by simp
  qed
  then show ?thesis
    using not_less by blast
qed

corollary invariance_of_domain_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and aff: "affine U" "affine V" "aff_dim V \<le> aff_dim U"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S"
    shows "openin (top_of_set V) (f ` S)"
proof (cases "S = {}")
  case False
  obtain a b where "a \<in> S" "a \<in> U" "b \<in> V"
    using False fim ope openin_contains_cball by fastforce
  have "openin (top_of_set ((+) (- b) ` V)) (((+) (- b) \<circ> f \<circ> (+) a) ` (+) (- a) ` S)"
  proof (rule invariance_of_domain_subspaces)
    show "openin (top_of_set ((+) (- a) ` U)) ((+) (- a) ` S)"
      by (metis ope homeomorphism_imp_open_map homeomorphism_translation translation_galois)
    show "subspace ((+) (- a) ` U)"
      by (simp add: \<open>a \<in> U\<close> affine_diffs_subspace_subtract \<open>affine U\<close> cong: image_cong_simp)
    show "subspace ((+) (- b) ` V)"
      by (simp add: \<open>b \<in> V\<close> affine_diffs_subspace_subtract \<open>affine V\<close> cong: image_cong_simp)
    show "dim ((+) (- b) ` V) \<le> dim ((+) (- a) ` U)"
      by (metis \<open>a \<in> U\<close> \<open>b \<in> V\<close> aff_dim_eq_dim affine_hull_eq aff of_nat_le_iff)
    show "continuous_on ((+) (- a) ` S) ((+) (- b) \<circ> f \<circ> (+) a)"
      by (metis contf continuous_on_compose homeomorphism_cont2 homeomorphism_translation translation_galois)
    show "((+) (- b) \<circ> f \<circ> (+) a) ` (+) (- a) ` S \<subseteq> (+) (- b) ` V"
      using fim by auto
    show "inj_on ((+) (- b) \<circ> f \<circ> (+) a) ((+) (- a) ` S)"
      by (auto simp: inj_on_def) (meson inj_onD injf)
  qed
  then show ?thesis
    by (metis (no_types, lifting) homeomorphism_imp_open_map homeomorphism_translation image_comp translation_galois)
qed auto

corollary invariance_of_dimension_affine_sets:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ope: "openin (top_of_set U) S"
      and aff: "affine U" "affine V"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> V"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "aff_dim U \<le> aff_dim V"
proof -
  obtain a b where "a \<in> S" "a \<in> U" "b \<in> V"
    using \<open>S \<noteq> {}\<close> fim ope openin_contains_cball by fastforce
  have "dim ((+) (- a) ` U) \<le> dim ((+) (- b) ` V)"
  proof (rule invariance_of_dimension_subspaces)
    show "openin (top_of_set ((+) (- a) ` U)) ((+) (- a) ` S)"
      by (metis ope homeomorphism_imp_open_map homeomorphism_translation translation_galois)
    show "subspace ((+) (- a) ` U)"
      by (simp add: \<open>a \<in> U\<close> affine_diffs_subspace_subtract \<open>affine U\<close> cong: image_cong_simp)
    show "subspace ((+) (- b) ` V)"
      by (simp add: \<open>b \<in> V\<close> affine_diffs_subspace_subtract \<open>affine V\<close> cong: image_cong_simp)
    show "continuous_on ((+) (- a) ` S) ((+) (- b) \<circ> f \<circ> (+) a)"
      by (metis contf continuous_on_compose homeomorphism_cont2 homeomorphism_translation translation_galois)
    show "((+) (- b) \<circ> f \<circ> (+) a) ` (+) (- a) ` S \<subseteq> (+) (- b) ` V"
      using fim by auto
    show "inj_on ((+) (- b) \<circ> f \<circ> (+) a) ((+) (- a) ` S)"
      by (auto simp: inj_on_def) (meson inj_onD injf)
  qed (use \<open>S \<noteq> {}\<close> in auto)
  then show ?thesis
    by (metis \<open>a \<in> U\<close> \<open>b \<in> V\<close> aff_dim_eq_dim affine_hull_eq aff of_nat_le_iff)
qed

corollary invariance_of_dimension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and "open S"
      and injf: "inj_on f S" and "S \<noteq> {}"
    shows "DIM('a) \<le> DIM('b)"
  using invariance_of_dimension_subspaces [of UNIV S UNIV f] assms
  by auto

corollary continuous_injective_image_subspace_dim_le:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace S" "subspace T"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> T"
      and injf: "inj_on f S"
    shows "dim S \<le> dim T"
  apply (rule invariance_of_dimension_subspaces [of S S _ f])
  using assms by (auto simp: subspace_affine)

lemma invariance_of_dimension_convex_domain:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "convex S"
      and contf: "continuous_on S f" and fim: "f ` S \<subseteq> affine hull T"
      and injf: "inj_on f S"
    shows "aff_dim S \<le> aff_dim T"
proof (cases "S = {}")
  case True
  then show ?thesis by (simp add: aff_dim_geq)
next
  case False
  have "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
  proof (rule invariance_of_dimension_affine_sets)
    show "openin (top_of_set (affine hull S)) (rel_interior S)"
      by (simp add: openin_rel_interior)
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "f ` rel_interior S \<subseteq> affine hull T"
      using fim rel_interior_subset by blast
    show "inj_on f (rel_interior S)"
      using inj_on_subset injf rel_interior_subset by blast
    show "rel_interior S \<noteq> {}"
      by (simp add: False \<open>convex S\<close> rel_interior_eq_empty)
  qed auto
  then show ?thesis
    by simp
qed

lemma homeomorphic_convex_sets_le:
  assumes "convex S" "S homeomorphic T"
  shows "aff_dim S \<le> aff_dim T"
proof -
  obtain h k where homhk: "homeomorphism S T h k"
    using homeomorphic_def assms  by blast
  show ?thesis
  proof (rule invariance_of_dimension_convex_domain [OF \<open>convex S\<close>])
    show "continuous_on S h"
      using homeomorphism_def homhk by blast
    show "h ` S \<subseteq> affine hull T"
      by (metis homeomorphism_def homhk hull_subset)
    show "inj_on h S"
      by (meson homeomorphism_apply1 homhk inj_on_inverseI)
  qed
qed

lemma homeomorphic_convex_sets:
  assumes "convex S" "convex T" "S homeomorphic T"
  shows "aff_dim S = aff_dim T"
  by (meson assms dual_order.antisym homeomorphic_convex_sets_le homeomorphic_sym)

lemma homeomorphic_convex_compact_sets_eq:
  assumes "convex S" "compact S" "convex T" "compact T"
  shows "S homeomorphic T \<longleftrightarrow> aff_dim S = aff_dim T"
  by (meson assms homeomorphic_convex_compact_sets homeomorphic_convex_sets)

lemma invariance_of_domain_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "inj_on f S" "DIM('b) \<le> DIM('a)"
    shows "open(f ` S)"
  using invariance_of_domain_subspaces [of UNIV S UNIV f] assms by auto

lemma injective_into_1d_imp_open_map_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "open T" "continuous_on S f" "inj_on f S" "T \<subseteq> S"
    shows "open (f ` T)"
  apply (rule invariance_of_domain_gen [OF \<open>open T\<close>])
  using assms apply (auto simp: elim: continuous_on_subset subset_inj_on)
  done

lemma continuous_on_inverse_open:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" and gf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    shows "continuous_on (f ` S) g"
proof (clarsimp simp add: continuous_openin_preimage_eq)
  fix T :: "'a set"
  assume "open T"
  have eq: "f ` S \<inter> g -` T = f ` (S \<inter> T)"
    by (auto simp: gf)
  have "openin (top_of_set (f ` S)) (f ` (S \<inter> T))"
  proof (rule open_openin_trans [OF invariance_of_domain_gen])
    show "inj_on f S"
      using inj_on_inverseI gf by auto
    show "open (f ` (S \<inter> T))"
      by (meson \<open>inj_on f S\<close> \<open>open T\<close> assms(1-3) continuous_on_subset inf_le1 inj_on_subset invariance_of_domain_gen open_Int)
  qed (use assms in auto)
  then show "openin (top_of_set (f ` S)) (f ` S \<inter> g -` T)"
    by (simp add: eq)
qed

lemma invariance_of_domain_homeomorphism:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" "inj_on f S"
  obtains g where "homeomorphism S (f ` S) f g"
proof
  show "homeomorphism S (f ` S) f (inv_into S f)"
    by (simp add: assms continuous_on_inverse_open homeomorphism_def)
qed

corollary invariance_of_domain_homeomorphic:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "open S" "continuous_on S f" "DIM('b) \<le> DIM('a)" "inj_on f S"
  shows "S homeomorphic (f ` S)"
  using invariance_of_domain_homeomorphism [OF assms]
  by (meson homeomorphic_def)

lemma continuous_image_subset_interior:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on S f" "inj_on f S" "DIM('b) \<le> DIM('a)"
  shows "f ` (interior S) \<subseteq> interior(f ` S)"
proof (rule interior_maximal)
  show "f ` interior S \<subseteq> f ` S"
    by (simp add: image_mono interior_subset)
  show "open (f ` interior S)"
    using assms
    by (auto simp: subset_inj_on interior_subset continuous_on_subset invariance_of_domain_gen)
qed

lemma homeomorphic_interiors_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and dimeq: "DIM('a) = DIM('b)"
  shows "(interior S) homeomorphic (interior T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have fim: "f ` interior S \<subseteq> interior T"
    using continuous_image_subset_interior [OF contf \<open>inj_on f S\<close>] dimeq fST by simp
  have gim: "g ` interior T \<subseteq> interior S"
    using continuous_image_subset_interior [OF contg \<open>inj_on g T\<close>] dimeq gTS by simp
  show "homeomorphism (interior S) (interior T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show "\<And>x. x \<in> interior S \<Longrightarrow> g (f x) = x"
      by (meson \<open>\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x\<close> subsetD interior_subset)
    have "interior T \<subseteq> f ` interior S"
    proof
      fix x assume "x \<in> interior T"
      then have "g x \<in> interior S"
        using gim by blast
      then show "x \<in> f ` interior S"
        by (metis T \<open>x \<in> interior T\<close> image_iff interior_subset subsetCE)
    qed
    then show "f ` interior S = interior T"
      using fim by blast
    show "continuous_on (interior S) f"
      by (metis interior_subset continuous_on_subset contf)
    show "\<And>y. y \<in> interior T \<Longrightarrow> f (g y) = y"
      by (meson T subsetD interior_subset)
    have "interior S \<subseteq> g ` interior T"
    proof
      fix x assume "x \<in> interior S"
      then have "f x \<in> interior T"
        using fim by blast
      then show "x \<in> g ` interior T"
        by (metis S \<open>x \<in> interior S\<close> image_iff interior_subset subsetCE)
    qed
    then show "g ` interior T = interior S"
      using gim by blast
    show "continuous_on (interior T) g"
      by (metis interior_subset continuous_on_subset contg)
  qed
qed

lemma homeomorphic_open_imp_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "open S" "S \<noteq> {}" "open T" "T \<noteq> {}"
  shows "DIM('a) = DIM('b)"
    using assms
    apply (simp add: homeomorphic_minimal)
    apply (rule order_antisym; metis inj_onI invariance_of_dimension)
    done

proposition homeomorphic_interiors:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "interior S = {} \<longleftrightarrow> interior T = {}"
    shows "(interior S) homeomorphic (interior T)"
proof (cases "interior T = {}")
  case True
  with assms show ?thesis by auto
next
  case False
  then have "DIM('a) = DIM('b)"
    using assms
    apply (simp add: homeomorphic_minimal)
    apply (rule order_antisym; metis continuous_on_subset inj_onI inj_on_subset interior_subset invariance_of_dimension open_interior)
    done
  then show ?thesis
    by (rule homeomorphic_interiors_same_dimension [OF \<open>S homeomorphic T\<close>])
qed

lemma homeomorphic_frontiers_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "closed S" "closed T" and dimeq: "DIM('a) = DIM('b)"
  shows "(frontier S) homeomorphic (frontier T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have "g ` interior T \<subseteq> interior S"
    using continuous_image_subset_interior [OF contg \<open>inj_on g T\<close>] dimeq gTS by simp
  then have fim: "f ` frontier S \<subseteq> frontier T"
    apply (simp add: frontier_def)
    using continuous_image_subset_interior assms(2) assms(3) S by auto
  have "f ` interior S \<subseteq> interior T"
    using continuous_image_subset_interior [OF contf \<open>inj_on f S\<close>] dimeq fST by simp
  then have gim: "g ` frontier T \<subseteq> frontier S"
    apply (simp add: frontier_def)
    using continuous_image_subset_interior T assms(2) assms(3) by auto
  show "homeomorphism (frontier S) (frontier T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show gf: "\<And>x. x \<in> frontier S \<Longrightarrow> g (f x) = x"
      by (simp add: S assms(2) frontier_def)
    show fg: "\<And>y. y \<in> frontier T \<Longrightarrow> f (g y) = y"
      by (simp add: T assms(3) frontier_def)
    have "frontier T \<subseteq> f ` frontier S"
    proof
      fix x assume "x \<in> frontier T"
      then have "g x \<in> frontier S"
        using gim by blast
      then show "x \<in> f ` frontier S"
        by (metis fg \<open>x \<in> frontier T\<close> imageI)
    qed
    then show "f ` frontier S = frontier T"
      using fim by blast
    show "continuous_on (frontier S) f"
      by (metis Diff_subset assms(2) closure_eq contf continuous_on_subset frontier_def)
    have "frontier S \<subseteq> g ` frontier T"
    proof
      fix x assume "x \<in> frontier S"
      then have "f x \<in> frontier T"
        using fim by blast
      then show "x \<in> g ` frontier T"
        by (metis gf \<open>x \<in> frontier S\<close> imageI)
    qed
    then show "g ` frontier T = frontier S"
      using gim by blast
    show "continuous_on (frontier T) g"
      by (metis Diff_subset assms(3) closure_closed contg continuous_on_subset frontier_def)
  qed
qed

lemma homeomorphic_frontiers:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "closed S" "closed T"
          "interior S = {} \<longleftrightarrow> interior T = {}"
    shows "(frontier S) homeomorphic (frontier T)"
proof (cases "interior T = {}")
  case True
  then show ?thesis
    by (metis Diff_empty assms closure_eq frontier_def)
next
  case False
  show ?thesis
    apply (rule homeomorphic_frontiers_same_dimension)
       apply (simp_all add: assms)
    using False assms homeomorphic_interiors homeomorphic_open_imp_same_dimension by blast
qed

lemma continuous_image_subset_rel_interior:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f ` S \<subseteq> T"
      and TS: "aff_dim T \<le> aff_dim S"
  shows "f ` (rel_interior S) \<subseteq> rel_interior(f ` S)"
proof (rule rel_interior_maximal)
  show "f ` rel_interior S \<subseteq> f ` S"
    by(simp add: image_mono rel_interior_subset)
  show "openin (top_of_set (affine hull f ` S)) (f ` rel_interior S)"
  proof (rule invariance_of_domain_affine_sets)
    show "openin (top_of_set (affine hull S)) (rel_interior S)"
      by (simp add: openin_rel_interior)
    show "aff_dim (affine hull f ` S) \<le> aff_dim (affine hull S)"
      by (metis aff_dim_affine_hull aff_dim_subset fim TS order_trans)
    show "f ` rel_interior S \<subseteq> affine hull f ` S"
      by (meson \<open>f ` rel_interior S \<subseteq> f ` S\<close> hull_subset order_trans)
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "inj_on f (rel_interior S)"
      using inj_on_subset injf rel_interior_subset by blast
  qed auto
qed

lemma homeomorphic_rel_interiors_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and aff: "aff_dim S = aff_dim T"
  shows "(rel_interior S) homeomorphic (rel_interior T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have fim: "f ` rel_interior S \<subseteq> rel_interior T"
    by (metis \<open>inj_on f S\<close> aff contf continuous_image_subset_rel_interior fST order_refl)
  have gim: "g ` rel_interior T \<subseteq> rel_interior S"
    by (metis \<open>inj_on g T\<close> aff contg continuous_image_subset_rel_interior gTS order_refl)
  show "homeomorphism (rel_interior S) (rel_interior T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show gf: "\<And>x. x \<in> rel_interior S \<Longrightarrow> g (f x) = x"
      using S rel_interior_subset by blast
    show fg: "\<And>y. y \<in> rel_interior T \<Longrightarrow> f (g y) = y"
      using T mem_rel_interior_ball by blast
    have "rel_interior T \<subseteq> f ` rel_interior S"
    proof
      fix x assume "x \<in> rel_interior T"
      then have "g x \<in> rel_interior S"
        using gim by blast
      then show "x \<in> f ` rel_interior S"
        by (metis fg \<open>x \<in> rel_interior T\<close> imageI)
    qed
    moreover have "f ` rel_interior S \<subseteq> rel_interior T"
      by (metis \<open>inj_on f S\<close> aff contf continuous_image_subset_rel_interior fST order_refl)
    ultimately show "f ` rel_interior S = rel_interior T"
      by blast
    show "continuous_on (rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    have "rel_interior S \<subseteq> g ` rel_interior T"
    proof
      fix x assume "x \<in> rel_interior S"
      then have "f x \<in> rel_interior T"
        using fim by blast
      then show "x \<in> g ` rel_interior T"
        by (metis gf \<open>x \<in> rel_interior S\<close> imageI)
    qed
    then show "g ` rel_interior T = rel_interior S"
      using gim by blast
    show "continuous_on (rel_interior T) g"
      using contg continuous_on_subset rel_interior_subset by blast
  qed
qed

lemma homeomorphic_rel_interiors:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "rel_interior S = {} \<longleftrightarrow> rel_interior T = {}"
    shows "(rel_interior S) homeomorphic (rel_interior T)"
proof (cases "rel_interior T = {}")
  case True
  with assms show ?thesis by auto
next
  case False
  obtain f g
    where S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
      and contf: "continuous_on S f" and contg: "continuous_on T g"
    using  assms [unfolded homeomorphic_minimal] by auto
  have "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
    apply (rule invariance_of_dimension_affine_sets [of _ "rel_interior S" _ f])
          apply (simp_all add: openin_rel_interior False assms)
    using contf continuous_on_subset rel_interior_subset apply blast
      apply (meson S hull_subset image_subsetI rel_interior_subset rev_subsetD)
    apply (metis S inj_on_inverseI inj_on_subset rel_interior_subset)
    done
  moreover have "aff_dim (affine hull T) \<le> aff_dim (affine hull S)"
    apply (rule invariance_of_dimension_affine_sets [of _ "rel_interior T" _ g])
          apply (simp_all add: openin_rel_interior False assms)
    using contg continuous_on_subset rel_interior_subset apply blast
      apply (meson T hull_subset image_subsetI rel_interior_subset rev_subsetD)
    apply (metis T inj_on_inverseI inj_on_subset rel_interior_subset)
    done
  ultimately have "aff_dim S = aff_dim T" by force
  then show ?thesis
    by (rule homeomorphic_rel_interiors_same_dimension [OF \<open>S homeomorphic T\<close>])
qed


lemma homeomorphic_rel_boundaries_same_dimension:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" and aff: "aff_dim S = aff_dim T"
  shows "(S - rel_interior S) homeomorphic (T - rel_interior T)"
  using assms [unfolded homeomorphic_minimal]
  unfolding homeomorphic_def
proof (clarify elim!: ex_forward)
  fix f g
  assume S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
     and contf: "continuous_on S f" and contg: "continuous_on T g"
  then have fST: "f ` S = T" and gTS: "g ` T = S" and "inj_on f S" "inj_on g T"
    by (auto simp: inj_on_def intro: rev_image_eqI) metis+
  have fim: "f ` rel_interior S \<subseteq> rel_interior T"
    by (metis \<open>inj_on f S\<close> aff contf continuous_image_subset_rel_interior fST order_refl)
  have gim: "g ` rel_interior T \<subseteq> rel_interior S"
    by (metis \<open>inj_on g T\<close> aff contg continuous_image_subset_rel_interior gTS order_refl)
  show "homeomorphism (S - rel_interior S) (T - rel_interior T) f g"
    unfolding homeomorphism_def
  proof (intro conjI ballI)
    show gf: "\<And>x. x \<in> S - rel_interior S \<Longrightarrow> g (f x) = x"
      using S rel_interior_subset by blast
    show fg: "\<And>y. y \<in> T - rel_interior T \<Longrightarrow> f (g y) = y"
      using T mem_rel_interior_ball by blast
    show "f ` (S - rel_interior S) = T - rel_interior T"
      using S fST fim gim by auto
    show "continuous_on (S - rel_interior S) f"
      using contf continuous_on_subset rel_interior_subset by blast
    show "g ` (T - rel_interior T) = S - rel_interior S"
      using T gTS gim fim by auto
    show "continuous_on (T - rel_interior T) g"
      using contg continuous_on_subset rel_interior_subset by blast
  qed
qed

lemma homeomorphic_rel_boundaries:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T" "rel_interior S = {} \<longleftrightarrow> rel_interior T = {}"
    shows "(S - rel_interior S) homeomorphic (T - rel_interior T)"
proof (cases "rel_interior T = {}")
  case True
  with assms show ?thesis by auto
next
  case False
  obtain f g
    where S: "\<forall>x\<in>S. f x \<in> T \<and> g (f x) = x" and T: "\<forall>y\<in>T. g y \<in> S \<and> f (g y) = y"
      and contf: "continuous_on S f" and contg: "continuous_on T g"
    using  assms [unfolded homeomorphic_minimal] by auto
  have "aff_dim (affine hull S) \<le> aff_dim (affine hull T)"
    apply (rule invariance_of_dimension_affine_sets [of _ "rel_interior S" _ f])
          apply (simp_all add: openin_rel_interior False assms)
    using contf continuous_on_subset rel_interior_subset apply blast
      apply (meson S hull_subset image_subsetI rel_interior_subset rev_subsetD)
    apply (metis S inj_on_inverseI inj_on_subset rel_interior_subset)
    done
  moreover have "aff_dim (affine hull T) \<le> aff_dim (affine hull S)"
    apply (rule invariance_of_dimension_affine_sets [of _ "rel_interior T" _ g])
          apply (simp_all add: openin_rel_interior False assms)
    using contg continuous_on_subset rel_interior_subset apply blast
      apply (meson T hull_subset image_subsetI rel_interior_subset rev_subsetD)
    apply (metis T inj_on_inverseI inj_on_subset rel_interior_subset)
    done
  ultimately have "aff_dim S = aff_dim T" by force
  then show ?thesis
    by (rule homeomorphic_rel_boundaries_same_dimension [OF \<open>S homeomorphic T\<close>])
qed

proposition uniformly_continuous_homeomorphism_UNIV_trivial:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes contf: "uniformly_continuous_on S f" and hom: "homeomorphism S UNIV f g"
  shows "S = UNIV"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (metis UNIV_I hom empty_iff homeomorphism_def image_eqI)
next
  case False
  have "inj g"
    by (metis UNIV_I hom homeomorphism_apply2 injI)
  then have "open (g ` UNIV)"
    by (blast intro: invariance_of_domain hom homeomorphism_cont2)
  then have "open S"
    using hom homeomorphism_image2 by blast
  moreover have "complete S"
    unfolding complete_def
  proof clarify
    fix \<sigma>
    assume \<sigma>: "\<forall>n. \<sigma> n \<in> S" and "Cauchy \<sigma>"
    have "Cauchy (f o \<sigma>)"
      using uniformly_continuous_imp_Cauchy_continuous \<open>Cauchy \<sigma>\<close> \<sigma> contf by blast
    then obtain l where "(f \<circ> \<sigma>) \<longlonglongrightarrow> l"
      by (auto simp: convergent_eq_Cauchy [symmetric])
    show "\<exists>l\<in>S. \<sigma> \<longlonglongrightarrow> l"
    proof
      show "g l \<in> S"
        using hom homeomorphism_image2 by blast
      have "(g \<circ> (f \<circ> \<sigma>)) \<longlonglongrightarrow> g l"
        by (meson UNIV_I \<open>(f \<circ> \<sigma>) \<longlonglongrightarrow> l\<close> continuous_on_sequentially hom homeomorphism_cont2)
      then show "\<sigma> \<longlonglongrightarrow> g l"
      proof -
        have "\<forall>n. \<sigma> n = (g \<circ> (f \<circ> \<sigma>)) n"
          by (metis (no_types) \<sigma> comp_eq_dest_lhs hom homeomorphism_apply1)
        then show ?thesis
          by (metis (no_types) LIMSEQ_iff \<open>(g \<circ> (f \<circ> \<sigma>)) \<longlonglongrightarrow> g l\<close>)
      qed
    qed
  qed
  then have "closed S"
    by (simp add: complete_eq_closed)
  ultimately show ?thesis
    using clopen [of S] False  by simp
qed

proposition invariance_of_domain_sphere_affine_set_gen:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f ` S \<subseteq> T"
      and U: "bounded U" "convex U"
      and "affine T" and affTU: "aff_dim T < aff_dim U"
      and ope: "openin (top_of_set (rel_frontier U)) S"
   shows "openin (top_of_set T) (f ` S)"
proof (cases "rel_frontier U = {}")
  case True
  then show ?thesis
    using ope openin_subset by force
next
  case False
  obtain b c where b: "b \<in> rel_frontier U" and c: "c \<in> rel_frontier U" and "b \<noteq> c"
    using \<open>bounded U\<close> rel_frontier_not_sing [of U] subset_singletonD False  by fastforce
  obtain V :: "'a set" where "affine V" and affV: "aff_dim V = aff_dim U - 1"
  proof (rule choose_affine_subset [OF affine_UNIV])
    show "- 1 \<le> aff_dim U - 1"
      by (metis aff_dim_empty aff_dim_geq aff_dim_negative_iff affTU diff_0 diff_right_mono not_le)
    show "aff_dim U - 1 \<le> aff_dim (UNIV::'a set)"
      by (metis aff_dim_UNIV aff_dim_le_DIM le_cases not_le zle_diff1_eq)
  qed auto
  have SU: "S \<subseteq> rel_frontier U"
    using ope openin_imp_subset by auto
  have homb: "rel_frontier U - {b} homeomorphic V"
   and homc: "rel_frontier U - {c} homeomorphic V"
    using homeomorphic_punctured_sphere_affine_gen [of U _ V]
    by (simp_all add: \<open>affine V\<close> affV U b c)
  then obtain g h j k
           where gh: "homeomorphism (rel_frontier U - {b}) V g h"
             and jk: "homeomorphism (rel_frontier U - {c}) V j k"
    by (auto simp: homeomorphic_def)
  with SU have hgsub: "(h ` g ` (S - {b})) \<subseteq> S" and kjsub: "(k ` j ` (S - {c})) \<subseteq> S"
    by (simp_all add: homeomorphism_def subset_eq)
  have [simp]: "aff_dim T \<le> aff_dim V"
    by (simp add: affTU affV)
  have "openin (top_of_set T) ((f \<circ> h) ` g ` (S - {b}))"
  proof (rule invariance_of_domain_affine_sets [OF _ \<open>affine V\<close>])
    show "openin (top_of_set V) (g ` (S - {b}))"
      apply (rule homeomorphism_imp_open_map [OF gh])
      by (meson Diff_mono Diff_subset SU ope openin_delete openin_subset_trans order_refl)
    show "continuous_on (g ` (S - {b})) (f \<circ> h)"
       apply (rule continuous_on_compose)
        apply (meson Diff_mono SU homeomorphism_def homeomorphism_of_subsets gh set_eq_subset)
      using contf continuous_on_subset hgsub by blast
    show "inj_on (f \<circ> h) (g ` (S - {b}))"
      using kjsub
      apply (clarsimp simp add: inj_on_def)
      by (metis SU b homeomorphism_def inj_onD injf insert_Diff insert_iff gh rev_subsetD)
    show "(f \<circ> h) ` g ` (S - {b}) \<subseteq> T"
      by (metis fim image_comp image_mono hgsub subset_trans)
  qed (auto simp: assms)
  moreover
  have "openin (top_of_set T) ((f \<circ> k) ` j ` (S - {c}))"
  proof (rule invariance_of_domain_affine_sets [OF _ \<open>affine V\<close>])
    show "openin (top_of_set V) (j ` (S - {c}))"
      apply (rule homeomorphism_imp_open_map [OF jk])
      by (meson Diff_mono Diff_subset SU ope openin_delete openin_subset_trans order_refl)
    show "continuous_on (j ` (S - {c})) (f \<circ> k)"
       apply (rule continuous_on_compose)
        apply (meson Diff_mono SU homeomorphism_def homeomorphism_of_subsets jk set_eq_subset)
      using contf continuous_on_subset kjsub by blast
    show "inj_on (f \<circ> k) (j ` (S - {c}))"
      using kjsub
      apply (clarsimp simp add: inj_on_def)
      by (metis SU c homeomorphism_def inj_onD injf insert_Diff insert_iff jk rev_subsetD)
    show "(f \<circ> k) ` j ` (S - {c}) \<subseteq> T"
      by (metis fim image_comp image_mono kjsub subset_trans)
  qed (auto simp: assms)
  ultimately have "openin (top_of_set T) ((f \<circ> h) ` g ` (S - {b}) \<union> ((f \<circ> k) ` j ` (S - {c})))"
    by (rule openin_Un)
  moreover have "(f \<circ> h) ` g ` (S - {b}) = f ` (S - {b})"
  proof -
    have "h ` g ` (S - {b}) = (S - {b})"
    proof
      show "h ` g ` (S - {b}) \<subseteq> S - {b}"
        using homeomorphism_apply1 [OF gh] SU
        by (fastforce simp add: image_iff image_subset_iff)
      show "S - {b} \<subseteq> h ` g ` (S - {b})"
        apply clarify
        by  (metis SU subsetD homeomorphism_apply1 [OF gh] image_iff member_remove remove_def)
    qed
    then show ?thesis
      by (metis image_comp)
  qed
  moreover have "(f \<circ> k) ` j ` (S - {c}) = f ` (S - {c})"
  proof -
    have "k ` j ` (S - {c}) = (S - {c})"
    proof
      show "k ` j ` (S - {c}) \<subseteq> S - {c}"
        using homeomorphism_apply1 [OF jk] SU
        by (fastforce simp add: image_iff image_subset_iff)
      show "S - {c} \<subseteq> k ` j ` (S - {c})"
        apply clarify
        by  (metis SU subsetD homeomorphism_apply1 [OF jk] image_iff member_remove remove_def)
    qed
    then show ?thesis
      by (metis image_comp)
  qed
  moreover have "f ` (S - {b}) \<union> f ` (S - {c}) = f ` (S)"
    using \<open>b \<noteq> c\<close> by blast
  ultimately show ?thesis
    by simp
qed

lemma invariance_of_domain_sphere_affine_set:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and injf: "inj_on f S" and fim: "f ` S \<subseteq> T"
      and "r \<noteq> 0" "affine T" and affTU: "aff_dim T < DIM('a)"
      and ope: "openin (top_of_set (sphere a r)) S"
   shows "openin (top_of_set T) (f ` S)"
proof (cases "sphere a r = {}")
  case True
  then show ?thesis
    using ope openin_subset by force
next
  case False
  show ?thesis
  proof (rule invariance_of_domain_sphere_affine_set_gen [OF contf injf fim bounded_cball convex_cball \<open>affine T\<close>])
    show "aff_dim T < aff_dim (cball a r)"
      by (metis False affTU aff_dim_cball assms(4) linorder_cases sphere_empty)
    show "openin (top_of_set (rel_frontier (cball a r))) S"
      by (simp add: \<open>r \<noteq> 0\<close> ope)
  qed
qed

lemma no_embedding_sphere_lowdim:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on (sphere a r) f" and injf: "inj_on f (sphere a r)" and "r > 0"
   shows "DIM('a) \<le> DIM('b)"
proof -
  have "False" if "DIM('a) > DIM('b)"
  proof -
    have "compact (f ` sphere a r)"
      using compact_continuous_image
      by (simp add: compact_continuous_image contf)
    then have "\<not> open (f ` sphere a r)"
      using compact_open
      by (metis assms(3) image_is_empty not_less_iff_gr_or_eq sphere_eq_empty)
    then show False
      using invariance_of_domain_sphere_affine_set [OF contf injf subset_UNIV] \<open>r > 0\<close>
      by (metis aff_dim_UNIV affine_UNIV less_irrefl of_nat_less_iff open_openin openin_subtopology_self subtopology_UNIV that)
  qed
  then show ?thesis
    using not_less by blast
qed

lemma empty_interior_lowdim_gen:
  fixes S :: "'N::euclidean_space set" and T :: "'M::euclidean_space set"
  assumes dim: "DIM('M) < DIM('N)" and ST: "S homeomorphic T" 
  shows "interior S = {}"
proof -
  obtain h :: "'M \<Rightarrow> 'N" where "linear h" "\<And>x. norm(h x) = norm x"
    by (rule isometry_subset_subspace [OF subspace_UNIV subspace_UNIV, where ?'a = 'M and ?'b = 'N])
       (use dim in auto)
  then have "inj h"
    by (metis linear_inj_iff_eq_0 norm_eq_zero)
  then have "h ` T homeomorphic T"
    using \<open>linear h\<close> homeomorphic_sym linear_homeomorphic_image by blast
  then have "interior (h ` T) homeomorphic interior S"
    using homeomorphic_interiors_same_dimension
    by (metis ST homeomorphic_sym homeomorphic_trans)
  moreover   
  have "interior (range h) = {}"
    by (simp add: \<open>inj h\<close> \<open>linear h\<close> dim dim_image_eq empty_interior_lowdim)
  then have "interior (h ` T) = {}"
    by (metis image_mono interior_mono subset_empty top_greatest)
  ultimately show ?thesis
    by simp
qed

lemma empty_interior_lowdim_gen_le:
  fixes S :: "'N::euclidean_space set" and T :: "'M::euclidean_space set"
  assumes "DIM('M) \<le> DIM('N)"  "interior T = {}" "S homeomorphic T" 
  shows "interior S = {}"
  by (metis assms empty_interior_lowdim_gen homeomorphic_empty(1) homeomorphic_interiors_same_dimension less_le)

lemma homeomorphic_affine_sets_eq:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "affine S" "affine T"
  shows "S homeomorphic T \<longleftrightarrow> aff_dim S = aff_dim T"
proof (cases "S = {} \<or> T = {}")
  case True
  then show ?thesis
    using assms homeomorphic_affine_sets by force
next
  case False
  then obtain a b where "a \<in> S" "b \<in> T"
    by blast
  then have "subspace ((+) (- a) ` S)" "subspace ((+) (- b) ` T)"
    using affine_diffs_subspace assms by blast+
  then show ?thesis
    by (metis affine_imp_convex assms homeomorphic_affine_sets homeomorphic_convex_sets)
qed

lemma homeomorphic_hyperplanes_eq:
  fixes a :: "'M::euclidean_space" and c :: "'N::euclidean_space"
  assumes "a \<noteq> 0" "c \<noteq> 0" 
  shows "({x. a \<bullet> x = b} homeomorphic {x. c \<bullet> x = d} \<longleftrightarrow> DIM('M) = DIM('N))" (is "?lhs = ?rhs")
proof -
  have "(DIM('M) - Suc 0 = DIM('N) - Suc 0) \<longleftrightarrow> (DIM('M) = DIM('N))"
    by auto (metis DIM_positive Suc_pred)
  then show ?thesis
    using assms by (simp add: homeomorphic_affine_sets_eq affine_hyperplane)
qed

end
