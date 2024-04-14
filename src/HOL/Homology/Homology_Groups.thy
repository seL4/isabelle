section\<open>Homology, II: Homology Groups\<close>

theory Homology_Groups
  imports Simplices "HOL-Algebra.Exact_Sequence"

begin
subsection\<open>Homology Groups\<close>

text\<open>Now actually connect to group theory and set up homology groups. Note that we define homomogy
groups for all \emph{integers} @{term p}, since this seems to avoid some special-case reasoning,
though they are trivial for @{term"p < 0"}.\<close>

definition chain_group :: "nat \<Rightarrow> 'a topology \<Rightarrow> 'a chain monoid"
  where "chain_group p X \<equiv> free_Abelian_group (singular_simplex_set p X)"

lemma carrier_chain_group [simp]: "carrier(chain_group p X) = singular_chain_set p X"
  by (auto simp: chain_group_def singular_chain_def free_Abelian_group_def)

lemma one_chain_group [simp]: "one(chain_group p X) = 0"
  by (auto simp: chain_group_def free_Abelian_group_def)

lemma mult_chain_group [simp]: "monoid.mult(chain_group p X) = (+)"
  by (auto simp: chain_group_def free_Abelian_group_def)

lemma m_inv_chain_group [simp]: "Poly_Mapping.keys a \<subseteq> singular_simplex_set p X \<Longrightarrow> inv\<^bsub>chain_group p X\<^esub> a = -a"
  unfolding chain_group_def by simp

lemma group_chain_group [simp]: "Group.group (chain_group p X)"
  by (simp add: chain_group_def)

lemma abelian_chain_group: "comm_group(chain_group p X)"
  by (simp add: free_Abelian_group_def group.group_comm_groupI [OF group_chain_group])

lemma subgroup_singular_relcycle:
     "subgroup (singular_relcycle_set p X S) (chain_group p X)"
proof
  show "x \<otimes>\<^bsub>chain_group p X\<^esub> y \<in> singular_relcycle_set p X S"
    if "x \<in> singular_relcycle_set p X S" and "y \<in> singular_relcycle_set p X S" for x y
    using that by (simp add: singular_relcycle_add)
next
  show "inv\<^bsub>chain_group p X\<^esub> x \<in> singular_relcycle_set p X S"
    if "x \<in> singular_relcycle_set p X S" for x
    using that
    by clarsimp (metis m_inv_chain_group singular_chain_def singular_relcycle singular_relcycle_minus)
qed (auto simp: singular_relcycle)


definition relcycle_group :: "nat \<Rightarrow> 'a topology \<Rightarrow> 'a set \<Rightarrow> ('a chain) monoid"
  where "relcycle_group p X S \<equiv>
        subgroup_generated (chain_group p X) (Collect(singular_relcycle p X S))"

lemma carrier_relcycle_group [simp]:
  "carrier (relcycle_group p X S) = singular_relcycle_set p X S"
proof -
  have "carrier (chain_group p X) \<inter> singular_relcycle_set p X S = singular_relcycle_set p X S"
    using subgroup.subset subgroup_singular_relcycle by blast
  moreover have "generate (chain_group p X) (singular_relcycle_set p X S) \<subseteq> singular_relcycle_set p X S"
    by (simp add: group.generate_subgroup_incl group_chain_group subgroup_singular_relcycle)
  ultimately show ?thesis
    by (auto simp: relcycle_group_def subgroup_generated_def generate.incl)
qed

lemma one_relcycle_group [simp]: "one(relcycle_group p X S) = 0"
  by (simp add: relcycle_group_def)

lemma mult_relcycle_group [simp]: "(\<otimes>\<^bsub>relcycle_group p X S\<^esub>) = (+)"
  by (simp add: relcycle_group_def)

lemma abelian_relcycle_group [simp]:
   "comm_group(relcycle_group p X S)"
  unfolding relcycle_group_def
  by (intro group.abelian_subgroup_generated group_chain_group) (auto simp: abelian_chain_group singular_relcycle)

lemma group_relcycle_group [simp]: "group(relcycle_group p X S)"
  by (simp add: comm_group.axioms(2))

lemma relcycle_group_restrict [simp]:
   "relcycle_group p X (topspace X \<inter> S) = relcycle_group p X S"
  by (metis relcycle_group_def singular_relcycle_restrict)


definition relative_homology_group :: "int \<Rightarrow> 'a topology \<Rightarrow> 'a set \<Rightarrow> ('a chain) set monoid"
  where
    "relative_homology_group p X S \<equiv>
        if p < 0 then singleton_group undefined else
        (relcycle_group (nat p) X S) Mod (singular_relboundary_set (nat p) X S)"

abbreviation homology_group
  where "homology_group p X \<equiv> relative_homology_group p X {}"

lemma relative_homology_group_restrict [simp]:
   "relative_homology_group p X (topspace X \<inter> S) = relative_homology_group p X S"
  by (simp add: relative_homology_group_def)

lemma nontrivial_relative_homology_group:
  fixes p::nat
  shows "relative_homology_group p X S
       = relcycle_group p X S Mod singular_relboundary_set p X S"
  by (simp add: relative_homology_group_def)

lemma singular_relboundary_ss:
  "singular_relboundary p X S x \<Longrightarrow> Poly_Mapping.keys x \<subseteq> singular_simplex_set p X"
    using singular_chain_def singular_relboundary_imp_chain by blast

lemma trivial_relative_homology_group [simp]:
  "p < 0 \<Longrightarrow> trivial_group(relative_homology_group p X S)"
  by (simp add: relative_homology_group_def)

lemma subgroup_singular_relboundary:
     "subgroup (singular_relboundary_set p X S) (chain_group p X)"
  unfolding chain_group_def
proof unfold_locales
  show "singular_relboundary_set p X S
        \<subseteq> carrier (free_Abelian_group (singular_simplex_set p X))"
    using singular_chain_def singular_relboundary_imp_chain by fastforce
next
  fix x
  assume "x \<in> singular_relboundary_set p X S"
  then show "inv\<^bsub>free_Abelian_group (singular_simplex_set p X)\<^esub> x
             \<in> singular_relboundary_set p X S"
    by (simp add: singular_relboundary_ss singular_relboundary_minus)
qed (auto simp: free_Abelian_group_def singular_relboundary_add)

lemma subgroup_singular_relboundary_relcycle:
  "subgroup (singular_relboundary_set p X S) (relcycle_group p X S)"
  unfolding relcycle_group_def
  by (simp add: Collect_mono group.subgroup_of_subgroup_generated singular_relboundary_imp_relcycle subgroup_singular_relboundary)

lemma normal_subgroup_singular_relboundary_relcycle:
   "(singular_relboundary_set p X S) \<lhd> (relcycle_group p X S)"
  by (simp add: comm_group.normal_iff_subgroup subgroup_singular_relboundary_relcycle)

lemma group_relative_homology_group [simp]:
  "group (relative_homology_group p X S)"
  by (simp add: relative_homology_group_def normal.factorgroup_is_group
                normal_subgroup_singular_relboundary_relcycle)

lemma right_coset_singular_relboundary:
  "r_coset (relcycle_group p X S) (singular_relboundary_set p X S)
  = (\<lambda>a. {b. homologous_rel p X S a b})"
  using singular_relboundary_minus
  by (force simp: r_coset_def homologous_rel_def relcycle_group_def subgroup_generated_def)

lemma carrier_relative_homology_group:
   "carrier(relative_homology_group (int p) X S)
 = (homologous_rel_set p X S) ` singular_relcycle_set p X S"
  by (auto simp: set_eq_iff image_iff relative_homology_group_def FactGroup_def RCOSETS_def right_coset_singular_relboundary)

lemma carrier_relative_homology_group_0:
   "carrier(relative_homology_group 0 X S)
 = (homologous_rel_set 0 X S) ` singular_relcycle_set 0 X S"
  using carrier_relative_homology_group [of 0 X S] by simp

lemma one_relative_homology_group [simp]:
  "one(relative_homology_group (int p) X S) = singular_relboundary_set p X S"
  by (simp add: relative_homology_group_def FactGroup_def)

lemma mult_relative_homology_group:
  "(\<otimes>\<^bsub>relative_homology_group (int p) X S\<^esub>) = (\<lambda>R S. (\<Union>r\<in>R. \<Union>s\<in>S. {r + s}))"
  unfolding relcycle_group_def subgroup_generated_def chain_group_def free_Abelian_group_def set_mult_def relative_homology_group_def FactGroup_def
  by force

lemma inv_relative_homology_group:
  assumes "R \<in> carrier (relative_homology_group (int p) X S)"
  shows "m_inv(relative_homology_group (int p) X S) R = uminus ` R"
proof (rule group.inv_equality [OF group_relative_homology_group _ assms])
  obtain c where c: "R = homologous_rel_set p X S c" "singular_relcycle p X S c"
    using assms by (auto simp: carrier_relative_homology_group)
  have "singular_relboundary p X S (b - a)"
    if "a \<in> R" and "b \<in> R" for a b
    using c that
    by clarify (metis homologous_rel_def homologous_rel_eq)
  moreover
  have "x \<in> (\<Union>x\<in>R. \<Union>y\<in>R. {y - x})"
    if "singular_relboundary p X S x" for x
    using c
    by simp (metis diff_eq_eq homologous_rel_def homologous_rel_refl homologous_rel_sym that)
  ultimately
  have "(\<Union>x\<in>R. \<Union>xa\<in>R. {xa - x}) = singular_relboundary_set p X S"
    by auto
  then show "uminus ` R \<otimes>\<^bsub>relative_homology_group (int p) X S\<^esub> R =
        \<one>\<^bsub>relative_homology_group (int p) X S\<^esub>"
    by (auto simp: carrier_relative_homology_group mult_relative_homology_group)
  have "singular_relcycle p X S (-c)"
    using c by (simp add: singular_relcycle_minus)
  moreover have "homologous_rel p X S c x \<Longrightarrow> homologous_rel p X S (-c) (- x)" for x
    by (metis homologous_rel_def homologous_rel_sym minus_diff_eq minus_diff_minus)
  moreover have "homologous_rel p X S (-c) x \<Longrightarrow> x \<in> uminus ` homologous_rel_set p X S c" for x
    by (clarsimp simp: image_iff) (metis add.inverse_inverse diff_0 homologous_rel_diff homologous_rel_refl)
  ultimately show "uminus ` R \<in> carrier (relative_homology_group (int p) X S)"
    using c by (auto simp: carrier_relative_homology_group)
qed

lemma homologous_rel_eq_relboundary:
     "homologous_rel p X S c = singular_relboundary p X S
  \<longleftrightarrow> singular_relboundary p X S c" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding homologous_rel_def
    by (metis diff_zero singular_relboundary_0)
next
  assume R: ?rhs
  show ?lhs
    unfolding homologous_rel_def
    using singular_relboundary_diff R by fastforce
qed

lemma homologous_rel_set_eq_relboundary:
     "homologous_rel_set p X S c = singular_relboundary_set p X S \<longleftrightarrow> singular_relboundary p X S c"
  by (auto simp flip: homologous_rel_eq_relboundary)

text\<open>Lift the boundary and induced maps to homology groups. We totalize both
 quite aggressively to the appropriate group identity in all "undefined"
 situations, which makes several of the properties cleaner and simpler.\<close>

lemma homomorphism_chain_boundary:
   "chain_boundary p \<in> hom (relcycle_group p X S) (relcycle_group(p - Suc 0) (subtopology X S) {})"
    (is "?h \<in> hom ?G ?H")
proof (rule homI)
  show "\<And>x. x \<in> carrier ?G \<Longrightarrow> ?h x  \<in> carrier ?H"
    by (auto simp: singular_relcycle_def mod_subset_def chain_boundary_boundary)
qed (simp add: relcycle_group_def subgroup_generated_def chain_boundary_add)


lemma hom_boundary1:
    "\<exists>d. \<forall>p X S.
          d p X S \<in> hom (relative_homology_group (int p) X S)
                        (homology_group (int (p - Suc 0)) (subtopology X S))
       \<and> (\<forall>c. singular_relcycle p X S c
              \<longrightarrow> d p X S (homologous_rel_set p X S c)
                = homologous_rel_set (p - Suc 0) (subtopology X S) {} (chain_boundary p c))"
    (is "\<exists>d. \<forall>p X S. ?\<Phi> (d p X S) p X S")
proof ((subst choice_iff [symmetric])+, clarify)
  fix p X and S :: "'a set"
  define \<theta> where "\<theta> \<equiv> r_coset (relcycle_group(p - Suc 0) (subtopology X S) {})
                       (singular_relboundary_set (p - Suc 0) (subtopology X S) {}) \<circ> chain_boundary p"
  define H where "H \<equiv> relative_homology_group (int (p - Suc 0)) (subtopology X S) {}"
  define J where "J \<equiv> relcycle_group (p - Suc 0) (subtopology X S) {}"

  have \<theta>: "\<theta> \<in> hom (relcycle_group p X S) H"
    unfolding \<theta>_def
  proof (rule hom_compose)
    show "chain_boundary p \<in> hom (relcycle_group p X S) J"
      by (simp add: J_def homomorphism_chain_boundary)
    show "(#>\<^bsub>relcycle_group (p - Suc 0) (subtopology X S) {}\<^esub>)
         (singular_relboundary_set (p - Suc 0) (subtopology X S) {}) \<in> hom J H"
      by (simp add: H_def J_def nontrivial_relative_homology_group
           normal.r_coset_hom_Mod normal_subgroup_singular_relboundary_relcycle)
  qed
  have *: "singular_relboundary (p - Suc 0) (subtopology X S) {} (chain_boundary p c)"
    if "singular_relboundary p X S c" for c
  proof (cases "p=0")
    case True
    then show ?thesis
      by (metis chain_boundary_def singular_relboundary_0)
  next
    case False
    with that have "\<exists>d. singular_chain p (subtopology X S) d \<and> chain_boundary p d = chain_boundary p c"
      by (metis add.left_neutral chain_boundary_add chain_boundary_boundary_alt singular_relboundary)
    with that False show ?thesis
      by (auto simp: singular_boundary)
  qed
  have \<theta>_eq: "\<theta> x = \<theta> y"
    if x: "x \<in> singular_relcycle_set p X S" and y: "y \<in> singular_relcycle_set p X S"
      and eq: "singular_relboundary_set p X S #>\<^bsub>relcycle_group p X S\<^esub> x
             = singular_relboundary_set p X S #>\<^bsub>relcycle_group p X S\<^esub> y" for x y
  proof -
    have "singular_relboundary p X S (x-y)"
      by (metis eq homologous_rel_def homologous_rel_eq mem_Collect_eq right_coset_singular_relboundary)
    with * have "(singular_relboundary (p - Suc 0) (subtopology X S) {}) (chain_boundary p (x-y))"
      by blast
  then show ?thesis
    unfolding \<theta>_def comp_def
    by (metis chain_boundary_diff homologous_rel_def homologous_rel_eq right_coset_singular_relboundary)
qed
  obtain d
    where "d \<in> hom ((relcycle_group p X S) Mod (singular_relboundary_set p X S)) H"
      and d: "\<And>u. u \<in> singular_relcycle_set p X S \<Longrightarrow> d (homologous_rel_set p X S u) = \<theta> u"
    by (metis FactGroup_universal [OF \<theta> normal_subgroup_singular_relboundary_relcycle \<theta>_eq] right_coset_singular_relboundary carrier_relcycle_group)
  then have "d \<in> hom (relative_homology_group p X S) H"
    by (simp add: nontrivial_relative_homology_group)
  then show  "\<exists>d. ?\<Phi> d p X S"
    by (force simp: H_def right_coset_singular_relboundary d \<theta>_def)
qed

lemma hom_boundary2:
  "\<exists>d. (\<forall>p X S.
           (d p X S) \<in> hom (relative_homology_group p X S)
                           (homology_group (p-1) (subtopology X S)))
     \<and> (\<forall>p X S c. singular_relcycle p X S c \<and> Suc 0 \<le> p
            \<longrightarrow> d p X S (homologous_rel_set p X S c)
              = homologous_rel_set (p - Suc 0) (subtopology X S) {} (chain_boundary p c))"
  (is "\<exists>d. ?\<Phi> d")
proof -
  have *: "\<exists>f. \<Phi>(\<lambda>p. if p \<le> 0 then \<lambda>q r t. undefined else f(nat p)) \<Longrightarrow> \<exists>f. \<Phi> f"  for \<Phi>
    by blast
  show ?thesis
    apply (rule * [OF ex_forward [OF hom_boundary1]])
    apply (simp add: not_le relative_homology_group_def nat_diff_distrib' int_eq_iff nat_diff_distrib flip: nat_1)
    by (simp add: hom_def singleton_group_def)
qed

lemma hom_boundary3:
  "\<exists>d. ((\<forall>p X S c. c \<notin> carrier(relative_homology_group p X S)
              \<longrightarrow> d p X S c = one(homology_group (p-1) (subtopology X S))) \<and>
       (\<forall>p X S.
          d p X S \<in> hom (relative_homology_group p X S)
                        (homology_group (p-1) (subtopology X S))) \<and>
       (\<forall>p X S c.
            singular_relcycle p X S c \<and> 1 \<le> p
            \<longrightarrow> d p X S (homologous_rel_set p X S c)
              = homologous_rel_set (p - Suc 0) (subtopology X S) {} (chain_boundary p c)) \<and>
       (\<forall>p X S. d p X S = d p X (topspace X \<inter> S))) \<and>
       (\<forall>p X S c. d p X S c \<in> carrier(homology_group (p-1) (subtopology X S))) \<and>
       (\<forall>p. p \<le> 0 \<longrightarrow> d p = (\<lambda>q r t. undefined))"
  (is "\<exists>x. ?P x \<and> ?Q x \<and> ?R x")
proof -
  have "\<And>x. ?Q x \<Longrightarrow> ?R x"
    by (erule all_forward) (force simp: relative_homology_group_def)
  moreover have "\<exists>x. ?P x \<and> ?Q x"
  proof -
    obtain d:: "[int, 'a topology, 'a set, ('a chain) set] \<Rightarrow> ('a chain) set"
      where 1: "\<And>p X S. d p X S \<in> hom (relative_homology_group p X S)
                                      (homology_group (p-1) (subtopology X S))"
        and 2: "\<And>n X S c. singular_relcycle n X S c \<and> Suc 0 \<le> n
                  \<Longrightarrow> d n X S (homologous_rel_set n X S c)
                    = homologous_rel_set (n - Suc 0) (subtopology X S) {} (chain_boundary n c)"
      using hom_boundary2 by blast
    have 4: "c \<in> carrier (relative_homology_group p X S) \<Longrightarrow>
        d p X (topspace X \<inter> S) c \<in> carrier (relative_homology_group (p-1) (subtopology X S) {})"
      for p X S c
      using hom_carrier [OF 1 [of p X "topspace X \<inter> S"]]
      by (simp add: image_subset_iff subtopology_restrict)
    show ?thesis
      apply (rule_tac x="\<lambda>p X S c.
               if c \<in> carrier(relative_homology_group p X S)
               then d p X (topspace X \<inter> S) c
               else one(homology_group (p-1) (subtopology X S))" in exI)
      apply (simp add: Int_left_absorb subtopology_restrict carrier_relative_homology_group
          group.is_monoid group.restrict_hom_iff 4 cong: if_cong)
      by (metis "1" "2" homologous_rel_restrict relative_homology_group_restrict singular_relcycle_def subtopology_restrict)
  qed
  ultimately show ?thesis
    by auto
qed


consts hom_boundary :: "[int,'a topology,'a set,'a chain set] \<Rightarrow> 'a chain set"
specification (hom_boundary)
  hom_boundary:
      "((\<forall>p X S c. c \<notin> carrier(relative_homology_group p X S)
              \<longrightarrow> hom_boundary p X S c = one(homology_group (p-1) (subtopology X (S::'a set)))) \<and>
       (\<forall>p X S.
          hom_boundary p X S \<in> hom (relative_homology_group p X S)
                        (homology_group (p-1) (subtopology X (S::'a set)))) \<and>
       (\<forall>p X S c.
            singular_relcycle p X S c \<and> 1 \<le> p
            \<longrightarrow> hom_boundary p X S (homologous_rel_set p X S c)
              = homologous_rel_set (p - Suc 0) (subtopology X (S::'a set)) {} (chain_boundary p c)) \<and>
       (\<forall>p X S. hom_boundary p X S = hom_boundary p X (topspace X \<inter> (S::'a set)))) \<and>
       (\<forall>p X S c. hom_boundary p X S c \<in> carrier(homology_group (p-1) (subtopology X (S::'a set)))) \<and>
       (\<forall>p. p \<le> 0 \<longrightarrow> hom_boundary p = (\<lambda>q r. \<lambda>t::'a chain set. undefined))"
  by (fact hom_boundary3)

lemma hom_boundary_default:
  "c \<notin> carrier(relative_homology_group p X S)
      \<Longrightarrow> hom_boundary p X S c = one(homology_group (p-1) (subtopology X S))"
  and hom_boundary_hom: "hom_boundary p X S \<in> hom (relative_homology_group p X S) (homology_group (p-1) (subtopology X S))"
  and hom_boundary_restrict [simp]: "hom_boundary p X (topspace X \<inter> S) = hom_boundary p X S"
  and hom_boundary_carrier: "hom_boundary p X S c \<in> carrier(homology_group (p-1) (subtopology X S))"
  and hom_boundary_trivial: "p \<le> 0 \<Longrightarrow> hom_boundary p = (\<lambda>q r t. undefined)"
  by (metis hom_boundary)+

lemma hom_boundary_chain_boundary:
  "\<lbrakk>singular_relcycle p X S c; 1 \<le> p\<rbrakk>
    \<Longrightarrow> hom_boundary (int p) X S (homologous_rel_set p X S c) =
        homologous_rel_set (p - Suc 0) (subtopology X S) {} (chain_boundary p c)"
  by (metis hom_boundary)+

lemma hom_chain_map:
   "\<lbrakk>continuous_map X Y f; f ` S \<subseteq> T\<rbrakk>
        \<Longrightarrow> (chain_map p f) \<in> hom (relcycle_group p X S) (relcycle_group p Y T)"
  by (force simp: chain_map_add singular_relcycle_chain_map hom_def)


lemma hom_induced1:
  "\<exists>hom_relmap.
    (\<forall>p X S Y T f.
        continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T
        \<longrightarrow> (hom_relmap p X S Y T f) \<in> hom (relative_homology_group (int p) X S)
                               (relative_homology_group (int p) Y T)) \<and>
    (\<forall>p X S Y T f c.
        continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and>
        singular_relcycle p X S c
        \<longrightarrow> hom_relmap p X S Y T f (homologous_rel_set p X S c) =
            homologous_rel_set p Y T (chain_map p f c))"
proof -
  have "\<exists>y. (y \<in> hom (relative_homology_group (int p) X S) (relative_homology_group (int p) Y T)) \<and>
           (\<forall>c. singular_relcycle p X S c \<longrightarrow>
                y (homologous_rel_set p X S c) = homologous_rel_set p Y T (chain_map p f c))"
    if contf: "continuous_map X Y f" and fim: "f ` (topspace X \<inter> S) \<subseteq> T"
    for p X S Y T and f :: "'a \<Rightarrow> 'b"
  proof -
    let ?f = "(#>\<^bsub>relcycle_group p Y T\<^esub>) (singular_relboundary_set p Y T) \<circ> chain_map p f"
    let ?F = "\<lambda>x. singular_relboundary_set p X S #>\<^bsub>relcycle_group p X S\<^esub> x"
    have "chain_map p f \<in> hom (relcycle_group p X S) (relcycle_group p Y T)"
      by (metis contf fim hom_chain_map relcycle_group_restrict)
    then have 1: "?f \<in> hom (relcycle_group p X S) (relative_homology_group (int p) Y T)"
      by (simp add: hom_compose normal.r_coset_hom_Mod normal_subgroup_singular_relboundary_relcycle relative_homology_group_def)
    have 2: "singular_relboundary_set p X S \<lhd> relcycle_group p X S"
      using normal_subgroup_singular_relboundary_relcycle by blast
    have 3: "?f x = ?f y"
      if "singular_relcycle p X S x" "singular_relcycle p X S y" "?F x = ?F y" for x y
    proof -
      have "homologous_rel p X S x y"
        by (metis (no_types) homologous_rel_set_eq right_coset_singular_relboundary that(3))
      then have "singular_relboundary p Y T (chain_map p f (x - y))"
        using  singular_relboundary_chain_map [OF _ contf fim] by (simp add: homologous_rel_def)
      then have "singular_relboundary p Y T (chain_map p f x - chain_map p f y)"
        by (simp add: chain_map_diff)
      with that
      show ?thesis
        by (metis comp_apply homologous_rel_def homologous_rel_set_eq right_coset_singular_relboundary)
    qed
    obtain g where "g \<in> hom (relcycle_group p X S Mod singular_relboundary_set p X S)
                            (relative_homology_group (int p) Y T)"
                   "\<And>x. x \<in> singular_relcycle_set p X S \<Longrightarrow> g (?F x) = ?f x"
      using FactGroup_universal [OF 1 2 3, unfolded carrier_relcycle_group] by blast
    then show ?thesis
      by (force simp: right_coset_singular_relboundary nontrivial_relative_homology_group)
  qed
  then show ?thesis
    apply (simp flip: all_conj_distrib)
    apply ((subst choice_iff [symmetric])+)
    apply metis
    done
qed

lemma hom_induced2:
    "\<exists>hom_relmap.
      (\<forall>p X S Y T f.
          continuous_map X Y f \<and>
          f ` (topspace X \<inter> S) \<subseteq> T
          \<longrightarrow> (hom_relmap p X S Y T f) \<in> hom (relative_homology_group p X S)
                                 (relative_homology_group p Y T)) \<and>
      (\<forall>p X S Y T f c.
          continuous_map X Y f \<and>
          f ` (topspace X \<inter> S) \<subseteq> T \<and>
          singular_relcycle p X S c
          \<longrightarrow> hom_relmap p X S Y T f (homologous_rel_set p X S c) =
              homologous_rel_set p Y T (chain_map p f c)) \<and>
      (\<forall>p. p < 0 \<longrightarrow> hom_relmap p = (\<lambda>X S Y T f c. undefined))"
  (is "\<exists>d. ?\<Phi> d")
proof -
  have *: "\<exists>f. \<Phi>(\<lambda>p. if p < 0 then \<lambda>X S Y T f c. undefined else f(nat p)) \<Longrightarrow> \<exists>f. \<Phi> f"  for \<Phi>
    by blast
  show ?thesis
    apply (rule * [OF ex_forward [OF hom_induced1]])
    apply (simp add: not_le relative_homology_group_def nat_diff_distrib' int_eq_iff nat_diff_distrib flip: nat_1)
    done
qed

lemma hom_induced3:
  "\<exists>hom_relmap.
    ((\<forall>p X S Y T f c.
        ~(continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and>
          c \<in> carrier(relative_homology_group p X S))
        \<longrightarrow> hom_relmap p X S Y T f c = one(relative_homology_group p Y T)) \<and>
    (\<forall>p X S Y T f.
        hom_relmap p X S Y T f \<in> hom (relative_homology_group p X S) (relative_homology_group p Y T)) \<and>
    (\<forall>p X S Y T f c.
        continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and> singular_relcycle p X S c
        \<longrightarrow> hom_relmap p X S Y T f (homologous_rel_set p X S c) =
            homologous_rel_set p Y T (chain_map p f c)) \<and>
    (\<forall>p X S Y T.
        hom_relmap p X S Y T =
        hom_relmap p X (topspace X \<inter> S) Y (topspace Y \<inter> T))) \<and>
    (\<forall>p X S Y f T c.
        hom_relmap p X S Y T f c \<in> carrier(relative_homology_group p Y T)) \<and>
    (\<forall>p. p < 0 \<longrightarrow> hom_relmap p = (\<lambda>X S Y T f c. undefined))"
  (is "\<exists>x. ?P x \<and> ?Q x \<and> ?R x")
proof -
  have "\<And>x. ?Q x \<Longrightarrow> ?R x"
    by (erule all_forward) (fastforce simp: relative_homology_group_def)
  moreover have "\<exists>x. ?P x \<and> ?Q x"
  proof -
    obtain hom_relmap:: "[int,'a topology,'a set,'b topology,'b set,'a \<Rightarrow> 'b,('a chain) set] \<Rightarrow> ('b chain) set"
      where 1: "\<And>p X S Y T f. \<lbrakk>continuous_map X Y f; f ` (topspace X \<inter> S) \<subseteq> T\<rbrakk> \<Longrightarrow>
                   hom_relmap p X S Y T f
                   \<in> hom (relative_homology_group p X S) (relative_homology_group p Y T)"
        and 2: "\<And>p X S Y T f c.
                   \<lbrakk>continuous_map X Y f; f ` (topspace X \<inter> S) \<subseteq> T; singular_relcycle p X S c\<rbrakk>
                   \<Longrightarrow>
                   hom_relmap (int p) X S Y T f (homologous_rel_set p X S c) =
                   homologous_rel_set p Y T (chain_map p f c)"
        and 3: "(\<forall>p. p < 0 \<longrightarrow> hom_relmap p = (\<lambda>X S Y T f c. undefined))"
      using hom_induced2 [where ?'a='a and ?'b='b]
      by (metis (mono_tags, lifting))
    have 4: "\<lbrakk>continuous_map X Y f; f ` (topspace X \<inter> S) \<subseteq> T; c \<in> carrier (relative_homology_group p X S)\<rbrakk> \<Longrightarrow>
        hom_relmap p X (topspace X \<inter> S) Y (topspace Y \<inter> T) f c
           \<in> carrier (relative_homology_group p Y T)"
      for p X S Y f T c
      using hom_carrier [OF 1 [of X Y f "topspace X \<inter> S" "topspace Y \<inter> T" p]] 
            continuous_map_image_subset_topspace by fastforce
    have inhom: "(\<lambda>c. if continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and>
                      c \<in> carrier (relative_homology_group p X S)
            then hom_relmap p X (topspace X \<inter> S) Y (topspace Y \<inter> T) f c
            else \<one>\<^bsub>relative_homology_group p Y T\<^esub>)
       \<in> hom (relative_homology_group p X S) (relative_homology_group p Y T)" (is "?h \<in> hom ?GX ?GY")
      for p X S Y T f
    proof (rule homI)
      show "\<And>x. x \<in> carrier ?GX \<Longrightarrow> ?h x \<in> carrier ?GY"
        by (auto simp: 4 group.is_monoid)
      show "?h (x \<otimes>\<^bsub>?GX\<^esub> y) = ?h x \<otimes>\<^bsub>?GY\<^esub>?h y" if "x \<in> carrier ?GX" "y \<in> carrier ?GX" for x y
      proof (cases "p < 0")
        case True
        with that show ?thesis
          by (simp add: relative_homology_group_def singleton_group_def 3)
      next
        case False
        show ?thesis
        proof (cases "continuous_map X Y f")
          case True
          then have "f ` (topspace X \<inter> S) \<subseteq> topspace Y"
            using continuous_map_image_subset_topspace by blast
          then show ?thesis
            using True False that
            using 1 [of X Y f "topspace X \<inter> S" "topspace Y \<inter> T" p]
          by (simp add: 4 continuous_map_image_subset_topspace hom_mult not_less group.is_monoid monoid.m_closed Int_left_absorb)
        qed (simp add: group.is_monoid)
      qed
    qed
    have hrel: "\<lbrakk>continuous_map X Y f; f ` (topspace X \<inter> S) \<subseteq> T; singular_relcycle p X S c\<rbrakk>
            \<Longrightarrow> hom_relmap (int p) X (topspace X \<inter> S) Y (topspace Y \<inter> T)
              f (homologous_rel_set p X S c) = homologous_rel_set p Y T (chain_map p f c)"
        for p X S Y T f c
      using 2 [of X Y f "topspace X \<inter> S" "topspace Y \<inter> T" p c]
            continuous_map_image_subset_topspace by fastforce
    show ?thesis
      apply (rule_tac x="\<lambda>p X S Y T f c.
               if continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and>
                  c \<in> carrier(relative_homology_group p X S)
               then hom_relmap p X (topspace X \<inter> S) Y (topspace Y \<inter> T) f c
               else one(relative_homology_group p Y T)" in exI)
      apply (simp add: Int_left_absorb subtopology_restrict carrier_relative_homology_group
          group.is_monoid group.restrict_hom_iff 4 inhom hrel cong: if_cong)
      apply (force simp: continuous_map_def intro!: ext)
      done
  qed
  ultimately show ?thesis
    by auto
qed


consts hom_induced:: "[int,'a topology,'a set,'b topology,'b set,'a \<Rightarrow> 'b,('a chain) set] \<Rightarrow> ('b chain) set"
specification (hom_induced)
  hom_induced:
    "((\<forall>p X S Y T f c.
        ~(continuous_map X Y f \<and>
          f ` (topspace X \<inter> S) \<subseteq> T \<and>
          c \<in> carrier(relative_homology_group p X S))
        \<longrightarrow> hom_induced p X (S::'a set) Y (T::'b set) f c =
            one(relative_homology_group p Y T)) \<and>
    (\<forall>p X S Y T f.
        (hom_induced p X (S::'a set) Y (T::'b set) f) \<in> hom (relative_homology_group p X S)
                           (relative_homology_group p Y T)) \<and>
    (\<forall>p X S Y T f c.
        continuous_map X Y f \<and>
        f ` (topspace X \<inter> S) \<subseteq> T \<and>
        singular_relcycle p X S c
        \<longrightarrow> hom_induced p X (S::'a set) Y (T::'b set) f (homologous_rel_set p X S c) =
            homologous_rel_set p Y T (chain_map p f c)) \<and>
    (\<forall>p X S Y T.
        hom_induced p X (S::'a set) Y (T::'b set) =
        hom_induced p X (topspace X \<inter> S) Y (topspace Y \<inter> T))) \<and>
    (\<forall>p X S Y f T c.
        hom_induced p X (S::'a set) Y (T::'b set) f c \<in>
        carrier(relative_homology_group p Y T)) \<and>
    (\<forall>p. p < 0 \<longrightarrow> hom_induced p = (\<lambda>X S Y T. \<lambda>f::'a\<Rightarrow>'b. \<lambda>c. undefined))"
  by (fact hom_induced3)

lemma hom_induced_default:
    "~(continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and> c \<in> carrier(relative_homology_group p X S))
          \<Longrightarrow> hom_induced p X S Y T f c = one(relative_homology_group p Y T)"
  and hom_induced_hom:
    "hom_induced p X S Y T f \<in> hom (relative_homology_group p X S) (relative_homology_group p Y T)"
  and hom_induced_restrict [simp]:
    "hom_induced p X (topspace X \<inter> S) Y (topspace Y \<inter> T) = hom_induced p X S Y T"
  and hom_induced_carrier:
    "hom_induced p X S Y T f c \<in> carrier(relative_homology_group p Y T)"
  and hom_induced_trivial: "p < 0 \<Longrightarrow> hom_induced p = (\<lambda>X S Y T f c. undefined)"
  by (metis hom_induced)+

lemma hom_induced_chain_map_gen:
  "\<lbrakk>continuous_map X Y f; f ` (topspace X \<inter> S) \<subseteq> T; singular_relcycle p X S c\<rbrakk>
  \<Longrightarrow> hom_induced p X S Y T f (homologous_rel_set p X S c) = homologous_rel_set p Y T (chain_map p f c)"
  by (metis hom_induced)

lemma hom_induced_chain_map:
   "\<lbrakk>continuous_map X Y f; f ` S \<subseteq> T; singular_relcycle p X S c\<rbrakk>
    \<Longrightarrow> hom_induced p X S Y T f (homologous_rel_set p X S c)
      = homologous_rel_set p Y T (chain_map p f c)"
  by (meson Int_lower2 hom_induced image_subsetI image_subset_iff subset_iff)


lemma hom_induced_eq:
  assumes "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x"
  shows "hom_induced p X S Y T f = hom_induced p X S Y T g"
proof -
  consider "p < 0" | n where "p = int n"
    by (metis int_nat_eq not_less)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp add: hom_induced_trivial)
  next
    case 2
    have "hom_induced n X S Y T f C = hom_induced n X S Y T g C" for C
    proof -
      have "continuous_map X Y f \<and> f ` (topspace X \<inter> S) \<subseteq> T \<and> C \<in> carrier (relative_homology_group n X S)
        \<longleftrightarrow> continuous_map X Y g \<and> g ` (topspace X \<inter> S) \<subseteq> T \<and> C \<in> carrier (relative_homology_group n X S)"
        (is "?P = ?Q")
        by (metis IntD1 assms continuous_map_eq image_cong)
      then consider "\<not> ?P \<and> \<not> ?Q" | "?P \<and> ?Q"
        by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          by (simp add: hom_induced_default)
      next
        case 2
        have "homologous_rel_set n Y T (chain_map n f c) = homologous_rel_set n Y T (chain_map n g c)"
          if "continuous_map X Y f" "f ` (topspace X \<inter> S) \<subseteq> T"
             "continuous_map X Y g" "g ` (topspace X \<inter> S) \<subseteq> T"
             "C = homologous_rel_set n X S c" "singular_relcycle n X S c"
          for c
        proof -
          have "chain_map n f c = chain_map n g c"
            using assms chain_map_eq singular_relcycle that by blast
          then show ?thesis
            by simp
        qed
        with 2 show ?thesis
          by (auto simp: relative_homology_group_def carrier_FactGroup
              right_coset_singular_relboundary hom_induced_chain_map_gen)
      qed
    qed
    with 2 show ?thesis
      by auto
  qed
qed


subsection\<open>Towards the Eilenberg-Steenrod axioms\<close>

text\<open>First prove we get functors into abelian groups with the boundary map
 being a natural transformation between them, and prove Eilenberg-Steenrod
 axioms (we also prove additivity a bit later on if one counts that). \<close>
(*1. Exact sequence from the inclusions and boundary map
    H_{p+1} X --(j')\<longlongrightarrow> H_{p+1}X (A) --(d')\<longlongrightarrow> H_p A --(i')\<longlongrightarrow> H_p X
 2. Dimension axiom: H_p X is trivial for one-point X and p =/= 0
 3. Homotopy invariance of the induced map
 4. Excision: inclusion (X - U,A - U) --(i')\<longlongrightarrow> X (A) induces an isomorphism
when cl U \<subseteq> int A*)


lemma abelian_relative_homology_group [simp]:
   "comm_group(relative_homology_group p X S)"
  by (simp add: comm_group.abelian_FactGroup relative_homology_group_def subgroup_singular_relboundary_relcycle)

lemma abelian_homology_group: "comm_group(homology_group p X)"
  by simp


lemma hom_induced_id_gen:
  assumes contf: "continuous_map X X f" and feq: "\<And>x. x \<in> topspace X \<Longrightarrow> f x = x"
    and c: "c \<in> carrier (relative_homology_group p X S)"
  shows "hom_induced p X S X S f c = c"
proof -
  consider "p < 0" | n where "p = int n"
    by (metis int_nat_eq not_less)
  then show ?thesis
  proof cases
    case 1
    with c show ?thesis
      by (simp add: hom_induced_trivial relative_homology_group_def)
  next
    case 2
    have cm: "chain_map n f d = d" if "singular_relcycle n X S d" for d
      using that assms by (auto simp: chain_map_id_gen singular_relcycle)
    have "f ` (topspace X \<inter> S) \<subseteq> S"
      using feq by auto
    with 2 c show ?thesis
      by (auto simp: nontrivial_relative_homology_group carrier_FactGroup
          cm right_coset_singular_relboundary hom_induced_chain_map_gen assms)
  qed
qed


lemma hom_induced_id:
   "c \<in> carrier (relative_homology_group p X S) \<Longrightarrow> hom_induced p X S X S id c = c"
  by (rule hom_induced_id_gen) auto

lemma hom_induced_compose:
  assumes "continuous_map X Y f" "f ` S \<subseteq> T" "continuous_map Y Z g" "g ` T \<subseteq> U"
  shows "hom_induced p X S Z U (g \<circ> f) = hom_induced p Y T Z U g \<circ> hom_induced p X S Y T f"
proof -
  consider (neg) "p < 0" | (int) n where "p = int n"
    by (metis int_nat_eq not_less)
  then show ?thesis
  proof cases
    case int
    have gf: "continuous_map X Z (g \<circ> f)"
      using assms continuous_map_compose by fastforce
    have gfim: "(g \<circ> f) ` S \<subseteq> U"
      unfolding o_def using assms by blast
    have sr: "\<And>a. singular_relcycle n X S a \<Longrightarrow> singular_relcycle n Y T (chain_map n f a)"
      by (simp add: assms singular_relcycle_chain_map)
    show ?thesis
    proof
      fix c
      show "hom_induced p X S Z U (g \<circ> f) c = (hom_induced p Y T Z U g \<circ> hom_induced p X S Y T f) c"
      proof (cases "c \<in> carrier(relative_homology_group p X S)")
        case True
        with gfim show ?thesis
          unfolding int
          by (auto simp: carrier_relative_homology_group gf gfim assms sr chain_map_compose  hom_induced_chain_map)
      next
        case False
        then show ?thesis
          by (simp add: hom_induced_default hom_one [OF hom_induced_hom])
      qed
    qed
  qed (force simp: hom_induced_trivial)
qed

lemma hom_induced_compose':
  assumes "continuous_map X Y f" "f ` S \<subseteq> T" "continuous_map Y Z g" "g ` T \<subseteq> U"
  shows "hom_induced p Y T Z U g (hom_induced p X S Y T f x) = hom_induced p X S Z U (g \<circ> f) x"
  using hom_induced_compose [OF assms] by simp

lemma naturality_hom_induced:
  assumes "continuous_map X Y f" "f ` S \<subseteq> T"
  shows "hom_boundary q Y T \<circ> hom_induced q X S Y T f
       = hom_induced (q - 1) (subtopology X S) {} (subtopology Y T) {} f \<circ> hom_boundary q X S"
proof (cases "q \<le> 0")
  case False
  then obtain p where p1: "p \<ge> Suc 0" and q: "q = int p"
    using zero_le_imp_eq_int by force
  show ?thesis
  proof
    fix c
    show "(hom_boundary q Y T \<circ> hom_induced q X S Y T f) c =
          (hom_induced (q - 1) (subtopology X S) {} (subtopology Y T) {} f \<circ> hom_boundary q X S) c"
    proof (cases "c \<in> carrier(relative_homology_group p X S)")
      case True
      then obtain a where ceq: "c = homologous_rel_set p X S a" and a: "singular_relcycle p X S a"
        by (force simp: carrier_relative_homology_group)
      then have sr: "singular_relcycle p Y T (chain_map p f a)"
        using assms singular_relcycle_chain_map by fastforce
      then have sb: "singular_relcycle (p - Suc 0) (subtopology X S) {} (chain_boundary p a)"
        by (metis One_nat_def a chain_boundary_boundary singular_chain_0 singular_relcycle)
      have p1_eq: "int p - 1 = int (p - Suc 0)"
        using p1 by auto
      have cbm: "(chain_boundary p (chain_map p f a))
               = (chain_map (p - Suc 0) f (chain_boundary p a))"
        using a chain_boundary_chain_map singular_relcycle by blast
      have contf: "continuous_map (subtopology X S) (subtopology Y T) f"
        using assms
        by (auto simp: continuous_map_in_subtopology topspace_subtopology
            continuous_map_from_subtopology)
      show ?thesis
        unfolding q using assms p1 a
        by (simp add: cbm ceq contf hom_boundary_chain_boundary hom_induced_chain_map p1_eq sb sr)
    next
      case False
      with assms show ?thesis
        unfolding q o_def using assms
        apply (simp add: hom_induced_default hom_boundary_default)
        by (metis group_relative_homology_group hom_boundary hom_induced hom_one one_relative_homology_group)
    qed
  qed
qed (force simp: hom_induced_trivial hom_boundary_trivial)



lemma homology_exactness_axiom_1:
   "exact_seq ([homology_group (p-1) (subtopology X S), relative_homology_group p X S, homology_group p X],
              [hom_boundary p X S,hom_induced p X {} X S id])"
proof -
  consider (neg) "p < 0" | (int) n where "p = int n"
    by (metis int_nat_eq not_less)
  then have "(hom_induced p X {} X S id) ` carrier (homology_group p X)
           = kernel (relative_homology_group p X S) (homology_group (p-1) (subtopology X S))
                    (hom_boundary p X S)"
  proof cases
    case neg
    then show ?thesis
      unfolding kernel_def singleton_group_def relative_homology_group_def
      by (auto simp: hom_induced_trivial hom_boundary_trivial)
  next
    case int
    have "hom_induced (int m) X {} X S id ` carrier (relative_homology_group (int m) X {})
        = carrier (relative_homology_group (int m) X S) \<inter>
          {c. hom_boundary (int m) X S c = \<one>\<^bsub>relative_homology_group (int m - 1) (subtopology X S) {}\<^esub>}" for m
    proof (cases m)
      case 0
      have "hom_induced 0 X {} X S id ` carrier (relative_homology_group 0 X {})
          = carrier (relative_homology_group 0 X S)"   (is "?lhs = ?rhs")
      proof
        show "?lhs \<subseteq> ?rhs"
          using hom_induced_hom [of 0 X "{}" X S id]
          by (simp add: hom_induced_hom hom_carrier)
        show "?rhs \<subseteq> ?lhs"
          apply (clarsimp simp add: image_iff carrier_relative_homology_group [of 0, simplified] singular_relcycle)
          apply (force simp: chain_map_id_gen chain_boundary_def singular_relcycle
              hom_induced_chain_map [of concl: 0, simplified])
          done
      qed
      with 0 show ?thesis
        by (simp add: hom_boundary_trivial relative_homology_group_def [of "-1"] singleton_group_def)
    next
      case (Suc n)
      have "(hom_induced (int (Suc n)) X {} X S id \<circ>
            homologous_rel_set (Suc n) X {}) ` singular_relcycle_set (Suc n) X {}
          = homologous_rel_set (Suc n) X S `
            (singular_relcycle_set (Suc n) X S \<inter>
             {c. hom_boundary (int (Suc n)) X S (homologous_rel_set (Suc n) X S c)
               = singular_relboundary_set n (subtopology X S) {}})"
        (is "?lhs = ?rhs")
      proof -
        have 1: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<longleftrightarrow> x \<in> C) \<Longrightarrow> f ` (A \<inter> B) = f ` (A \<inter> C)" for f A B C
          by blast
        have 2: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> B \<and> f x = f y; \<And>x. x \<in> B \<Longrightarrow> \<exists>y. y \<in> A \<and> f x = f y\<rbrakk>
    \<Longrightarrow> f ` A = f ` B" for f A B
          by blast
        have "?lhs = homologous_rel_set (Suc n) X S ` singular_relcycle_set (Suc n) X {}"
          using hom_induced_chain_map chain_map_ident [of _ X] singular_relcycle 
          by (smt (verit) bot.extremum comp_apply continuous_map_id image_cong image_empty mem_Collect_eq)
        also have "\<dots> = homologous_rel_set (Suc n) X S `
                         (singular_relcycle_set (Suc n) X S \<inter>
                          {c. singular_relboundary n (subtopology X S) {} (chain_boundary (Suc n) c)})"
        proof (rule 2)
          fix c
          assume "c \<in> singular_relcycle_set (Suc n) X {}"
          then show "\<exists>y. y \<in> singular_relcycle_set (Suc n) X S \<inter>
                         {c. singular_relboundary n (subtopology X S) {} (chain_boundary (Suc n) c)} \<and>
                    homologous_rel_set (Suc n) X S c = homologous_rel_set (Suc n) X S y"
            using singular_cycle singular_relcycle by (fastforce simp: singular_boundary)
        next
          fix c
          assume c: "c \<in> singular_relcycle_set (Suc n) X S \<inter>
                      {c. singular_relboundary n (subtopology X S) {} (chain_boundary (Suc n) c)}"
          then obtain d where d: "singular_chain (Suc n) (subtopology X S) d"
            "chain_boundary (Suc n) d = chain_boundary (Suc n) c"
            by (auto simp: singular_boundary)
          with c have "c - d \<in> singular_relcycle_set (Suc n) X {}"
            by (auto simp: singular_cycle chain_boundary_diff singular_chain_subtopology singular_relcycle singular_chain_diff)
          moreover have "homologous_rel_set (Suc n) X S c = homologous_rel_set (Suc n) X S (c - d)"
          proof (simp add: homologous_rel_set_eq)
            show "homologous_rel (Suc n) X S c (c - d)"
              using d by (simp add: homologous_rel_def singular_chain_imp_relboundary)
          qed
          ultimately show "\<exists>y. y \<in> singular_relcycle_set (Suc n) X {} \<and>
                    homologous_rel_set (Suc n) X S c = homologous_rel_set (Suc n) X S y"
            by blast
        qed
        also have "\<dots> = ?rhs"
          by (rule 1) (simp add: hom_boundary_chain_boundary homologous_rel_set_eq_relboundary del: of_nat_Suc)
        finally show "?lhs = ?rhs" .
      qed
      with Suc show ?thesis
        unfolding carrier_relative_homology_group image_comp id_def by auto
    qed
    then show ?thesis
      by (auto simp: kernel_def int)
  qed
  then show ?thesis
    using hom_boundary_hom hom_induced_hom
    by (force simp: group_hom_def group_hom_axioms_def)
qed


lemma homology_exactness_axiom_2:
   "exact_seq ([homology_group (p-1) X, homology_group (p-1) (subtopology X S), relative_homology_group p X S],
              [hom_induced (p-1) (subtopology X S) {} X {} id, hom_boundary p X S])"
proof -
  consider (neg) "p \<le> 0" | (int) n where "p = int (Suc n)"
    by (metis linear not0_implies_Suc of_nat_0 zero_le_imp_eq_int)
  then have "kernel (relative_homology_group (p-1) (subtopology X S) {})
                     (relative_homology_group (p-1) X {})
                     (hom_induced (p-1) (subtopology X S) {} X {} id)
            = hom_boundary p X S ` carrier (relative_homology_group p X S)"
  proof cases
    case neg
    obtain x where "x \<in> carrier (relative_homology_group p X S)"
      using group_relative_homology_group group.is_monoid by blast
    with neg show ?thesis
      unfolding kernel_def singleton_group_def relative_homology_group_def
      by (force simp: hom_induced_trivial hom_boundary_trivial)
  next
    case int
    have "hom_boundary (int (Suc n)) X S ` carrier (relative_homology_group (int (Suc n)) X S)
        = carrier (relative_homology_group n (subtopology X S) {}) \<inter>
          {c. hom_induced n (subtopology X S) {} X {} id c =
           \<one>\<^bsub>relative_homology_group n X {}\<^esub>}"
        (is "?lhs = ?rhs")
    proof -
      have 1: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<longleftrightarrow> x \<in> C) \<Longrightarrow> f ` (A \<inter> B) = f ` (A \<inter> C)" for f A B C
        by blast
      have 2: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B \<longleftrightarrow> x \<in> f -` C) \<Longrightarrow> f ` (A \<inter> B) = f ` A \<inter> C" for f A B C
        by blast
      have "?lhs = homologous_rel_set n (subtopology X S) {}
                   ` (chain_boundary (Suc n) ` singular_relcycle_set (Suc n) X S)"
        unfolding carrier_relative_homology_group image_comp
        by (rule image_cong [OF refl]) (simp add: o_def hom_boundary_chain_boundary del: of_nat_Suc)
      also have "\<dots> = homologous_rel_set n (subtopology X S) {} `
                       (singular_relcycle_set n (subtopology X S) {} \<inter> singular_relboundary_set n X {})"
        by (force simp: singular_relcycle singular_boundary chain_boundary_boundary_alt)
      also have "\<dots> = ?rhs"
        unfolding carrier_relative_homology_group vimage_def
        by (intro 2) (auto simp: hom_induced_chain_map chain_map_ident homologous_rel_set_eq_relboundary singular_relcycle)
      finally show ?thesis .
    qed
    then show ?thesis
      by (auto simp: kernel_def int)
  qed
  then show ?thesis
    using hom_boundary_hom hom_induced_hom
    by (force simp: group_hom_def group_hom_axioms_def)
qed


lemma homology_exactness_axiom_3:
   "exact_seq ([relative_homology_group p X S, homology_group p X, homology_group p (subtopology X S)],
              [hom_induced p X {} X S id, hom_induced p (subtopology X S) {} X {} id])"
proof (cases "p < 0")
  case True
  then show ?thesis
    unfolding relative_homology_group_def
    by (simp add: group_hom.kernel_to_trivial_group group_hom_axioms_def group_hom_def hom_induced_trivial)
next
  case False
  then obtain n where peq: "p = int n"
    by (metis int_ops(1) linorder_neqE_linordered_idom pos_int_cases)
  have "hom_induced n (subtopology X S) {} X {} id `
        (homologous_rel_set n (subtopology X S) {} `
        singular_relcycle_set n (subtopology X S) {})
      = {c \<in> homologous_rel_set n X {} ` singular_relcycle_set n X {}.
         hom_induced n X {} X S id c = singular_relboundary_set n X S}"
        (is "?lhs = ?rhs")
  proof -
    have 2: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> \<exists>y. y \<in> B \<and> f x = f y; \<And>x. x \<in> B \<Longrightarrow> \<exists>y. y \<in> A \<and> f x = f y\<rbrakk>
    \<Longrightarrow> f ` A = f ` B" for f A B
      by blast
    have "?lhs = homologous_rel_set n X {} ` (singular_relcycle_set n (subtopology X S) {})"
      by (smt (verit) chain_map_ident continuous_map_id_subt empty_subsetI hom_induced_chain_map image_cong image_empty image_image mem_Collect_eq singular_relcycle)
    also have "\<dots> = homologous_rel_set n X {} ` (singular_relcycle_set n X {} \<inter> singular_relboundary_set n X S)"
    proof (rule 2)
      fix c
      assume "c \<in> singular_relcycle_set n (subtopology X S) {}"
      then show "\<exists>y. y \<in> singular_relcycle_set n X {} \<inter> singular_relboundary_set n X S \<and>
            homologous_rel_set n X {} c = homologous_rel_set n X {} y"
        using singular_chain_imp_relboundary singular_cycle singular_relboundary_imp_chain singular_relcycle by fastforce
    next
      fix c
      assume "c \<in> singular_relcycle_set n X {} \<inter> singular_relboundary_set n X S"
      then obtain d e where c: "singular_relcycle n X {} c" "singular_relboundary n X S c"
        and d:  "singular_chain n (subtopology X S) d"
        and e: "singular_chain (Suc n) X e" "chain_boundary (Suc n) e = c + d"
        using singular_relboundary_alt by blast
      then have "chain_boundary n (c + d) = 0"
        using chain_boundary_boundary_alt by fastforce
      then have "chain_boundary n c + chain_boundary n d = 0"
        by (metis chain_boundary_add)
      with c have "singular_relcycle n (subtopology X S) {} (- d)"
        by (metis (no_types) d eq_add_iff singular_cycle singular_relcycle_minus)
      moreover have "homologous_rel n X {} c (- d)"
        using c
        by (metis diff_minus_eq_add e homologous_rel_def singular_boundary)
      ultimately
      show "\<exists>y. y \<in> singular_relcycle_set n (subtopology X S) {} \<and>
            homologous_rel_set n X {} c = homologous_rel_set n X {} y"
        by (force simp: homologous_rel_set_eq)
    qed
    also have "\<dots> = homologous_rel_set n X {} `
                  (singular_relcycle_set n X {} \<inter> homologous_rel_set n X {} -` {x. hom_induced n X {} X S id x = singular_relboundary_set n X S})"
      by (rule 2) (auto simp: hom_induced_chain_map homologous_rel_set_eq_relboundary chain_map_ident [of _ X] singular_cycle cong: conj_cong)
    also have "\<dots> = ?rhs"
      by blast
    finally show ?thesis .
  qed
  then have "kernel (relative_homology_group p X {}) (relative_homology_group p X S) (hom_induced p X {} X S id)
      = hom_induced p (subtopology X S) {} X {} id ` carrier (relative_homology_group p (subtopology X S) {})"
    by (simp add: kernel_def carrier_relative_homology_group peq)
  then show ?thesis
    by (simp add: not_less group_hom_def group_hom_axioms_def hom_induced_hom)
qed


lemma homology_dimension_axiom:
  assumes X: "topspace X = {a}" and "p \<noteq> 0"
  shows "trivial_group(homology_group p X)"
proof (cases "p < 0")
  case True
  then show ?thesis
    by simp
next
  case False
  then obtain n where peq: "p = int n" "n > 0"
    by (metis assms(2) neq0_conv nonneg_int_cases not_less of_nat_0)
  have "homologous_rel_set n X {} ` singular_relcycle_set n X {} = {singular_relcycle_set n X {}}"
        (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
      using peq assms
      by (auto simp: image_subset_iff homologous_rel_set_eq_relboundary simp flip: singular_boundary_set_eq_cycle_singleton)
    have "singular_relboundary n X {} 0"
      by simp
    with peq assms
    show "?rhs \<subseteq> ?lhs"
      by (auto simp: image_iff simp flip: homologous_rel_eq_relboundary singular_boundary_set_eq_cycle_singleton)
  qed
  with peq assms show ?thesis
    unfolding trivial_group_def
    by (simp add:  carrier_relative_homology_group singular_boundary_set_eq_cycle_singleton [OF X])
qed


proposition homology_homotopy_axiom:
  assumes "homotopic_with (\<lambda>h. h ` S \<subseteq> T) X Y f g"
  shows "hom_induced p X S Y T f = hom_induced p X S Y T g"
proof (cases "p < 0")
  case True
  then show ?thesis
    by (simp add: hom_induced_trivial)
next
  case False
  then obtain n where peq: "p = int n"
    by (metis int_nat_eq not_le)
  have cont: "continuous_map X Y f" "continuous_map X Y g"
    using assms homotopic_with_imp_continuous_maps by blast+
  have im: "f ` (topspace X \<inter> S) \<subseteq> T" "g ` (topspace X \<inter> S) \<subseteq> T"
    using homotopic_with_imp_property assms by blast+
  show ?thesis
  proof
    fix c show "hom_induced p X S Y T f c = hom_induced p X S Y T g c"
    proof (cases "c \<in> carrier(relative_homology_group p X S)")
      case True
      then obtain a where a: "c = homologous_rel_set n X S a" "singular_relcycle n X S a"
        unfolding carrier_relative_homology_group peq by auto
      with assms homotopic_imp_homologous_rel_chain_maps show ?thesis
        by (force simp add: peq hom_induced_chain_map_gen cont im homologous_rel_set_eq)
    qed (simp add: hom_induced_default)
  qed
qed

proposition homology_excision_axiom:
  assumes "X closure_of U \<subseteq> X interior_of T" "T \<subseteq> S"
  shows
   "hom_induced p (subtopology X (S - U)) (T - U) (subtopology X S) T id
    \<in> iso (relative_homology_group p (subtopology X (S - U)) (T - U))
          (relative_homology_group p (subtopology X S) T)"
proof (cases "p < 0")
  case True
  then show ?thesis
    unfolding iso_def bij_betw_def relative_homology_group_def by (simp add: hom_induced_trivial)
next
  case False
  then obtain n where peq: "p = int n"
    by (metis int_nat_eq not_le)
  have cont: "continuous_map (subtopology X (S - U)) (subtopology X S) id"
    by (simp add: closure_of_subtopology_mono continuous_map_eq_image_closure_subset)
  have TU: "topspace X \<inter> (S - U) \<inter> (T - U) \<subseteq> T"
    by auto
  show ?thesis
  proof (simp add: iso_def peq carrier_relative_homology_group bij_betw_def hom_induced_hom, intro conjI)
    show "inj_on (hom_induced n (subtopology X (S - U)) (T - U) (subtopology X S) T id)
         (homologous_rel_set n (subtopology X (S - U)) (T - U) `
          singular_relcycle_set n (subtopology X (S - U)) (T - U))"
      unfolding inj_on_def
    proof (clarsimp simp add: homologous_rel_set_eq)
      fix c d
      assume c: "singular_relcycle n (subtopology X (S - U)) (T - U) c"
        and d: "singular_relcycle n (subtopology X (S - U)) (T - U) d"
        and hh: "hom_induced n (subtopology X (S - U)) (T - U) (subtopology X S) T id
                   (homologous_rel_set n (subtopology X (S - U)) (T - U) c)
               = hom_induced n (subtopology X (S - U)) (T - U) (subtopology X S) T id
                   (homologous_rel_set n (subtopology X (S - U)) (T - U) d)"
      then have scc: "singular_chain n (subtopology X (S - U)) c"
           and  scd: "singular_chain n (subtopology X (S - U)) d"
        using singular_relcycle by blast+
      have "singular_relboundary n (subtopology X (S - U)) (T - U) c"
        if srb: "singular_relboundary n (subtopology X S) T c"
          and src: "singular_relcycle n (subtopology X (S - U)) (T - U) c" for c
      proof -
        have [simp]: "(S - U) \<inter> (T - U) = T - U" "S \<inter> T = T"
          using \<open>T \<subseteq> S\<close> by blast+
        have c: "singular_chain n (subtopology X (S - U)) c"
             "singular_chain (n - Suc 0) (subtopology X (T - U)) (chain_boundary n c)"
          using that by (auto simp: singular_relcycle_def mod_subset_def subtopology_subtopology)
        obtain d e where d: "singular_chain (Suc n) (subtopology X S) d"
          and e: "singular_chain n (subtopology X T) e"
          and dce: "chain_boundary (Suc n) d = c + e"
          using srb by (auto simp: singular_relboundary_alt subtopology_subtopology)
        obtain m f g where f: "singular_chain (Suc n) (subtopology X (S - U)) f"
                       and g: "singular_chain (Suc n) (subtopology X T) g"
                       and dfg: "(singular_subdivision (Suc n) ^^ m) d = f + g"
          using excised_chain_exists [OF assms d] .
        obtain h where
            h0:  "\<And>p. h p 0 = (0 :: 'a chain)"
         and hdiff: "\<And>p c1 c2. h p (c1-c2) = h p c1 - h p c2"
         and hSuc: "\<And>p X c. singular_chain p X c \<Longrightarrow> singular_chain (Suc p) X (h p c)"
         and hchain: "\<And>p X c. singular_chain p X c
                           \<Longrightarrow> chain_boundary (Suc p) (h p c) + h (p - Suc 0) (chain_boundary p c)
                             = (singular_subdivision p ^^ m) c - c"
          using chain_homotopic_iterated_singular_subdivision by blast
        have hadd: "\<And>p c1 c2. h p (c1 + c2) = h p c1 + h p c2"
          by (metis add_diff_cancel diff_add_cancel hdiff)
        define c1 where "c1 \<equiv> f - h n c"
        define c2 where "c2 \<equiv> chain_boundary (Suc n) (h n e) - (chain_boundary (Suc n) g - e)"
        show ?thesis
          unfolding singular_relboundary_alt
        proof (intro exI conjI)
          show c1: "singular_chain (Suc n) (subtopology X (S - U)) c1"
            by (simp add: \<open>singular_chain n (subtopology X (S - U)) c\<close> c1_def f hSuc singular_chain_diff)
          have "chain_boundary (Suc n) (chain_boundary (Suc (Suc n)) (h (Suc n) d) + h n (c+e))
            = chain_boundary (Suc n) (f + g - d)"
              using hchain [OF d] by (simp add: dce dfg)
            then have "chain_boundary (Suc n) (h n (c + e))
                 = chain_boundary (Suc n) f + chain_boundary (Suc n) g - (c + e)"
              using chain_boundary_boundary_alt [of "Suc n" "subtopology X S"]
              by (simp add: chain_boundary_add chain_boundary_diff d hSuc dce)
            then have "chain_boundary (Suc n) (h n c) + chain_boundary (Suc n) (h n e)
                 = chain_boundary (Suc n) f + chain_boundary (Suc n) g - (c + e)"
              by (simp add: chain_boundary_add hadd)
            then have *: "chain_boundary (Suc n) (f - h n c) = c + (chain_boundary (Suc n) (h n e) - (chain_boundary (Suc n) g - e))"
              by (simp add: algebra_simps chain_boundary_diff)
            then show "chain_boundary (Suc n) c1 = c + c2"
            unfolding c1_def c2_def
              by (simp add: algebra_simps chain_boundary_diff)
            obtain "singular_chain n (subtopology X (S - U)) c2" "singular_chain n (subtopology X T) c2"
              using singular_chain_diff c c1 *
              unfolding c1_def c2_def
              by (metis add_diff_cancel_left' e g hSuc singular_chain_boundary_alt)
            then show "singular_chain n (subtopology (subtopology X (S - U)) (T - U)) c2"
              by (fastforce simp add: singular_chain_subtopology)
        qed
      qed
      then have "singular_relboundary n (subtopology X S) T (c - d) \<Longrightarrow>
                 singular_relboundary n (subtopology X (S - U)) (T - U) (c - d)"
        using c d singular_relcycle_diff by metis
      with hh show "homologous_rel n (subtopology X (S - U)) (T - U) c d"
        apply (simp add: hom_induced_chain_map cont c d chain_map_ident [OF scc] chain_map_ident [OF scd])
        using homologous_rel_set_eq homologous_rel_def by metis
    qed
  next
    have h: "homologous_rel_set n (subtopology X S) T a
          \<in> (\<lambda>x. homologous_rel_set n (subtopology X S) T (chain_map n id x)) `
            singular_relcycle_set n (subtopology X (S - U)) (T - U)"
      if a: "singular_relcycle n (subtopology X S) T a" for a
    proof -
      obtain c' where c': "singular_relcycle n (subtopology X (S - U)) (T - U) c'"
                          "homologous_rel n (subtopology X S) T a c'"
        using a by (blast intro: excised_relcycle_exists [OF assms])
      then have scc': "singular_chain n (subtopology X S) c'"
        using homologous_rel_singular_chain singular_relcycle that by blast
      then show ?thesis
        using scc' chain_map_ident [of _ "subtopology X S"] c' homologous_rel_set_eq
        by fastforce
    qed
    have "(\<lambda>x. homologous_rel_set n (subtopology X S) T (chain_map n id x)) `
          singular_relcycle_set n (subtopology X (S - U)) (T - U) =
          homologous_rel_set n (subtopology X S) T `
          singular_relcycle_set n (subtopology X S) T"
      by (force simp: cont h singular_relcycle_chain_map)
    then
    show "hom_induced n (subtopology X (S - U)) (T - U) (subtopology X S) T id `
          homologous_rel_set n (subtopology X (S - U)) (T - U) `
          singular_relcycle_set n (subtopology X (S - U)) (T - U)
        = homologous_rel_set n (subtopology X S) T ` singular_relcycle_set n (subtopology X S) T"
      by (simp add: image_comp o_def hom_induced_chain_map_gen cont TU topspace_subtopology
                       cong: image_cong_simp)
  qed
qed


subsection\<open>Additivity axiom\<close>

text\<open>Not in the original Eilenberg-Steenrod list but usually included nowadays,
following Milnor's "On Axiomatic Homology Theory".\<close>

lemma iso_chain_group_sum:
  assumes disj: "pairwise disjnt \<U>" and UU: "\<Union>\<U> = topspace X"
    and subs: "\<And>C T. \<lbrakk>compactin X C; path_connectedin X C; T \<in> \<U>; ~ disjnt C T\<rbrakk> \<Longrightarrow> C \<subseteq> T"
  shows "(\<lambda>f. sum' f \<U>) \<in> iso (sum_group \<U> (\<lambda>S. chain_group p (subtopology X S))) (chain_group p X)"
proof -
  have pw: "pairwise (\<lambda>i j. disjnt (singular_simplex_set p (subtopology X i))
                                   (singular_simplex_set p (subtopology X j))) \<U>"
  proof
    fix S T
    assume "S \<in> \<U>" "T \<in> \<U>" "S \<noteq> T"
    then show "disjnt (singular_simplex_set p (subtopology X S))
                      (singular_simplex_set p (subtopology X T))"
      using nonempty_standard_simplex [of p] disj
      by (fastforce simp: pairwise_def disjnt_def singular_simplex_subtopology image_subset_iff)
  qed
  have "\<exists>S\<in>\<U>. singular_simplex p (subtopology X S) f"
    if f: "singular_simplex p X f" for f
  proof -
    obtain x where x: "x \<in> topspace X" "x \<in> f ` standard_simplex p"
      using f nonempty_standard_simplex [of p] continuous_map_image_subset_topspace
      unfolding singular_simplex_def by fastforce
    then obtain S where "S \<in> \<U>" "x \<in> S"
      using UU by auto
    have "f ` standard_simplex p \<subseteq> S"
    proof (rule subs)
      have cont: "continuous_map (subtopology (powertop_real UNIV)
                                 (standard_simplex p)) X f"
        using f singular_simplex_def by auto
      show "compactin X (f ` standard_simplex p)"
        by (simp add: compactin_subtopology compactin_standard_simplex image_compactin [OF _ cont])
      show "path_connectedin X (f ` standard_simplex p)"
        by (simp add: path_connectedin_subtopology path_connectedin_standard_simplex path_connectedin_continuous_map_image [OF cont])
      have "standard_simplex p \<noteq> {}"
        by (simp add: nonempty_standard_simplex)
      then
      show "\<not> disjnt (f ` standard_simplex p) S"
        using x \<open>x \<in> S\<close> by (auto simp: disjnt_def)
    qed (auto simp: \<open>S \<in> \<U>\<close>)
    then show ?thesis
      by (meson \<open>S \<in> \<U>\<close> singular_simplex_subtopology that)
  qed
  then have "(\<Union>i\<in>\<U>. singular_simplex_set p (subtopology X i)) = singular_simplex_set p X"
    by (auto simp: singular_simplex_subtopology)
  then show ?thesis
    using iso_free_Abelian_group_sum [OF pw] by (simp add: chain_group_def)
qed

lemma relcycle_group_0_eq_chain_group: "relcycle_group 0 X {} = chain_group 0 X"
proof (rule monoid.equality)
  show "carrier (relcycle_group 0 X {}) = carrier (chain_group 0 X)"
    by (simp add: Collect_mono chain_boundary_def singular_cycle subset_antisym)
qed (simp_all add: relcycle_group_def chain_group_def)

proposition iso_cycle_group_sum:
  assumes disj: "pairwise disjnt \<U>" and UU: "\<Union>\<U> = topspace X"
    and subs: "\<And>C T. \<lbrakk>compactin X C; path_connectedin X C; T \<in> \<U>; \<not> disjnt C T\<rbrakk> \<Longrightarrow> C \<subseteq> T"
  shows "(\<lambda>f. sum' f \<U>) \<in> iso (sum_group \<U> (\<lambda>T. relcycle_group p (subtopology X T) {}))
                               (relcycle_group p X {})"
proof (cases "p = 0")
  case True
  then show ?thesis
    by (simp add: relcycle_group_0_eq_chain_group iso_chain_group_sum [OF assms])
next
  case False
  let ?SG = "(sum_group \<U> (\<lambda>T. chain_group p (subtopology X T)))"
  let ?PI = "(\<Pi>\<^sub>E T\<in>\<U>. singular_relcycle_set p (subtopology X T) {})"
  have "(\<lambda>f. sum' f \<U>) \<in> Group.iso (subgroup_generated ?SG (carrier ?SG \<inter> ?PI))
                            (subgroup_generated (chain_group p X) (singular_relcycle_set p X {}))"
  proof (rule group_hom.iso_between_subgroups)
    have iso: "(\<lambda>f. sum' f \<U>) \<in> Group.iso ?SG (chain_group p X)"
      by (auto simp: assms iso_chain_group_sum)
    then show "group_hom ?SG (chain_group p X) (\<lambda>f. sum' f \<U>)"
      by (auto simp: iso_imp_homomorphism group_hom_def group_hom_axioms_def)
    have B: "sum' f \<U> \<in> singular_relcycle_set p X {} \<longleftrightarrow> f \<in> (carrier ?SG \<inter> ?PI)"
      if "f \<in> (carrier ?SG)" for f
    proof -
      have f: "\<And>S. S \<in> \<U> \<longrightarrow> singular_chain p (subtopology X S) (f S)"
              "f \<in> extensional \<U>" "finite {i \<in> \<U>. f i \<noteq> 0}"
        using that by (auto simp: carrier_sum_group PiE_def Pi_def)
      then have rfin: "finite {S \<in> \<U>. restrict (chain_boundary p \<circ> f) \<U> S \<noteq> 0}"
        by (auto elim: rev_finite_subset)
      have "chain_boundary p ((\<Sum>x | x \<in> \<U> \<and> f x \<noteq> 0. f x)) = 0
        \<longleftrightarrow> (\<forall>S \<in> \<U>. chain_boundary p (f S) = 0)" (is "?cb = 0 \<longleftrightarrow> ?rhs")
      proof
        assume "?cb = 0"
        moreover have "?cb = sum' (\<lambda>S. chain_boundary p (f S)) \<U>"
          unfolding sum.G_def using rfin f
          by (force simp: chain_boundary_sum intro: sum.mono_neutral_right cong: conj_cong)
        ultimately have eq0: "sum' (\<lambda>S. chain_boundary p (f S)) \<U> = 0"
          by simp
        have "(\<lambda>f. sum' f \<U>) \<in> hom (sum_group \<U> (\<lambda>S. chain_group (p - Suc 0) (subtopology X S)))
                                    (chain_group (p - Suc 0) X)"
          and inj: "inj_on (\<lambda>f. sum' f \<U>) (carrier (sum_group \<U> (\<lambda>S. chain_group (p - Suc 0) (subtopology X S))))"
          using iso_chain_group_sum [OF assms, of "p-1"] by (auto simp: iso_def bij_betw_def)
        then have eq: "\<lbrakk>f \<in> (\<Pi>\<^sub>E i\<in>\<U>. singular_chain_set (p - Suc 0) (subtopology X i));
                    finite {S \<in> \<U>. f S \<noteq> 0}; sum' f \<U> = 0; S \<in> \<U>\<rbrakk> \<Longrightarrow> f S = 0" for f S
          apply (simp add: group_hom_def group_hom_axioms_def group_hom.inj_on_one_iff [of _ "chain_group (p-1) X"])
          apply (auto simp: carrier_sum_group fun_eq_iff that)
          done
        show ?rhs
        proof clarify
          fix S assume "S \<in> \<U>"
          then show "chain_boundary p (f S) = 0"
            using eq [of "restrict (chain_boundary p \<circ> f) \<U>" S] rfin f eq0
            by (simp add: singular_chain_boundary cong: conj_cong)
        qed
      next
        assume ?rhs
        then show "?cb = 0"
          by (force simp: chain_boundary_sum intro: sum.mono_neutral_right)
      qed
      moreover
      have "(\<And>S. S \<in> \<U> \<longrightarrow> singular_chain p (subtopology X S) (f S))
            \<Longrightarrow> singular_chain p X (\<Sum>x | x \<in> \<U> \<and> f x \<noteq> 0. f x)"
        by (metis (no_types, lifting) mem_Collect_eq singular_chain_subtopology singular_chain_sum)
      ultimately show ?thesis
        using f by (auto simp: carrier_sum_group sum.G_def singular_cycle PiE_iff)
    qed
    have "singular_relcycle_set p X {} \<subseteq> carrier (chain_group p X)"
      using subgroup.subset subgroup_singular_relcycle by blast
    then show "(\<lambda>f. sum' f \<U>) ` (carrier ?SG \<inter> ?PI) = singular_relcycle_set p X {}"
      using iso B unfolding Group.iso_def
      by (smt (verit, del_insts) Int_iff bij_betw_def image_iff mem_Collect_eq subset_antisym subset_iff)  
  qed (auto simp: assms iso_chain_group_sum)
  then show ?thesis
    by (simp add: relcycle_group_def sum_group_subgroup_generated subgroup_singular_relcycle)
qed


proposition homology_additivity_axiom_gen:
  assumes disj: "pairwise disjnt \<U>" and UU: "\<Union>\<U> = topspace X"
    and subs: "\<And>C T. \<lbrakk>compactin X C; path_connectedin X C; T \<in> \<U>; \<not> disjnt C T\<rbrakk> \<Longrightarrow> C \<subseteq> T"
  shows "(\<lambda>x. gfinprod (homology_group p X)
                       (\<lambda>V. hom_induced p (subtopology X V) {} X {} id (x V)) \<U>)
      \<in> iso (sum_group \<U> (\<lambda>S. homology_group p (subtopology X S))) (homology_group p X)"
     (is  "?h \<in> iso ?SG ?HG")
proof (cases "p < 0")
  case True
  then have [simp]: "gfinprod (singleton_group undefined) (\<lambda>v. undefined) \<U> = undefined"
    by (metis Pi_I carrier_singleton_group comm_group_def comm_monoid.gfinprod_closed singletonD singleton_abelian_group)
  show ?thesis
    using True
    apply (simp add: iso_def relative_homology_group_def hom_induced_trivial carrier_sum_group)
    apply (auto simp: singleton_group_def bij_betw_def inj_on_def fun_eq_iff)
    done
next
  case False
  then obtain n where peq: "p = int n"
    by (metis int_ops(1) linorder_neqE_linordered_idom pos_int_cases)
  interpret comm_group "homology_group p X"
    by (rule abelian_homology_group)
  show ?thesis
  proof (simp add: iso_def bij_betw_def, intro conjI)
    show "?h \<in> hom ?SG ?HG"
      by (rule hom_group_sum) (simp_all add: hom_induced_hom)
    then interpret group_hom ?SG ?HG ?h
      by (simp add: group_hom_def group_hom_axioms_def)
    have carrSG: "carrier ?SG
        = (\<lambda>x. \<lambda>S\<in>\<U>. homologous_rel_set n (subtopology X S) {} (x S))
          ` (carrier (sum_group \<U> (\<lambda>S. relcycle_group n (subtopology X S) {})))" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof (clarsimp simp: carrier_sum_group carrier_relative_homology_group peq)
        fix z
        assume z: "z \<in> (\<Pi>\<^sub>E S\<in>\<U>. homologous_rel_set n (subtopology X S) {} ` singular_relcycle_set n (subtopology X S) {})"
        and fin: "finite {S \<in> \<U>. z S \<noteq> singular_relboundary_set n (subtopology X S) {}}"
        then obtain c where c: "\<forall>S\<in>\<U>. singular_relcycle n (subtopology X S) {} (c S)
                                 \<and> z S = homologous_rel_set n (subtopology X S) {} (c S)"
          by (simp add: PiE_def Pi_def image_def) metis
        let ?f = "\<lambda>S\<in>\<U>. if singular_relboundary n (subtopology X S) {} (c S) then 0 else c S"
        have "z = (\<lambda>S\<in>\<U>. homologous_rel_set n (subtopology X S) {} (?f S))"
          by (smt (verit) PiE_restrict c homologous_rel_eq_relboundary restrict_apply restrict_ext singular_relboundary_0 z)
        moreover have "?f \<in> (\<Pi>\<^sub>E i\<in>\<U>. singular_relcycle_set n (subtopology X i) {})"
          by (simp add: c fun_eq_iff PiE_arb [OF z])
        moreover have "finite {i \<in> \<U>. ?f i \<noteq> 0}"
          using z c  by (intro finite_subset [OF _ fin]) auto 
        ultimately
        show "z \<in> (\<lambda>x. \<lambda>S\<in>\<U>. homologous_rel_set n (subtopology X S) {} (x S)) `
             {x \<in> \<Pi>\<^sub>E i\<in>\<U>. singular_relcycle_set n (subtopology X i) {}. finite {i \<in> \<U>. x i \<noteq> 0}}"
          by blast
      qed
      show "?rhs \<subseteq> ?lhs"
        by (force simp: peq carrier_sum_group carrier_relative_homology_group homologous_rel_set_eq_relboundary
                  elim: rev_finite_subset)
    qed
    have gf: "gfinprod (homology_group p X)
                 (\<lambda>V. hom_induced n (subtopology X V) {} X {} id
                      ((\<lambda>S\<in>\<U>. homologous_rel_set n (subtopology X S) {} (z S)) V)) \<U>
            = homologous_rel_set n X {} (sum' z \<U>)"  (is "?lhs = ?rhs")
      if z: "z \<in> carrier (sum_group \<U> (\<lambda>S. relcycle_group n (subtopology X S) {}))" for z
    proof -
      have hom_pi: "(\<lambda>S. homologous_rel_set n X {} (z S)) \<in> \<U> \<rightarrow> carrier (homology_group p X)"
        using z
        by (intro Pi_I) (force simp: peq carrier_sum_group carrier_relative_homology_group singular_chain_subtopology singular_cycle)
      have fin: "finite {S \<in> \<U>. z S \<noteq> 0}"
        using that by (force simp: carrier_sum_group)
      have "?lhs = gfinprod (homology_group p X) (\<lambda>S. homologous_rel_set n X {} (z S)) \<U>"
      proof (rule gfinprod_cong [OF refl Pi_I])
        fix i 
        show "i \<in> \<U> =simp=> hom_induced (int n) (subtopology X i) {} X {} id ((\<lambda>S\<in>\<U>. homologous_rel_set n (subtopology X S) {} (z S)) i)
                 = homologous_rel_set n X {} (z i)"
          using that
          by (auto simp: peq simp_implies_def carrier_sum_group PiE_def Pi_def chain_map_ident singular_cycle hom_induced_chain_map)
      qed (simp add: hom_induced_carrier peq)
      also have "\<dots> = gfinprod (homology_group p X)
                                (\<lambda>S. homologous_rel_set n X {} (z S)) {S \<in> \<U>. z S \<noteq> 0}"
      proof -
        have "homologous_rel_set n X {} 0 = singular_relboundary_set n X {}"
          by (metis homologous_rel_eq_relboundary singular_relboundary_0)
        with hom_pi peq show ?thesis
          by (intro gfinprod_mono_neutral_cong_right) auto
      qed
      also have "\<dots> = ?rhs"
      proof -
        have "gfinprod (homology_group p X) (\<lambda>S. homologous_rel_set n X {} (z S)) \<F>
          = homologous_rel_set n X {} (sum z \<F>)"
          if "finite \<F>" "\<F> \<subseteq> {S \<in> \<U>. z S \<noteq> 0}" for \<F>
          using that
        proof (induction \<F>)
          case empty
          have "\<one>\<^bsub>homology_group p X\<^esub> = homologous_rel_set n X {} 0"
            by (metis homologous_rel_eq_relboundary one_relative_homology_group peq singular_relboundary_0)
          then show ?case
            by simp
        next
          case (insert S \<F>)
          with z have pi: "(\<lambda>S. homologous_rel_set n X {} (z S)) \<in> \<F> \<rightarrow> carrier (homology_group p X)"
            "homologous_rel_set n X {} (z S) \<in> carrier (homology_group p X)"
            by (force simp: peq carrier_sum_group carrier_relative_homology_group singular_chain_subtopology singular_cycle)+
          have hom: "homologous_rel_set n X {} (z S) \<in> carrier (homology_group p X)"
            using insert z
            by (force simp: peq carrier_sum_group carrier_relative_homology_group singular_chain_subtopology singular_cycle)
          show ?case
            using insert z
          proof (simp add: pi)
            have "\<And>x. homologous_rel n X {} (z S + sum z \<F>) x
            \<Longrightarrow> \<exists>u v. homologous_rel n X {} (z S) u \<and> homologous_rel n X {} (sum z \<F>) v \<and> x = u + v"
              by (metis (no_types, lifting) diff_add_cancel diff_diff_eq2 homologous_rel_def homologous_rel_refl)
            with insert z
            show "homologous_rel_set n X {} (z S) \<otimes>\<^bsub>homology_group p X\<^esub> homologous_rel_set n X {} (sum z \<F>)
              = homologous_rel_set n X {} (z S + sum z \<F>)"
              using insert z by (auto simp: peq homologous_rel_add mult_relative_homology_group)
          qed
        qed
        with fin show ?thesis
          by (simp add: sum.G_def)
      qed
      finally show ?thesis .
    qed
    show "inj_on ?h (carrier ?SG)"
    proof (clarsimp simp add: inj_on_one_iff)
      fix x
      assume x: "x \<in> carrier (sum_group \<U> (\<lambda>S. homology_group p (subtopology X S)))"
        and 1: "gfinprod (homology_group p X) (\<lambda>V. hom_induced p (subtopology X V) {} X {} id (x V)) \<U>
              = \<one>\<^bsub>homology_group p X\<^esub>"
      have feq: "(\<lambda>S\<in>\<U>. homologous_rel_set n (subtopology X S) {} (z S))
               = (\<lambda>S\<in>\<U>. \<one>\<^bsub>homology_group p (subtopology X S)\<^esub>)"
        if z: "z \<in> carrier (sum_group \<U> (\<lambda>S. relcycle_group n (subtopology X S) {}))"
          and eq: "homologous_rel_set n X {} (sum' z \<U>) = \<one>\<^bsub>homology_group p X\<^esub>" for z
      proof -
        have "z \<in> (\<Pi>\<^sub>E S\<in>\<U>. singular_relcycle_set n (subtopology X S) {})" "finite {S \<in> \<U>. z S \<noteq> 0}"
          using z by (auto simp: carrier_sum_group)
        have "singular_relboundary n X {} (sum' z \<U>)"
          using eq singular_chain_imp_relboundary by (auto simp: relative_homology_group_def peq)
        then obtain d where scd: "singular_chain (Suc n) X d" and cbd: "chain_boundary (Suc n) d = sum' z \<U>"
          by (auto simp: singular_boundary)
        have *: "\<exists>d. singular_chain (Suc n) (subtopology X S) d \<and> chain_boundary (Suc n) d = z S"
          if "S \<in> \<U>" for S
        proof -
          have inj': "inj_on (\<lambda>f. sum' f \<U>) {x \<in> \<Pi>\<^sub>E S\<in>\<U>. singular_chain_set (Suc n) (subtopology X S). finite {S \<in> \<U>. x S \<noteq> 0}}"
            using iso_chain_group_sum [OF assms, of "Suc n"]
            by (simp add: iso_iff_mon_epi mon_def carrier_sum_group)
          obtain w where w: "w \<in> (\<Pi>\<^sub>E S\<in>\<U>. singular_chain_set (Suc n) (subtopology X S))"
            and finw: "finite {S \<in> \<U>. w S \<noteq> 0}"
            and deq: "d = sum' w \<U>"
            using iso_chain_group_sum [OF assms, of "Suc n"] scd
            by (auto simp: iso_iff_mon_epi epi_def carrier_sum_group set_eq_iff)
          with \<open>S \<in> \<U>\<close> have scwS: "singular_chain (Suc n) (subtopology X S) (w S)"
            by blast
          have "inj_on (\<lambda>f. sum' f \<U>) {x \<in> \<Pi>\<^sub>E S\<in>\<U>. singular_chain_set n (subtopology X S). finite {S \<in> \<U>. x S \<noteq> 0}}"
            using iso_chain_group_sum [OF assms, of n]
            by (simp add: iso_iff_mon_epi mon_def carrier_sum_group)
          then have "(\<lambda>S\<in>\<U>. chain_boundary (Suc n) (w S)) = z"
          proof (rule inj_onD)
            have "sum' (\<lambda>S\<in>\<U>. chain_boundary (Suc n) (w S)) \<U> = sum' (chain_boundary (Suc n) \<circ> w) {S \<in> \<U>. w S \<noteq> 0}"
              by (auto simp: o_def intro: sum.mono_neutral_right')
            also have "\<dots> = chain_boundary (Suc n) d"
              by (auto simp: sum.G_def deq chain_boundary_sum finw intro: finite_subset [OF _ finw] sum.mono_neutral_left)
            finally show "sum' (\<lambda>S\<in>\<U>. chain_boundary (Suc n) (w S)) \<U> = sum' z \<U>"
              by (simp add: cbd)
            show "(\<lambda>S\<in>\<U>. chain_boundary (Suc n) (w S)) \<in> {x \<in> \<Pi>\<^sub>E S\<in>\<U>. singular_chain_set n (subtopology X S). finite {S \<in> \<U>. x S \<noteq> 0}}"
              using w by (auto simp: PiE_iff singular_chain_boundary_alt cong: rev_conj_cong intro: finite_subset [OF _ finw])
            show "z \<in> {x \<in> \<Pi>\<^sub>E S\<in>\<U>. singular_chain_set n (subtopology X S). finite {S \<in> \<U>. x S \<noteq> 0}}"
              using z by (simp_all add: carrier_sum_group PiE_iff singular_cycle)
          qed
          with \<open>S \<in> \<U>\<close> scwS show ?thesis
            by force
        qed
        show ?thesis
          using that *
          by (force intro!: restrict_ext simp add: singular_boundary relative_homology_group_def homologous_rel_set_eq_relboundary peq)
      qed
      show "x = (\<lambda>S\<in>\<U>. \<one>\<^bsub>homology_group p (subtopology X S)\<^esub>)"
        using x 1 carrSG gf
        by (auto simp: peq feq)
    qed
    show "?h ` carrier ?SG = carrier ?HG"
    proof safe
      fix A
      assume "A \<in> carrier (homology_group p X)"
      then obtain y where y: "singular_relcycle n X {} y" and xeq: "A = homologous_rel_set n X {} y"
        by (auto simp: peq carrier_relative_homology_group)
      then obtain x where "x \<in> carrier (sum_group \<U> (\<lambda>T. relcycle_group n (subtopology X T) {}))"
                          "y = sum' x \<U>"
        using iso_cycle_group_sum [OF assms, of n] that by (force simp: iso_iff_mon_epi epi_def)
      then show "A \<in> (\<lambda>x. gfinprod (homology_group p X) (\<lambda>V. hom_induced p (subtopology X V) {} X {} id (x V)) \<U>) `
             carrier (sum_group \<U> (\<lambda>S. homology_group p (subtopology X S)))"
        apply (simp add: carrSG image_comp o_def xeq)
        apply (simp add: hom_induced_carrier peq flip: gf cong: gfinprod_cong)
        done
    qed auto
  qed
qed


corollary homology_additivity_axiom:
  assumes disj: "pairwise disjnt \<U>" and UU: "\<Union>\<U> = topspace X"
   and ope: "\<And>v. v \<in> \<U> \<Longrightarrow> openin X v"
 shows "(\<lambda>x. gfinprod (homology_group p X)
                      (\<lambda>v. hom_induced p (subtopology X v) {} X {} id (x v)) \<U>)
     \<in> iso (sum_group \<U> (\<lambda>S. homology_group p (subtopology X S))) (homology_group p X)"
proof (rule homology_additivity_axiom_gen [OF disj UU])
  fix C T
  assume
    "compactin X C" and
    "path_connectedin X C" and
    "T \<in> \<U>" and
    "\<not> disjnt C T"
  then have  *: "\<And>B. \<lbrakk>openin X T; T \<inter> B \<inter> C = {}; C \<subseteq> T \<union> B; openin X B\<rbrakk> \<Longrightarrow> B \<inter> C = {}"
    by (meson connectedin disjnt_def disjnt_sym path_connectedin_imp_connectedin)
  have "C \<subseteq> Union \<U>"
    by (simp add: UU \<open>compactin X C\<close> compactin_subset_topspace)
  moreover have "\<Union> (\<U> - {T}) \<inter> C = {}"
  proof (rule *)
    show "T \<inter> \<Union> (\<U> - {T}) \<inter> C = {}"
      using \<open>T \<in> \<U>\<close> disj disjointD by fastforce
    show "C \<subseteq> T \<union> \<Union> (\<U> - {T})"
      using \<open>C \<subseteq> \<Union> \<U>\<close> by fastforce
  qed (auto simp: \<open>T \<in> \<U>\<close> ope)
  ultimately show "C \<subseteq> T"
    by blast
qed


subsection\<open>Special properties of singular homology\<close>

text\<open>In particular: the zeroth homology group is isomorphic to the free abelian group
generated by the path components. So, the "coefficient group" is the integers.\<close>

lemma iso_integer_zeroth_homology_group_aux:
  assumes X: "path_connected_space X" and f: "singular_simplex 0 X f" and f': "singular_simplex 0 X f'"
  shows "homologous_rel 0 X {} (frag_of f) (frag_of f')"
proof -
  let ?p = "\<lambda>j. if j = 0 then 1 else 0"
  have "f ?p \<in> topspace X" "f' ?p \<in> topspace X"
  using assms by (auto simp: singular_simplex_def continuous_map_def)
  then obtain g where g: "pathin X g"
                  and g0: "g 0 = f ?p"
                  and g1: "g 1 = f' ?p"
    using assms by (force simp: path_connected_space_def)
  then have contg: "continuous_map (subtopology euclideanreal {0..1}) X g"
    by (simp add: pathin_def)
  have "singular_chain (Suc 0) X (frag_of (restrict (g \<circ> (\<lambda>x. x 0)) (standard_simplex 1)))"
  proof -
    have "continuous_map (subtopology (powertop_real UNIV) (standard_simplex (Suc 0)))
                         euclideanreal (\<lambda>x. x 0)"
      by (metis (mono_tags) UNIV_I continuous_map_from_subtopology continuous_map_product_projection)
    then have "continuous_map (subtopology (powertop_real UNIV) (standard_simplex (Suc 0)))
                              (top_of_set {0..1}) (\<lambda>x. x 0)"
      unfolding continuous_map_in_subtopology g
      by (auto simp: continuous_map_in_subtopology standard_simplex_def g)
    moreover have "continuous_map (top_of_set {0..1}) X g"
      using contg by blast
    ultimately show ?thesis
      by (force simp: singular_chain_of chain_boundary_of singular_simplex_def continuous_map_compose)
  qed
  moreover
  have "chain_boundary (Suc 0) (frag_of (restrict (g \<circ> (\<lambda>x. x 0)) (standard_simplex 1))) =
      frag_of f - frag_of f'"
  proof -
    have "singular_face (Suc 0) 0 (g \<circ> (\<lambda>x. x 0)) = f"
         "singular_face (Suc 0) (Suc 0) (g \<circ> (\<lambda>x. x 0)) = f'"
      using assms
      by (auto simp: singular_face_def singular_simplex_def extensional_def simplical_face_def standard_simplex_0 g0 g1)
    then show ?thesis
      by (simp add: singular_chain_of chain_boundary_of)
  qed
  ultimately
  show ?thesis
    by (auto simp: homologous_rel_def singular_boundary)
qed


proposition iso_integer_zeroth_homology_group:
  assumes X: "path_connected_space X" and f: "singular_simplex 0 X f"
  shows "pow (homology_group 0 X) (homologous_rel_set 0 X {} (frag_of f))
       \<in> iso integer_group (homology_group 0 X)" (is "pow ?H ?q \<in> iso _ ?H")
proof -
  have srf: "singular_relcycle 0 X {} (frag_of f)"
    by (simp add: chain_boundary_def f singular_chain_of singular_cycle)
  then have qcarr: "?q \<in> carrier ?H"
    by (simp add: carrier_relative_homology_group_0)
  have 1: "homologous_rel_set 0 X {} a \<in> range (\<lambda>n. homologous_rel_set 0 X {} (frag_cmul n (frag_of f)))"
    if "singular_relcycle 0 X {} a" for a
  proof -
    have "singular_chain 0 X d \<Longrightarrow>
          homologous_rel_set 0 X {} d \<in> range (\<lambda>n. homologous_rel_set 0 X {} (frag_cmul n (frag_of f)))" for d
      unfolding singular_chain_def
    proof (induction d rule: frag_induction)
      case zero
      then show ?case
        by (metis frag_cmul_zero rangeI)
    next
      case (one x)
      then have "\<exists>i. homologous_rel_set 0 X {} (frag_cmul i (frag_of f))
                   = homologous_rel_set 0 X {} (frag_of x)"
        by (metis (no_types) iso_integer_zeroth_homology_group_aux [OF X] f frag_cmul_one homologous_rel_eq mem_Collect_eq)
      with one show ?case
        by auto
    next
      case (diff a b)
      then obtain c d where
        "homologous_rel 0 X {} (a - b) (frag_cmul c (frag_of f) - frag_cmul d (frag_of f))"
        using homologous_rel_diff by (fastforce simp add: homologous_rel_set_eq)
      then show ?case
        by (rule_tac x="c-d" in image_eqI) (auto simp: homologous_rel_set_eq frag_cmul_diff_distrib)
    qed
    with that show ?thesis
      unfolding singular_relcycle_def by blast
  qed
  have 2: "n = 0"
    if "homologous_rel_set 0 X {} (frag_cmul n (frag_of f)) = \<one>\<^bsub>relative_homology_group 0 X {}\<^esub>"
    for n
  proof -
    have "singular_chain (Suc 0) X d
          \<Longrightarrow> frag_extend (\<lambda>x. frag_of f) (chain_boundary (Suc 0) d) = 0" for d
      unfolding singular_chain_def
    proof (induction d rule: frag_induction)
      case (one x)
      then show ?case
        by (simp add: frag_extend_diff chain_boundary_of)
    next
      case (diff a b)
      then show ?case
        by (simp add: chain_boundary_diff frag_extend_diff)
    qed auto
    with that show ?thesis
      by (force simp: singular_boundary relative_homology_group_def homologous_rel_set_eq_relboundary frag_extend_cmul)
  qed
  interpret GH : group_hom integer_group ?H "([^]\<^bsub>?H\<^esub>) ?q"
    by (simp add: group_hom_def group_hom_axioms_def qcarr group.hom_integer_group_pow)
  have eq: "pow ?H ?q = (\<lambda>n. homologous_rel_set 0 X {} (frag_cmul n (frag_of f)))"
  proof
    fix n
    have "frag_of f
          \<in> carrier (subgroup_generated
                (free_Abelian_group (singular_simplex_set 0 X)) (singular_relcycle_set 0 X {}))"
      by (metis carrier_relcycle_group chain_group_def mem_Collect_eq relcycle_group_def srf)
    then have ff: "frag_of f [^]\<^bsub>relcycle_group 0 X {}\<^esub> n = frag_cmul n (frag_of f)"
      by (simp add: relcycle_group_def chain_group_def group.int_pow_subgroup_generated f)
    show "pow ?H ?q n = homologous_rel_set 0 X {} (frag_cmul n (frag_of f))"
      apply (rule subst [OF right_coset_singular_relboundary])
      by (simp add: ff normal.FactGroup_int_pow normal_subgroup_singular_relboundary_relcycle relative_homology_group_def srf)
  qed
  show ?thesis
    apply (subst GH.iso_iff)
    apply (simp add: eq)
    apply (auto simp: carrier_relative_homology_group_0 1 2)
    done
qed


corollary isomorphic_integer_zeroth_homology_group:
  assumes X: "path_connected_space X" "topspace X \<noteq> {}"
  shows "homology_group 0 X \<cong> integer_group"
proof -
  obtain a where a: "a \<in> topspace X"
    using assms by blast
  have "singular_simplex 0 X (restrict (\<lambda>x. a) (standard_simplex 0))"
    by (simp add: singular_simplex_def a)
  then show ?thesis
    using X group.iso_sym group_integer_group is_isoI iso_integer_zeroth_homology_group by blast
qed


corollary homology_coefficients:
   "topspace X = {a} \<Longrightarrow> homology_group 0 X \<cong> integer_group"
  using isomorphic_integer_zeroth_homology_group path_connectedin_topspace by fastforce

proposition zeroth_homology_group:
   "homology_group 0 X \<cong> free_Abelian_group (path_components_of X)"
proof -
  obtain h where h: "h \<in> iso (sum_group (path_components_of X) (\<lambda>S. homology_group 0 (subtopology X S)))
                             (homology_group 0 X)"
  proof (rule that [OF homology_additivity_axiom_gen])
    show "disjoint (path_components_of X)"
      by (simp add: pairwise_disjoint_path_components_of)
    show "\<Union>(path_components_of X) = topspace X"
      by (rule Union_path_components_of)
  next
    fix C T
    assume "path_connectedin X C" "T \<in> path_components_of X" "\<not> disjnt C T"
    then show "C \<subseteq> T"
      by (metis path_components_of_maximal disjnt_sym)+
  qed
  have "homology_group 0 X \<cong> sum_group (path_components_of X) (\<lambda>S. homology_group 0 (subtopology X S))"
    by (rule group.iso_sym) (use h is_iso_def in auto)
  also have "\<dots>  \<cong> sum_group (path_components_of X) (\<lambda>i. integer_group)"
  proof (rule iso_sum_groupI)
    show "homology_group 0 (subtopology X i) \<cong> integer_group" if "i \<in> path_components_of X" for i
      by (metis that isomorphic_integer_zeroth_homology_group nonempty_path_components_of
          path_connectedin_def path_connectedin_path_components_of topspace_subtopology_subset)
  qed auto
  also have "\<dots>  \<cong> free_Abelian_group (path_components_of X)"
    using path_connectedin_path_components_of nonempty_path_components_of
    by (simp add: isomorphic_sum_integer_group path_connectedin_def)
  finally show ?thesis .
qed


lemma isomorphic_homology_imp_path_components:
  assumes "homology_group 0 X \<cong> homology_group 0 Y"
  shows "path_components_of X \<approx> path_components_of Y"
proof -
  have "free_Abelian_group (path_components_of X) \<cong> homology_group 0 X"
    by (rule group.iso_sym) (auto simp: zeroth_homology_group)
  also have "\<dots> \<cong> homology_group 0 Y"
    by (rule assms)
  also have "\<dots> \<cong> free_Abelian_group (path_components_of Y)"
    by (rule zeroth_homology_group)
  finally have "free_Abelian_group (path_components_of X) \<cong> free_Abelian_group (path_components_of Y)" .
  then show ?thesis
    by (simp add: isomorphic_free_Abelian_groups)
qed


lemma isomorphic_homology_imp_path_connectedness:
  assumes "homology_group 0 X \<cong> homology_group 0 Y"
  shows "path_connected_space X \<longleftrightarrow> path_connected_space Y"
proof -
  obtain h where h: "bij_betw h (path_components_of X) (path_components_of Y)"
    using assms isomorphic_homology_imp_path_components eqpoll_def by blast
  have 1: "path_components_of X \<subseteq> {a} \<Longrightarrow> path_components_of Y \<subseteq> {h a}" for a
    using h unfolding bij_betw_def by blast
  have 2: "path_components_of Y \<subseteq> {a}
           \<Longrightarrow> path_components_of X \<subseteq> {inv_into (path_components_of X) h a}" for a
    using h [THEN bij_betw_inv_into] unfolding bij_betw_def by blast
  show ?thesis
    unfolding path_connected_space_iff_components_subset_singleton
    by (blast intro: dest: 1 2)
qed


subsection\<open>More basic properties of homology groups, deduced from the E-S axioms\<close>

lemma trivial_homology_group:
   "p < 0 \<Longrightarrow> trivial_group(homology_group p X)"
  by simp

lemma hom_induced_empty_hom:
   "(hom_induced p X {} X' {} f) \<in> hom (homology_group p X) (homology_group p X')"
  by (simp add: hom_induced_hom)

lemma hom_induced_compose_empty:
  "\<lbrakk>continuous_map X Y f; continuous_map Y Z g\<rbrakk>
   \<Longrightarrow> hom_induced p X {} Z {} (g \<circ> f) = hom_induced p Y {} Z {} g \<circ> hom_induced p X {} Y {} f"
  by (simp add: hom_induced_compose)

lemma homology_homotopy_empty:
   "homotopic_with (\<lambda>h. True) X Y f g \<Longrightarrow> hom_induced p X {} Y {} f = hom_induced p X {} Y {} g"
  by (simp add: homology_homotopy_axiom)

lemma homotopy_equivalence_relative_homology_group_isomorphisms:
  assumes contf: "continuous_map X Y f" and fim: "f ` S \<subseteq> T"
      and contg: "continuous_map Y X g" and gim: "g ` T \<subseteq> S"
      and gf: "homotopic_with (\<lambda>h. h ` S \<subseteq> S) X X (g \<circ> f) id"
      and fg: "homotopic_with (\<lambda>k. k ` T \<subseteq> T) Y Y (f \<circ> g) id"
    shows "group_isomorphisms (relative_homology_group p X S) (relative_homology_group p Y T)
                (hom_induced p X S Y T f) (hom_induced p Y T X S g)"
  unfolding group_isomorphisms_def
proof (intro conjI ballI)
  fix x
  assume x: "x \<in> carrier (relative_homology_group p X S)"
  then show "hom_induced p Y T X S g (hom_induced p X S Y T f x) = x"
    using homology_homotopy_axiom [OF gf, of p]
    by (simp add: contf contg fim gim hom_induced_compose' hom_induced_id)
next
  fix y
  assume "y \<in> carrier (relative_homology_group p Y T)"
  then show "hom_induced p X S Y T f (hom_induced p Y T X S g y) = y"
    using homology_homotopy_axiom [OF fg, of p]
    by (simp add: contf contg fim gim hom_induced_compose' hom_induced_id)
qed (auto simp: hom_induced_hom)


lemma homotopy_equivalence_relative_homology_group_isomorphism:
  assumes "continuous_map X Y f" and fim: "f ` S \<subseteq> T"
      and "continuous_map Y X g" and gim: "g ` T \<subseteq> S"
      and "homotopic_with (\<lambda>h. h ` S \<subseteq> S) X X (g \<circ> f) id"
      and "homotopic_with (\<lambda>k. k ` T \<subseteq> T) Y Y (f \<circ> g) id"
    shows "(hom_induced p X S Y T f) \<in> iso (relative_homology_group p X S) (relative_homology_group p Y T)"
  using homotopy_equivalence_relative_homology_group_isomorphisms [OF assms] group_isomorphisms_imp_iso
  by metis

lemma homotopy_equivalence_homology_group_isomorphism:
  assumes "continuous_map X Y f"
      and "continuous_map Y X g"
      and "homotopic_with (\<lambda>h. True) X X (g \<circ> f) id"
      and "homotopic_with (\<lambda>k. True) Y Y (f \<circ> g) id"
    shows "(hom_induced p X {} Y {} f) \<in> iso (homology_group p X) (homology_group p Y)"
  using assms by (intro homotopy_equivalence_relative_homology_group_isomorphism) auto

lemma homotopy_equivalent_space_imp_isomorphic_relative_homology_groups:
  assumes "continuous_map X Y f" and fim: "f ` S \<subseteq> T"
      and "continuous_map Y X g" and gim: "g ` T \<subseteq> S"
      and "homotopic_with (\<lambda>h. h ` S \<subseteq> S) X X (g \<circ> f) id"
      and "homotopic_with (\<lambda>k. k ` T \<subseteq> T) Y Y (f \<circ> g) id"
    shows "relative_homology_group p X S \<cong> relative_homology_group p Y T"
  using homotopy_equivalence_relative_homology_group_isomorphism [OF assms]
  unfolding is_iso_def by blast

lemma homotopy_equivalent_space_imp_isomorphic_homology_groups:
   "X homotopy_equivalent_space Y \<Longrightarrow> homology_group p X \<cong> homology_group p Y"
  unfolding homotopy_equivalent_space_def
  by (auto intro: homotopy_equivalent_space_imp_isomorphic_relative_homology_groups)

lemma homeomorphic_space_imp_isomorphic_homology_groups:
   "X homeomorphic_space Y \<Longrightarrow> homology_group p X \<cong> homology_group p Y"
  by (simp add: homeomorphic_imp_homotopy_equivalent_space homotopy_equivalent_space_imp_isomorphic_homology_groups)

lemma trivial_relative_homology_group_gen:
  assumes "continuous_map X (subtopology X S) f"
    "homotopic_with (\<lambda>h. True) (subtopology X S) (subtopology X S) f id"
    "homotopic_with (\<lambda>k. True) X X f id"
  shows "trivial_group(relative_homology_group p X S)"
proof (rule exact_seq_imp_triviality)
  show "exact_seq ([homology_group (p-1) X,
                    homology_group (p-1) (subtopology X S),
                    relative_homology_group p X S, homology_group p X, homology_group p (subtopology X S)],
                   [hom_induced (p-1) (subtopology X S) {} X {} id,
                    hom_boundary p X S,
                    hom_induced p X {} X S id,
                    hom_induced p (subtopology X S) {} X {} id])"
    using homology_exactness_axiom_1 homology_exactness_axiom_2 homology_exactness_axiom_3
    by (metis exact_seq_cons_iff)
next
  show "hom_induced p (subtopology X S) {} X {} id
        \<in> iso (homology_group p (subtopology X S)) (homology_group p X)"
       "hom_induced (p-1) (subtopology X S) {} X {} id
        \<in> iso (homology_group (p-1) (subtopology X S)) (homology_group (p-1) X)"
    using assms
    by (auto intro: homotopy_equivalence_relative_homology_group_isomorphism)
qed


lemma trivial_relative_homology_group_topspace:
   "trivial_group(relative_homology_group p X (topspace X))"
  by (rule trivial_relative_homology_group_gen [where f=id]) auto

lemma trivial_relative_homology_group_empty:
   "topspace X = {} \<Longrightarrow> trivial_group(relative_homology_group p X S)"
  by (metis Int_absorb2 empty_subsetI relative_homology_group_restrict trivial_relative_homology_group_topspace)

lemma trivial_homology_group_empty:
   "topspace X = {} \<Longrightarrow> trivial_group(homology_group p X)"
  by (simp add: trivial_relative_homology_group_empty)

lemma homeomorphic_maps_relative_homology_group_isomorphisms:
  assumes "homeomorphic_maps X Y f g" and im: "f ` S \<subseteq> T" "g ` T \<subseteq> S"
  shows "group_isomorphisms (relative_homology_group p X S) (relative_homology_group p Y T)
                            (hom_induced p X S Y T f) (hom_induced p Y T X S g)"
proof -
  have fg: "continuous_map X Y f" "continuous_map Y X g"
       "(\<forall>x\<in>topspace X. g (f x) = x)" "(\<forall>y\<in>topspace Y. f (g y) = y)"
  using assms by (simp_all add: homeomorphic_maps_def)
  have "group_isomorphisms
         (relative_homology_group p X (topspace X \<inter> S))
         (relative_homology_group p Y (topspace Y \<inter> T))
         (hom_induced p X (topspace X \<inter> S) Y (topspace Y \<inter> T) f)
         (hom_induced p Y (topspace Y \<inter> T) X (topspace X \<inter> S) g)"
  proof (rule homotopy_equivalence_relative_homology_group_isomorphisms)
    show "homotopic_with (\<lambda>h. h ` (topspace X \<inter> S) \<subseteq> topspace X \<inter> S) X X (g \<circ> f) id"
      using fg im by (auto intro: homotopic_with_equal continuous_map_compose)
  next
    show "homotopic_with (\<lambda>k. k ` (topspace Y \<inter> T) \<subseteq> topspace Y \<inter> T) Y Y (f \<circ> g) id"
      using fg im by (auto intro: homotopic_with_equal continuous_map_compose)
  qed (use im fg in \<open>auto simp: continuous_map_def\<close>)
  then show ?thesis
    by simp
qed

lemma homeomorphic_map_relative_homology_iso:
  assumes f: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X" "f ` S = T"
  shows "(hom_induced p X S Y T f) \<in> iso (relative_homology_group p X S) (relative_homology_group p Y T)"
proof -
  obtain g where g: "homeomorphic_maps X Y f g"
    using homeomorphic_map_maps f by metis
  then have "group_isomorphisms (relative_homology_group p X S) (relative_homology_group p Y T)
                                (hom_induced p X S Y T f) (hom_induced p Y T X S g)"
    using S g by (auto simp: homeomorphic_maps_def intro!: homeomorphic_maps_relative_homology_group_isomorphisms)
  then show ?thesis
    by (rule group_isomorphisms_imp_iso)
qed

lemma inj_on_hom_induced_section_map:
  assumes "section_map X Y f"
  shows "inj_on (hom_induced p X {} Y {} f) (carrier (homology_group p X))"
proof -
  obtain g where cont: "continuous_map X Y f" "continuous_map Y X g"
           and gf: "\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x"
    using assms by (auto simp: section_map_def retraction_maps_def)
  show ?thesis
  proof (rule inj_on_inverseI)
    fix x
    assume x: "x \<in> carrier (homology_group p X)"
    have "continuous_map X X (\<lambda>x. g (f x))"
      by (metis (no_types, lifting) continuous_map_eq continuous_map_id gf id_apply)
    with x show "hom_induced p Y {} X {} g (hom_induced p X {} Y {} f x) = x"
      using hom_induced_compose_empty [OF cont, symmetric]
      by (metis comp_apply cont continuous_map_compose gf hom_induced_id_gen)
  qed
qed

corollary mon_hom_induced_section_map:
  assumes "section_map X Y f"
  shows "(hom_induced p X {} Y {} f) \<in> mon (homology_group p X) (homology_group p Y)"
  by (simp add: hom_induced_empty_hom inj_on_hom_induced_section_map [OF assms] mon_def)

lemma surj_hom_induced_retraction_map:
  assumes "retraction_map X Y f"
  shows "carrier (homology_group p Y) = (hom_induced p X {} Y {} f) ` carrier (homology_group p X)"
         (is "?lhs = ?rhs")
proof -
  obtain g where cont: "continuous_map Y X g"  "continuous_map X Y f"
    and fg: "\<And>x. x \<in> topspace Y \<Longrightarrow> f (g x) = x"
    using assms by (auto simp: retraction_map_def retraction_maps_def)
  have "x = hom_induced p X {} Y {} f (hom_induced p Y {} X {} g x)"
    if x: "x \<in> carrier (homology_group p Y)" for x
  proof -
    have "continuous_map Y Y (\<lambda>x. f (g x))"
      by (metis (no_types, lifting) continuous_map_eq continuous_map_id fg id_apply)
    with x show ?thesis
      using hom_induced_compose_empty [OF cont, symmetric]
      by (metis comp_def cont continuous_map_compose fg hom_induced_id_gen)
  qed
  moreover
  have "(hom_induced p Y {} X {} g x) \<in> carrier (homology_group p X)"
    if "x \<in> carrier (homology_group p Y)" for x
    by (metis hom_induced)
  ultimately have "?lhs \<subseteq> ?rhs"
    by auto
  moreover have "?rhs \<subseteq> ?lhs"
    using hom_induced_hom [of p X "{}" Y "{}" f]
    by (simp add: hom_def flip: image_subset_iff_funcset)
  ultimately show ?thesis
    by auto
qed


corollary epi_hom_induced_retraction_map:
  assumes "retraction_map X Y f"
  shows "(hom_induced p X {} Y {} f) \<in> epi (homology_group p X) (homology_group p Y)"
  using assms epi_iff_subset hom_induced_empty_hom surj_hom_induced_retraction_map by fastforce


lemma homeomorphic_map_homology_iso:
  assumes "homeomorphic_map X Y f"
  shows "(hom_induced p X {} Y {} f) \<in> iso (homology_group p X) (homology_group p Y)"
  using assms by (simp add: homeomorphic_map_relative_homology_iso)

(*See also hom_hom_induced_inclusion*)
lemma inj_on_hom_induced_inclusion:
  assumes "S = {} \<or> S retract_of_space X"
  shows "inj_on (hom_induced p (subtopology X S) {} X {} id) (carrier (homology_group p (subtopology X S)))"
  using assms
proof
  assume "S = {}"
  then have "trivial_group(homology_group p (subtopology X S))"
    by (auto simp: topspace_subtopology intro: trivial_homology_group_empty)
  then show ?thesis
    by (auto simp: inj_on_def trivial_group_def)
next
  assume "S retract_of_space X"
  then show ?thesis
    by (simp add: retract_of_space_section_map inj_on_hom_induced_section_map)
qed

lemma trivial_homomorphism_hom_boundary_inclusion:
  assumes "S = {} \<or> S retract_of_space X"
  shows "trivial_homomorphism
             (relative_homology_group p X S) (homology_group (p-1) (subtopology X S))
             (hom_boundary p X S)"
  using exact_seq_mon_eq_triviality inj_on_hom_induced_inclusion [OF assms]
  by (metis exact_seq_cons_iff homology_exactness_axiom_1 homology_exactness_axiom_2)

lemma epi_hom_induced_relativization:
  assumes "S = {} \<or> S retract_of_space X"
  shows "(hom_induced p X {} X S id) ` carrier (homology_group p X) = carrier (relative_homology_group p X S)"
  using exact_seq_epi_eq_triviality trivial_homomorphism_hom_boundary_inclusion
  by (metis assms exact_seq_cons_iff homology_exactness_axiom_1 homology_exactness_axiom_2)

(*different in HOL Light because we don't need short_exact_sequence*)
lemmas short_exact_sequence_hom_induced_inclusion = homology_exactness_axiom_3

lemma group_isomorphisms_homology_group_prod_retract:
  assumes "S = {} \<or> S retract_of_space X"
  obtains \<H> \<K> where
    "subgroup \<H> (homology_group p X)"
    "subgroup \<K> (homology_group p X)"
    "(\<lambda>(x, y). x \<otimes>\<^bsub>homology_group p X\<^esub> y)
    \<in> iso (DirProd (subgroup_generated (homology_group p X) \<H>) (subgroup_generated (homology_group p X) \<K>))
          (homology_group p X)"
    "(hom_induced p (subtopology X S) {} X {} id)
    \<in> iso (homology_group p (subtopology X S)) (subgroup_generated (homology_group p X) \<H>)"
    "(hom_induced p X {} X S id)
    \<in> iso (subgroup_generated (homology_group p X) \<K>) (relative_homology_group p X S)"
  using assms
proof
  assume "S = {}"
  show thesis
  proof (rule splitting_lemma_left [OF homology_exactness_axiom_3 [of p]])
    let ?f = "\<lambda>x. one(homology_group p (subtopology X {}))"
    show "?f \<in> hom (homology_group p X) (homology_group p (subtopology X {}))"
      by (simp add: trivial_hom)
    have tg: "trivial_group (homology_group p (subtopology X {}))"
      by (auto simp: topspace_subtopology trivial_homology_group_empty)
    then have [simp]: "carrier (homology_group p (subtopology X {})) = {one (homology_group p (subtopology X {}))}"
      by (auto simp: trivial_group_def)
    then show "?f (hom_induced p (subtopology X {}) {} X {} id x) = x"
      if "x \<in> carrier (homology_group p (subtopology X {}))" for x
      using that by auto
    show "inj_on (hom_induced p (subtopology X {}) {} X {} id)
               (carrier (homology_group p (subtopology X {})))"
      by (meson inj_on_hom_induced_inclusion)
    show "hom_induced p X {} X {} id ` carrier (homology_group p X) = carrier (homology_group p X)"
      by (metis epi_hom_induced_relativization)
  next
    fix \<H> \<K>
    assume *: "\<H> \<lhd> homology_group p X" "\<K> \<lhd> homology_group p X"
      "\<H> \<inter> \<K> \<subseteq> {\<one>\<^bsub>homology_group p X\<^esub>}"
      "hom_induced p (subtopology X {}) {} X {} id
     \<in> Group.iso (homology_group p (subtopology X {})) (subgroup_generated (homology_group p X) \<H>)"
      "hom_induced p X {} X {} id
     \<in> Group.iso (subgroup_generated (homology_group p X) \<K>) (relative_homology_group p X {})"
      "\<H> <#>\<^bsub>homology_group p X\<^esub> \<K> = carrier (homology_group p X)"
    show thesis
    proof (rule that)
      show "(\<lambda>(x, y). x \<otimes>\<^bsub>homology_group p X\<^esub> y)
        \<in> iso (subgroup_generated (homology_group p X) \<H> \<times>\<times> subgroup_generated (homology_group p X) \<K>)
            (homology_group p X)"
        using * by (simp add: group_disjoint_sum.iso_group_mul normal_def group_disjoint_sum_def)
    qed (use \<open>S = {}\<close> * in \<open>auto simp: normal_def\<close>)
  qed
next
  assume "S retract_of_space X"
  then obtain r where "S \<subseteq> topspace X" and r: "continuous_map X (subtopology X S) r"
                   and req: "\<forall>x \<in> S. r x = x"
    by (auto simp: retract_of_space_def)
  show thesis
  proof (rule splitting_lemma_left [OF homology_exactness_axiom_3 [of p]])
    let ?f = "hom_induced p X {} (subtopology X S) {} r"
    show "?f \<in> hom (homology_group p X) (homology_group p (subtopology X S))"
      by (simp add: hom_induced_empty_hom)
    show eqx: "?f (hom_induced p (subtopology X S) {} X {} id x) = x"
      if "x \<in> carrier (homology_group p (subtopology X S))" for x
    proof -
      have "hom_induced p (subtopology X S) {} (subtopology X S) {} r x = x"
        by (metis \<open>S \<subseteq> topspace X\<close> continuous_map_from_subtopology hom_induced_id_gen inf.absorb_iff2 r req that topspace_subtopology)
      then show ?thesis
        by (simp add: r hom_induced_compose [unfolded o_def fun_eq_iff, rule_format, symmetric])
    qed
    then show "inj_on (hom_induced p (subtopology X S) {} X {} id)
               (carrier (homology_group p (subtopology X S)))"
      unfolding inj_on_def by metis
    show "hom_induced p X {} X S id ` carrier (homology_group p X) = carrier (relative_homology_group p X S)"
      by (simp add: \<open>S retract_of_space X\<close> epi_hom_induced_relativization)
  next
    fix \<H> \<K>
    assume *: "\<H> \<lhd> homology_group p X" "\<K> \<lhd> homology_group p X"
      "\<H> \<inter> \<K> \<subseteq> {\<one>\<^bsub>homology_group p X\<^esub>}"
      "\<H> <#>\<^bsub>homology_group p X\<^esub> \<K> = carrier (homology_group p X)"
      "hom_induced p (subtopology X S) {} X {} id
     \<in> Group.iso (homology_group p (subtopology X S)) (subgroup_generated (homology_group p X) \<H>)"
      "hom_induced p X {} X S id
     \<in> Group.iso (subgroup_generated (homology_group p X) \<K>) (relative_homology_group p X S)"
    show "thesis"
    proof (rule that)
      show "(\<lambda>(x, y). x \<otimes>\<^bsub>homology_group p X\<^esub> y)
          \<in> iso (subgroup_generated (homology_group p X) \<H> \<times>\<times> subgroup_generated (homology_group p X) \<K>)
                (homology_group p X)"
        using *
        by (simp add: group_disjoint_sum.iso_group_mul normal_def group_disjoint_sum_def)
    qed (use * in \<open>auto simp: normal_def\<close>)
  qed
qed



lemma isomorphic_group_homology_group_prod_retract:
  assumes "S = {} \<or> S retract_of_space X"
  shows "homology_group p X \<cong> homology_group p (subtopology X S) \<times>\<times> relative_homology_group p X S"
        (is "?lhs \<cong> ?rhs")
proof -
  obtain \<H> \<K> where
    "subgroup \<H> (homology_group p X)"
    "subgroup \<K> (homology_group p X)"
   and 1: "(\<lambda>(x, y). x \<otimes>\<^bsub>homology_group p X\<^esub> y)
    \<in> iso (DirProd (subgroup_generated (homology_group p X) \<H>) (subgroup_generated (homology_group p X) \<K>))
          (homology_group p X)"
    "(hom_induced p (subtopology X S) {} X {} id)
    \<in> iso (homology_group p (subtopology X S)) (subgroup_generated (homology_group p X) \<H>)"
    "(hom_induced p X {} X S id)
    \<in> iso (subgroup_generated (homology_group p X) \<K>) (relative_homology_group p X S)"
    using group_isomorphisms_homology_group_prod_retract [OF assms] by blast
  have "?lhs \<cong> subgroup_generated (homology_group p X) \<H> \<times>\<times> subgroup_generated (homology_group p X) \<K>"
    by (meson DirProd_group 1 abelian_homology_group comm_group_def group.abelian_subgroup_generated group.iso_sym is_isoI)
  also have "\<dots> \<cong> ?rhs"
    by (meson "1"(2) "1"(3) abelian_homology_group comm_group_def group.DirProd_iso_trans group.abelian_subgroup_generated group.iso_sym is_isoI)
  finally show ?thesis .
qed


lemma homology_additivity_explicit:
  assumes "openin X S" "openin X T" "disjnt S T" and SUT: "S \<union> T = topspace X"
  shows "(\<lambda>(a,b).(hom_induced p (subtopology X S) {} X {} id a)
                  \<otimes>\<^bsub>homology_group p X\<^esub>
                 (hom_induced p (subtopology X T) {} X {} id b))
       \<in> iso (DirProd (homology_group p (subtopology X S)) (homology_group p (subtopology X T)))
             (homology_group p X)"
proof -
  have "closedin X S" "closedin X T"
    using assms Un_commute disjnt_sym
    by (metis Diff_cancel Diff_triv Un_Diff disjnt_def openin_closedin_eq sup_bot.right_neutral)+
  with \<open>openin X S\<close> \<open>openin X T\<close> have SS: "X closure_of S \<subseteq> X interior_of S" and TT: "X closure_of T \<subseteq> X interior_of T"
    by (simp_all add: closure_of_closedin interior_of_openin)
  have [simp]: "S \<union> T - T = S" "S \<union> T - S = T"
    using \<open>disjnt S T\<close>
    by (auto simp: Diff_triv Un_Diff disjnt_def)
  let ?f = "hom_induced p X {} X T id"
  let ?g = "hom_induced p X {} X S id"
  let ?h = "hom_induced p (subtopology X S) {} X T id"
  let ?i = "hom_induced p (subtopology X S) {} X {} id"
  let ?j = "hom_induced p (subtopology X T) {} X {} id"
  let ?k = "hom_induced p (subtopology X T) {} X S id"
  let ?A = "homology_group p (subtopology X S)"
  let ?B = "homology_group p (subtopology X T)"
  let ?C = "relative_homology_group p X T"
  let ?D = "relative_homology_group p X S"
  let ?G = "homology_group p X"
  have h: "?h \<in> iso ?A ?C" and k: "?k \<in> iso ?B ?D"
    using homology_excision_axiom [OF TT, of "S \<union> T" p]
    using homology_excision_axiom [OF SS, of "S \<union> T" p]
    by auto (simp_all add: SUT)
  have 1: "\<And>x. (hom_induced p X {} X T id \<circ> hom_induced p (subtopology X S) {} X {} id) x
             = hom_induced p (subtopology X S) {} X T id x"
    by (simp flip: hom_induced_compose)
  have 2: "\<And>x. (hom_induced p X {} X S id \<circ> hom_induced p (subtopology X T) {} X {} id) x
              = hom_induced p (subtopology X T) {} X S id x"
    by (simp flip: hom_induced_compose)
  show ?thesis
    using exact_sequence_sum_lemma
          [OF abelian_homology_group h k homology_exactness_axiom_3 homology_exactness_axiom_3] 1 2
    by auto
qed


subsection\<open>Generalize exact homology sequence to triples\<close>

definition hom_relboundary  :: "[int,'a topology,'a set,'a set,'a chain set] \<Rightarrow> 'a chain set"
  where
  "hom_relboundary p X S T =
    hom_induced (p-1) (subtopology X S) {} (subtopology X S) T id \<circ>
    hom_boundary p X S"

lemma group_homomorphism_hom_relboundary:
   "hom_relboundary p X S T
  \<in> hom (relative_homology_group p X S) (relative_homology_group (p-1) (subtopology X S) T)"
  unfolding hom_relboundary_def
  proof (rule hom_compose)
    show "hom_boundary p X S \<in> hom (relative_homology_group p X S) (homology_group(p-1) (subtopology X S))"
      by (simp add: hom_boundary_hom)
  show "hom_induced (p-1) (subtopology X S) {} (subtopology X S) T id
      \<in> hom (homology_group(p-1) (subtopology X S)) (relative_homology_group (p-1) (subtopology X S) T)"
    by (simp add: hom_induced_hom)
qed

lemma hom_relboundary:
   "hom_relboundary p X S T c \<in> carrier (relative_homology_group (p-1) (subtopology X S) T)"
  by (simp add: hom_relboundary_def hom_induced_carrier)

lemma hom_relboundary_empty: "hom_relboundary p X S {} = hom_boundary p X S"
  by (simp add: ext hom_boundary_carrier hom_induced_id hom_relboundary_def)

lemma naturality_hom_induced_relboundary:
  assumes "continuous_map X Y f" "f ` S \<subseteq> U" "f ` T \<subseteq> V"
  shows "hom_relboundary p Y U V \<circ>
         hom_induced p X S Y (U) f =
         hom_induced (p-1) (subtopology X S) T (subtopology Y U) V f \<circ>
         hom_relboundary p X S T"
proof -
  have [simp]: "continuous_map (subtopology X S) (subtopology Y U) f"
    using assms continuous_map_from_subtopology continuous_map_in_subtopology topspace_subtopology by fastforce
  have "hom_induced (p-1) (subtopology Y U) {} (subtopology Y U) V id \<circ>
        hom_induced (p-1) (subtopology X S) {} (subtopology Y U) {} f
      = hom_induced (p-1) (subtopology X S) T (subtopology Y U) V f \<circ>
        hom_induced (p-1) (subtopology X S) {} (subtopology X S) T id"
    using assms by (simp flip: hom_induced_compose)
  with assms show ?thesis
    by (metis (no_types, lifting) fun.map_comp hom_relboundary_def naturality_hom_induced)
qed

proposition homology_exactness_triple_1:
  assumes "T \<subseteq> S"
  shows "exact_seq ([relative_homology_group(p-1) (subtopology X S) T,
                     relative_homology_group p X S,
                     relative_homology_group p X T],
                    [hom_relboundary p X S T, hom_induced p X T X S id])"
    (is "exact_seq ([?G1,?G2,?G3], [?h1,?h2])")
proof -
  have iTS: "id ` T \<subseteq> S" and [simp]: "S \<inter> T = T"
    using assms by auto
  have "?h2 B \<in> kernel ?G2 ?G1 ?h1" for B
  proof -
    have "hom_boundary p X T B \<in> carrier (relative_homology_group (p-1) (subtopology X T) {})"
      by (metis (no_types) hom_boundary)
    then have *: "hom_induced (p-1) (subtopology X S) {} (subtopology X S) T id
         (hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id
         (hom_boundary p X T B))
       = \<one>\<^bsub>?G1\<^esub>"
      using homology_exactness_axiom_3 [of "p-1" "subtopology X S" T]
      by (auto simp: subtopology_subtopology kernel_def)
    show ?thesis
      using naturality_hom_induced [OF continuous_map_id iTS]
      by (smt (verit, best) * comp_apply hom_induced_carrier hom_relboundary_def kernel_def mem_Collect_eq)
  qed
  moreover have "B \<in> ?h2 ` carrier ?G3" if "B \<in> kernel ?G2 ?G1 ?h1" for B
  proof -
    have Bcarr: "B \<in> carrier ?G2"
      and Beq: "?h1 B = \<one>\<^bsub>?G1\<^esub>"
      using that by (auto simp: kernel_def)
    have "\<exists>A' \<in> carrier (homology_group (p-1) (subtopology X T)). hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id A' = A"
      if "A \<in> carrier (homology_group (p-1) (subtopology X S))"
        "hom_induced (p-1) (subtopology X S) {} (subtopology X S) T id A =
      \<one>\<^bsub>?G1\<^esub>" for A
      using homology_exactness_axiom_3 [of "p-1" "subtopology X S" T] that
      by (simp add: kernel_def subtopology_subtopology image_iff set_eq_iff) meson
    then obtain C where Ccarr: "C \<in> carrier (homology_group (p-1) (subtopology X T))"
      and Ceq: "hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id C = hom_boundary p X S B"
      using Beq by (simp add: hom_relboundary_def) (metis hom_boundary_carrier)
    let ?hi_XT = "hom_induced (p-1) (subtopology X T) {} X {} id"
    have "?hi_XT
        = hom_induced (p-1) (subtopology X S) {} X {} id
            \<circ> (hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id)"
      by (metis assms comp_id continuous_map_id_subt hom_induced_compose_empty inf.absorb_iff2 subtopology_subtopology)
    then have "?hi_XT C
        = hom_induced (p-1) (subtopology X S) {} X {} id (hom_boundary p X S B)"
      by (simp add: Ceq)
    also have eq: "\<dots> = \<one>\<^bsub>homology_group (p-1) X\<^esub>"
      using homology_exactness_axiom_2 [of p X S] Bcarr by (auto simp: kernel_def)
    finally have "?hi_XT C = \<one>\<^bsub>homology_group (p-1) X\<^esub>" .
    then obtain D where Dcarr: "D \<in> carrier ?G3" and Deq: "hom_boundary p X T D = C"
      using homology_exactness_axiom_2 [of p X T] Ccarr
      by (auto simp: kernel_def image_iff set_eq_iff) meson
    interpret hb: group_hom "?G2" "homology_group (p-1) (subtopology X S)"
                           "hom_boundary p X S"
      using hom_boundary_hom group_hom_axioms_def group_hom_def by fastforce
    let ?A = "B \<otimes>\<^bsub>?G2\<^esub> inv\<^bsub>?G2\<^esub> ?h2 D"
    have "\<exists>A' \<in> carrier (homology_group p X). hom_induced p X {} X S id A' = A"
      if "A \<in> carrier ?G2"
         "hom_boundary p X S A = one (homology_group (p-1) (subtopology X S))" for A
      using that homology_exactness_axiom_1 [of p X S]
      by (simp add: kernel_def subtopology_subtopology image_iff set_eq_iff) meson
    moreover
    have "?A \<in> carrier ?G2"
      by (simp add: Bcarr abelian_relative_homology_group comm_groupE(1) hom_induced_carrier)
    moreover have "hom_boundary p X S (?h2 D) = hom_boundary p X S B"
      by (metis (mono_tags, lifting) Ceq Deq comp_eq_dest continuous_map_id iTS naturality_hom_induced)
    then have "hom_boundary p X S ?A = one (homology_group (p-1) (subtopology X S))"
      by (simp add: hom_induced_carrier Bcarr)
    ultimately obtain W where Wcarr: "W \<in> carrier (homology_group p X)"
      and Weq: "hom_induced p X {} X S id W = ?A"
      by blast
    let ?W = "D \<otimes>\<^bsub>?G3\<^esub> hom_induced p X {} X T id W"
    show ?thesis
    proof
      interpret comm_group "?G2"
        by (rule abelian_relative_homology_group)
      have "hom_induced p X T X S id (hom_induced p X {} X T id W) = hom_induced p X {} X S id W"
        by (simp add: assms hom_induced_compose')
      then have "B = (?h2 \<circ> hom_induced p X {} X T id) W \<otimes>\<^bsub>?G2\<^esub> ?h2 D"
        by (simp add: Bcarr Weq hb.G.m_assoc hom_induced_carrier)
      then show "B = ?h2 ?W"
        by (metis hom_mult [OF hom_induced_hom] Dcarr comp_apply hom_induced_carrier m_comm)
      show "?W \<in> carrier ?G3"
        by (simp add: Dcarr comm_groupE(1) hom_induced_carrier)
    qed
  qed
  ultimately show ?thesis
    by (auto simp: group_hom_def group_hom_axioms_def hom_induced_hom group_homomorphism_hom_relboundary)
qed


proposition homology_exactness_triple_2:
  assumes "T \<subseteq> S"
  shows "exact_seq ([relative_homology_group(p-1) X T,
                     relative_homology_group(p-1) (subtopology X S) T,
                     relative_homology_group p X S],
                    [hom_induced (p-1) (subtopology X S) T X T id, hom_relboundary p X S T])"
    (is "exact_seq ([?G1,?G2,?G3], [?h1,?h2])")
proof -
  let ?H2 = "homology_group (p-1) (subtopology X S)"
  have iTS: "id ` T \<subseteq> S" and [simp]: "S \<inter> T = T"
    using assms by auto
  have "?h2 C \<in> kernel ?G2 ?G1 ?h1" for C
  proof -
    have "?h1 (?h2 C)
       = (hom_induced (p-1) X {} X T id \<circ> hom_induced (p-1) (subtopology X S) {} X {} id \<circ> hom_boundary p X S) C"
      unfolding hom_relboundary_def
      by (metis (no_types, lifting) comp_apply continuous_map_id continuous_map_id_subt empty_subsetI hom_induced_compose id_apply image_empty image_id order_refl)
    also have "\<dots> = \<one>\<^bsub>?G1\<^esub>"
    proof -
      have *: "hom_boundary p X S C \<in> carrier ?H2"
        by (simp add: hom_boundary_carrier)
      moreover have "hom_boundary p X S C \<in> hom_boundary p X S ` carrier ?G3"
        using homology_exactness_axiom_2 [of p X S] *
        apply (simp add: kernel_def set_eq_iff)
        by (metis group_relative_homology_group hom_boundary_default hom_one image_eqI)
      ultimately
      have 1: "hom_induced (p-1) (subtopology X S) {} X {} id (hom_boundary p X S C)
             = \<one>\<^bsub>homology_group (p-1) X\<^esub>"
        using homology_exactness_axiom_2 [of p X S] by (simp add: kernel_def) blast
      show ?thesis
        by (simp add: 1 hom_one [OF hom_induced_hom])
    qed
    finally have "?h1 (?h2 C) = \<one>\<^bsub>?G1\<^esub>" .
    then show ?thesis
      by (simp add: kernel_def hom_relboundary_def hom_induced_carrier)
  qed
  moreover have "x \<in> ?h2 ` carrier ?G3" if "x \<in> kernel ?G2 ?G1 ?h1" for x
  proof -
    let ?homX = "hom_induced (p-1) (subtopology X S) {} X {} id"
    let ?homXS = "hom_induced (p-1) (subtopology X S) {} (subtopology X S) T id"
    have "x \<in> carrier (relative_homology_group (p-1) (subtopology X S) T)"
      using that by (simp add: kernel_def)
    moreover
    have "hom_boundary (p-1) X T \<circ> hom_induced (p-1) (subtopology X S) T X T id = hom_boundary (p-1) (subtopology X S) T"
      by (metis Int_lower2 \<open>S \<inter> T = T\<close> continuous_map_id_subt hom_relboundary_def hom_relboundary_empty id_apply image_id naturality_hom_induced subtopology_subtopology)
    then have "hom_boundary (p-1) (subtopology X S) T x = \<one>\<^bsub>homology_group (p - 2) (subtopology (subtopology X S) T)\<^esub>"
      using naturality_hom_induced [of "subtopology X S" X id T T "p-1"] that
        hom_one [OF hom_boundary_hom group_relative_homology_group group_relative_homology_group, of "p-1" X T]
      by (smt (verit) assms comp_apply inf.absorb_iff2 kernel_def mem_Collect_eq subtopology_subtopology)
    ultimately
    obtain y where ycarr: "y \<in> carrier ?H2"
               and yeq: "?homXS y = x"
      using homology_exactness_axiom_1 [of "p-1" "subtopology X S" T]
      by (simp add: kernel_def image_def set_eq_iff) meson
    have "?homX y \<in> carrier (homology_group (p-1) X)"
      by (simp add: hom_induced_carrier)
    moreover
    have "(hom_induced (p-1) X {} X T id \<circ> ?homX) y = \<one>\<^bsub>relative_homology_group (p-1) X T\<^esub>"
      using that 
      apply (simp add: kernel_def flip: hom_induced_compose)
      using hom_induced_compose [of "subtopology X S" "subtopology X S" id "{}" T X id T "p-1"] yeq 
        by auto
    then have "hom_induced (p-1) X {} X T id (?homX y) = \<one>\<^bsub>relative_homology_group (p-1) X T\<^esub>"
      by simp
    ultimately obtain z where zcarr: "z \<in> carrier (homology_group (p-1) (subtopology X T))"
               and zeq: "hom_induced (p-1) (subtopology X T) {} X {} id z = ?homX y"
      using homology_exactness_axiom_3 [of "p-1" X T]
      by (auto simp: kernel_def dest!: equalityD1 [of "Collect _"])
    have *: "\<And>t. \<lbrakk>t \<in> carrier ?H2;
                  hom_induced (p-1) (subtopology X S) {} X {} id t = \<one>\<^bsub>homology_group (p-1) X\<^esub>\<rbrakk>
                  \<Longrightarrow> t \<in> hom_boundary p X S ` carrier ?G3"
      using homology_exactness_axiom_2 [of p X S]
      by (auto simp: kernel_def dest!: equalityD1 [of "Collect _"])
    interpret comm_group "?H2"
      by (rule abelian_relative_homology_group)
    interpret gh: group_hom ?H2 "homology_group (p-1) X" "hom_induced (p-1) (subtopology X S) {} X {} id"
      by (meson group_hom_axioms_def group_hom_def group_relative_homology_group hom_induced)
    let ?yz = "y \<otimes>\<^bsub>?H2\<^esub> inv\<^bsub>?H2\<^esub> hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id z"
    have yzcarr: "?yz \<in> carrier ?H2"
      by (simp add: hom_induced_carrier ycarr)
    have "hom_induced (p-1) (subtopology X S) {} X {} id y =
          hom_induced (p-1) (subtopology X S) {} X {} id
            (hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id z)"
      by (metis assms continuous_map_id_subt hom_induced_compose_empty inf.absorb_iff2 o_apply o_id subtopology_subtopology zeq)
    then have yzeq: "hom_induced (p-1) (subtopology X S) {} X {} id ?yz = \<one>\<^bsub>homology_group (p-1) X\<^esub>"
      by (simp add: hom_induced_carrier ycarr gh.inv_solve_right')
    obtain w where wcarr: "w \<in> carrier ?G3" and weq: "hom_boundary p X S w = ?yz"
      using * [OF yzcarr yzeq] by blast
    interpret gh2: group_hom ?H2 ?G2 ?homXS
      by (simp add: group_hom_axioms_def group_hom_def hom_induced_hom)
    have "?homXS (hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id z)
        = \<one>\<^bsub>relative_homology_group (p-1) (subtopology X S) T\<^esub>"
      using homology_exactness_axiom_3 [of "p-1" "subtopology X S" T] zcarr
      by (auto simp: kernel_def subtopology_subtopology)
    then show ?thesis
      apply (rule_tac x=w in image_eqI)
       apply (simp_all add: hom_relboundary_def weq wcarr)
      by (metis gh2.hom_inv gh2.hom_mult gh2.inv_one gh2.r_one group.inv_closed group_l_invI hom_induced_carrier l_inv_ex ycarr yeq)
  qed
  ultimately show ?thesis
    by (auto simp: group_hom_axioms_def group_hom_def group_homomorphism_hom_relboundary hom_induced_hom)
qed

proposition homology_exactness_triple_3:
  assumes "T \<subseteq> S"
  shows "exact_seq ([relative_homology_group p X S,
                     relative_homology_group p X T,
                     relative_homology_group p (subtopology X S) T],
                    [hom_induced p X T X S id, hom_induced p (subtopology X S) T X T id])"
    (is "exact_seq ([?G1,?G2,?G3], [?h1,?h2])")
proof -
  have iTS: "id ` T \<subseteq> S" and [simp]: "S \<inter> T = T"
    using assms by auto
  have 1: "?h2 x \<in> kernel ?G2 ?G1 ?h1" for x
  proof -
    have "?h1 (?h2 x)
        = (hom_induced p (subtopology X S) S X S id \<circ>
           hom_induced p (subtopology X S) T (subtopology X S) S id) x"
      by (metis comp_eq_dest_lhs continuous_map_id continuous_map_id_subt hom_induced_compose iTS id_apply image_subsetI)
    also have "\<dots> = \<one>\<^bsub>relative_homology_group p X S\<^esub>"
    proof -
      have "trivial_group (relative_homology_group p (subtopology X S) S)"
        using trivial_relative_homology_group_topspace [of p "subtopology X S"]
        by (metis inf_right_idem relative_homology_group_restrict topspace_subtopology)
      then have 1: "hom_induced p (subtopology X S) T (subtopology X S) S id x
         = \<one>\<^bsub>relative_homology_group p (subtopology X S) S\<^esub>"
        using hom_induced_carrier by (fastforce simp add: trivial_group_def)
      show ?thesis
        by (simp add: 1 hom_one [OF hom_induced_hom])
    qed
    finally have "?h1 (?h2 x) = \<one>\<^bsub>relative_homology_group p X S\<^esub>" .
    then show ?thesis
      by (simp add: hom_induced_carrier kernel_def)
  qed
  moreover have "x \<in> ?h2 ` carrier ?G3" if x: "x \<in> kernel ?G2 ?G1 ?h1" for x
  proof -
    have xcarr: "x \<in> carrier ?G2"
      using that by (auto simp: kernel_def)
    interpret G2: comm_group "?G2"
      by (rule abelian_relative_homology_group)
    let ?b = "hom_boundary p X T x"
    have bcarr: "?b \<in> carrier(homology_group(p-1) (subtopology X T))"
      by (simp add: hom_boundary_carrier)
    have "hom_boundary p X S (hom_induced p X T X S id x)
        = hom_induced (p-1) (subtopology X T) {} (subtopology X S) {} id
            (hom_boundary p X T x)"
      using naturality_hom_induced [of X X id T S p]  by (simp add: assms o_def) meson
    with bcarr have "hom_boundary p X T x \<in> hom_boundary p (subtopology X S) T ` carrier ?G3"
      using homology_exactness_axiom_2 [of p "subtopology X S" T] x
      apply (simp add: kernel_def set_eq_iff subtopology_subtopology)
      by (metis group_relative_homology_group hom_boundary_hom hom_one set_eq_iff)
    then obtain u where ucarr: "u \<in> carrier ?G3"
            and ueq: "hom_boundary p X T x = hom_boundary p (subtopology X S) T u"
      by (auto simp: kernel_def set_eq_iff subtopology_subtopology hom_boundary_carrier)
    define y where "y = x \<otimes>\<^bsub>?G2\<^esub> inv\<^bsub>?G2\<^esub> ?h2 u"
    have ycarr: "y \<in> carrier ?G2"
      using x by (simp add: y_def kernel_def hom_induced_carrier)
    interpret hb: group_hom ?G2 "homology_group (p-1) (subtopology X T)" "hom_boundary p X T"
      by (simp add: group_hom_axioms_def group_hom_def hom_boundary_hom)
    have yyy: "hom_boundary p X T y = \<one>\<^bsub>homology_group (p-1) (subtopology X T)\<^esub>"
      apply (simp add: y_def bcarr xcarr hom_induced_carrier hom_boundary_carrier hb.inv_solve_right')
      using naturality_hom_induced [of concl: p X T "subtopology X S" T id]
      by (smt (verit, best) \<open>S \<inter> T = T\<close> bcarr comp_eq_dest continuous_map_id_subt hom_induced_id id_apply 
          image_subset_iff subtopology_subtopology ueq)
    then have "y \<in> hom_induced p X {} X T id ` carrier (homology_group p X)"
      using homology_exactness_axiom_1 [of p X T] x ycarr by (auto simp: kernel_def)
    then obtain z where zcarr: "z \<in> carrier (homology_group p X)"
                    and zeq: "hom_induced p X {} X T id z = y"
      by auto
    interpret gh1: group_hom ?G2 ?G1 ?h1
      by (meson group_hom_axioms_def group_hom_def group_relative_homology_group hom_induced)

    have "hom_induced p X {} X S id z = (hom_induced p X T X S id \<circ> hom_induced p X {} X T id) z"
      by (simp add: assms flip: hom_induced_compose)
    also have "\<dots> = \<one>\<^bsub>relative_homology_group p X S\<^esub>"
      using x 1 by (simp add: kernel_def zeq y_def)
    finally have "hom_induced p X {} X S id z = \<one>\<^bsub>relative_homology_group p X S\<^esub>" .
    then have "z \<in> hom_induced p (subtopology X S) {} X {} id `
                   carrier (homology_group p (subtopology X S))"
      using homology_exactness_axiom_3 [of p X S] zcarr by (auto simp: kernel_def)
    then obtain w where wcarr: "w \<in> carrier (homology_group p (subtopology X S))"
                and weq: "hom_induced p (subtopology X S) {} X {} id w = z"
      by blast
    let ?u = "hom_induced p (subtopology X S) {} (subtopology X S) T id w \<otimes>\<^bsub>?G3\<^esub> u"
    show ?thesis
    proof
      have *: "x = z \<otimes>\<^bsub>?G2\<^esub> u"
          if "z = x \<otimes>\<^bsub>?G2\<^esub> inv\<^bsub>?G2\<^esub> u" "z \<in> carrier ?G2" "u \<in> carrier ?G2" for z u
        using that by (simp add: group.inv_solve_right xcarr)
      have eq: "?h2 \<circ> hom_induced p (subtopology X S) {} (subtopology X S) T id
            = hom_induced p X {} X T id \<circ> hom_induced p (subtopology X S) {} X {} id"
        by (simp flip: hom_induced_compose)
      show "x = hom_induced p (subtopology X S) T X T id ?u"
        using hom_mult [OF hom_induced_hom] hom_induced_carrier *
        by (smt (verit, best) comp_eq_dest eq ucarr weq y_def zeq)
      show "?u \<in> carrier (relative_homology_group p (subtopology X S) T)"
        by (simp add: abelian_relative_homology_group comm_groupE(1) hom_induced_carrier ucarr)
    qed
  qed
  ultimately show ?thesis
    by (auto simp: group_hom_axioms_def group_hom_def hom_induced_hom)
qed

end


