section \<open>Absolute Retracts, Absolute Neighbourhood Retracts and Euclidean Neighbourhood Retracts\<close>

theory Retracts
imports
  Brouwer_Fixpoint
  Continuous_Extension
begin

text \<open>Absolute retracts (AR), absolute neighbourhood retracts (ANR) and also Euclidean neighbourhood
retracts (ENR). We define AR and ANR by specializing the standard definitions for a set to embedding
in spaces of higher dimension.

John Harrison writes: "This turns out to be sufficient (since any set in \<open>\<real>\<^sup>n\<close> can be
embedded as a closed subset of a convex subset of \<open>\<real>\<^sup>n\<^sup>+\<^sup>1\<close>) to derive the usual
definitions, but we need to split them into two implications because of the lack of type
quantifiers. Then ENR turns out to be equivalent to ANR plus local compactness."\<close>

definition\<^marker>\<open>tag important\<close> AR :: "'a::topological_space set \<Rightarrow> bool" where
"AR S \<equiv> \<forall>U. \<forall>S'::('a * real) set.
  S homeomorphic S' \<and> closedin (top_of_set U) S' \<longrightarrow> S' retract_of U"

definition\<^marker>\<open>tag important\<close> ANR :: "'a::topological_space set \<Rightarrow> bool" where
"ANR S \<equiv> \<forall>U. \<forall>S'::('a * real) set.
  S homeomorphic S' \<and> closedin (top_of_set U) S'
  \<longrightarrow> (\<exists>T. openin (top_of_set U) T \<and> S' retract_of T)"

definition\<^marker>\<open>tag important\<close> ENR :: "'a::topological_space set \<Rightarrow> bool" where
"ENR S \<equiv> \<exists>U. open U \<and> S retract_of U"

text \<open>First, show that we do indeed get the "usual" properties of ARs and ANRs.\<close>

lemma AR_imp_absolute_extensor:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "AR S" and contf: "continuous_on T f" and "f ` T \<subseteq> S"
      and cloUT: "closedin (top_of_set U) T"
  obtains g where "continuous_on U g" "g ` U \<subseteq> S" "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
proof -
  have "aff_dim S < int (DIM('b \<times> real))"
    using aff_dim_le_DIM [of S] by simp
  then obtain C and S' :: "('b * real) set"
          where C: "convex C" "C \<noteq> {}"
            and cloCS: "closedin (top_of_set C) S'"
            and hom: "S homeomorphic S'"
    by (metis that homeomorphic_closedin_convex)
  then have "S' retract_of C"
    using \<open>AR S\<close> by (simp add: AR_def)
  then obtain r where "S' \<subseteq> C" and contr: "continuous_on C r"
                  and "r ` C \<subseteq> S'" and rid: "\<And>x. x\<in>S' \<Longrightarrow> r x = x"
    by (auto simp: retraction_def retract_of_def)
  obtain g h where "homeomorphism S S' g h"
    using hom by (force simp: homeomorphic_def)
  then have "continuous_on (f ` T) g"
    by (meson \<open>f ` T \<subseteq> S\<close> continuous_on_subset homeomorphism_def)
  then have contgf: "continuous_on T (g \<circ> f)"
    by (metis continuous_on_compose contf)
  have gfTC: "(g \<circ> f) ` T \<subseteq> C"
  proof -
    have "g ` S = S'"
      by (metis (no_types) \<open>homeomorphism S S' g h\<close> homeomorphism_def)
    with \<open>S' \<subseteq> C\<close> \<open>f ` T \<subseteq> S\<close> show ?thesis by force
  qed
  obtain f' where f': "continuous_on U f'"  "f' ` U \<subseteq> C"
                      "\<And>x. x \<in> T \<Longrightarrow> f' x = (g \<circ> f) x"
    by (metis Dugundji [OF C cloUT contgf gfTC])
  show ?thesis
  proof (rule_tac g = "h \<circ> r \<circ> f'" in that)
    show "continuous_on U (h \<circ> r \<circ> f')"
    proof (intro continuous_on_compose f')
      show "continuous_on (f' ` U) r"
        using continuous_on_subset contr f' by blast
      show "continuous_on (r ` f' ` U) h"
        using \<open>homeomorphism S S' g h\<close> \<open>f' ` U \<subseteq> C\<close> 
        unfolding homeomorphism_def
        by (metis \<open>r ` C \<subseteq> S'\<close> continuous_on_subset image_mono)
    qed
    show "(h \<circ> r \<circ> f') ` U \<subseteq> S"
      using \<open>homeomorphism S S' g h\<close> \<open>r ` C \<subseteq> S'\<close> \<open>f' ` U \<subseteq> C\<close>
      by (fastforce simp: homeomorphism_def)
    show "\<And>x. x \<in> T \<Longrightarrow> (h \<circ> r \<circ> f') x = f x"
      using \<open>homeomorphism S S' g h\<close> \<open>f ` T \<subseteq> S\<close> f'
      by (auto simp: rid homeomorphism_def)
  qed
qed

lemma AR_imp_absolute_retract:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "AR S" "S homeomorphic S'"
      and clo: "closedin (top_of_set U) S'"
    shows "S' retract_of U"
proof -
  obtain g h where hom: "homeomorphism S S' g h"
    using assms by (force simp: homeomorphic_def)
  obtain h: "continuous_on S' h" " h ` S' \<subseteq> S"
    using hom homeomorphism_def by blast
  obtain h' where h': "continuous_on U h'" "h' ` U \<subseteq> S"
              and h'h: "\<And>x. x \<in> S' \<Longrightarrow> h' x = h x"
    by (blast intro: AR_imp_absolute_extensor [OF \<open>AR S\<close> h clo])
  have [simp]: "S' \<subseteq> U" using clo closedin_limpt by blast
  show ?thesis
  proof (simp add: retraction_def retract_of_def, intro exI conjI)
    show "continuous_on U (g \<circ> h')"
      by (meson continuous_on_compose continuous_on_subset h' hom homeomorphism_cont1)
    show "(g \<circ> h') ` U \<subseteq> S'"
      using h'  by clarsimp (metis hom subsetD homeomorphism_def imageI)
    show "\<forall>x\<in>S'. (g \<circ> h') x = x"
      by clarsimp (metis h'h hom homeomorphism_def)
  qed
qed

lemma AR_imp_absolute_retract_UNIV:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "AR S" "S homeomorphic S'" "closed S'"
    shows "S' retract_of UNIV"
  using AR_imp_absolute_retract assms by fastforce

lemma absolute_extensor_imp_AR:
  fixes S :: "'a::euclidean_space set"
  assumes "\<And>f :: 'a * real \<Rightarrow> 'a.
           \<And>U T. \<lbrakk>continuous_on T f;  f ` T \<subseteq> S;
                  closedin (top_of_set U) T\<rbrakk>
                 \<Longrightarrow> \<exists>g. continuous_on U g \<and> g ` U \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)"
  shows "AR S"
proof (clarsimp simp: AR_def)
  fix U and T :: "('a * real) set"
  assume "S homeomorphic T" and clo: "closedin (top_of_set U) T"
  then obtain g h where hom: "homeomorphism S T g h"
    by (force simp: homeomorphic_def)
  obtain h: "continuous_on T h" " h ` T \<subseteq> S"
    using hom homeomorphism_def by blast
  obtain h' where h': "continuous_on U h'" "h' ` U \<subseteq> S"
              and h'h: "\<forall>x\<in>T. h' x = h x"
    using assms [OF h clo] by blast
  have [simp]: "T \<subseteq> U"
    using clo closedin_imp_subset by auto
  show "T retract_of U"
  proof (simp add: retraction_def retract_of_def, intro exI conjI)
    show "continuous_on U (g \<circ> h')"
      by (meson continuous_on_compose continuous_on_subset h' hom homeomorphism_cont1)
    show "(g \<circ> h') ` U \<subseteq> T"
      using h'  by clarsimp (metis hom subsetD homeomorphism_def imageI)
    show "\<forall>x\<in>T. (g \<circ> h') x = x"
      by clarsimp (metis h'h hom homeomorphism_def)
  qed
qed

lemma AR_eq_absolute_extensor:
  fixes S :: "'a::euclidean_space set"
  shows "AR S \<longleftrightarrow>
       (\<forall>f :: 'a * real \<Rightarrow> 'a.
        \<forall>U T. continuous_on T f \<longrightarrow> f ` T \<subseteq> S \<longrightarrow>
               closedin (top_of_set U) T \<longrightarrow>
                (\<exists>g. continuous_on U g \<and> g ` U \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)))"
  by (metis (mono_tags, opaque_lifting) AR_imp_absolute_extensor absolute_extensor_imp_AR)

lemma AR_imp_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "AR S \<and> closedin (top_of_set U) S"
    shows "S retract_of U"
using AR_imp_absolute_retract assms homeomorphic_refl by blast

lemma AR_homeomorphic_AR:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "AR T" "S homeomorphic T"
    shows "AR S"
unfolding AR_def
by (metis assms AR_imp_absolute_retract homeomorphic_trans [of _ S] homeomorphic_sym)

lemma homeomorphic_AR_iff_AR:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  shows "S homeomorphic T \<Longrightarrow> AR S \<longleftrightarrow> AR T"
by (metis AR_homeomorphic_AR homeomorphic_sym)


lemma ANR_imp_absolute_neighbourhood_extensor:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "ANR S" and contf: "continuous_on T f" and "f ` T \<subseteq> S"
      and cloUT: "closedin (top_of_set U) T"
  obtains V g where "T \<subseteq> V" "openin (top_of_set U) V"
                    "continuous_on V g"
                    "g ` V \<subseteq> S" "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
proof -
  have "aff_dim S < int (DIM('b \<times> real))"
    using aff_dim_le_DIM [of S] by simp
  then obtain C and S' :: "('b * real) set"
          where C: "convex C" "C \<noteq> {}"
            and cloCS: "closedin (top_of_set C) S'"
            and hom: "S homeomorphic S'"
    by (metis that homeomorphic_closedin_convex)
  then obtain D where opD: "openin (top_of_set C) D" and "S' retract_of D"
    using \<open>ANR S\<close> by (auto simp: ANR_def)
  then obtain r where "S' \<subseteq> D" and contr: "continuous_on D r"
                  and "r ` D \<subseteq> S'" and rid: "\<And>x. x \<in> S' \<Longrightarrow> r x = x"
    by (auto simp: retraction_def retract_of_def)
  obtain g h where homgh: "homeomorphism S S' g h"
    using hom by (force simp: homeomorphic_def)
  have "continuous_on (f ` T) g"
    by (meson \<open>f ` T \<subseteq> S\<close> continuous_on_subset homeomorphism_def homgh)
  then have contgf: "continuous_on T (g \<circ> f)"
    by (intro continuous_on_compose contf)
  have gfTC: "(g \<circ> f) ` T \<subseteq> C"
  proof -
    have "g ` S = S'"
      by (metis (no_types) homeomorphism_def homgh)
    then show ?thesis
      by (metis (no_types) assms(3) cloCS closedin_def image_comp image_mono order.trans topspace_euclidean_subtopology)
  qed
  obtain f' where contf': "continuous_on U f'"
              and "f' ` U \<subseteq> C"
              and eq: "\<And>x. x \<in> T \<Longrightarrow> f' x = (g \<circ> f) x"
    by (metis Dugundji [OF C cloUT contgf gfTC])
  show ?thesis
  proof (rule_tac V = "U \<inter> f' -` D" and g = "h \<circ> r \<circ> f'" in that)
    show "T \<subseteq> U \<inter> f' -` D"
      using cloUT closedin_imp_subset \<open>S' \<subseteq> D\<close> \<open>f ` T \<subseteq> S\<close> eq homeomorphism_image1 homgh
      by fastforce
    show ope: "openin (top_of_set U) (U \<inter> f' -` D)"
      using  \<open>f' ` U \<subseteq> C\<close> by (auto simp: opD contf' continuous_openin_preimage)
    have conth: "continuous_on (r ` f' ` (U \<inter> f' -` D)) h"
    proof (rule continuous_on_subset [of S'])
      show "continuous_on S' h"
        using homeomorphism_def homgh by blast
    qed (use \<open>r ` D \<subseteq> S'\<close> in blast)
    show "continuous_on (U \<inter> f' -` D) (h \<circ> r \<circ> f')"
      by (blast intro: continuous_on_compose conth continuous_on_subset [OF contr] continuous_on_subset [OF contf'])
    show "(h \<circ> r \<circ> f') ` (U \<inter> f' -` D) \<subseteq> S"
      using \<open>homeomorphism S S' g h\<close>  \<open>f' ` U \<subseteq> C\<close>  \<open>r ` D \<subseteq> S'\<close>
      by (auto simp: homeomorphism_def)
    show "\<And>x. x \<in> T \<Longrightarrow> (h \<circ> r \<circ> f') x = f x"
      using \<open>homeomorphism S S' g h\<close> \<open>f ` T \<subseteq> S\<close> eq
      by (auto simp: rid homeomorphism_def)
  qed
qed


corollary ANR_imp_absolute_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ANR S" "S homeomorphic S'"
      and clo: "closedin (top_of_set U) S'"
  obtains V where "openin (top_of_set U) V" "S' retract_of V"
proof -
  obtain g h where hom: "homeomorphism S S' g h"
    using assms by (force simp: homeomorphic_def)
  obtain h: "continuous_on S' h" " h ` S' \<subseteq> S"
    using hom homeomorphism_def by blast
    from ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> h clo]
  obtain V h' where "S' \<subseteq> V" and opUV: "openin (top_of_set U) V"
                and h': "continuous_on V h'" "h' ` V \<subseteq> S"
                and h'h:"\<And>x. x \<in> S' \<Longrightarrow> h' x = h x"
    by (blast intro: ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> h clo])
  have "S' retract_of V"
  proof (simp add: retraction_def retract_of_def, intro exI conjI \<open>S' \<subseteq> V\<close>)
    show "continuous_on V (g \<circ> h')"
      by (meson continuous_on_compose continuous_on_subset h'(1) h'(2) hom homeomorphism_cont1)
    show "(g \<circ> h') ` V \<subseteq> S'"
      using h'  by clarsimp (metis hom subsetD homeomorphism_def imageI)
    show "\<forall>x\<in>S'. (g \<circ> h') x = x"
      by clarsimp (metis h'h hom homeomorphism_def)
  qed
  then show ?thesis
    by (rule that [OF opUV])
qed

corollary ANR_imp_absolute_neighbourhood_retract_UNIV:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ANR S" and hom: "S homeomorphic S'" and clo: "closed S'"
  obtains V where "open V" "S' retract_of V"
  using ANR_imp_absolute_neighbourhood_retract [OF \<open>ANR S\<close> hom]
by (metis clo closed_closedin open_openin subtopology_UNIV)

corollary neighbourhood_extension_into_ANR:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and fim: "f ` S \<subseteq> T" and "ANR T" "closed S"
  obtains V g where "S \<subseteq> V" "open V" "continuous_on V g"
                    "g ` V \<subseteq> T" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  using ANR_imp_absolute_neighbourhood_extensor [OF  \<open>ANR T\<close> contf fim]
  by (metis \<open>closed S\<close> closed_closedin open_openin subtopology_UNIV)

lemma absolute_neighbourhood_extensor_imp_ANR:
  fixes S :: "'a::euclidean_space set"
  assumes "\<And>f :: 'a * real \<Rightarrow> 'a.
           \<And>U T. \<lbrakk>continuous_on T f;  f ` T \<subseteq> S;
                  closedin (top_of_set U) T\<rbrakk>
                 \<Longrightarrow> \<exists>V g. T \<subseteq> V \<and> openin (top_of_set U) V \<and>
                       continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)"
  shows "ANR S"
proof (clarsimp simp: ANR_def)
  fix U and T :: "('a * real) set"
  assume "S homeomorphic T" and clo: "closedin (top_of_set U) T"
  then obtain g h where hom: "homeomorphism S T g h"
    by (force simp: homeomorphic_def)
  obtain h: "continuous_on T h" " h ` T \<subseteq> S"
    using hom homeomorphism_def by blast
  obtain V h' where "T \<subseteq> V" and opV: "openin (top_of_set U) V"
                and h': "continuous_on V h'" "h' ` V \<subseteq> S"
              and h'h: "\<forall>x\<in>T. h' x = h x"
    using assms [OF h clo] by blast
  have [simp]: "T \<subseteq> U"
    using clo closedin_imp_subset by auto
  have "T retract_of V"
  proof (simp add: retraction_def retract_of_def, intro exI conjI \<open>T \<subseteq> V\<close>)
    show "continuous_on V (g \<circ> h')"
      by (meson continuous_on_compose continuous_on_subset h' hom homeomorphism_cont1)
    show "(g \<circ> h') ` V \<subseteq> T"
      using h'  by clarsimp (metis hom subsetD homeomorphism_def imageI)
    show "\<forall>x\<in>T. (g \<circ> h') x = x"
      by clarsimp (metis h'h hom homeomorphism_def)
  qed
  then show "\<exists>V. openin (top_of_set U) V \<and> T retract_of V"
    using opV by blast
qed

lemma ANR_eq_absolute_neighbourhood_extensor:
  fixes S :: "'a::euclidean_space set"
  shows "ANR S \<longleftrightarrow>
         (\<forall>f :: 'a * real \<Rightarrow> 'a.
          \<forall>U T. continuous_on T f \<longrightarrow> f ` T \<subseteq> S \<longrightarrow>
                closedin (top_of_set U) T \<longrightarrow>
               (\<exists>V g. T \<subseteq> V \<and> openin (top_of_set U) V \<and>
                       continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)))" (is "_ = ?rhs")
proof
  assume "ANR S" then show ?rhs
    by (metis ANR_imp_absolute_neighbourhood_extensor)
qed (simp add: absolute_neighbourhood_extensor_imp_ANR)

lemma ANR_imp_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S" "closedin (top_of_set U) S"
  obtains V where "openin (top_of_set U) V" "S retract_of V"
using ANR_imp_absolute_neighbourhood_retract assms homeomorphic_refl by blast

lemma ANR_imp_absolute_closed_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ANR S" "S homeomorphic S'" and US': "closedin (top_of_set U) S'"
  obtains V W
    where "openin (top_of_set U) V"
          "closedin (top_of_set U) W"
          "S' \<subseteq> V" "V \<subseteq> W" "S' retract_of W"
proof -
  obtain Z where "openin (top_of_set U) Z" and S'Z: "S' retract_of Z"
    by (blast intro: assms ANR_imp_absolute_neighbourhood_retract)
  then have UUZ: "closedin (top_of_set U) (U - Z)"
    by auto
  have "S' \<inter> (U - Z) = {}"
    using \<open>S' retract_of Z\<close> closedin_retract closedin_subtopology by fastforce
  then obtain V W
      where "openin (top_of_set U) V"
        and "openin (top_of_set U) W"
        and "S' \<subseteq> V" "U - Z \<subseteq> W" "V \<inter> W = {}"
      using separation_normal_local [OF US' UUZ]  by auto
  moreover have "S' retract_of U - W"
  proof (rule retract_of_subset [OF S'Z])
    show "S' \<subseteq> U - W"
      using US' \<open>S' \<subseteq> V\<close> \<open>V \<inter> W = {}\<close> closedin_subset by fastforce
    show "U - W \<subseteq> Z"
      using Diff_subset_conv \<open>U - Z \<subseteq> W\<close> by blast
  qed
  ultimately show ?thesis
    by (metis Diff_subset_conv Diff_triv Int_Diff_Un Int_absorb1 openin_closedin_eq that topspace_euclidean_subtopology)
qed

lemma ANR_imp_closed_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S" "closedin (top_of_set U) S"
  obtains V W where "openin (top_of_set U) V"
                    "closedin (top_of_set U) W"
                    "S \<subseteq> V" "V \<subseteq> W" "S retract_of W"
by (meson ANR_imp_absolute_closed_neighbourhood_retract assms homeomorphic_refl)

lemma ANR_homeomorphic_ANR:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "ANR T" "S homeomorphic T"
    shows "ANR S"
unfolding ANR_def
by (metis assms ANR_imp_absolute_neighbourhood_retract homeomorphic_trans [of _ S] homeomorphic_sym)

lemma homeomorphic_ANR_iff_ANR:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  shows "S homeomorphic T \<Longrightarrow> ANR S \<longleftrightarrow> ANR T"
by (metis ANR_homeomorphic_ANR homeomorphic_sym)

subsection \<open>Analogous properties of ENRs\<close>

lemma ENR_imp_absolute_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ENR S" and hom: "S homeomorphic S'"
      and "S' \<subseteq> U"
  obtains V where "openin (top_of_set U) V" "S' retract_of V"
proof -
  obtain X where "open X" "S retract_of X"
    using \<open>ENR S\<close> by (auto simp: ENR_def)
  then obtain r where "retraction X S r"
    by (auto simp: retract_of_def)
  have "locally compact S'"
    using retract_of_locally_compact open_imp_locally_compact
          homeomorphic_local_compactness \<open>S retract_of X\<close> \<open>open X\<close> hom by blast
  then obtain W where UW: "openin (top_of_set U) W"
                  and WS': "closedin (top_of_set W) S'"
    apply (rule locally_compact_closedin_open)
    by (meson Int_lower2 assms(3) closedin_imp_subset closedin_subset_trans le_inf_iff openin_open)
  obtain f g where hom: "homeomorphism S S' f g"
    using assms by (force simp: homeomorphic_def)
  have contg: "continuous_on S' g"
    using hom homeomorphism_def by blast
  moreover have "g ` S' \<subseteq> S" by (metis hom equalityE homeomorphism_def)
  ultimately obtain h where conth: "continuous_on W h" and hg: "\<And>x. x \<in> S' \<Longrightarrow> h x = g x"
    using Tietze_unbounded [of S' g W] WS' by blast
  have "W \<subseteq> U" using UW openin_open by auto
  have "S' \<subseteq> W" using WS' closedin_closed by auto
  have him: "\<And>x. x \<in> S' \<Longrightarrow> h x \<in> X"
    by (metis (no_types) \<open>S retract_of X\<close> hg hom homeomorphism_def image_insert insert_absorb insert_iff retract_of_imp_subset subset_eq)
  have "S' retract_of (W \<inter> h -` X)"
  proof (simp add: retraction_def retract_of_def, intro exI conjI)
    show "S' \<subseteq> W" "S' \<subseteq> h -` X"
      using him WS' closedin_imp_subset by blast+
    show "continuous_on (W \<inter> h -` X) (f \<circ> r \<circ> h)"
    proof (intro continuous_on_compose)
      show "continuous_on (W \<inter> h -` X) h"
        by (meson conth continuous_on_subset inf_le1)
      show "continuous_on (h ` (W \<inter> h -` X)) r"
      proof -
        have "h ` (W \<inter> h -` X) \<subseteq> X"
          by blast
        then show "continuous_on (h ` (W \<inter> h -` X)) r"
          by (meson \<open>retraction X S r\<close> continuous_on_subset retraction)
      qed
      show "continuous_on (r ` h ` (W \<inter> h -` X)) f"
      proof (rule continuous_on_subset [of S])
        show "continuous_on S f"
          using hom homeomorphism_def by blast
        show "r ` h ` (W \<inter> h -` X) \<subseteq> S"
          by (metis \<open>retraction X S r\<close> image_mono image_subset_iff_subset_vimage inf_le2 retraction)
      qed
    qed
    show "(f \<circ> r \<circ> h) ` (W \<inter> h -` X) \<subseteq> S'"
      using \<open>retraction X S r\<close> hom
      by (auto simp: retraction_def homeomorphism_def)
    show "\<forall>x\<in>S'. (f \<circ> r \<circ> h) x = x"
      using \<open>retraction X S r\<close> hom by (auto simp: retraction_def homeomorphism_def hg)
  qed
  then show ?thesis
    using UW \<open>open X\<close> conth continuous_openin_preimage_eq openin_trans that by blast
qed

corollary ENR_imp_absolute_neighbourhood_retract_UNIV:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ENR S" "S homeomorphic S'"
  obtains T' where "open T'" "S' retract_of T'"
by (metis ENR_imp_absolute_neighbourhood_retract UNIV_I assms(1) assms(2) open_openin subsetI subtopology_UNIV)

lemma ENR_homeomorphic_ENR:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "ENR T" "S homeomorphic T"
    shows "ENR S"
unfolding ENR_def
by (meson ENR_imp_absolute_neighbourhood_retract_UNIV assms homeomorphic_sym)

lemma homeomorphic_ENR_iff_ENR:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "S homeomorphic T"
    shows "ENR S \<longleftrightarrow> ENR T"
by (meson ENR_homeomorphic_ENR assms homeomorphic_sym)

lemma ENR_translation:
  fixes S :: "'a::euclidean_space set"
  shows "ENR(image (\<lambda>x. a + x) S) \<longleftrightarrow> ENR S"
by (meson homeomorphic_sym homeomorphic_translation homeomorphic_ENR_iff_ENR)

lemma ENR_linear_image_eq:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "linear f" "inj f"
  shows "ENR (image f S) \<longleftrightarrow> ENR S"
  by (meson assms homeomorphic_ENR_iff_ENR linear_homeomorphic_image)

text \<open>Some relations among the concepts. We also relate AR to being a retract of UNIV, which is
often a more convenient proxy in the closed case.\<close>

lemma AR_imp_ANR: "AR S \<Longrightarrow> ANR S"
  using ANR_def AR_def by fastforce

lemma ENR_imp_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "ENR S \<Longrightarrow> ANR S"
  by (meson ANR_def ENR_imp_absolute_neighbourhood_retract closedin_imp_subset)

lemma ENR_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "ENR S \<longleftrightarrow> ANR S \<and> locally compact S"
proof
  assume "ENR S"
  then have "locally compact S"
    using ENR_def open_imp_locally_compact retract_of_locally_compact by auto
  then show "ANR S \<and> locally compact S"
    using ENR_imp_ANR \<open>ENR S\<close> by blast
next
  assume "ANR S \<and> locally compact S"
  then have "ANR S" "locally compact S" by auto
  then obtain T :: "('a * real) set" where "closed T" "S homeomorphic T"
    using locally_compact_homeomorphic_closed
    by (metis DIM_prod DIM_real Suc_eq_plus1 lessI)
  then show "ENR S"
    using \<open>ANR S\<close>
    by (meson ANR_imp_absolute_neighbourhood_retract_UNIV ENR_def ENR_homeomorphic_ENR)
qed


lemma AR_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "AR S \<longleftrightarrow> ANR S \<and> contractible S \<and> S \<noteq> {}"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  have "aff_dim S < int DIM('a \<times> real)"
      using aff_dim_le_DIM [of S] by auto
    then obtain C and S' :: "('a * real) set"
    where "convex C" "C \<noteq> {}" "closedin (top_of_set C) S'" "S homeomorphic S'"
    using homeomorphic_closedin_convex by blast
  with \<open>AR S\<close> have "contractible S"
    by (meson AR_def convex_imp_contractible homeomorphic_contractible_eq retract_of_contractible)
  with \<open>AR S\<close> show ?rhs
    using AR_imp_ANR AR_imp_retract by fastforce
next
  assume ?rhs
  then obtain a and h:: "real \<times> 'a \<Rightarrow> 'a"
      where conth: "continuous_on ({0..1} \<times> S) h"
        and hS: "h ` ({0..1} \<times> S) \<subseteq> S"
        and [simp]: "\<And>x. h(0, x) = x"
        and [simp]: "\<And>x. h(1, x) = a"
        and "ANR S" "S \<noteq> {}"
    by (auto simp: contractible_def homotopic_with_def)
  then have "a \<in> S"
    by (metis all_not_in_conv atLeastAtMost_iff image_subset_iff mem_Sigma_iff order_refl zero_le_one)
  have "\<exists>g. continuous_on W g \<and> g ` W \<subseteq> S \<and> (\<forall>x\<in>T. g x = f x)"
         if      f: "continuous_on T f" "f ` T \<subseteq> S"
            and WT: "closedin (top_of_set W) T"
         for W T and f :: "'a \<times> real \<Rightarrow> 'a"
  proof -
    obtain U g
      where "T \<subseteq> U" and WU: "openin (top_of_set W) U"
        and contg: "continuous_on U g"
        and "g ` U \<subseteq> S" and gf: "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
      using iffD1 [OF ANR_eq_absolute_neighbourhood_extensor \<open>ANR S\<close>, rule_format, OF f WT]
      by auto
    have WWU: "closedin (top_of_set W) (W - U)"
      using WU closedin_diff by fastforce
    moreover have "(W - U) \<inter> T = {}"
      using \<open>T \<subseteq> U\<close> by auto
    ultimately obtain V V'
      where WV': "openin (top_of_set W) V'"
        and WV: "openin (top_of_set W) V"
        and "W - U \<subseteq> V'" "T \<subseteq> V" "V' \<inter> V = {}"
      using separation_normal_local [of W "W-U" T] WT by blast
    then have WVT: "T \<inter> (W - V) = {}"
      by auto
    have WWV: "closedin (top_of_set W) (W - V)"
      using WV closedin_diff by fastforce
    obtain j :: " 'a \<times> real \<Rightarrow> real"
      where contj: "continuous_on W j"
        and j:  "\<And>x. x \<in> W \<Longrightarrow> j x \<in> {0..1}"
        and j0: "\<And>x. x \<in> W - V \<Longrightarrow> j x = 1"
        and j1: "\<And>x. x \<in> T \<Longrightarrow> j x = 0"
      by (rule Urysohn_local [OF WT WWV WVT, of 0 "1::real"]) (auto simp: in_segment)
    have Weq: "W = (W - V) \<union> (W - V')"
      using \<open>V' \<inter> V = {}\<close> by force
    show ?thesis
    proof (intro conjI exI)
      have *: "continuous_on (W - V') (\<lambda>x. h (j x, g x))"
      proof (rule continuous_on_compose2 [OF conth continuous_on_Pair])
        show "continuous_on (W - V') j"
          by (rule continuous_on_subset [OF contj Diff_subset])
        show "continuous_on (W - V') g"
          by (metis Diff_subset_conv \<open>W - U \<subseteq> V'\<close> contg continuous_on_subset Un_commute)
        show "(\<lambda>x. (j x, g x)) ` (W - V') \<subseteq> {0..1} \<times> S"
          using j \<open>g ` U \<subseteq> S\<close> \<open>W - U \<subseteq> V'\<close> by fastforce
      qed
      show "continuous_on W (\<lambda>x. if x \<in> W - V then a else h (j x, g x))"
      proof (subst Weq, rule continuous_on_cases_local)
        show "continuous_on (W - V') (\<lambda>x. h (j x, g x))"
          using "*" by blast
      qed (use WWV WV' Weq j0 j1 in auto)
    next
      have "h (j (x, y), g (x, y)) \<in> S" if "(x, y) \<in> W" "(x, y) \<in> V" for x y
      proof -
        have "j(x, y) \<in> {0..1}"
          using j that by blast
        moreover have "g(x, y) \<in> S"
          using \<open>V' \<inter> V = {}\<close> \<open>W - U \<subseteq> V'\<close> \<open>g ` U \<subseteq> S\<close> that by fastforce
        ultimately show ?thesis
          using hS by blast
      qed
      with \<open>a \<in> S\<close> \<open>g ` U \<subseteq> S\<close>
      show "(\<lambda>x. if x \<in> W - V then a else h (j x, g x)) ` W \<subseteq> S"
        by auto
    next
      show "\<forall>x\<in>T. (if x \<in> W - V then a else h (j x, g x)) = f x"
        using \<open>T \<subseteq> V\<close> by (auto simp: j0 j1 gf)
    qed
  qed
  then show ?lhs
    by (simp add: AR_eq_absolute_extensor)
qed


lemma ANR_retract_of_ANR:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR T" and ST: "S retract_of T"
  shows "ANR S"
proof (clarsimp simp add: ANR_eq_absolute_neighbourhood_extensor)
  fix f::"'a \<times> real \<Rightarrow> 'a" and U W
  assume W: "continuous_on W f" "f ` W \<subseteq> S" "closedin (top_of_set U) W"
  then obtain r where "S \<subseteq> T" and r: "continuous_on T r" "r ` T \<subseteq> S" "\<forall>x\<in>S. r x = x" "continuous_on W f" "f ` W \<subseteq> S"
                                     "closedin (top_of_set U) W"
    by (meson ST retract_of_def retraction_def)
  then have "f ` W \<subseteq> T"
    by blast
  with W obtain V g where V: "W \<subseteq> V" "openin (top_of_set U) V" "continuous_on V g" "g ` V \<subseteq> T" "\<forall>x\<in>W. g x = f x"
    by (metis ANR_imp_absolute_neighbourhood_extensor \<open>ANR T\<close>)
  with r have "continuous_on V (r \<circ> g) \<and> (r \<circ> g) ` V \<subseteq> S \<and> (\<forall>x\<in>W. (r \<circ> g) x = f x)"
    by (metis (no_types, lifting) comp_apply continuous_on_compose continuous_on_subset image_subset_iff)
  then show "\<exists>V. W \<subseteq> V \<and> openin (top_of_set U) V \<and> (\<exists>g. continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x\<in>W. g x = f x))"
    by (meson V)
qed

lemma AR_retract_of_AR:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>AR T; S retract_of T\<rbrakk> \<Longrightarrow> AR S"
using ANR_retract_of_ANR AR_ANR retract_of_contractible by fastforce

lemma ENR_retract_of_ENR:
   "\<lbrakk>ENR T; S retract_of T\<rbrakk> \<Longrightarrow> ENR S"
by (meson ENR_def retract_of_trans)

lemma retract_of_UNIV:
  fixes S :: "'a::euclidean_space set"
  shows "S retract_of UNIV \<longleftrightarrow> AR S \<and> closed S"
by (metis AR_ANR AR_imp_retract ENR_def ENR_imp_ANR closed_UNIV closed_closedin contractible_UNIV empty_not_UNIV open_UNIV retract_of_closed retract_of_contractible retract_of_empty(1) subtopology_UNIV)

lemma compact_AR:
  fixes S :: "'a::euclidean_space set"
  shows "compact S \<and> AR S \<longleftrightarrow> compact S \<and> S retract_of UNIV"
using compact_imp_closed retract_of_UNIV by blast

text \<open>More properties of ARs, ANRs and ENRs\<close>

lemma not_AR_empty [simp]: "\<not> AR({})"
  by (auto simp: AR_def)

lemma ENR_empty [simp]: "ENR {}"
  by (simp add: ENR_def)

lemma ANR_empty [simp]: "ANR ({} :: 'a::euclidean_space set)"
  by (simp add: ENR_imp_ANR)

lemma convex_imp_AR:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>convex S; S \<noteq> {}\<rbrakk> \<Longrightarrow> AR S"
  by (metis (mono_tags, lifting) Dugundji absolute_extensor_imp_AR)

lemma convex_imp_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "convex S \<Longrightarrow> ANR S"
using ANR_empty AR_imp_ANR convex_imp_AR by blast

lemma ENR_convex_closed:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>closed S; convex S\<rbrakk> \<Longrightarrow> ENR S"
using ENR_def ENR_empty convex_imp_AR retract_of_UNIV by blast

lemma AR_UNIV [simp]: "AR (UNIV :: 'a::euclidean_space set)"
  using retract_of_UNIV by auto

lemma ANR_UNIV [simp]: "ANR (UNIV :: 'a::euclidean_space set)"
  by (simp add: AR_imp_ANR)

lemma ENR_UNIV [simp]:"ENR UNIV"
  using ENR_def by blast

lemma AR_singleton:
    fixes a :: "'a::euclidean_space"
    shows "AR {a}"
  using retract_of_UNIV by blast

lemma ANR_singleton:
    fixes a :: "'a::euclidean_space"
    shows "ANR {a}"
  by (simp add: AR_imp_ANR AR_singleton)

lemma ENR_singleton: "ENR {a}"
  using ENR_def by blast

text \<open>ARs closed under union\<close>

lemma AR_closed_Un_local_aux:
  fixes U :: "'a::euclidean_space set"
  assumes "closedin (top_of_set U) S"
          "closedin (top_of_set U) T"
          "AR S" "AR T" "AR(S \<inter> T)"
  shows "(S \<union> T) retract_of U"
proof -
  have "S \<inter> T \<noteq> {}"
    using assms AR_def by fastforce
  have "S \<subseteq> U" "T \<subseteq> U"
    using assms by (auto simp: closedin_imp_subset)
  define S' where "S' \<equiv> {x \<in> U. setdist {x} S \<le> setdist {x} T}"
  define T' where "T' \<equiv> {x \<in> U. setdist {x} T \<le> setdist {x} S}"
  define W  where "W \<equiv> {x \<in> U. setdist {x} S = setdist {x} T}"
  have US': "closedin (top_of_set U) S'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} S - setdist {x} T" "{..0}"]
    by (simp add: S'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have UT': "closedin (top_of_set U) T'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} T - setdist {x} S" "{..0}"]
    by (simp add: T'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have "S \<subseteq> S'"
    using S'_def \<open>S \<subseteq> U\<close> setdist_sing_in_set by fastforce
  have "T \<subseteq> T'"
    using T'_def \<open>T \<subseteq> U\<close> setdist_sing_in_set by fastforce
  have "S \<inter> T \<subseteq> W" "W \<subseteq> U"
    using \<open>S \<subseteq> U\<close> by (auto simp: W_def setdist_sing_in_set)
  have "(S \<inter> T) retract_of W"
  proof (rule AR_imp_absolute_retract [OF \<open>AR(S \<inter> T)\<close>])
    show "S \<inter> T homeomorphic S \<inter> T"
      by (simp add: homeomorphic_refl)
    show "closedin (top_of_set W) (S \<inter> T)"
      by (meson \<open>S \<inter> T \<subseteq> W\<close> \<open>W \<subseteq> U\<close> assms closedin_Int closedin_subset_trans)
  qed
  then obtain r0
    where "S \<inter> T \<subseteq> W" and contr0: "continuous_on W r0"
      and "r0 ` W \<subseteq> S \<inter> T"
      and r0 [simp]: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> r0 x = x"
      by (auto simp: retract_of_def retraction_def)
  have ST: "x \<in> W \<Longrightarrow> x \<in> S \<longleftrightarrow> x \<in> T" for x
    using setdist_eq_0_closedin \<open>S \<inter> T \<noteq> {}\<close> assms
    by (force simp: W_def setdist_sing_in_set)
  have "S' \<inter> T' = W"
    by (auto simp: S'_def T'_def W_def)
  then have cloUW: "closedin (top_of_set U) W"
    using closedin_Int US' UT' by blast
  define r where "r \<equiv> \<lambda>x. if x \<in> W then r0 x else x"
  have contr: "continuous_on (W \<union> (S \<union> T)) r"
  unfolding r_def
  proof (rule continuous_on_cases_local [OF _ _ contr0 continuous_on_id])
    show "closedin (top_of_set (W \<union> (S \<union> T))) W"
      using \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> \<open>W \<subseteq> U\<close> \<open>closedin (top_of_set U) W\<close> closedin_subset_trans by fastforce
    show "closedin (top_of_set (W \<union> (S \<union> T))) (S \<union> T)"
      by (meson \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> \<open>W \<subseteq> U\<close> assms closedin_Un closedin_subset_trans sup.bounded_iff sup.cobounded2)
    show "\<And>x. x \<in> W \<and> x \<notin> W \<or> x \<in> S \<union> T \<and> x \<in> W \<Longrightarrow> r0 x = x"
      by (auto simp: ST)
  qed
  have rim: "r ` (W \<union> S) \<subseteq> S" "r ` (W \<union> T) \<subseteq> T"
    using \<open>r0 ` W \<subseteq> S \<inter> T\<close> r_def by auto
  have cloUWS: "closedin (top_of_set U) (W \<union> S)"
    by (simp add: cloUW assms closedin_Un)
  obtain g where contg: "continuous_on U g"
    and "g ` U \<subseteq> S" and geqr: "\<And>x. x \<in> W \<union> S \<Longrightarrow> g x = r x"
  proof (rule AR_imp_absolute_extensor [OF \<open>AR S\<close> _ _ cloUWS])
    show "continuous_on (W \<union> S) r"
      using continuous_on_subset contr sup_assoc by blast
  qed (use rim in auto)
  have cloUWT: "closedin (top_of_set U) (W \<union> T)"
    by (simp add: cloUW assms closedin_Un)
  obtain h where conth: "continuous_on U h"
             and "h ` U \<subseteq> T" and heqr: "\<And>x. x \<in> W \<union> T \<Longrightarrow> h x = r x"
  proof (rule AR_imp_absolute_extensor [OF \<open>AR T\<close> _ _ cloUWT])
    show "continuous_on (W \<union> T) r"
      using continuous_on_subset contr sup_assoc by blast
  qed (use rim in auto)
  have U: "U = S' \<union> T'"
    by (force simp: S'_def T'_def)
  have cont: "continuous_on U (\<lambda>x. if x \<in> S' then g x else h x)"
    unfolding U
    apply (rule continuous_on_cases_local)
    using US' UT' \<open>S' \<inter> T' = W\<close> \<open>U = S' \<union> T'\<close>
          contg conth continuous_on_subset geqr heqr by auto
  have UST: "(\<lambda>x. if x \<in> S' then g x else h x) ` U \<subseteq> S \<union> T"
    using \<open>g ` U \<subseteq> S\<close> \<open>h ` U \<subseteq> T\<close> by auto
  show ?thesis
    apply (simp add: retract_of_def retraction_def \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close>)
    apply (rule_tac x="\<lambda>x. if x \<in> S' then g x else h x" in exI)
    using ST UST \<open>S \<subseteq> S'\<close> \<open>S' \<inter> T' = W\<close> \<open>T \<subseteq> T'\<close> cont geqr heqr r_def by auto
qed


lemma AR_closed_Un_local:
  fixes S :: "'a::euclidean_space set"
  assumes STS: "closedin (top_of_set (S \<union> T)) S"
      and STT: "closedin (top_of_set (S \<union> T)) T"
      and "AR S" "AR T" "AR(S \<inter> T)"
    shows "AR(S \<union> T)"
proof -
  have "C retract_of U"
       if hom: "S \<union> T homeomorphic C" and UC: "closedin (top_of_set U) C"
       for U and C :: "('a * real) set"
  proof -
    obtain f g where hom: "homeomorphism (S \<union> T) C f g"
      using hom by (force simp: homeomorphic_def)
    have US: "closedin (top_of_set U) (C \<inter> g -` S)"
      by (metis STS continuous_on_imp_closedin hom homeomorphism_def closedin_trans [OF _ UC])
    have UT: "closedin (top_of_set U) (C \<inter> g -` T)"
      by (metis STT continuous_on_closed hom homeomorphism_def closedin_trans [OF _ UC])
    have "homeomorphism (C \<inter> g -` S) S g f"
      using hom 
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    then have ARS: "AR (C \<inter> g -` S)"
      using \<open>AR S\<close> homeomorphic_AR_iff_AR homeomorphic_def by blast
    have "homeomorphism (C \<inter> g -` T) T g f"
      using hom 
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    then have ART: "AR (C \<inter> g -` T)"
      using \<open>AR T\<close> homeomorphic_AR_iff_AR homeomorphic_def by blast
    have "homeomorphism (C \<inter> g -` S \<inter> (C \<inter> g -` T)) (S \<inter> T) g f"
      using hom
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    then have ARI: "AR ((C \<inter> g -` S) \<inter> (C \<inter> g -` T))"
      using \<open>AR (S \<inter> T)\<close> homeomorphic_AR_iff_AR homeomorphic_def by blast
    have "C = (C \<inter> g -` S) \<union> (C \<inter> g -` T)"
      using hom  by (auto simp: homeomorphism_def)
    then show ?thesis
      by (metis AR_closed_Un_local_aux [OF US UT ARS ART ARI])
  qed
  then show ?thesis
    by (force simp: AR_def)
qed

corollary AR_closed_Un:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>closed S; closed T; AR S; AR T; AR (S \<inter> T)\<rbrakk> \<Longrightarrow> AR (S \<union> T)"
by (metis AR_closed_Un_local_aux closed_closedin retract_of_UNIV subtopology_UNIV)

text \<open>ANRs closed under union\<close>

lemma ANR_closed_Un_local_aux:
  fixes U :: "'a::euclidean_space set"
  assumes US: "closedin (top_of_set U) S"
      and UT: "closedin (top_of_set U) T"
      and "ANR S" "ANR T" "ANR(S \<inter> T)"
  obtains V where "openin (top_of_set U) V" "(S \<union> T) retract_of V"
proof (cases "S = {} \<or> T = {}")
  case True with assms that show ?thesis
    by (metis ANR_imp_neighbourhood_retract Un_commute inf_bot_right sup_inf_absorb)
next
  case False
  then have [simp]: "S \<noteq> {}" "T \<noteq> {}" by auto
  have "S \<subseteq> U" "T \<subseteq> U"
    using assms by (auto simp: closedin_imp_subset)
  define S' where "S' \<equiv> {x \<in> U. setdist {x} S \<le> setdist {x} T}"
  define T' where "T' \<equiv> {x \<in> U. setdist {x} T \<le> setdist {x} S}"
  define W  where "W \<equiv> {x \<in> U. setdist {x} S = setdist {x} T}"
  have cloUS': "closedin (top_of_set U) S'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} S - setdist {x} T" "{..0}"]
    by (simp add: S'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have cloUT': "closedin (top_of_set U) T'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} T - setdist {x} S" "{..0}"]
    by (simp add: T'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have "S \<subseteq> S'"
    using S'_def \<open>S \<subseteq> U\<close> setdist_sing_in_set by fastforce
  have "T \<subseteq> T'"
    using T'_def \<open>T \<subseteq> U\<close> setdist_sing_in_set by fastforce
  have "S' \<union> T' = U"
    by (auto simp: S'_def T'_def)
  have "W \<subseteq> S'"
    by (simp add: Collect_mono S'_def W_def)
  have "W \<subseteq> T'"
    by (simp add: Collect_mono T'_def W_def)
  have ST_W: "S \<inter> T \<subseteq> W" and "W \<subseteq> U"
    using \<open>S \<subseteq> U\<close> by (force simp: W_def setdist_sing_in_set)+
  have "S' \<inter> T' = W"
    by (auto simp: S'_def T'_def W_def)
  then have cloUW: "closedin (top_of_set U) W"
    using closedin_Int cloUS' cloUT' by blast
  obtain W' W0 where "openin (top_of_set W) W'"
                 and cloWW0: "closedin (top_of_set W) W0"
                 and "S \<inter> T \<subseteq> W'" "W' \<subseteq> W0"
                 and ret: "(S \<inter> T) retract_of W0"
    by (meson ANR_imp_closed_neighbourhood_retract ST_W US UT \<open>W \<subseteq> U\<close> \<open>ANR(S \<inter> T)\<close> closedin_Int closedin_subset_trans)
  then obtain U0 where opeUU0: "openin (top_of_set U) U0"
                   and U0: "S \<inter> T \<subseteq> U0" "U0 \<inter> W \<subseteq> W0"
    unfolding openin_open  using \<open>W \<subseteq> U\<close> by blast
  have "W0 \<subseteq> U"
    using \<open>W \<subseteq> U\<close> cloWW0 closedin_subset by fastforce
  obtain r0
    where "S \<inter> T \<subseteq> W0" and contr0: "continuous_on W0 r0" and "r0 ` W0 \<subseteq> S \<inter> T"
      and r0 [simp]: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> r0 x = x"
    using ret  by (force simp: retract_of_def retraction_def)
  have ST: "x \<in> W \<Longrightarrow> x \<in> S \<longleftrightarrow> x \<in> T" for x
    using assms by (auto simp: W_def setdist_sing_in_set dest!: setdist_eq_0_closedin)
  define r where "r \<equiv> \<lambda>x. if x \<in> W0 then r0 x else x"
  have "r ` (W0 \<union> S) \<subseteq> S" "r ` (W0 \<union> T) \<subseteq> T"
    using \<open>r0 ` W0 \<subseteq> S \<inter> T\<close> r_def by auto
  have contr: "continuous_on (W0 \<union> (S \<union> T)) r"
  unfolding r_def
  proof (rule continuous_on_cases_local [OF _ _ contr0 continuous_on_id])
    show "closedin (top_of_set (W0 \<union> (S \<union> T))) W0"
      using closedin_subset_trans [of U]
      by (metis le_sup_iff order_refl cloWW0 cloUW closedin_trans \<open>W0 \<subseteq> U\<close> \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close>)
    show "closedin (top_of_set (W0 \<union> (S \<union> T))) (S \<union> T)"
      by (meson \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> \<open>W0 \<subseteq> U\<close> assms closedin_Un closedin_subset_trans sup.bounded_iff sup.cobounded2)
    show "\<And>x. x \<in> W0 \<and> x \<notin> W0 \<or> x \<in> S \<union> T \<and> x \<in> W0 \<Longrightarrow> r0 x = x"
      using ST cloWW0 closedin_subset by fastforce
  qed
  have cloS'WS: "closedin (top_of_set S') (W0 \<union> S)"
    by (meson closedin_subset_trans US cloUS' \<open>S \<subseteq> S'\<close> \<open>W \<subseteq> S'\<close> cloUW cloWW0 
              closedin_Un closedin_imp_subset closedin_trans)
  obtain W1 g where "W0 \<union> S \<subseteq> W1" and contg: "continuous_on W1 g"
                and opeSW1: "openin (top_of_set S') W1"
                and "g ` W1 \<subseteq> S" and geqr: "\<And>x. x \<in> W0 \<union> S \<Longrightarrow> g x = r x"
  proof (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> _ \<open>r ` (W0 \<union> S) \<subseteq> S\<close> cloS'WS])
    show "continuous_on (W0 \<union> S) r"
      using continuous_on_subset contr sup_assoc by blast
  qed auto
  have cloT'WT: "closedin (top_of_set T') (W0 \<union> T)"
    by (meson closedin_subset_trans UT cloUT' \<open>T \<subseteq> T'\<close> \<open>W \<subseteq> T'\<close> cloUW cloWW0 
              closedin_Un closedin_imp_subset closedin_trans)
  obtain W2 h where "W0 \<union> T \<subseteq> W2" and conth: "continuous_on W2 h"
                and opeSW2: "openin (top_of_set T') W2"
                and "h ` W2 \<subseteq> T" and heqr: "\<And>x. x \<in> W0 \<union> T \<Longrightarrow> h x = r x"
  proof (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR T\<close> _ \<open>r ` (W0 \<union> T) \<subseteq> T\<close> cloT'WT])
    show "continuous_on (W0 \<union> T) r"
      using continuous_on_subset contr sup_assoc by blast
  qed auto
  have "S' \<inter> T' = W"
    by (force simp: S'_def T'_def W_def)
  obtain O1 O2 where O12: "open O1" "W1 = S' \<inter> O1" "open O2" "W2 = T' \<inter> O2"
    using opeSW1 opeSW2 by (force simp: openin_open)
  show ?thesis
  proof
    have eq: "W1 - (W - U0) \<union> (W2 - (W - U0)) 
            = ((U - T') \<inter> O1 \<union> (U - S') \<inter> O2 \<union> U \<inter> O1 \<inter> O2) - (W - U0)" (is "?WW1 \<union> ?WW2 = ?rhs")
      using \<open>U0 \<inter> W \<subseteq> W0\<close> \<open>W0 \<union> S \<subseteq> W1\<close> \<open>W0 \<union> T \<subseteq> W2\<close>
      by (auto simp: \<open>S' \<union> T' = U\<close> [symmetric] \<open>S' \<inter> T' = W\<close> [symmetric] \<open>W1 = S' \<inter> O1\<close> \<open>W2 = T' \<inter> O2\<close>)
    show "openin (top_of_set U) (?WW1 \<union> ?WW2)"
      by (simp add: eq \<open>open O1\<close> \<open>open O2\<close> cloUS' cloUT' cloUW closedin_diff opeUU0 openin_Int_open openin_Un openin_diff)
    obtain SU' where "closed SU'" "S' = U \<inter> SU'"
      using cloUS' by (auto simp add: closedin_closed)
    moreover have "?WW1 = (?WW1 \<union> ?WW2) \<inter> SU'"
      using \<open>S' = U \<inter> SU'\<close> \<open>W1 = S' \<inter> O1\<close> \<open>S' \<union> T' = U\<close> \<open>W2 = T' \<inter> O2\<close>  \<open>S' \<inter> T' = W\<close> \<open>W0 \<union> S \<subseteq> W1\<close> U0
      by auto
    ultimately have cloW1: "closedin (top_of_set (W1 - (W - U0) \<union> (W2 - (W - U0)))) (W1 - (W - U0))"
      by (metis closedin_closed_Int)
    obtain TU' where "closed TU'" "T' = U \<inter> TU'"
      using cloUT' by (auto simp add: closedin_closed)
    moreover have "?WW2 = (?WW1 \<union> ?WW2) \<inter> TU'"
      using \<open>T' = U \<inter> TU'\<close> \<open>W1 = S' \<inter> O1\<close> \<open>S' \<union> T' = U\<close> \<open>W2 = T' \<inter> O2\<close>  \<open>S' \<inter> T' = W\<close> \<open>W0 \<union> T \<subseteq> W2\<close> U0
      by auto
    ultimately have cloW2: "closedin (top_of_set (?WW1 \<union> ?WW2)) ?WW2"
      by (metis closedin_closed_Int)
    let ?gh = "\<lambda>x. if x \<in> S' then g x else h x"
    have "\<exists>r. continuous_on (?WW1 \<union> ?WW2) r \<and> r ` (?WW1 \<union> ?WW2) \<subseteq> S \<union> T \<and> (\<forall>x\<in>S \<union> T. r x = x)"
    proof (intro exI conjI)
      show "\<forall>x\<in>S \<union> T. ?gh x = x"
        using ST \<open>S' \<inter> T' = W\<close> geqr heqr O12  
        by (metis Int_iff Un_iff \<open>W0 \<union> S \<subseteq> W1\<close> \<open>W0 \<union> T \<subseteq> W2\<close> r0 r_def sup.order_iff)  
      have "\<And>x. x \<in> ?WW1 \<and> x \<notin> S' \<or> x \<in> ?WW2 \<and> x \<in> S' \<Longrightarrow> g x = h x"
        using O12
        by (metis (full_types) DiffD1 DiffD2 DiffI IntE IntI U0(2) UnCI \<open>S' \<inter> T' = W\<close> geqr heqr in_mono)
      then show "continuous_on (?WW1 \<union> ?WW2) ?gh"
        using continuous_on_cases_local [OF cloW1 cloW2 continuous_on_subset [OF contg] continuous_on_subset [OF conth]]
        by simp
      show "?gh ` (?WW1 \<union> ?WW2) \<subseteq> S \<union> T"
        using \<open>W1 = S' \<inter> O1\<close> \<open>W2 = T' \<inter> O2\<close> \<open>S' \<inter> T' = W\<close> \<open>g ` W1 \<subseteq> S\<close> \<open>h ` W2 \<subseteq> T\<close> \<open>U0 \<inter> W \<subseteq> W0\<close> \<open>W0 \<union> S \<subseteq> W1\<close>  
        by (auto simp add: image_subset_iff)
    qed
    then show "S \<union> T retract_of ?WW1 \<union> ?WW2"
      using  \<open>W0 \<union> S \<subseteq> W1\<close> \<open>W0 \<union> T \<subseteq> W2\<close> ST opeUU0 U0
      by (auto simp: retract_of_def retraction_def)
  qed
qed


lemma ANR_closed_Un_local:
  fixes S :: "'a::euclidean_space set"
  assumes STS: "closedin (top_of_set (S \<union> T)) S"
      and STT: "closedin (top_of_set (S \<union> T)) T"
      and "ANR S" "ANR T" "ANR(S \<inter> T)" 
    shows "ANR(S \<union> T)"
proof -
  have "\<exists>T. openin (top_of_set U) T \<and> C retract_of T"
       if hom: "S \<union> T homeomorphic C" and UC: "closedin (top_of_set U) C"
       for U and C :: "('a * real) set"
  proof -
    obtain f g where hom: "homeomorphism (S \<union> T) C f g"
      using hom by (force simp: homeomorphic_def)
    have US: "closedin (top_of_set U) (C \<inter> g -` S)"
      by (metis STS UC closedin_trans continuous_on_imp_closedin hom homeomorphism_def)
    have UT: "closedin (top_of_set U) (C \<inter> g -` T)"
      by (metis STT UC closedin_trans continuous_on_imp_closedin hom homeomorphism_def)
    have "homeomorphism (C \<inter> g -` S) S g f"
      using hom 
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      by (rule_tac x="f x" in image_eqI, auto)
    then have ANRS: "ANR (C \<inter> g -` S)"
      using \<open>ANR S\<close> homeomorphic_ANR_iff_ANR homeomorphic_def by blast
    have "homeomorphism (C \<inter> g -` T) T g f"
      using hom apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      by (rule_tac x="f x" in image_eqI, auto)
    then have ANRT: "ANR (C \<inter> g -` T)"
      using \<open>ANR T\<close> homeomorphic_ANR_iff_ANR homeomorphic_def by blast
    have "homeomorphism (C \<inter> g -` S \<inter> (C \<inter> g -` T)) (S \<inter> T) g f"
      using hom
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      by (rule_tac x="f x" in image_eqI, auto)
    then have ANRI: "ANR ((C \<inter> g -` S) \<inter> (C \<inter> g -` T))"
      using \<open>ANR (S \<inter> T)\<close> homeomorphic_ANR_iff_ANR homeomorphic_def by blast
    have "C = (C \<inter> g -` S) \<union> (C \<inter> g -` T)"
      using hom by (auto simp: homeomorphism_def)
    then show ?thesis
      by (metis ANR_closed_Un_local_aux [OF US UT ANRS ANRT ANRI])
  qed
  then show ?thesis
    by (auto simp: ANR_def)
qed    

corollary ANR_closed_Un:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>closed S; closed T; ANR S; ANR T; ANR (S \<inter> T)\<rbrakk> \<Longrightarrow> ANR (S \<union> T)"
by (simp add: ANR_closed_Un_local closedin_def diff_eq open_Compl openin_open_Int)

lemma ANR_openin:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR T" and opeTS: "openin (top_of_set T) S"
  shows "ANR S"
proof (clarsimp simp only: ANR_eq_absolute_neighbourhood_extensor)
  fix f :: "'a \<times> real \<Rightarrow> 'a" and U C
  assume contf: "continuous_on C f" and fim: "f ` C \<subseteq> S"
     and cloUC: "closedin (top_of_set U) C"
  have "f ` C \<subseteq> T"
    using fim opeTS openin_imp_subset by blast
  obtain W g where "C \<subseteq> W"
               and UW: "openin (top_of_set U) W"
               and contg: "continuous_on W g"
               and gim: "g ` W \<subseteq> T"
               and geq: "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
    using ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR T\<close> contf \<open>f ` C \<subseteq> T\<close> cloUC] fim by auto
  show "\<exists>V g. C \<subseteq> V \<and> openin (top_of_set U) V \<and> continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x\<in>C. g x = f x)"
  proof (intro exI conjI)
    show "C \<subseteq> W \<inter> g -` S"
      using \<open>C \<subseteq> W\<close> fim geq by blast
    show "openin (top_of_set U) (W \<inter> g -` S)"
      by (metis (mono_tags, lifting) UW contg continuous_openin_preimage gim opeTS openin_trans)
    show "continuous_on (W \<inter> g -` S) g"
      by (blast intro: continuous_on_subset [OF contg])
    show "g ` (W \<inter> g -` S) \<subseteq> S"
      using gim by blast
    show "\<forall>x\<in>C. g x = f x"
      using geq by blast
  qed
qed

lemma ENR_openin:
    fixes S :: "'a::euclidean_space set"
    assumes "ENR T" "openin (top_of_set T) S"
    shows "ENR S"
  by (meson ANR_openin ENR_ANR assms locally_open_subset)

lemma ANR_neighborhood_retract:
    fixes S :: "'a::euclidean_space set"
    assumes "ANR U" "S retract_of T" "openin (top_of_set U) T"
    shows "ANR S"
  using ANR_openin ANR_retract_of_ANR assms by blast

lemma ENR_neighborhood_retract:
    fixes S :: "'a::euclidean_space set"
    assumes "ENR U" "S retract_of T" "openin (top_of_set U) T"
    shows "ENR S"
  using ENR_openin ENR_retract_of_ENR assms by blast

lemma ANR_rel_interior:
  fixes S :: "'a::euclidean_space set"
  shows "ANR S \<Longrightarrow> ANR(rel_interior S)"
   by (blast intro: ANR_openin openin_set_rel_interior)

lemma ANR_delete:
  fixes S :: "'a::euclidean_space set"
  shows "ANR S \<Longrightarrow> ANR(S - {a})"
   by (blast intro: ANR_openin openin_delete openin_subtopology_self)

lemma ENR_rel_interior:
  fixes S :: "'a::euclidean_space set"
  shows "ENR S \<Longrightarrow> ENR(rel_interior S)"
   by (blast intro: ENR_openin openin_set_rel_interior)

lemma ENR_delete:
  fixes S :: "'a::euclidean_space set"
  shows "ENR S \<Longrightarrow> ENR(S - {a})"
   by (blast intro: ENR_openin openin_delete openin_subtopology_self)

lemma open_imp_ENR: "open S \<Longrightarrow> ENR S"
    using ENR_def by blast

lemma open_imp_ANR:
    fixes S :: "'a::euclidean_space set"
    shows "open S \<Longrightarrow> ANR S"
  by (simp add: ENR_imp_ANR open_imp_ENR)

lemma ANR_ball [iff]:
    fixes a :: "'a::euclidean_space"
    shows "ANR(ball a r)"
  by (simp add: convex_imp_ANR)

lemma ENR_ball [iff]: "ENR(ball a r)"
  by (simp add: open_imp_ENR)

lemma AR_ball [simp]:
    fixes a :: "'a::euclidean_space"
    shows "AR(ball a r) \<longleftrightarrow> 0 < r"
  by (auto simp: AR_ANR convex_imp_contractible)

lemma ANR_cball [iff]:
    fixes a :: "'a::euclidean_space"
    shows "ANR(cball a r)"
  by (simp add: convex_imp_ANR)

lemma ENR_cball:
    fixes a :: "'a::euclidean_space"
    shows "ENR(cball a r)"
  using ENR_convex_closed by blast

lemma AR_cball [simp]:
    fixes a :: "'a::euclidean_space"
    shows "AR(cball a r) \<longleftrightarrow> 0 \<le> r"
  by (auto simp: AR_ANR convex_imp_contractible)

lemma ANR_box [iff]:
    fixes a :: "'a::euclidean_space"
    shows "ANR(cbox a b)" "ANR(box a b)"
  by (auto simp: convex_imp_ANR open_imp_ANR)

lemma ENR_box [iff]:
    fixes a :: "'a::euclidean_space"
    shows "ENR(cbox a b)" "ENR(box a b)"
  by (simp_all add: ENR_convex_closed closed_cbox open_box open_imp_ENR)

lemma AR_box [simp]:
    "AR(cbox a b) \<longleftrightarrow> cbox a b \<noteq> {}" "AR(box a b) \<longleftrightarrow> box a b \<noteq> {}"
  by (auto simp: AR_ANR convex_imp_contractible)

lemma ANR_interior:
     fixes S :: "'a::euclidean_space set"
     shows "ANR(interior S)"
  by (simp add: open_imp_ANR)

lemma ENR_interior:
     fixes S :: "'a::euclidean_space set"
     shows "ENR(interior S)"
  by (simp add: open_imp_ENR)

lemma AR_imp_contractible:
    fixes S :: "'a::euclidean_space set"
    shows "AR S \<Longrightarrow> contractible S"
  by (simp add: AR_ANR)

lemma ENR_imp_locally_compact:
    fixes S :: "'a::euclidean_space set"
    shows "ENR S \<Longrightarrow> locally compact S"
  by (simp add: ENR_ANR)

lemma ANR_imp_locally_path_connected:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S"
    shows "locally path_connected S"
proof -
  obtain U and T :: "('a \<times> real) set"
     where "convex U" "U \<noteq> {}"
       and UT: "closedin (top_of_set U) T" and "S homeomorphic T"
  proof (rule homeomorphic_closedin_convex)
    show "aff_dim S < int DIM('a \<times> real)"
      using aff_dim_le_DIM [of S] by auto
  qed auto
  then have "locally path_connected T"
    by (meson ANR_imp_absolute_neighbourhood_retract
        assms convex_imp_locally_path_connected locally_open_subset retract_of_locally_path_connected)
  then have S: "locally path_connected S"
      if "openin (top_of_set U) V" "T retract_of V" "U \<noteq> {}" for V
    using \<open>S homeomorphic T\<close> homeomorphic_locally homeomorphic_path_connectedness by blast
  obtain Ta where "(openin (top_of_set U) Ta \<and> T retract_of Ta)"
    using ANR_def UT \<open>S homeomorphic T\<close> assms by moura
  then show ?thesis
    using S \<open>U \<noteq> {}\<close> by blast
qed

lemma ANR_imp_locally_connected:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S"
    shows "locally connected S"
using locally_path_connected_imp_locally_connected ANR_imp_locally_path_connected assms by auto

lemma AR_imp_locally_path_connected:
  fixes S :: "'a::euclidean_space set"
  assumes "AR S"
    shows "locally path_connected S"
by (simp add: ANR_imp_locally_path_connected AR_imp_ANR assms)

lemma AR_imp_locally_connected:
  fixes S :: "'a::euclidean_space set"
  assumes "AR S"
    shows "locally connected S"
using ANR_imp_locally_connected AR_ANR assms by blast

lemma ENR_imp_locally_path_connected:
  fixes S :: "'a::euclidean_space set"
  assumes "ENR S"
    shows "locally path_connected S"
by (simp add: ANR_imp_locally_path_connected ENR_imp_ANR assms)

lemma ENR_imp_locally_connected:
  fixes S :: "'a::euclidean_space set"
  assumes "ENR S"
    shows "locally connected S"
using ANR_imp_locally_connected ENR_ANR assms by blast

lemma ANR_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "ANR S" "ANR T" shows "ANR(S \<times> T)"
proof (clarsimp simp only: ANR_eq_absolute_neighbourhood_extensor)
  fix f :: " ('a \<times> 'b) \<times> real \<Rightarrow> 'a \<times> 'b" and U C
  assume "continuous_on C f" and fim: "f ` C \<subseteq> S \<times> T"
     and cloUC: "closedin (top_of_set U) C"
  have contf1: "continuous_on C (fst \<circ> f)"
    by (simp add: \<open>continuous_on C f\<close> continuous_on_fst)
  obtain W1 g where "C \<subseteq> W1"
               and UW1: "openin (top_of_set U) W1"
               and contg: "continuous_on W1 g"
               and gim: "g ` W1 \<subseteq> S"
               and geq: "\<And>x. x \<in> C \<Longrightarrow> g x = (fst \<circ> f) x"
  proof (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> contf1 _ cloUC])
    show "(fst \<circ> f) ` C \<subseteq> S"
      using fim by auto
  qed auto
  have contf2: "continuous_on C (snd \<circ> f)"
    by (simp add: \<open>continuous_on C f\<close> continuous_on_snd)
  obtain W2 h where "C \<subseteq> W2"
               and UW2: "openin (top_of_set U) W2"
               and conth: "continuous_on W2 h"
               and him: "h ` W2 \<subseteq> T"
               and heq: "\<And>x. x \<in> C \<Longrightarrow> h x = (snd \<circ> f) x"
  proof (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR T\<close> contf2 _ cloUC])
    show "(snd \<circ> f) ` C \<subseteq> T"
      using fim by auto
  qed auto
  show "\<exists>V g. C \<subseteq> V \<and>
               openin (top_of_set U) V \<and>
               continuous_on V g \<and> g ` V \<subseteq> S \<times> T \<and> (\<forall>x\<in>C. g x = f x)"
  proof (intro exI conjI)
    show "C \<subseteq> W1 \<inter> W2"
      by (simp add: \<open>C \<subseteq> W1\<close> \<open>C \<subseteq> W2\<close>)
    show "openin (top_of_set U) (W1 \<inter> W2)"
      by (simp add: UW1 UW2 openin_Int)
    show  "continuous_on (W1 \<inter> W2) (\<lambda>x. (g x, h x))"
      by (metis (no_types) contg conth continuous_on_Pair continuous_on_subset inf_commute inf_le1)
    show  "(\<lambda>x. (g x, h x)) ` (W1 \<inter> W2) \<subseteq> S \<times> T"
      using gim him by blast
    show  "(\<forall>x\<in>C. (g x, h x) = f x)"
      using geq heq by auto
  qed
qed

lemma AR_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "AR S" "AR T" shows "AR(S \<times> T)"
  using assms by (simp add: AR_ANR ANR_Times contractible_Times)

(* Unused and requires ordered_euclidean_space
subsection\<^marker>\<open>tag unimportant\<close>\<open>Retracts and intervals in ordered euclidean space\<close>

lemma ANR_interval [iff]:
  fixes a :: "'a::ordered_euclidean_space"
  shows "ANR{a..b}"
  by (simp add: interval_cbox)

lemma ENR_interval [iff]:
  fixes a :: "'a::ordered_euclidean_space"
  shows "ENR{a..b}"
  by (auto simp: interval_cbox)
*)

subsection \<open>More advanced properties of ANRs and ENRs\<close>

lemma ENR_rel_frontier_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" "convex S"
    shows "ENR(rel_frontier S)"
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False
  with assms have "rel_interior S \<noteq> {}"
    by (simp add: rel_interior_eq_empty)
  then obtain a where a: "a \<in> rel_interior S"
    by auto
  have ahS: "affine hull S - {a} \<subseteq> {x. closest_point (affine hull S) x \<noteq> a}"
    by (auto simp: closest_point_self)
  have "rel_frontier S retract_of affine hull S - {a}"
    by (simp add: assms a rel_frontier_retract_of_punctured_affine_hull)
  also have "\<dots> retract_of {x. closest_point (affine hull S) x \<noteq> a}"
    unfolding retract_of_def retraction_def ahS
    apply (rule_tac x="closest_point (affine hull S)" in exI)
    apply (auto simp: False closest_point_self affine_imp_convex closest_point_in_set continuous_on_closest_point)
    done
  finally have "rel_frontier S retract_of {x. closest_point (affine hull S) x \<noteq> a}" .
  moreover have "openin (top_of_set UNIV) (UNIV \<inter> closest_point (affine hull S) -` (- {a}))"
    by (intro continuous_openin_preimage_gen) (auto simp: False affine_imp_convex continuous_on_closest_point)
  ultimately show ?thesis
    by (meson ENR_convex_closed ENR_delete ENR_retract_of_ENR \<open>rel_frontier S retract_of affine hull S - {a}\<close> 
              closed_affine_hull convex_affine_hull)
qed

lemma ANR_rel_frontier_convex:
                 fixes S :: "'a::euclidean_space set"
  assumes "bounded S" "convex S"
    shows "ANR(rel_frontier S)"
by (simp add: ENR_imp_ANR ENR_rel_frontier_convex assms)
    
lemma ENR_closedin_Un_local:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>ENR S; ENR T; ENR(S \<inter> T);
          closedin (top_of_set (S \<union> T)) S; closedin (top_of_set (S \<union> T)) T\<rbrakk>
        \<Longrightarrow> ENR(S \<union> T)"
by (simp add: ENR_ANR ANR_closed_Un_local locally_compact_closedin_Un)

lemma ENR_closed_Un:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>closed S; closed T; ENR S; ENR T; ENR(S \<inter> T)\<rbrakk> \<Longrightarrow> ENR(S \<union> T)"
by (auto simp: closed_subset ENR_closedin_Un_local)

lemma absolute_retract_Un:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>S retract_of UNIV; T retract_of UNIV; (S \<inter> T) retract_of UNIV\<rbrakk>
         \<Longrightarrow> (S \<union> T) retract_of UNIV"
  by (meson AR_closed_Un_local_aux closed_subset retract_of_UNIV retract_of_imp_subset)

lemma retract_from_Un_Int:
  fixes S :: "'a::euclidean_space set"
  assumes clS: "closedin (top_of_set (S \<union> T)) S"
      and clT: "closedin (top_of_set (S \<union> T)) T"
      and Un: "(S \<union> T) retract_of U" and Int: "(S \<inter> T) retract_of T"
    shows "S retract_of U"
proof -
  obtain r where r: "continuous_on T r" "r ` T \<subseteq> S \<inter> T" "\<forall>x\<in>S \<inter> T. r x = x"
    using Int by (auto simp: retraction_def retract_of_def)
  have "S retract_of S \<union> T"
    unfolding retraction_def retract_of_def
  proof (intro exI conjI)
    show "continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then x else r x)"
      using r by (intro continuous_on_cases_local [OF clS clT]) auto
  qed (use r in auto)
  also have "\<dots> retract_of U"
    by (rule Un)
  finally show ?thesis .
qed

lemma AR_from_Un_Int_local:
  fixes S :: "'a::euclidean_space set"
  assumes clS: "closedin (top_of_set (S \<union> T)) S"
      and clT: "closedin (top_of_set (S \<union> T)) T"
      and Un: "AR(S \<union> T)" and Int: "AR(S \<inter> T)"
    shows "AR S"
  by (meson AR_imp_retract AR_retract_of_AR Un assms closedin_closed_subset local.Int 
            retract_from_Un_Int retract_of_refl sup_ge2)

lemma AR_from_Un_Int_local':
  fixes S :: "'a::euclidean_space set"
  assumes "closedin (top_of_set (S \<union> T)) S"
      and "closedin (top_of_set (S \<union> T)) T"
      and "AR(S \<union> T)" "AR(S \<inter> T)"
    shows "AR T"
  using AR_from_Un_Int_local [of T S] assms by (simp add: Un_commute Int_commute)

lemma AR_from_Un_Int:
  fixes S :: "'a::euclidean_space set"
  assumes clo: "closed S" "closed T" and Un: "AR(S \<union> T)" and Int: "AR(S \<inter> T)"
  shows "AR S"
  by (metis AR_from_Un_Int_local [OF _ _ Un Int] Un_commute clo closed_closedin closedin_closed_subset inf_sup_absorb subtopology_UNIV top_greatest)

lemma ANR_from_Un_Int_local:
  fixes S :: "'a::euclidean_space set"
  assumes clS: "closedin (top_of_set (S \<union> T)) S"
      and clT: "closedin (top_of_set (S \<union> T)) T"
      and Un: "ANR(S \<union> T)" and Int: "ANR(S \<inter> T)"
    shows "ANR S"
proof -
  obtain V where clo: "closedin (top_of_set (S \<union> T)) (S \<inter> T)"
             and ope: "openin (top_of_set (S \<union> T)) V"
             and ret: "S \<inter> T retract_of V"
    using ANR_imp_neighbourhood_retract [OF Int] by (metis clS clT closedin_Int)
  then obtain r where r: "continuous_on V r" and rim: "r ` V \<subseteq> S \<inter> T" and req: "\<forall>x\<in>S \<inter> T. r x = x"
    by (auto simp: retraction_def retract_of_def)
  have Vsub: "V \<subseteq> S \<union> T"
    by (meson ope openin_contains_cball)
  have Vsup: "S \<inter> T \<subseteq> V"
    by (simp add: retract_of_imp_subset ret)
  then have eq: "S \<union> V = ((S \<union> T) - T) \<union> V"
    by auto
  have eq': "S \<union> V = S \<union> (V \<inter> T)"
    using Vsub by blast
  have "continuous_on (S \<union> V \<inter> T) (\<lambda>x. if x \<in> S then x else r x)"
  proof (rule continuous_on_cases_local)
    show "closedin (top_of_set (S \<union> V \<inter> T)) S"
      using clS closedin_subset_trans inf.boundedE by blast
    show "closedin (top_of_set (S \<union> V \<inter> T)) (V \<inter> T)"
      using clT Vsup by (auto simp: closedin_closed)
    show "continuous_on (V \<inter> T) r"
      by (meson Int_lower1 continuous_on_subset r)
  qed (use req continuous_on_id in auto)
  with rim have "S retract_of S \<union> V"
    unfolding retraction_def retract_of_def using eq' by fastforce
  then show ?thesis
    using ANR_neighborhood_retract [OF Un]
    using \<open>S \<union> V = S \<union> T - T \<union> V\<close> clT ope by fastforce
qed

lemma ANR_from_Un_Int:
  fixes S :: "'a::euclidean_space set"
  assumes clo: "closed S" "closed T" and Un: "ANR(S \<union> T)" and Int: "ANR(S \<inter> T)"
  shows "ANR S"
  by (metis ANR_from_Un_Int_local [OF _ _ Un Int] Un_commute clo closed_closedin closedin_closed_subset inf_sup_absorb subtopology_UNIV top_greatest)

lemma ANR_finite_Union_convex_closed:
  fixes \<T> :: "'a::euclidean_space set set"
  assumes \<T>: "finite \<T>" and clo: "\<And>C. C \<in> \<T> \<Longrightarrow> closed C" and con: "\<And>C. C \<in> \<T> \<Longrightarrow> convex C"
  shows "ANR(\<Union>\<T>)"
proof -
  have "ANR(\<Union>\<T>)" if "card \<T> < n" for n
  using assms that
  proof (induction n arbitrary: \<T>)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "ANR(\<Union>\<U>)" if "finite \<U>" "\<U> \<subseteq> \<T>" for \<U>
      using that
    proof (induction \<U>)
      case empty
      then show ?case  by simp
    next
      case (insert C \<U>)
      have "ANR (C \<union> \<Union>\<U>)"
      proof (rule ANR_closed_Un)
        show "ANR (C \<inter> \<Union>\<U>)"
          unfolding Int_Union
        proof (rule Suc)
          show "finite ((\<inter>) C ` \<U>)"
            by (simp add: insert.hyps(1))
          show "\<And>Ca. Ca \<in> (\<inter>) C ` \<U> \<Longrightarrow> closed Ca"
            by (metis (no_types, opaque_lifting) Suc.prems(2) closed_Int subsetD imageE insert.prems insertI1 insertI2)
          show "\<And>Ca. Ca \<in> (\<inter>) C ` \<U> \<Longrightarrow> convex Ca"
            by (metis (mono_tags, lifting) Suc.prems(3) convex_Int imageE insert.prems insert_subset subsetCE)
          show "card ((\<inter>) C ` \<U>) < n"
          proof -
            have "card \<T> \<le> n"
              by (meson Suc.prems(4) not_less not_less_eq)
            then show ?thesis
              by (metis Suc.prems(1) card_image_le card_seteq insert.hyps insert.prems insert_subset le_trans not_less)
          qed
        qed
        show "closed (\<Union>\<U>)"
          using Suc.prems(2) insert.hyps(1) insert.prems by blast
      qed (use Suc.prems convex_imp_ANR insert.prems insert.IH in auto)
      then show ?case
        by simp
    qed
    then show ?case
      using Suc.prems(1) by blast
  qed
  then show ?thesis
    by blast
qed


lemma finite_imp_ANR:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S"
  shows "ANR S"
proof -
  have "ANR(\<Union>x \<in> S. {x})"
    by (blast intro: ANR_finite_Union_convex_closed assms)
  then show ?thesis
    by simp
qed

lemma ANR_insert:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S" "closed S"
  shows "ANR(insert a S)"
  by (metis ANR_closed_Un ANR_empty ANR_singleton Diff_disjoint Diff_insert_absorb assms closed_singleton insert_absorb insert_is_Un)

lemma ANR_path_component_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "ANR S \<Longrightarrow> ANR(path_component_set S x)"
  using ANR_imp_locally_path_connected ANR_openin openin_path_component_locally_path_connected by blast

lemma ANR_connected_component_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "ANR S \<Longrightarrow> ANR(connected_component_set S x)"
  by (metis ANR_openin openin_connected_component_locally_connected ANR_imp_locally_connected)

lemma ANR_component_ANR:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S" "c \<in> components S"
  shows "ANR c"
  by (metis ANR_connected_component_ANR assms componentsE)

subsection\<open>Original ANR material, now for ENRs\<close>

lemma ENR_bounded:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S"
  shows "ENR S \<longleftrightarrow> (\<exists>U. open U \<and> bounded U \<and> S retract_of U)"
         (is "?lhs = ?rhs")
proof
  obtain r where "0 < r" and r: "S \<subseteq> ball 0 r"
    using bounded_subset_ballD assms by blast
  assume ?lhs
  then show ?rhs
    by (meson ENR_def Elementary_Metric_Spaces.open_ball bounded_Int bounded_ball inf_le2 le_inf_iff 
              open_Int r retract_of_imp_subset retract_of_subset)
next
  assume ?rhs
  then show ?lhs
    using ENR_def by blast
qed

lemma absolute_retract_imp_AR_gen:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "S retract_of T" "convex T" "T \<noteq> {}" "S homeomorphic S'" "closedin (top_of_set U) S'"
  shows "S' retract_of U"
proof -
  have "AR T"
    by (simp add: assms convex_imp_AR)
  then have "AR S"
    using AR_retract_of_AR assms by auto
  then show ?thesis
    using assms AR_imp_absolute_retract by metis
qed

lemma absolute_retract_imp_AR:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "S retract_of UNIV" "S homeomorphic S'" "closed S'"
  shows "S' retract_of UNIV"
  using AR_imp_absolute_retract_UNIV assms retract_of_UNIV by blast

lemma homeomorphic_compact_arness:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "S homeomorphic S'"
  shows "compact S \<and> S retract_of UNIV \<longleftrightarrow> compact S' \<and> S' retract_of UNIV"
  using assms homeomorphic_compactness
  by (metis compact_AR homeomorphic_AR_iff_AR)

lemma absolute_retract_from_Un_Int:
  fixes S :: "'a::euclidean_space set"
  assumes "(S \<union> T) retract_of UNIV" "(S \<inter> T) retract_of UNIV" "closed S" "closed T"
  shows "S retract_of UNIV"
  using AR_from_Un_Int assms retract_of_UNIV by auto

lemma ENR_from_Un_Int_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "closedin (top_of_set (S \<union> T)) S" "closedin (top_of_set (S \<union> T)) T" "ENR(S \<union> T)" "ENR(S \<inter> T)"
  shows "ENR S"
  by (meson ANR_from_Un_Int_local ANR_imp_neighbourhood_retract ENR_ANR ENR_neighborhood_retract assms)


lemma ENR_from_Un_Int:
  fixes S :: "'a::euclidean_space set"
  assumes "closed S" "closed T" "ENR(S \<union> T)" "ENR(S \<inter> T)"
  shows "ENR S"
  by (meson ENR_from_Un_Int_gen assms closed_subset sup_ge1 sup_ge2)


lemma ENR_finite_Union_convex_closed:
  fixes \<T> :: "'a::euclidean_space set set"
  assumes \<T>: "finite \<T>" and clo: "\<And>C. C \<in> \<T> \<Longrightarrow> closed C" and con: "\<And>C. C \<in> \<T> \<Longrightarrow> convex C"
  shows "ENR(\<Union> \<T>)"
  by (simp add: ENR_ANR ANR_finite_Union_convex_closed \<T> clo closed_Union closed_imp_locally_compact con)

lemma finite_imp_ENR:
  fixes S :: "'a::euclidean_space set"
  shows "finite S \<Longrightarrow> ENR S"
  by (simp add: ENR_ANR finite_imp_ANR finite_imp_closed closed_imp_locally_compact)

lemma ENR_insert:
  fixes S :: "'a::euclidean_space set"
  assumes "closed S" "ENR S"
  shows "ENR(insert a S)"
proof -
  have "ENR ({a} \<union> S)"
    by (metis ANR_insert ENR_ANR Un_commute Un_insert_right assms closed_imp_locally_compact closed_insert sup_bot_right)
  then show ?thesis
    by auto
qed

lemma ENR_path_component_ENR:
  fixes S :: "'a::euclidean_space set"
  assumes "ENR S"
  shows "ENR(path_component_set S x)"
  by (metis ANR_imp_locally_path_connected ENR_empty ENR_imp_ANR ENR_openin assms
            locally_path_connected_2 openin_subtopology_self path_component_eq_empty)

(*UNUSED
lemma ENR_Times:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "ENR S" "ENR T" shows "ENR(S \<times> T)"
using assms apply (simp add: ENR_ANR ANR_Times)
thm locally_compact_Times
oops
  SIMP_TAC[ENR_ANR; ANR_PCROSS; LOCALLY_COMPACT_PCROSS]);;
*)

subsection\<open>Finally, spheres are ANRs and ENRs\<close>

lemma absolute_retract_homeomorphic_convex_compact:
  fixes S :: "'a::euclidean_space set" and U :: "'b::euclidean_space set"
  assumes "S homeomorphic U" "S \<noteq> {}" "S \<subseteq> T" "convex U" "compact U"
  shows "S retract_of T"
  by (metis UNIV_I assms compact_AR convex_imp_AR homeomorphic_AR_iff_AR homeomorphic_compactness homeomorphic_empty(1) retract_of_subset subsetI)

lemma frontier_retract_of_punctured_universe:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "a \<in> interior S"
  shows "(frontier S) retract_of (- {a})"
  using rel_frontier_retract_of_punctured_affine_hull
  by (metis Compl_eq_Diff_UNIV affine_hull_nonempty_interior assms empty_iff rel_frontier_frontier rel_interior_nonempty_interior)

lemma sphere_retract_of_punctured_universe_gen:
  fixes a :: "'a::euclidean_space"
  assumes "b \<in> ball a r"
  shows  "sphere a r retract_of (- {b})"
proof -
  have "frontier (cball a r) retract_of (- {b})"
    using assms frontier_retract_of_punctured_universe interior_cball by blast
  then show ?thesis
    by simp
qed

lemma sphere_retract_of_punctured_universe:
  fixes a :: "'a::euclidean_space"
  assumes "0 < r"
  shows "sphere a r retract_of (- {a})"
  by (simp add: assms sphere_retract_of_punctured_universe_gen)

lemma ENR_sphere:
  fixes a :: "'a::euclidean_space"
  shows "ENR(sphere a r)"
proof (cases "0 < r")
  case True
  then have "sphere a r retract_of -{a}"
    by (simp add: sphere_retract_of_punctured_universe)
  with open_delete show ?thesis
    by (auto simp: ENR_def)
next
  case False
  then show ?thesis
    using finite_imp_ENR
    by (metis finite_insert infinite_imp_nonempty less_linear sphere_eq_empty sphere_trivial)
qed

corollary\<^marker>\<open>tag unimportant\<close> ANR_sphere:
  fixes a :: "'a::euclidean_space"
  shows "ANR(sphere a r)"
  by (simp add: ENR_imp_ANR ENR_sphere)

subsection\<open>Spheres are connected, etc\<close>

lemma locally_path_connected_sphere_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" and "convex S" 
  shows "locally path_connected (rel_frontier S)"
proof (cases "rel_interior S = {}")
  case True
  with assms show ?thesis
    by (simp add: rel_interior_eq_empty)
next
  case False
  then obtain a where a: "a \<in> rel_interior S"
    by blast
  show ?thesis
  proof (rule retract_of_locally_path_connected)
    show "locally path_connected (affine hull S - {a})"
      by (meson convex_affine_hull convex_imp_locally_path_connected locally_open_subset openin_delete openin_subtopology_self)
    show "rel_frontier S retract_of affine hull S - {a}"
      using a assms rel_frontier_retract_of_punctured_affine_hull by blast
  qed
qed

lemma locally_connected_sphere_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" and "convex S" 
  shows "locally connected (rel_frontier S)"
  by (simp add: ANR_imp_locally_connected ANR_rel_frontier_convex assms)

lemma locally_path_connected_sphere:
  fixes a :: "'a::euclidean_space"
  shows "locally path_connected (sphere a r)"
  using ENR_imp_locally_path_connected ENR_sphere by blast

lemma locally_connected_sphere:
  fixes a :: "'a::euclidean_space"
  shows "locally connected(sphere a r)"
  using ANR_imp_locally_connected ANR_sphere by blast

subsection\<open>Borsuk homotopy extension theorem\<close>

text\<open>It's only this late so we can use the concept of retraction,
  saying that the domain sets or range set are ENRs.\<close>

theorem Borsuk_homotopy_extension_homotopic:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes cloTS: "closedin (top_of_set T) S"
      and anr: "(ANR S \<and> ANR T) \<or> ANR U"
      and contf: "continuous_on T f"
      and "f ` T \<subseteq> U"
      and "homotopic_with_canon (\<lambda>x. True) S U f g"
   obtains g' where "homotopic_with_canon (\<lambda>x. True) T U f g'"
                    "continuous_on T g'" "image g' T \<subseteq> U"
                    "\<And>x. x \<in> S \<Longrightarrow> g' x = g x"
proof -
  have "S \<subseteq> T" using assms closedin_imp_subset by blast
  obtain h where conth: "continuous_on ({0..1} \<times> S) h"
             and him: "h ` ({0..1} \<times> S) \<subseteq> U"
             and [simp]: "\<And>x. h(0, x) = f x" "\<And>x. h(1::real, x) = g x"
       using assms by (auto simp: homotopic_with_def)
  define h' where "h' \<equiv>  \<lambda>z. if snd z \<in> S then h z else (f \<circ> snd) z"
  define B where "B \<equiv> {0::real} \<times> T \<union> {0..1} \<times> S"
  have clo0T: "closedin (top_of_set ({0..1} \<times> T)) ({0::real} \<times> T)"
    by (simp add: Abstract_Topology.closedin_Times)
  moreover have cloT1S: "closedin (top_of_set ({0..1} \<times> T)) ({0..1} \<times> S)"
    by (simp add: Abstract_Topology.closedin_Times assms)
  ultimately have clo0TB:"closedin (top_of_set ({0..1} \<times> T)) B"
    by (auto simp: B_def)
  have cloBS: "closedin (top_of_set B) ({0..1} \<times> S)"
    by (metis (no_types) Un_subset_iff B_def closedin_subset_trans [OF cloT1S] clo0TB closedin_imp_subset closedin_self)
  moreover have cloBT: "closedin (top_of_set B) ({0} \<times> T)"
    using \<open>S \<subseteq> T\<close> closedin_subset_trans [OF clo0T]
    by (metis B_def Un_upper1 clo0TB closedin_closed inf_le1)
  moreover have "continuous_on ({0} \<times> T) (f \<circ> snd)"
  proof (rule continuous_intros)+
    show "continuous_on (snd ` ({0} \<times> T)) f"
      by (simp add: contf)
  qed
  ultimately have "continuous_on ({0..1} \<times> S \<union> {0} \<times> T) (\<lambda>x. if snd x \<in> S then h x else (f \<circ> snd) x)"
    by (auto intro!: continuous_on_cases_local conth simp: B_def Un_commute [of "{0} \<times> T"])
  then have conth': "continuous_on B h'"
    by (simp add: h'_def B_def Un_commute [of "{0} \<times> T"])
  have "image h' B \<subseteq> U"
    using \<open>f ` T \<subseteq> U\<close> him by (auto simp: h'_def B_def)
  obtain V k where "B \<subseteq> V" and opeTV: "openin (top_of_set ({0..1} \<times> T)) V"
               and contk: "continuous_on V k" and kim: "k ` V \<subseteq> U"
               and keq: "\<And>x. x \<in> B \<Longrightarrow> k x = h' x"
  using anr
  proof
    assume ST: "ANR S \<and> ANR T"
    have eq: "({0} \<times> T \<inter> {0..1} \<times> S) = {0::real} \<times> S"
      using \<open>S \<subseteq> T\<close> by auto
    have "ANR B"
      unfolding B_def
    proof (rule ANR_closed_Un_local)
      show "closedin (top_of_set ({0} \<times> T \<union> {0..1} \<times> S)) ({0::real} \<times> T)"
        by (metis cloBT B_def)
      show "closedin (top_of_set ({0} \<times> T \<union> {0..1} \<times> S)) ({0..1::real} \<times> S)"
        by (metis Un_commute cloBS B_def)
    qed (simp_all add: ANR_Times convex_imp_ANR ANR_singleton ST eq)
    note Vk = that
    have *: thesis if "openin (top_of_set ({0..1::real} \<times> T)) V"
                      "retraction V B r" for V r
    proof -
      have "continuous_on V (h' \<circ> r)"
        using conth' continuous_on_compose retractionE that(2) by blast
      moreover have "(h' \<circ> r) ` V \<subseteq> U"
        by (metis \<open>h' ` B \<subseteq> U\<close> image_comp retractionE that(2))
      ultimately show ?thesis
        using Vk [of V "h' \<circ> r"] by (metis comp_apply retraction that)
    qed
    show thesis
      by (meson "*" ANR_imp_neighbourhood_retract \<open>ANR B\<close> clo0TB retract_of_def)
  next
    assume "ANR U"
    with ANR_imp_absolute_neighbourhood_extensor \<open>h' ` B \<subseteq> U\<close> clo0TB conth' that
    show ?thesis by blast
  qed
  define S' where "S' \<equiv> {x. \<exists>u::real. u \<in> {0..1} \<and> (u, x::'a) \<in> {0..1} \<times> T - V}"
  have "closedin (top_of_set T) S'"
    unfolding S'_def using closedin_self opeTV 
    by (blast intro: closedin_compact_projection)
  have S'_def: "S' = {x. \<exists>u::real.  (u, x::'a) \<in> {0..1} \<times> T - V}"
    by (auto simp: S'_def)
  have cloTS': "closedin (top_of_set T) S'"
    using S'_def \<open>closedin (top_of_set T) S'\<close> by blast
  have "S \<inter> S' = {}"
    using S'_def B_def \<open>B \<subseteq> V\<close> by force
  obtain a :: "'a \<Rightarrow> real" where conta: "continuous_on T a"
      and "\<And>x. x \<in> T \<Longrightarrow> a x \<in> closed_segment 1 0"
      and a1: "\<And>x. x \<in> S \<Longrightarrow> a x = 1"
      and a0: "\<And>x. x \<in> S' \<Longrightarrow> a x = 0"
    by (rule Urysohn_local [OF cloTS cloTS' \<open>S \<inter> S' = {}\<close>, of 1 0], blast)
  then have ain: "\<And>x. x \<in> T \<Longrightarrow> a x \<in> {0..1}"
    using closed_segment_eq_real_ivl by auto
  have inV: "(u * a t, t) \<in> V" if "t \<in> T" "0 \<le> u" "u \<le> 1" for t u
  proof (rule ccontr)
    assume "(u * a t, t) \<notin> V"
    with ain [OF \<open>t \<in> T\<close>] have "a t = 0"
      apply simp
      by (metis (no_types, lifting) a0 DiffI S'_def SigmaI atLeastAtMost_iff mem_Collect_eq mult_le_one mult_nonneg_nonneg that)
    show False
      using B_def \<open>(u * a t, t) \<notin> V\<close> \<open>B \<subseteq> V\<close> \<open>a t = 0\<close> that by auto
  qed
  show ?thesis
  proof
    show hom: "homotopic_with_canon (\<lambda>x. True) T U f (\<lambda>x. k (a x, x))"
    proof (simp add: homotopic_with, intro exI conjI)
      show "continuous_on ({0..1} \<times> T) (k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z)))"
        apply (intro continuous_on_compose continuous_intros)
        apply (force intro: inV continuous_on_subset [OF contk] continuous_on_subset [OF conta])+
        done
      show "(k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z))) ` ({0..1} \<times> T) \<subseteq> U"
        using inV kim by auto
      show "\<forall>x\<in>T. (k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z))) (0, x) = f x"
        by (simp add: B_def h'_def keq)
      show "\<forall>x\<in>T. (k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z))) (1, x) = k (a x, x)"
        by auto
    qed
  show "continuous_on T (\<lambda>x. k (a x, x))"
    using homotopic_with_imp_continuous_maps [OF hom] by auto
  show "(\<lambda>x. k (a x, x)) ` T \<subseteq> U"
  proof clarify
    fix t
    assume "t \<in> T"
    show "k (a t, t) \<in> U"
      by (metis \<open>t \<in> T\<close> image_subset_iff inV kim not_one_le_zero linear mult_cancel_right1)
  qed
  show "\<And>x. x \<in> S \<Longrightarrow> k (a x, x) = g x"
    by (simp add: B_def a1 h'_def keq)
  qed
qed


corollary\<^marker>\<open>tag unimportant\<close> nullhomotopic_into_ANR_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "closed S"
      and contf: "continuous_on S f"
      and "ANR T"
      and fim: "f ` S \<subseteq> T"
      and "S \<noteq> {}"
   shows "(\<exists>c. homotopic_with_canon (\<lambda>x. True) S T f (\<lambda>x. c)) \<longleftrightarrow>
          (\<exists>g. continuous_on UNIV g \<and> range g \<subseteq> T \<and> (\<forall>x \<in> S. g x = f x))"
       (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain c where c: "homotopic_with_canon (\<lambda>x. True) S T (\<lambda>x. c) f"
    by (blast intro: homotopic_with_symD)
  have "closedin (top_of_set UNIV) S"
    using \<open>closed S\<close> closed_closedin by fastforce
  then obtain g where "continuous_on UNIV g" "range g \<subseteq> T"
                      "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
  proof (rule Borsuk_homotopy_extension_homotopic)
    show "range (\<lambda>x. c) \<subseteq> T"
      using \<open>S \<noteq> {}\<close> c homotopic_with_imp_subset1 by fastforce
  qed (use assms c in auto)
  then show ?rhs by blast
next
  assume ?rhs
  then obtain g where "continuous_on UNIV g" "range g \<subseteq> T" "\<And>x. x\<in>S \<Longrightarrow> g x = f x"
    by blast
  then obtain c where "homotopic_with_canon (\<lambda>h. True) UNIV T g (\<lambda>x. c)"
    using nullhomotopic_from_contractible [of UNIV g T] contractible_UNIV by blast
  then have "homotopic_with_canon (\<lambda>x. True) S T g (\<lambda>x. c)"
    by (simp add: homotopic_from_subtopology)
  then show ?lhs
    by (force elim: homotopic_with_eq [of _ _ _ g "\<lambda>x. c"] simp: \<open>\<And>x. x \<in> S \<Longrightarrow> g x = f x\<close>)
qed

corollary\<^marker>\<open>tag unimportant\<close> nullhomotopic_into_rel_frontier_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "closed S"
      and contf: "continuous_on S f"
      and "convex T" "bounded T"
      and fim: "f ` S \<subseteq> rel_frontier T"
      and "S \<noteq> {}"
   shows "(\<exists>c. homotopic_with_canon (\<lambda>x. True) S (rel_frontier T) f (\<lambda>x. c)) \<longleftrightarrow>
          (\<exists>g. continuous_on UNIV g \<and> range g \<subseteq> rel_frontier T \<and> (\<forall>x \<in> S. g x = f x))"
by (simp add: nullhomotopic_into_ANR_extension assms ANR_rel_frontier_convex)

corollary\<^marker>\<open>tag unimportant\<close> nullhomotopic_into_sphere_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "closed S" and contf: "continuous_on S f"
      and "S \<noteq> {}" and fim: "f ` S \<subseteq> sphere a r"
    shows "((\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere a r) f (\<lambda>x. c)) \<longleftrightarrow>
           (\<exists>g. continuous_on UNIV g \<and> range g \<subseteq> sphere a r \<and> (\<forall>x \<in> S. g x = f x)))"
           (is "?lhs = ?rhs")
proof (cases "r = 0")
  case True with fim show ?thesis
    by (metis ANR_sphere \<open>closed S\<close> \<open>S \<noteq> {}\<close> contf nullhomotopic_into_ANR_extension)
next
  case False
  then have eq: "sphere a r = rel_frontier (cball a r)" by simp
  show ?thesis
    using fim nullhomotopic_into_rel_frontier_extension [OF \<open>closed S\<close> contf convex_cball bounded_cball]
    by (simp add: \<open>S \<noteq> {}\<close> eq)
qed

proposition\<^marker>\<open>tag unimportant\<close> Borsuk_map_essential_bounded_component:
  fixes a :: "'a :: euclidean_space"
  assumes "compact S" and "a \<notin> S"
   shows "bounded (connected_component_set (- S) a) \<longleftrightarrow>
          \<not>(\<exists>c. homotopic_with_canon (\<lambda>x. True) S (sphere 0 1)
                               (\<lambda>x. inverse(norm(x - a)) *\<^sub>R (x - a)) (\<lambda>x. c))"
   (is "?lhs = ?rhs")
proof (cases "S = {}")
  case True then show ?thesis
    by simp
next
  case False
  have "closed S" "bounded S"
    using \<open>compact S\<close> compact_eq_bounded_closed by auto
  have s01: "(\<lambda>x. (x - a) /\<^sub>R norm (x - a)) ` S \<subseteq> sphere 0 1"
    using \<open>a \<notin> S\<close>  by clarsimp (metis dist_eq_0_iff dist_norm mult.commute right_inverse)
  have aincc: "a \<in> connected_component_set (- S) a"
    by (simp add: \<open>a \<notin> S\<close>)
  obtain r where "r>0" and r: "S \<subseteq> ball 0 r"
    using bounded_subset_ballD \<open>bounded S\<close> by blast
  have "\<not> ?rhs \<longleftrightarrow> \<not> ?lhs"
  proof
    assume notr: "\<not> ?rhs"
    have nog: "\<nexists>g. continuous_on (S \<union> connected_component_set (- S) a) g \<and>
                   g ` (S \<union> connected_component_set (- S) a) \<subseteq> sphere 0 1 \<and>
                   (\<forall>x\<in>S. g x = (x - a) /\<^sub>R norm (x - a))"
      if "bounded (connected_component_set (- S) a)"
      using non_extensible_Borsuk_map [OF \<open>compact S\<close> componentsI _ aincc] \<open>a \<notin> S\<close> that by auto
    obtain g where "range g \<subseteq> sphere 0 1" "continuous_on UNIV g"
                        "\<And>x. x \<in> S \<Longrightarrow> g x = (x - a) /\<^sub>R norm (x - a)"
      using notr
      by (auto simp: nullhomotopic_into_sphere_extension
                 [OF \<open>closed S\<close> continuous_on_Borsuk_map [OF \<open>a \<notin> S\<close>] False s01])
    with \<open>a \<notin> S\<close> show  "\<not> ?lhs"
      by (metis UNIV_I continuous_on_subset image_subset_iff nog subsetI)
  next
    assume "\<not> ?lhs"
    then obtain b where b: "b \<in> connected_component_set (- S) a" and "r \<le> norm b"
      using bounded_iff linear by blast
    then have bnot: "b \<notin> ball 0 r"
      by simp
    have "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. (x - a) /\<^sub>R norm (x - a))
                                                         (\<lambda>x. (x - b) /\<^sub>R norm (x - b))"
    proof -
      have "path_component (- S) a b"
        by (metis (full_types) \<open>closed S\<close> b mem_Collect_eq open_Compl open_path_connected_component)
      then show ?thesis
        using Borsuk_maps_homotopic_in_path_component by blast
    qed
    moreover
    obtain c where "homotopic_with_canon (\<lambda>x. True) (ball 0 r) (sphere 0 1)
                                   (\<lambda>x. inverse (norm (x - b)) *\<^sub>R (x - b)) (\<lambda>x. c)"
    proof (rule nullhomotopic_from_contractible)
      show "contractible (ball (0::'a) r)"
        by (metis convex_imp_contractible convex_ball)
      show "continuous_on (ball 0 r) (\<lambda>x. inverse(norm (x - b)) *\<^sub>R (x - b))"
        by (rule continuous_on_Borsuk_map [OF bnot])
      show "(\<lambda>x. (x - b) /\<^sub>R norm (x - b)) ` ball 0 r \<subseteq> sphere 0 1"
        using bnot Borsuk_map_into_sphere by blast
    qed blast
    ultimately have "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. (x - a) /\<^sub>R norm (x - a)) (\<lambda>x. c)"
      by (meson homotopic_with_subset_left homotopic_with_trans r)
    then show "\<not> ?rhs"
      by blast
  qed
  then show ?thesis by blast
qed

lemma homotopic_Borsuk_maps_in_bounded_component:
  fixes a :: "'a :: euclidean_space"
  assumes "compact S" and "a \<notin> S"and "b \<notin> S"
      and boc: "bounded (connected_component_set (- S) a)"
      and hom: "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1)
                               (\<lambda>x. (x - a) /\<^sub>R norm (x - a))
                               (\<lambda>x. (x - b) /\<^sub>R norm (x - b))"
   shows "connected_component (- S) a b"
proof (rule ccontr)
  assume notcc: "\<not> connected_component (- S) a b"
  let ?T = "S \<union> connected_component_set (- S) a"
  have "\<nexists>g. continuous_on (S \<union> connected_component_set (- S) a) g \<and>
            g ` (S \<union> connected_component_set (- S) a) \<subseteq> sphere 0 1 \<and>
            (\<forall>x\<in>S. g x = (x - a) /\<^sub>R norm (x - a))"
    by (simp add: \<open>a \<notin> S\<close> componentsI non_extensible_Borsuk_map [OF \<open>compact S\<close> _ boc])
  moreover obtain g where "continuous_on (S \<union> connected_component_set (- S) a) g"
                          "g ` (S \<union> connected_component_set (- S) a) \<subseteq> sphere 0 1"
                          "\<And>x. x \<in> S \<Longrightarrow> g x = (x - a) /\<^sub>R norm (x - a)"
  proof (rule Borsuk_homotopy_extension_homotopic)
    show "closedin (top_of_set ?T) S"
      by (simp add: \<open>compact S\<close> closed_subset compact_imp_closed)
    show "continuous_on ?T (\<lambda>x. (x - b) /\<^sub>R norm (x - b))"
      by (simp add: \<open>b \<notin> S\<close> notcc continuous_on_Borsuk_map)
    show "(\<lambda>x. (x - b) /\<^sub>R norm (x - b)) ` ?T \<subseteq> sphere 0 1"
      by (simp add: \<open>b \<notin> S\<close> notcc Borsuk_map_into_sphere)
    show "homotopic_with_canon (\<lambda>x. True) S (sphere 0 1)
             (\<lambda>x. (x - b) /\<^sub>R norm (x - b)) (\<lambda>x. (x - a) /\<^sub>R norm (x - a))"
      by (simp add: hom homotopic_with_symD)
    qed (auto simp: ANR_sphere intro: that)
  ultimately show False by blast
qed


lemma Borsuk_maps_homotopic_in_connected_component_eq:
  fixes a :: "'a :: euclidean_space"
  assumes S: "compact S" "a \<notin> S" "b \<notin> S" and 2: "2 \<le> DIM('a)"
    shows "(homotopic_with_canon (\<lambda>x. True) S (sphere 0 1)
                   (\<lambda>x. (x - a) /\<^sub>R norm (x - a))
                   (\<lambda>x. (x - b) /\<^sub>R norm (x - b)) \<longleftrightarrow>
           connected_component (- S) a b)"
         (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof (cases "bounded(connected_component_set (- S) a)")
    case True
    show ?thesis
      by (rule homotopic_Borsuk_maps_in_bounded_component [OF S True L])
  next
    case not_bo_a: False
    show ?thesis
    proof (cases "bounded(connected_component_set (- S) b)")
      case True
      show ?thesis
        using homotopic_Borsuk_maps_in_bounded_component [OF S]
        by (simp add: L True assms connected_component_sym homotopic_Borsuk_maps_in_bounded_component homotopic_with_sym)
    next
      case False
      then show ?thesis
        using cobounded_unique_unbounded_component [of "-S" a b] \<open>compact S\<close> not_bo_a
        by (auto simp: compact_eq_bounded_closed assms connected_component_eq_eq)
    qed
  qed
next
  assume R: ?rhs
  then have "path_component (- S) a b"
    using assms(1) compact_eq_bounded_closed open_Compl open_path_connected_component_set by fastforce
  then show ?lhs
    by (simp add: Borsuk_maps_homotopic_in_path_component)
qed

subsection\<open>More extension theorems\<close>

lemma extension_from_clopen:
  assumes ope: "openin (top_of_set S) T"
      and clo: "closedin (top_of_set S) T"
      and contf: "continuous_on T f" and fim: "f ` T \<subseteq> U" and null: "U = {} \<Longrightarrow> S = {}"
 obtains g where "continuous_on S g" "g ` S \<subseteq> U" "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
proof (cases "U = {}")
  case True
  then show ?thesis
    by (simp add: null that)
next
  case False
  then obtain a where "a \<in> U"
    by auto
  let ?g = "\<lambda>x. if x \<in> T then f x else a"
  have Seq: "S = T \<union> (S - T)"
    using clo closedin_imp_subset by fastforce
  show ?thesis
  proof
    have "continuous_on (T \<union> (S - T)) ?g"
      using Seq clo ope  by (intro continuous_on_cases_local) (auto simp: contf)
    with Seq show "continuous_on S ?g"
      by metis
    show "?g ` S \<subseteq> U"
      using \<open>a \<in> U\<close> fim by auto
    show "\<And>x. x \<in> T \<Longrightarrow> ?g x = f x"
      by auto
  qed
qed


lemma extension_from_component:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes S: "locally connected S \<or> compact S" and "ANR U"
     and C: "C \<in> components S" and contf: "continuous_on C f" and fim: "f ` C \<subseteq> U"
 obtains g where "continuous_on S g" "g ` S \<subseteq> U" "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
proof -
  obtain T g where ope: "openin (top_of_set S) T"
               and clo: "closedin (top_of_set S) T"
               and "C \<subseteq> T" and contg: "continuous_on T g" and gim: "g ` T \<subseteq> U"
               and gf: "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
    using S
  proof
    assume "locally connected S"
    show ?thesis
      by (metis C \<open>locally connected S\<close> openin_components_locally_connected closedin_component contf fim order_refl that)
  next
    assume "compact S"
    then obtain W g where "C \<subseteq> W" and opeW: "openin (top_of_set S) W"
                 and contg: "continuous_on W g"
                 and gim: "g ` W \<subseteq> U" and gf: "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
      using ANR_imp_absolute_neighbourhood_extensor [of U C f S] C \<open>ANR U\<close> closedin_component contf fim by blast
    then obtain V where "open V" and V: "W = S \<inter> V"
      by (auto simp: openin_open)
    moreover have "locally compact S"
      by (simp add: \<open>compact S\<close> closed_imp_locally_compact compact_imp_closed)
    ultimately obtain K where opeK: "openin (top_of_set S) K" and "compact K" "C \<subseteq> K" "K \<subseteq> V"
      by (metis C Int_subset_iff \<open>C \<subseteq> W\<close> \<open>compact S\<close> compact_components Sura_Bura_clopen_subset)
    show ?thesis
    proof
      show "closedin (top_of_set S) K"
        by (meson \<open>compact K\<close> \<open>compact S\<close> closedin_compact_eq opeK openin_imp_subset)
      show "continuous_on K g"
        by (metis Int_subset_iff V \<open>K \<subseteq> V\<close> contg continuous_on_subset opeK openin_subtopology subset_eq)
      show "g ` K \<subseteq> U"
        using V \<open>K \<subseteq> V\<close> gim opeK openin_imp_subset by fastforce
    qed (use opeK gf \<open>C \<subseteq> K\<close> in auto)
  qed
  obtain h where "continuous_on S h" "h ` S \<subseteq> U" "\<And>x. x \<in> T \<Longrightarrow> h x = g x"
    using extension_from_clopen
    by (metis C bot.extremum_uniqueI clo contg gim fim image_is_empty in_components_nonempty ope)
  then show ?thesis
    by (metis \<open>C \<subseteq> T\<close> gf subset_eq that)
qed


lemma tube_lemma:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact S" and S: "S \<noteq> {}" "(\<lambda>x. (x,a)) ` S \<subseteq> U" 
      and ope: "openin (top_of_set (S \<times> T)) U"
  obtains V where "openin (top_of_set T) V" "a \<in> V" "S \<times> V \<subseteq> U"
proof -
  let ?W = "{y. \<exists>x. x \<in> S \<and> (x, y) \<in> (S \<times> T - U)}"
  have "U \<subseteq> S \<times> T" "closedin (top_of_set (S \<times> T)) (S \<times> T - U)"
    using ope by (auto simp: openin_closedin_eq)
  then have "closedin (top_of_set T) ?W"
    using \<open>compact S\<close> closedin_compact_projection by blast
  moreover have "a \<in> T - ?W"
    using \<open>U \<subseteq> S \<times> T\<close> S by auto
  moreover have "S \<times> (T - ?W) \<subseteq> U"
    by auto
  ultimately show ?thesis
    by (metis (no_types, lifting) Sigma_cong closedin_def that topspace_euclidean_subtopology)
qed

lemma tube_lemma_gen:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes "compact S" "S \<noteq> {}" "T \<subseteq> T'" "S \<times> T \<subseteq> U"
      and ope: "openin (top_of_set (S \<times> T')) U"
  obtains V where "openin (top_of_set T') V" "T \<subseteq> V" "S \<times> V \<subseteq> U"
proof -
  have "\<And>x. x \<in> T \<Longrightarrow> \<exists>V. openin (top_of_set T') V \<and> x \<in> V \<and> S \<times> V \<subseteq> U"
    using assms by (auto intro:  tube_lemma [OF \<open>compact S\<close>])
  then obtain F where F: "\<And>x. x \<in> T \<Longrightarrow> openin (top_of_set T') (F x) \<and> x \<in> F x \<and> S \<times> F x \<subseteq> U"
    by metis
  show ?thesis
  proof
    show "openin (top_of_set T') (\<Union>(F ` T))"
      using F by blast
    show "T \<subseteq> \<Union>(F ` T)"
      using F by blast
    show "S \<times> \<Union>(F ` T) \<subseteq> U"
      using F by auto
  qed
qed

proposition\<^marker>\<open>tag unimportant\<close> homotopic_neighbourhood_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and fim: "f ` S \<subseteq> U"
      and contg: "continuous_on S g" and gim: "g ` S \<subseteq> U"
      and clo: "closedin (top_of_set S) T"
      and "ANR U" and hom: "homotopic_with_canon (\<lambda>x. True) T U f g"
    obtains V where "T \<subseteq> V" "openin (top_of_set S) V"
                    "homotopic_with_canon (\<lambda>x. True) V U f g"
proof -
  have "T \<subseteq> S"
    using clo closedin_imp_subset by blast
  obtain h where conth: "continuous_on ({0..1::real} \<times> T) h"
             and him: "h ` ({0..1} \<times> T) \<subseteq> U"
             and h0: "\<And>x. h(0, x) = f x" and h1: "\<And>x. h(1, x) = g x"
    using hom by (auto simp: homotopic_with_def)
  define h' where "h' \<equiv> \<lambda>z. if fst z \<in> {0} then f(snd z)
                             else if fst z \<in> {1} then g(snd z)
                             else h z"
  let ?S0 = "{0::real} \<times> S" and ?S1 = "{1::real} \<times> S"
  have "continuous_on(?S0 \<union> (?S1 \<union> {0..1} \<times> T)) h'"
    unfolding h'_def
  proof (intro continuous_on_cases_local)
    show "closedin (top_of_set (?S0 \<union> (?S1 \<union> {0..1} \<times> T))) ?S0"
         "closedin (top_of_set (?S1 \<union> {0..1} \<times> T)) ?S1"
      using \<open>T \<subseteq> S\<close> by (force intro: closedin_Times closedin_subset_trans [of "{0..1} \<times> S"])+
    show "closedin (top_of_set (?S0 \<union> (?S1 \<union> {0..1} \<times> T))) (?S1 \<union> {0..1} \<times> T)"
         "closedin (top_of_set (?S1 \<union> {0..1} \<times> T)) ({0..1} \<times> T)"
      using \<open>T \<subseteq> S\<close> by (force intro: clo closedin_Times closedin_subset_trans [of "{0..1} \<times> S"])+
    show "continuous_on (?S0) (\<lambda>x. f (snd x))"
      by (intro continuous_intros continuous_on_compose2 [OF contf]) auto
    show "continuous_on (?S1) (\<lambda>x. g (snd x))"
      by (intro continuous_intros continuous_on_compose2 [OF contg]) auto
  qed (use h0 h1 conth in auto)
  then have "continuous_on ({0,1} \<times> S \<union> ({0..1} \<times> T)) h'"
    by (metis Sigma_Un_distrib1 Un_assoc insert_is_Un) 
  moreover have "h' ` ({0,1} \<times> S \<union> {0..1} \<times> T) \<subseteq> U"
    using fim gim him \<open>T \<subseteq> S\<close> unfolding h'_def by force
  moreover have "closedin (top_of_set ({0..1::real} \<times> S)) ({0,1} \<times> S \<union> {0..1::real} \<times> T)"
    by (intro closedin_Times closedin_Un clo) (simp_all add: closed_subset)
  ultimately
  obtain W k where W: "({0,1} \<times> S) \<union> ({0..1} \<times> T) \<subseteq> W"
               and opeW: "openin (top_of_set ({0..1} \<times> S)) W"
               and contk: "continuous_on W k"
               and kim: "k ` W \<subseteq> U"
               and kh': "\<And>x. x \<in> ({0,1} \<times> S) \<union> ({0..1} \<times> T) \<Longrightarrow> k x = h' x"
    by (metis ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR U\<close>, of "({0,1} \<times> S) \<union> ({0..1} \<times> T)" h' "{0..1} \<times> S"])
  obtain T' where opeT': "openin (top_of_set S) T'" 
              and "T \<subseteq> T'" and TW: "{0..1} \<times> T' \<subseteq> W"
    using tube_lemma_gen [of "{0..1::real}" T S W] W \<open>T \<subseteq> S\<close> opeW by auto
  moreover have "homotopic_with_canon (\<lambda>x. True) T' U f g"
  proof (simp add: homotopic_with, intro exI conjI)
    show "continuous_on ({0..1} \<times> T') k"
      using TW continuous_on_subset contk by auto
    show "k ` ({0..1} \<times> T') \<subseteq> U"
      using TW kim by fastforce
    have "T' \<subseteq> S"
      by (meson opeT' subsetD openin_imp_subset)
    then show "\<forall>x\<in>T'. k (0, x) = f x" "\<forall>x\<in>T'. k (1, x) = g x"
      by (auto simp: kh' h'_def)
  qed
  ultimately show ?thesis
    by (blast intro: that)
qed

text\<open> Homotopy on a union of closed-open sets.\<close>
proposition\<^marker>\<open>tag unimportant\<close> homotopic_on_clopen_Union:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> closedin (top_of_set (\<Union>\<F>)) S"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set (\<Union>\<F>)) S"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> homotopic_with_canon (\<lambda>x. True) S T f g"
  shows "homotopic_with_canon (\<lambda>x. True) (\<Union>\<F>) T f g"
proof -
  obtain \<V> where "\<V> \<subseteq> \<F>" "countable \<V>" and eqU: "\<Union>\<V> = \<Union>\<F>"
    using Lindelof_openin assms by blast
  show ?thesis
  proof (cases "\<V> = {}")
    case True
    then show ?thesis
      by (metis Union_empty eqU homotopic_with_canon_on_empty)
  next
    case False
    then obtain V :: "nat \<Rightarrow> 'a set" where V: "range V = \<V>"
      using range_from_nat_into \<open>countable \<V>\<close> by metis
    with \<open>\<V> \<subseteq> \<F>\<close> have clo: "\<And>n. closedin (top_of_set (\<Union>\<F>)) (V n)"
                  and ope: "\<And>n. openin (top_of_set (\<Union>\<F>)) (V n)"
                  and hom: "\<And>n. homotopic_with_canon (\<lambda>x. True) (V n) T f g"
      using assms by auto 
    then obtain h where conth: "\<And>n. continuous_on ({0..1::real} \<times> V n) (h n)"
                  and him: "\<And>n. h n ` ({0..1} \<times> V n) \<subseteq> T" 
                  and h0: "\<And>n. \<And>x. x \<in> V n \<Longrightarrow> h n (0, x) = f x" 
                  and h1: "\<And>n. \<And>x. x \<in> V n \<Longrightarrow> h n (1, x) = g x"
      by (simp add: homotopic_with) metis
    have wop: "b \<in> V x \<Longrightarrow> \<exists>k. b \<in> V k \<and> (\<forall>j<k. b \<notin> V j)" for b x
        using nat_less_induct [where P = "\<lambda>i. b \<notin> V i"] by meson
    obtain \<zeta> where cont: "continuous_on ({0..1} \<times> \<Union>(V ` UNIV)) \<zeta>"
              and eq: "\<And>x i. \<lbrakk>x \<in> {0..1} \<times> \<Union>(V ` UNIV) \<inter>
                                   {0..1} \<times> (V i - (\<Union>m<i. V m))\<rbrakk> \<Longrightarrow> \<zeta> x = h i x"
    proof (rule pasting_lemma_exists)
      let ?X = "top_of_set ({0..1::real} \<times> \<Union>(range V))"
      show "topspace ?X \<subseteq> (\<Union>i. {0..1::real} \<times> (V i - (\<Union>m<i. V m)))"
        by (force simp: Ball_def dest: wop)
      show "openin (top_of_set ({0..1} \<times> \<Union>(V ` UNIV))) 
                   ({0..1::real} \<times> (V i - (\<Union>m<i. V m)))" for i
      proof (intro openin_Times openin_subtopology_self openin_diff)
        show "openin (top_of_set (\<Union>(V ` UNIV))) (V i)"
          using ope V eqU by auto
        show "closedin (top_of_set (\<Union>(V ` UNIV))) (\<Union>m<i. V m)"
          using V clo eqU by (force intro: closedin_Union)
      qed
      show "continuous_map (subtopology ?X ({0..1} \<times> (V i - \<Union> (V ` {..<i})))) euclidean (h i)"  for i
        by (auto simp add: subtopology_subtopology intro!: continuous_on_subset [OF conth])
      show "\<And>i j x. x \<in> topspace ?X \<inter> {0..1} \<times> (V i - (\<Union>m<i. V m)) \<inter> {0..1} \<times> (V j - (\<Union>m<j. V m))
                    \<Longrightarrow> h i x = h j x"
        by clarsimp (metis lessThan_iff linorder_neqE_nat)
    qed auto
    show ?thesis
    proof (simp add: homotopic_with eqU [symmetric], intro exI conjI ballI)
      show "continuous_on ({0..1} \<times> \<Union>\<V>) \<zeta>"
        using V eqU by (blast intro!:  continuous_on_subset [OF cont])
      show "\<zeta>` ({0..1} \<times> \<Union>\<V>) \<subseteq> T"
      proof clarsimp
        fix t :: real and y :: "'a" and X :: "'a set"
        assume "y \<in> X" "X \<in> \<V>" and t: "0 \<le> t" "t \<le> 1"
        then obtain k where "y \<in> V k" and j: "\<forall>j<k. y \<notin> V j"
          by (metis image_iff V wop)
        with him t show "\<zeta>(t, y) \<in> T"
          by (subst eq) force+
      qed
      fix X y
      assume "X \<in> \<V>" "y \<in> X"
      then obtain k where "y \<in> V k" and j: "\<forall>j<k. y \<notin> V j"
        by (metis image_iff V wop)
      then show "\<zeta>(0, y) = f y" and "\<zeta>(1, y) = g y"
        by (subst eq [where i=k]; force simp: h0 h1)+ 
    qed
  qed
qed

lemma homotopic_on_components_eq:
  fixes S :: "'a :: euclidean_space set" and T :: "'b :: euclidean_space set"
  assumes S: "locally connected S \<or> compact S" and "ANR T"
  shows "homotopic_with_canon (\<lambda>x. True) S T f g \<longleftrightarrow>
         (continuous_on S f \<and> f ` S \<subseteq> T \<and> continuous_on S g \<and> g ` S \<subseteq> T) \<and>
         (\<forall>C \<in> components S. homotopic_with_canon (\<lambda>x. True) C T f g)"
    (is "?lhs \<longleftrightarrow> ?C \<and> ?rhs")
proof -
  have "continuous_on S f" "f ` S \<subseteq> T" "continuous_on S g" "g ` S \<subseteq> T" if ?lhs
    using homotopic_with_imp_continuous homotopic_with_imp_subset1 homotopic_with_imp_subset2 that by blast+
  moreover have "?lhs \<longleftrightarrow> ?rhs"
    if contf: "continuous_on S f" and fim: "f ` S \<subseteq> T" and contg: "continuous_on S g" and gim: "g ` S \<subseteq> T"
  proof
    assume ?lhs
    with that show ?rhs
      by (simp add: homotopic_with_subset_left in_components_subset)
  next
    assume R: ?rhs
    have "\<exists>U. C \<subseteq> U \<and> closedin (top_of_set S) U \<and>
              openin (top_of_set S) U \<and>
              homotopic_with_canon (\<lambda>x. True) U T f g" if C: "C \<in> components S" for C
    proof -
      have "C \<subseteq> S"
        by (simp add: in_components_subset that)
      show ?thesis
        using S
      proof
        assume "locally connected S"
        show ?thesis
        proof (intro exI conjI)
          show "closedin (top_of_set S) C"
            by (simp add: closedin_component that)
          show "openin (top_of_set S) C"
            by (simp add: \<open>locally connected S\<close> openin_components_locally_connected that)
          show "homotopic_with_canon (\<lambda>x. True) C T f g"
            by (simp add: R that)
        qed auto
      next
        assume "compact S"
        have hom: "homotopic_with_canon (\<lambda>x. True) C T f g"
          using R that by blast
        obtain U where "C \<subseteq> U" and opeU: "openin (top_of_set S) U"
                  and hom: "homotopic_with_canon (\<lambda>x. True) U T f g"
          using homotopic_neighbourhood_extension [OF contf fim contg gim _ \<open>ANR T\<close> hom]
            \<open>C \<in> components S\<close> closedin_component by blast
        then obtain V where "open V" and V: "U = S \<inter> V"
          by (auto simp: openin_open)
        moreover have "locally compact S"
          by (simp add: \<open>compact S\<close> closed_imp_locally_compact compact_imp_closed)
        ultimately obtain K where opeK: "openin (top_of_set S) K" and "compact K" "C \<subseteq> K" "K \<subseteq> V"
          by (metis C Int_subset_iff Sura_Bura_clopen_subset \<open>C \<subseteq> U\<close> \<open>compact S\<close> compact_components)
        show ?thesis
        proof (intro exI conjI)
          show "closedin (top_of_set S) K"
            by (meson \<open>compact K\<close> \<open>compact S\<close> closedin_compact_eq opeK openin_imp_subset)
          show "homotopic_with_canon (\<lambda>x. True) K T f g"
            using V \<open>K \<subseteq> V\<close> hom homotopic_with_subset_left opeK openin_imp_subset by fastforce
        qed (use opeK \<open>C \<subseteq> K\<close> in auto)
      qed
    qed
    then obtain \<phi> where \<phi>: "\<And>C. C \<in> components S \<Longrightarrow> C \<subseteq> \<phi> C"
                  and clo\<phi>: "\<And>C. C \<in> components S \<Longrightarrow> closedin (top_of_set S) (\<phi> C)"
                  and ope\<phi>: "\<And>C. C \<in> components S \<Longrightarrow> openin (top_of_set S) (\<phi> C)"
                  and hom\<phi>: "\<And>C. C \<in> components S \<Longrightarrow> homotopic_with_canon (\<lambda>x. True) (\<phi> C) T f g"
      by metis
    have Seq: "S = \<Union> (\<phi> ` components S)"
    proof
      show "S \<subseteq> \<Union> (\<phi> ` components S)"
        by (metis Sup_mono Union_components \<phi> imageI)
      show "\<Union> (\<phi> ` components S) \<subseteq> S"
        using ope\<phi> openin_imp_subset by fastforce
    qed
    show ?lhs
      apply (subst Seq)
      using Seq clo\<phi> ope\<phi> hom\<phi> by (intro homotopic_on_clopen_Union) auto
  qed
  ultimately show ?thesis by blast
qed


lemma cohomotopically_trivial_on_components:
  fixes S :: "'a :: euclidean_space set" and T :: "'b :: euclidean_space set"
  assumes S: "locally connected S \<or> compact S" and "ANR T"
  shows
   "(\<forall>f g. continuous_on S f \<longrightarrow> f ` S \<subseteq> T \<longrightarrow> continuous_on S g \<longrightarrow> g ` S \<subseteq> T \<longrightarrow>
           homotopic_with_canon (\<lambda>x. True) S T f g)
    \<longleftrightarrow>
    (\<forall>C\<in>components S.
        \<forall>f g. continuous_on C f \<longrightarrow> f ` C \<subseteq> T \<longrightarrow> continuous_on C g \<longrightarrow> g ` C \<subseteq> T \<longrightarrow>
              homotopic_with_canon (\<lambda>x. True) C T f g)"
     (is "?lhs = ?rhs")
proof
  assume L[rule_format]: ?lhs
  show ?rhs
  proof clarify
    fix C f g
    assume contf: "continuous_on C f" and fim: "f ` C \<subseteq> T"
       and contg: "continuous_on C g" and gim: "g ` C \<subseteq> T" and C: "C \<in> components S"
    obtain f' where contf': "continuous_on S f'" and f'im: "f' ` S \<subseteq> T" and f'f: "\<And>x. x \<in> C \<Longrightarrow> f' x = f x"
      using extension_from_component [OF S \<open>ANR T\<close> C contf fim] by metis
    obtain g' where contg': "continuous_on S g'" and g'im: "g' ` S \<subseteq> T" and g'g: "\<And>x. x \<in> C \<Longrightarrow> g' x = g x"
      using extension_from_component [OF S \<open>ANR T\<close> C contg gim] by metis
    have "homotopic_with_canon (\<lambda>x. True) C T f' g'"
      using L [OF contf' f'im contg' g'im] homotopic_with_subset_left C in_components_subset by fastforce
    then show "homotopic_with_canon (\<lambda>x. True) C T f g"
      using f'f g'g homotopic_with_eq by force
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
  proof clarify
    fix f g
    assume contf: "continuous_on S f" and fim: "f ` S \<subseteq> T"
      and contg: "continuous_on S g" and gim: "g ` S \<subseteq> T"
    moreover have "homotopic_with_canon (\<lambda>x. True) C T f g" if "C \<in> components S" for C
      using R [OF that]
      by (meson contf contg continuous_on_subset fim gim image_mono in_components_subset order.trans that)
    ultimately show "homotopic_with_canon (\<lambda>x. True) S T f g"
      by (subst homotopic_on_components_eq [OF S \<open>ANR T\<close>]) auto
  qed
qed

subsection\<open>The complement of a set and path-connectedness\<close>

text\<open>Complement in dimension N > 1 of set homeomorphic to any interval in
 any dimension is (path-)connected. This naively generalizes the argument
 in Ryuji Maehara's paper "The Jordan curve theorem via the Brouwer fixed point theorem",
American Mathematical Monthly 1984.\<close>

lemma unbounded_components_complement_absolute_retract:
  fixes S :: "'a::euclidean_space set"
  assumes C: "C \<in> components(- S)" and S: "compact S" "AR S"
    shows "\<not> bounded C"
proof -
  obtain y where y: "C = connected_component_set (- S) y" and "y \<notin> S"
    using C by (auto simp: components_def)
  have "open(- S)"
    using S by (simp add: closed_open compact_eq_bounded_closed)
  have "S retract_of UNIV"
    using S compact_AR by blast
  then obtain r where contr: "continuous_on UNIV r" and ontor: "range r \<subseteq> S"
                  and r: "\<And>x. x \<in> S \<Longrightarrow> r x = x"
    by (auto simp: retract_of_def retraction_def)
  show ?thesis
  proof
    assume "bounded C"
    have "connected_component_set (- S) y \<subseteq> S"
    proof (rule frontier_subset_retraction)
      show "bounded (connected_component_set (- S) y)"
        using \<open>bounded C\<close> y by blast
      show "frontier (connected_component_set (- S) y) \<subseteq> S"
        using C \<open>compact S\<close> compact_eq_bounded_closed frontier_of_components_closed_complement y by blast
      show "continuous_on (closure (connected_component_set (- S) y)) r"
        by (blast intro: continuous_on_subset [OF contr])
    qed (use ontor r in auto)
    with \<open>y \<notin> S\<close> show False by force
  qed
qed

lemma connected_complement_absolute_retract:
  fixes S :: "'a::euclidean_space set"
  assumes S: "compact S" "AR S" and 2: "2 \<le> DIM('a)"
    shows "connected(- S)"
proof -
  have "S retract_of UNIV"
    using S compact_AR by blast
  show ?thesis
  proof (clarsimp simp: connected_iff_connected_component_eq)
    have "\<not> bounded (connected_component_set (- S) x)" if "x \<notin> S" for x
      by (meson Compl_iff assms componentsI that unbounded_components_complement_absolute_retract)
    then show "connected_component_set (- S) x = connected_component_set (- S) y" 
      if "x \<notin> S" "y \<notin> S" for x y
      using cobounded_unique_unbounded_component [OF _ 2]
      by (metis \<open>compact S\<close> compact_imp_bounded double_compl that)
  qed
qed

lemma path_connected_complement_absolute_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "AR S" "2 \<le> DIM('a)"
    shows "path_connected(- S)"
  using connected_complement_absolute_retract [OF assms]
  using \<open>compact S\<close> compact_eq_bounded_closed connected_open_path_connected by blast

theorem connected_complement_homeomorphic_convex_compact:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes hom: "S homeomorphic T" and T: "convex T" "compact T" and 2: "2 \<le> DIM('a)"
    shows "connected(- S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: connected_UNIV)
next
  case False
  show ?thesis
  proof (rule connected_complement_absolute_retract)
    show "compact S"
      using \<open>compact T\<close> hom homeomorphic_compactness by auto
    show "AR S"
      by (meson AR_ANR False \<open>convex T\<close> convex_imp_ANR convex_imp_contractible hom homeomorphic_ANR_iff_ANR homeomorphic_contractible_eq)
  qed (rule 2)
qed

corollary path_connected_complement_homeomorphic_convex_compact:
  fixes S :: "'a::euclidean_space set" and T :: "'b::euclidean_space set"
  assumes hom: "S homeomorphic T" "convex T" "compact T" "2 \<le> DIM('a)"
    shows "path_connected(- S)"
  using connected_complement_homeomorphic_convex_compact [OF assms]
  using \<open>compact T\<close> compact_eq_bounded_closed connected_open_path_connected hom homeomorphic_compactness by blast

lemma path_connected_complement_homeomorphic_interval:
  fixes S :: "'a::euclidean_space set"
  assumes "S homeomorphic cbox a b" "2 \<le> DIM('a)"
  shows "path_connected(-S)"
  using assms compact_cbox convex_box(1) path_connected_complement_homeomorphic_convex_compact by blast

lemma connected_complement_homeomorphic_interval:
  fixes S :: "'a::euclidean_space set"
  assumes "S homeomorphic cbox a b" "2 \<le> DIM('a)"
  shows "connected(-S)"
  using assms path_connected_complement_homeomorphic_interval path_connected_imp_connected by blast

end
