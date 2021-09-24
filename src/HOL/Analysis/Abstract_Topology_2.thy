(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Abstract Topology 2\<close>

theory Abstract_Topology_2
  imports
    Elementary_Topology
    Abstract_Topology
    "HOL-Library.Indicator_Function"
begin

text \<open>Combination of Elementary and Abstract Topology\<close>

lemma approachable_lt_le2: 
    "(\<exists>(d::real) > 0. \<forall>x. Q x \<longrightarrow> f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> Q x \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI, auto)
  done

lemma triangle_lemma:
  fixes x y z :: real
  assumes x: "0 \<le> x"
    and y: "0 \<le> y"
    and z: "0 \<le> z"
    and xy: "x\<^sup>2 \<le> y\<^sup>2 + z\<^sup>2"
  shows "x \<le> y + z"
proof -
  have "y\<^sup>2 + z\<^sup>2 \<le> y\<^sup>2 + 2 * y * z + z\<^sup>2"
    using z y by simp
  with xy have th: "x\<^sup>2 \<le> (y + z)\<^sup>2"
    by (simp add: power2_eq_square field_simps)
  from y z have yz: "y + z \<ge> 0"
    by arith
  from power2_le_imp_le[OF th yz] show ?thesis .
qed

lemma isCont_indicator:
  fixes x :: "'a::t2_space"
  shows "isCont (indicator A :: 'a \<Rightarrow> real) x = (x \<notin> frontier A)"
proof auto
  fix x
  assume cts_at: "isCont (indicator A :: 'a \<Rightarrow> real) x" and fr: "x \<in> frontier A"
  with continuous_at_open have 1: "\<forall>V::real set. open V \<and> indicator A x \<in> V \<longrightarrow>
    (\<exists>U::'a set. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> V))" by auto
  show False
  proof (cases "x \<in> A")
    assume x: "x \<in> A"
    hence "indicator A x \<in> ({0<..<2} :: real set)" by simp
    with 1 obtain U where U: "open U" "x \<in> U" "\<forall>y\<in>U. indicator A y \<in> ({0<..<2} :: real set)"
      using open_greaterThanLessThan by metis
    hence "\<forall>y\<in>U. indicator A y > (0::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> A" using indicator_eq_0_iff by force
    hence "x \<in> interior A" using U interiorI by auto
    thus ?thesis using fr unfolding frontier_def by simp
  next
    assume x: "x \<notin> A"
    hence "indicator A x \<in> ({-1<..<1} :: real set)" by simp
    with 1 obtain U where U: "open U" "x \<in> U" "\<forall>y\<in>U. indicator A y \<in> ({-1<..<1} :: real set)"
      using 1 open_greaterThanLessThan by metis
    hence "\<forall>y\<in>U. indicator A y < (1::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> -A" by auto
    hence "x \<in> interior (-A)" using U interiorI by auto
    thus ?thesis using fr interior_complement unfolding frontier_def by auto
  qed
next
  assume nfr: "x \<notin> frontier A"
  hence "x \<in> interior A \<or> x \<in> interior (-A)"
    by (auto simp: frontier_def closure_interior)
  thus "isCont ((indicator A)::'a \<Rightarrow> real) x"
  proof
    assume int: "x \<in> interior A"
    then obtain U where U: "open U" "x \<in> U" "U \<subseteq> A" unfolding interior_def by auto
    hence "\<forall>y\<in>U. indicator A y = (1::real)" unfolding indicator_def by auto
    hence "continuous_on U (indicator A)" by (simp add: indicator_eq_1_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  next
    assume ext: "x \<in> interior (-A)"
    then obtain U where U: "open U" "x \<in> U" "U \<subseteq> -A" unfolding interior_def by auto
    then have "continuous_on U (indicator A)"
      using continuous_on_topological by (auto simp: subset_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  qed
qed

lemma closedin_limpt:
  "closedin (top_of_set T) S \<longleftrightarrow> S \<subseteq> T \<and> (\<forall>x. x islimpt S \<and> x \<in> T \<longrightarrow> x \<in> S)"
  apply (simp add: closedin_closed, safe)
   apply (simp add: closed_limpt islimpt_subset)
  apply (rule_tac x="closure S" in exI, simp)
  apply (force simp: closure_def)
  done

lemma closedin_closed_eq: "closed S \<Longrightarrow> closedin (top_of_set S) T \<longleftrightarrow> closed T \<and> T \<subseteq> S"
  by (meson closedin_limpt closed_subset closedin_closed_trans)

lemma connected_closed_set:
   "closed S
    \<Longrightarrow> connected S \<longleftrightarrow> (\<nexists>A B. closed A \<and> closed B \<and> A \<noteq> {} \<and> B \<noteq> {} \<and> A \<union> B = S \<and> A \<inter> B = {})"
  unfolding connected_closedin_eq closedin_closed_eq connected_closedin_eq by blast

text \<open>If a connnected set is written as the union of two nonempty closed sets, then these sets
have to intersect.\<close>

lemma connected_as_closed_union:
  assumes "connected C" "C = A \<union> B" "closed A" "closed B" "A \<noteq> {}" "B \<noteq> {}"
  shows "A \<inter> B \<noteq> {}"
by (metis assms closed_Un connected_closed_set)

lemma closedin_subset_trans:
  "closedin (top_of_set U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    closedin (top_of_set T) S"
  by (meson closedin_limpt subset_iff)

lemma openin_subset_trans:
  "openin (top_of_set U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    openin (top_of_set T) S"
  by (auto simp: openin_open)

lemma closedin_compact:
   "\<lbrakk>compact S; closedin (top_of_set S) T\<rbrakk> \<Longrightarrow> compact T"
by (metis closedin_closed compact_Int_closed)

lemma closedin_compact_eq:
  fixes S :: "'a::t2_space set"
  shows
   "compact S
         \<Longrightarrow> (closedin (top_of_set S) T \<longleftrightarrow>
              compact T \<and> T \<subseteq> S)"
by (metis closedin_imp_subset closedin_compact closed_subset compact_imp_closed)


subsection \<open>Closure\<close>

lemma euclidean_closure_of [simp]: "euclidean closure_of S = closure S"
  by (auto simp: closure_of_def closure_def islimpt_def)

lemma closure_openin_Int_closure:
  assumes ope: "openin (top_of_set U) S" and "T \<subseteq> U"
  shows "closure(S \<inter> closure T) = closure(S \<inter> T)"
proof
  obtain V where "open V" and S: "S = U \<inter> V"
    using ope using openin_open by metis
  show "closure (S \<inter> closure T) \<subseteq> closure (S \<inter> T)"
    proof (clarsimp simp: S)
      fix x
      assume  "x \<in> closure (U \<inter> V \<inter> closure T)"
      then have "V \<inter> closure T \<subseteq> A \<Longrightarrow> x \<in> closure A" for A
          by (metis closure_mono subsetD inf.coboundedI2 inf_assoc)
      then have "x \<in> closure (T \<inter> V)"
         by (metis \<open>open V\<close> closure_closure inf_commute open_Int_closure_subset)
      then show "x \<in> closure (U \<inter> V \<inter> T)"
        by (metis \<open>T \<subseteq> U\<close> inf.absorb_iff2 inf_assoc inf_commute)
    qed
next
  show "closure (S \<inter> T) \<subseteq> closure (S \<inter> closure T)"
    by (meson Int_mono closure_mono closure_subset order_refl)
qed

corollary infinite_openin:
  fixes S :: "'a :: t1_space set"
  shows "\<lbrakk>openin (top_of_set U) S; x \<in> S; x islimpt U\<rbrakk> \<Longrightarrow> infinite S"
  by (clarsimp simp add: openin_open islimpt_eq_acc_point inf_commute)

lemma closure_Int_ballI:
  assumes "\<And>U. \<lbrakk>openin (top_of_set S) U; U \<noteq> {}\<rbrakk> \<Longrightarrow> T \<inter> U \<noteq> {}"
  shows "S \<subseteq> closure T"
proof (clarsimp simp: closure_iff_nhds_not_empty)
  fix x and A and V
  assume "x \<in> S" "V \<subseteq> A" "open V" "x \<in> V" "T \<inter> A = {}"
  then have "openin (top_of_set S) (A \<inter> V \<inter> S)"
    by (auto simp: openin_open intro!: exI[where x="V"])
  moreover have "A \<inter> V \<inter> S \<noteq> {}" using \<open>x \<in> V\<close> \<open>V \<subseteq> A\<close> \<open>x \<in> S\<close>
    by auto
  ultimately have "T \<inter> (A \<inter> V \<inter> S) \<noteq> {}"
    by (rule assms)
  with \<open>T \<inter> A = {}\<close> show False by auto
qed


subsection \<open>Frontier\<close>

lemma euclidean_interior_of [simp]: "euclidean interior_of S = interior S"
  by (auto simp: interior_of_def interior_def)

lemma euclidean_frontier_of [simp]: "euclidean frontier_of S = frontier S"
  by (auto simp: frontier_of_def frontier_def)

lemma connected_Int_frontier:
     "\<lbrakk>connected s; s \<inter> t \<noteq> {}; s - t \<noteq> {}\<rbrakk> \<Longrightarrow> (s \<inter> frontier t \<noteq> {})"
  apply (simp add: frontier_interiors connected_openin, safe)
  apply (drule_tac x="s \<inter> interior t" in spec, safe)
   apply (drule_tac [2] x="s \<inter> interior (-t)" in spec)
   apply (auto simp: disjoint_eq_subset_Compl dest: interior_subset [THEN subsetD])
  done

subsection \<open>Compactness\<close>

lemma openin_delete:
  fixes a :: "'a :: t1_space"
  shows "openin (top_of_set u) s
         \<Longrightarrow> openin (top_of_set u) (s - {a})"
by (metis Int_Diff open_delete openin_open)

lemma compact_eq_openin_cover:
  "compact S \<longleftrightarrow>
    (\<forall>C. (\<forall>c\<in>C. openin (top_of_set S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"
proof safe
  fix C
  assume "compact S" and "\<forall>c\<in>C. openin (top_of_set S) c" and "S \<subseteq> \<Union>C"
  then have "\<forall>c\<in>{T. open T \<and> S \<inter> T \<in> C}. open c" and "S \<subseteq> \<Union>{T. open T \<and> S \<inter> T \<in> C}"
    unfolding openin_open by force+
  with \<open>compact S\<close> obtain D where "D \<subseteq> {T. open T \<and> S \<inter> T \<in> C}" and "finite D" and "S \<subseteq> \<Union>D"
    by (meson compactE)
  then have "image (\<lambda>T. S \<inter> T) D \<subseteq> C \<and> finite (image (\<lambda>T. S \<inter> T) D) \<and> S \<subseteq> \<Union>(image (\<lambda>T. S \<inter> T) D)"
    by auto
  then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
next
  assume 1: "\<forall>C. (\<forall>c\<in>C. openin (top_of_set S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
        (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D)"
  show "compact S"
  proof (rule compactI)
    fix C
    let ?C = "image (\<lambda>T. S \<inter> T) C"
    assume "\<forall>t\<in>C. open t" and "S \<subseteq> \<Union>C"
    then have "(\<forall>c\<in>?C. openin (top_of_set S) c) \<and> S \<subseteq> \<Union>?C"
      unfolding openin_open by auto
    with 1 obtain D where "D \<subseteq> ?C" and "finite D" and "S \<subseteq> \<Union>D"
      by metis
    let ?D = "inv_into C (\<lambda>T. S \<inter> T) ` D"
    have "?D \<subseteq> C \<and> finite ?D \<and> S \<subseteq> \<Union>?D"
    proof (intro conjI)
      from \<open>D \<subseteq> ?C\<close> show "?D \<subseteq> C"
        by (fast intro: inv_into_into)
      from \<open>finite D\<close> show "finite ?D"
        by (rule finite_imageI)
      from \<open>S \<subseteq> \<Union>D\<close> show "S \<subseteq> \<Union>?D"
        apply (rule subset_trans)
        by (metis Int_Union Int_lower2 \<open>D \<subseteq> (\<inter>) S ` C\<close> image_inv_into_cancel)
    qed
    then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
  qed
qed


subsection \<open>Continuity\<close>

lemma interior_image_subset:
  assumes "inj f" "\<And>x. continuous (at x) f"
  shows "interior (f ` S) \<subseteq> f ` (interior S)"
proof
  fix x assume "x \<in> interior (f ` S)"
  then obtain T where as: "open T" "x \<in> T" "T \<subseteq> f ` S" ..
  then have "x \<in> f ` S" by auto
  then obtain y where y: "y \<in> S" "x = f y" by auto
  have "open (f -` T)"
    using assms \<open>open T\<close> by (simp add: continuous_at_imp_continuous_on open_vimage)
  moreover have "y \<in> vimage f T"
    using \<open>x = f y\<close> \<open>x \<in> T\<close> by simp
  moreover have "vimage f T \<subseteq> S"
    using \<open>T \<subseteq> image f S\<close> \<open>inj f\<close> unfolding inj_on_def subset_eq by auto
  ultimately have "y \<in> interior S" ..
  with \<open>x = f y\<close> show "x \<in> f ` interior S" ..
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Equality of continuous functions on closure and related results\<close>

lemma continuous_closedin_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on S f \<Longrightarrow> closedin (top_of_set S) {x \<in> S. f x = a}"
  using continuous_closedin_preimage[of S f "{a}"] by (simp add: vimage_def Collect_conj_eq)

lemma continuous_closed_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on S f \<Longrightarrow> closed S \<Longrightarrow> closed {x \<in> S. f x = a}"
  using continuous_closed_preimage[of S f "{a}"] by (simp add: vimage_def Collect_conj_eq)

lemma continuous_constant_on_closure:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes "continuous_on (closure S) f"
      and "\<And>x. x \<in> S \<Longrightarrow> f x = a"
      and "x \<in> closure S"
  shows "f x = a"
    using continuous_closed_preimage_constant[of "closure S" f a]
      assms closure_minimal[of S "{x \<in> closure S. f x = a}"] closure_subset
    unfolding subset_eq
    by auto

lemma image_closure_subset:
  assumes contf: "continuous_on (closure S) f"
    and "closed T"
    and "(f ` S) \<subseteq> T"
  shows "f ` (closure S) \<subseteq> T"
proof -
  have "S \<subseteq> {x \<in> closure S. f x \<in> T}"
    using assms(3) closure_subset by auto
  moreover have "closed (closure S \<inter> f -` T)"
    using continuous_closed_preimage[OF contf] \<open>closed T\<close> by auto
  ultimately have "closure S = (closure S \<inter> f -` T)"
    using closure_minimal[of S "(closure S \<inter> f -` T)"] by auto
  then show ?thesis by auto
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>A function constant on a set\<close>

definition constant_on  (infixl "(constant'_on)" 50)
  where "f constant_on A \<equiv> \<exists>y. \<forall>x\<in>A. f x = y"

lemma constant_on_subset: "\<lbrakk>f constant_on A; B \<subseteq> A\<rbrakk> \<Longrightarrow> f constant_on B"
  unfolding constant_on_def by blast

lemma injective_not_constant:
  fixes S :: "'a::{perfect_space} set"
  shows "\<lbrakk>open S; inj_on f S; f constant_on S\<rbrakk> \<Longrightarrow> S = {}"
unfolding constant_on_def
by (metis equals0I inj_on_contraD islimpt_UNIV islimpt_def)

lemma constant_on_closureI:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes cof: "f constant_on S" and contf: "continuous_on (closure S) f"
    shows "f constant_on (closure S)"
using continuous_constant_on_closure [OF contf] cof unfolding constant_on_def
by metis


subsection\<^marker>\<open>tag unimportant\<close> \<open>Continuity relative to a union.\<close>

lemma continuous_on_Un_local:
    "\<lbrakk>closedin (top_of_set (s \<union> t)) s; closedin (top_of_set (s \<union> t)) t;
      continuous_on s f; continuous_on t f\<rbrakk>
     \<Longrightarrow> continuous_on (s \<union> t) f"
  unfolding continuous_on closedin_limpt
  by (metis Lim_trivial_limit Lim_within_union Un_iff trivial_limit_within)

lemma continuous_on_cases_local:
     "\<lbrakk>closedin (top_of_set (s \<union> t)) s; closedin (top_of_set (s \<union> t)) t;
       continuous_on s f; continuous_on t g;
       \<And>x. \<lbrakk>x \<in> s \<and> \<not>P x \<or> x \<in> t \<and> P x\<rbrakk> \<Longrightarrow> f x = g x\<rbrakk>
      \<Longrightarrow> continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)"
  by (rule continuous_on_Un_local) (auto intro: continuous_on_eq)

lemma continuous_on_cases_le:
  fixes h :: "'a :: topological_space \<Rightarrow> real"
  assumes "continuous_on {t \<in> s. h t \<le> a} f"
      and "continuous_on {t \<in> s. a \<le> h t} g"
      and h: "continuous_on s h"
      and "\<And>t. \<lbrakk>t \<in> s; h t = a\<rbrakk> \<Longrightarrow> f t = g t"
    shows "continuous_on s (\<lambda>t. if h t \<le> a then f(t) else g(t))"
proof -
  have s: "s = (s \<inter> h -` atMost a) \<union> (s \<inter> h -` atLeast a)"
    by force
  have 1: "closedin (top_of_set s) (s \<inter> h -` atMost a)"
    by (rule continuous_closedin_preimage [OF h closed_atMost])
  have 2: "closedin (top_of_set s) (s \<inter> h -` atLeast a)"
    by (rule continuous_closedin_preimage [OF h closed_atLeast])
  have eq: "s \<inter> h -` {..a} = {t \<in> s. h t \<le> a}" "s \<inter> h -` {a..} = {t \<in> s. a \<le> h t}"
    by auto
  show ?thesis
    apply (rule continuous_on_subset [of s, OF _ order_refl])
    apply (subst s)
    apply (rule continuous_on_cases_local)
    using 1 2 s assms apply (auto simp: eq)
    done
qed

lemma continuous_on_cases_1:
  fixes s :: "real set"
  assumes "continuous_on {t \<in> s. t \<le> a} f"
      and "continuous_on {t \<in> s. a \<le> t} g"
      and "a \<in> s \<Longrightarrow> f a = g a"
    shows "continuous_on s (\<lambda>t. if t \<le> a then f(t) else g(t))"
using assms
by (auto intro: continuous_on_cases_le [where h = id, simplified])


subsection\<^marker>\<open>tag unimportant\<close>\<open>Inverse function property for open/closed maps\<close>

lemma continuous_on_inverse_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and oo: "\<And>U. openin (top_of_set S) U \<Longrightarrow> openin (top_of_set T) (f ` U)"
  shows "continuous_on T g"
proof -
  from imf injf have gTS: "g ` T = S"
    by force
  from imf injf have fU: "U \<subseteq> S \<Longrightarrow> (f ` U) = T \<inter> g -` U" for U
    by force
  show ?thesis
    by (simp add: continuous_on_open [of T g] gTS) (metis openin_imp_subset fU oo)
qed

lemma continuous_on_inverse_closed_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    and oo: "\<And>U. closedin (top_of_set S) U \<Longrightarrow> closedin (top_of_set T) (f ` U)"
  shows "continuous_on T g"
proof -
  from imf injf have gTS: "g ` T = S"
    by force
  from imf injf have fU: "U \<subseteq> S \<Longrightarrow> (f ` U) = T \<inter> g -` U" for U
    by force
  show ?thesis
    by (simp add: continuous_on_closed [of T g] gTS) (metis closedin_imp_subset fU oo)
qed

lemma homeomorphism_injective_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "inj_on f S"
    and oo: "\<And>U. openin (top_of_set S) U \<Longrightarrow> openin (top_of_set T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_open_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_injective_closed_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "inj_on f S"
    and oo: "\<And>U. closedin (top_of_set S) U \<Longrightarrow> closedin (top_of_set T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_closed_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_imp_open_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "openin (top_of_set S) U"
  shows "openin (top_of_set T) (f ` U)"
proof -
  from hom oo have [simp]: "f ` U = T \<inter> g -` U"
    using openin_subset by (fastforce simp: homeomorphism_def rev_image_eqI)
  from hom have "continuous_on T g"
    unfolding homeomorphism_def by blast
  moreover have "g ` T = S"
    by (metis hom homeomorphism_def)
  ultimately show ?thesis
    by (simp add: continuous_on_open oo)
qed

lemma homeomorphism_imp_closed_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "closedin (top_of_set S) U"
  shows "closedin (top_of_set T) (f ` U)"
proof -
  from hom oo have [simp]: "f ` U = T \<inter> g -` U"
    using closedin_subset by (fastforce simp: homeomorphism_def rev_image_eqI)
  from hom have "continuous_on T g"
    unfolding homeomorphism_def by blast
  moreover have "g ` T = S"
    by (metis hom homeomorphism_def)
  ultimately show ?thesis
    by (simp add: continuous_on_closed oo)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>Seperability\<close>

lemma subset_second_countable:
  obtains \<B> :: "'a:: second_countable_topology set set"
    where "countable \<B>"
          "{} \<notin> \<B>"
          "\<And>C. C \<in> \<B> \<Longrightarrow> openin(top_of_set S) C"
          "\<And>T. openin(top_of_set S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>"
      and opeB: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(top_of_set S) C"
      and \<B>:    "\<And>T. openin(top_of_set S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
  proof -
    obtain \<C> :: "'a set set"
      where "countable \<C>" and ope: "\<And>C. C \<in> \<C> \<Longrightarrow> open C"
        and \<C>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<C> \<and> S = \<Union>U"
      by (metis univ_second_countable that)
    show ?thesis
    proof
      show "countable ((\<lambda>C. S \<inter> C) ` \<C>)"
        by (simp add: \<open>countable \<C>\<close>)
      show "\<And>C. C \<in> (\<inter>) S ` \<C> \<Longrightarrow> openin (top_of_set S) C"
        using ope by auto
      show "\<And>T. openin (top_of_set S) T \<Longrightarrow> \<exists>\<U>\<subseteq>(\<inter>) S ` \<C>. T = \<Union>\<U>"
        by (metis \<C> image_mono inf_Sup openin_open)
    qed
  qed
  show ?thesis
  proof
    show "countable (\<B> - {{}})"
      using \<open>countable \<B>\<close> by blast
    show "\<And>C. \<lbrakk>C \<in> \<B> - {{}}\<rbrakk> \<Longrightarrow> openin (top_of_set S) C"
      by (simp add: \<open>\<And>C. C \<in> \<B> \<Longrightarrow> openin (top_of_set S) C\<close>)
    show "\<exists>\<U>\<subseteq>\<B> - {{}}. T = \<Union>\<U>" if "openin (top_of_set S) T" for T
      using \<B> [OF that]
      apply clarify
      apply (rule_tac x="\<U> - {{}}" in exI, auto)
        done
  qed auto
qed

lemma Lindelof_openin:
  fixes \<F> :: "'a::second_countable_topology set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> openin (top_of_set U) S"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
proof -
  have "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>T. open T \<and> S = U \<inter> T"
    using assms by (simp add: openin_open)
  then obtain tf where tf: "\<And>S. S \<in> \<F> \<Longrightarrow> open (tf S) \<and> (S = U \<inter> tf S)"
    by metis
  have [simp]: "\<And>\<F>'. \<F>' \<subseteq> \<F> \<Longrightarrow> \<Union>\<F>' = U \<inter> \<Union>(tf ` \<F>')"
    using tf by fastforce
  obtain \<G> where "countable \<G> \<and> \<G> \<subseteq> tf ` \<F>" "\<Union>\<G> = \<Union>(tf ` \<F>)"
    using tf by (force intro: Lindelof [of "tf ` \<F>"])
  then obtain \<F>' where \<F>': "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
    by (clarsimp simp add: countable_subset_image)
  then show ?thesis ..
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Closed Maps\<close>

lemma continuous_imp_closed_map:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::t2_space"
  assumes "closedin (top_of_set S) U"
          "continuous_on S f" "f ` S = T" "compact S"
    shows "closedin (top_of_set T) (f ` U)"
  by (metis assms closedin_compact_eq compact_continuous_image continuous_on_subset subset_image_iff)

lemma closed_map_restrict:
  assumes cloU: "closedin (top_of_set (S \<inter> f -` T')) U"
    and cc: "\<And>U. closedin (top_of_set S) U \<Longrightarrow> closedin (top_of_set T) (f ` U)"
    and "T' \<subseteq> T"
  shows "closedin (top_of_set T') (f ` U)"
proof -
  obtain V where "closed V" "U = S \<inter> f -` T' \<inter> V"
    using cloU by (auto simp: closedin_closed)
  with cc [of "S \<inter> V"] \<open>T' \<subseteq> T\<close> show ?thesis
    by (fastforce simp add: closedin_closed)
qed

subsection\<^marker>\<open>tag unimportant\<close>\<open>Open Maps\<close>

lemma open_map_restrict:
  assumes opeU: "openin (top_of_set (S \<inter> f -` T')) U"
    and oo: "\<And>U. openin (top_of_set S) U \<Longrightarrow> openin (top_of_set T) (f ` U)"
    and "T' \<subseteq> T"
  shows "openin (top_of_set T') (f ` U)"
proof -
  obtain V where "open V" "U = S \<inter> f -` T' \<inter> V"
    using opeU by (auto simp: openin_open)
  with oo [of "S \<inter> V"] \<open>T' \<subseteq> T\<close> show ?thesis
    by (fastforce simp add: openin_open)
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Quotient maps\<close>

lemma quotient_map_imp_continuous_open:
  assumes T: "f ` S \<subseteq> T"
      and ope: "\<And>U. U \<subseteq> T
              \<Longrightarrow> (openin (top_of_set S) (S \<inter> f -` U) \<longleftrightarrow>
                   openin (top_of_set T) U)"
    shows "continuous_on S f"
proof -
  have [simp]: "S \<inter> f -` f ` S = S" by auto
  show ?thesis
    by (meson T continuous_on_open_gen ope openin_imp_subset)
qed

lemma quotient_map_imp_continuous_closed:
  assumes T: "f ` S \<subseteq> T"
      and ope: "\<And>U. U \<subseteq> T
                  \<Longrightarrow> (closedin (top_of_set S) (S \<inter> f -` U) \<longleftrightarrow>
                       closedin (top_of_set T) U)"
    shows "continuous_on S f"
proof -
  have [simp]: "S \<inter> f -` f ` S = S" by auto
  show ?thesis
    by (meson T closedin_imp_subset continuous_on_closed_gen ope)
qed

lemma open_map_imp_quotient_map:
  assumes contf: "continuous_on S f"
      and T: "T \<subseteq> f ` S"
      and ope: "\<And>T. openin (top_of_set S) T
                   \<Longrightarrow> openin (top_of_set (f ` S)) (f ` T)"
    shows "openin (top_of_set S) (S \<inter> f -` T) =
           openin (top_of_set (f ` S)) T"
proof -
  have "T = f ` (S \<inter> f -` T)"
    using T by blast
  then show ?thesis
    using "ope" contf continuous_on_open by metis
qed

lemma closed_map_imp_quotient_map:
  assumes contf: "continuous_on S f"
      and T: "T \<subseteq> f ` S"
      and ope: "\<And>T. closedin (top_of_set S) T
              \<Longrightarrow> closedin (top_of_set (f ` S)) (f ` T)"
    shows "openin (top_of_set S) (S \<inter> f -` T) \<longleftrightarrow>
           openin (top_of_set (f ` S)) T"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have *: "closedin (top_of_set S) (S - (S \<inter> f -` T))"
    using closedin_diff by fastforce
  have [simp]: "(f ` S - f ` (S - (S \<inter> f -` T))) = T"
    using T by blast
  show ?rhs
    using ope [OF *, unfolded closedin_def] by auto
next
  assume ?rhs
  with contf show ?lhs
    by (auto simp: continuous_on_open)
qed

lemma continuous_right_inverse_imp_quotient_map:
  assumes contf: "continuous_on S f" and imf: "f ` S \<subseteq> T"
      and contg: "continuous_on T g" and img: "g ` T \<subseteq> S"
      and fg [simp]: "\<And>y. y \<in> T \<Longrightarrow> f(g y) = y"
      and U: "U \<subseteq> T"
    shows "openin (top_of_set S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (top_of_set T) U"
          (is "?lhs = ?rhs")
proof -
  have f: "\<And>Z. openin (top_of_set (f ` S)) Z \<Longrightarrow>
                openin (top_of_set S) (S \<inter> f -` Z)"
  and  g: "\<And>Z. openin (top_of_set (g ` T)) Z \<Longrightarrow>
                openin (top_of_set T) (T \<inter> g -` Z)"
    using contf contg by (auto simp: continuous_on_open)
  show ?thesis
  proof
    have "T \<inter> g -` (g ` T \<inter> (S \<inter> f -` U)) = {x \<in> T. f (g x) \<in> U}"
      using imf img by blast
    also have "... = U"
      using U by auto
    finally have eq: "T \<inter> g -` (g ` T \<inter> (S \<inter> f -` U)) = U" .
    assume ?lhs
    then have *: "openin (top_of_set (g ` T)) (g ` T \<inter> (S \<inter> f -` U))"
      by (meson img openin_Int openin_subtopology_Int_subset openin_subtopology_self)
    show ?rhs
      using g [OF *] eq by auto
  next
    assume rhs: ?rhs
    show ?lhs
      by (metis f fg image_eqI image_subset_iff imf img openin_subopen openin_subtopology_self openin_trans rhs)
  qed
qed

lemma continuous_left_inverse_imp_quotient_map:
  assumes "continuous_on S f"
      and "continuous_on (f ` S) g"
      and  "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
      and "U \<subseteq> f ` S"
    shows "openin (top_of_set S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (top_of_set (f ` S)) U"
apply (rule continuous_right_inverse_imp_quotient_map)
using assms apply force+
done

lemma continuous_imp_quotient_map:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::t2_space"
  assumes "continuous_on S f" "f ` S = T" "compact S" "U \<subseteq> T"
    shows "openin (top_of_set S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (top_of_set T) U"
  by (metis (no_types, lifting) assms closed_map_imp_quotient_map continuous_imp_closed_map)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Pasting lemmas for functions, for of casewise definitions\<close>

subsubsection\<open>on open sets\<close>

lemma pasting_lemma:
  assumes ope: "\<And>i. i \<in> I \<Longrightarrow> openin X (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_map(subtopology X (T i)) Y (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> topspace X \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_map X Y g"
  unfolding continuous_map_openin_preimage_eq
proof (intro conjI allI impI)
  show "g ` topspace X \<subseteq> topspace Y"
    using g cont continuous_map_image_subset_topspace by fastforce
next
  fix U
  assume Y: "openin Y U"
  have T: "T i \<subseteq> topspace X" if "i \<in> I" for i
    using ope by (simp add: openin_subset that)
  have *: "topspace X \<inter> g -` U = (\<Union>i \<in> I. T i \<inter> f i -` U)"
    using f g T by fastforce
  have "\<And>i. i \<in> I \<Longrightarrow> openin X (T i \<inter> f i -` U)"
    using cont unfolding continuous_map_openin_preimage_eq
    by (metis Y T inf.commute inf_absorb1 ope topspace_subtopology openin_trans_full)
  then show "openin X (topspace X \<inter> g -` U)"
    by (auto simp: *)
qed

lemma pasting_lemma_exists:
  assumes X: "topspace X \<subseteq> (\<Union>i \<in> I. T i)"
      and ope: "\<And>i. i \<in> I \<Longrightarrow> openin X (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_map (subtopology X (T i)) Y (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> topspace X \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_map X Y g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> topspace X \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  let ?h = "\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x"
  show "continuous_map X Y ?h"
    apply (rule pasting_lemma [OF ope cont])
     apply (blast intro: f)+
    by (metis (no_types, lifting) UN_E X subsetD someI_ex)
  show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x" if "i \<in> I" "x \<in> topspace X \<inter> T i" for i x
    by (metis (no_types, lifting) IntD2 IntI f someI_ex that)
qed

lemma pasting_lemma_locally_finite:
  assumes fin: "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>V. openin X V \<and> x \<in> V \<and> finite {i \<in> I. T i \<inter> V \<noteq> {}}"
    and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin X (T i)"
    and cont:  "\<And>i. i \<in> I \<Longrightarrow> continuous_map(subtopology X (T i)) Y (f i)"
    and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> topspace X \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    and g: "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
  shows "continuous_map X Y g"
  unfolding continuous_map_closedin_preimage_eq
proof (intro conjI allI impI)
  show "g ` topspace X \<subseteq> topspace Y"
    using g cont continuous_map_image_subset_topspace by fastforce
next
  fix U
  assume Y: "closedin Y U"
  have T: "T i \<subseteq> topspace X" if "i \<in> I" for i
    using clo by (simp add: closedin_subset that)
  have *: "topspace X \<inter> g -` U = (\<Union>i \<in> I. T i \<inter> f i -` U)"
    using f g T by fastforce
  have cTf: "\<And>i. i \<in> I \<Longrightarrow> closedin X (T i \<inter> f i -` U)"
    using cont unfolding continuous_map_closedin_preimage_eq topspace_subtopology
    by (simp add: Int_absorb1 T Y clo closedin_closed_subtopology)
  have sub: "{Z \<in> (\<lambda>i. T i \<inter> f i -` U) ` I. Z \<inter> V \<noteq> {}}
           \<subseteq> (\<lambda>i. T i \<inter> f i -` U) ` {i \<in> I. T i \<inter> V \<noteq> {}}" for V
    by auto
  have 1: "(\<Union>i\<in>I. T i \<inter> f i -` U) \<subseteq> topspace X"
    using T by blast
  then have lf: "locally_finite_in X ((\<lambda>i. T i \<inter> f i -` U) ` I)"
    unfolding locally_finite_in_def
    using finite_subset [OF sub] fin by force
  show "closedin X (topspace X \<inter> g -` U)"
    apply (subst *)
    apply (rule closedin_locally_finite_Union)
     apply (auto intro: cTf lf)
    done
qed

subsubsection\<open>Likewise on closed sets, with a finiteness assumption\<close>

lemma pasting_lemma_closed:
  assumes fin: "finite I"
    and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin X (T i)"
    and cont:  "\<And>i. i \<in> I \<Longrightarrow> continuous_map(subtopology X (T i)) Y (f i)"
    and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> topspace X \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    and g: "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
  shows "continuous_map X Y g"
  using pasting_lemma_locally_finite [OF _ clo cont f g] fin by auto

lemma pasting_lemma_exists_locally_finite:
  assumes fin: "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>V. openin X V \<and> x \<in> V \<and> finite {i \<in> I. T i \<inter> V \<noteq> {}}"
    and X: "topspace X \<subseteq> \<Union>(T ` I)"
    and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin X (T i)"
    and cont:  "\<And>i. i \<in> I \<Longrightarrow> continuous_map(subtopology X (T i)) Y (f i)"
    and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> topspace X \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    and g: "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
  obtains g where "continuous_map X Y g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> topspace X \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_map X Y (\<lambda>x. f(@i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma_locally_finite [OF fin])
        apply (blast intro: assms)+
    by (metis (no_types, lifting) UN_E X set_rev_mp someI_ex)
next
  fix x i
  assume "i \<in> I" and "x \<in> topspace X \<inter> T i"
  show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    apply (rule someI2_ex)
    using \<open>i \<in> I\<close> \<open>x \<in> topspace X \<inter> T i\<close> apply blast
    by (meson Int_iff \<open>i \<in> I\<close> \<open>x \<in> topspace X \<inter> T i\<close> f)
qed

lemma pasting_lemma_exists_closed:
  assumes fin: "finite I"
    and X: "topspace X \<subseteq> \<Union>(T ` I)"
    and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin X (T i)"
    and cont:  "\<And>i. i \<in> I \<Longrightarrow> continuous_map(subtopology X (T i)) Y (f i)"
    and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> topspace X \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
  obtains g where "continuous_map X Y g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> topspace X \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_map X Y (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma_closed [OF \<open>finite I\<close> clo cont])
     apply (blast intro: f)+
    by (metis (mono_tags, lifting) UN_iff X someI_ex subset_iff)
next
  fix x i
  assume "i \<in> I" "x \<in> topspace X \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed

lemma continuous_map_cases:
  assumes f: "continuous_map (subtopology X (X closure_of {x. P x})) Y f"
      and g: "continuous_map (subtopology X (X closure_of {x. \<not> P x})) Y g"
      and fg: "\<And>x. x \<in> X frontier_of {x. P x} \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if P x then f x else g x)"
proof (rule pasting_lemma_closed)
  let ?f = "\<lambda>b. if b then f else g"
  let ?g = "\<lambda>x. if P x then f x else g x"
  let ?T = "\<lambda>b. if b then X closure_of {x. P x} else X closure_of {x. ~P x}"
  show "finite {True,False}" by auto
  have eq: "topspace X - Collect P = topspace X \<inter> {x. \<not> P x}"
    by blast
  show "?f i x = ?f j x"
    if "i \<in> {True,False}" "j \<in> {True,False}" and x: "x \<in> topspace X \<inter> ?T i \<inter> ?T j" for i j x
  proof -
    have "f x = g x"
      if "i" "\<not> j"
      apply (rule fg)
      unfolding frontier_of_closures eq
      using x that closure_of_restrict by fastforce
    moreover
    have "g x = f x"
      if "x \<in> X closure_of {x. \<not> P x}" "x \<in> X closure_of Collect P" "\<not> i" "j" for x
        apply (rule fg [symmetric])
        unfolding frontier_of_closures eq
        using x that closure_of_restrict by fastforce
    ultimately show ?thesis
      using that by (auto simp flip: closure_of_restrict)
  qed
  show "\<exists>j. j \<in> {True,False} \<and> x \<in> ?T j \<and> (if P x then f x else g x) = ?f j x"
    if "x \<in> topspace X" for x
    apply simp
    apply safe
    apply (metis Int_iff closure_of inf_sup_absorb mem_Collect_eq that)
    by (metis DiffI eq closure_of_subset_Int contra_subsetD mem_Collect_eq that)
qed (auto simp: f g)

lemma continuous_map_cases_alt:
  assumes f: "continuous_map (subtopology X (X closure_of {x \<in> topspace X. P x})) Y f"
      and g: "continuous_map (subtopology X (X closure_of {x \<in> topspace X. ~P x})) Y g"
      and fg: "\<And>x. x \<in> X frontier_of {x \<in> topspace X. P x} \<Longrightarrow> f x = g x"
    shows "continuous_map X Y (\<lambda>x. if P x then f x else g x)"
  apply (rule continuous_map_cases)
  using assms
    apply (simp_all add: Collect_conj_eq closure_of_restrict [symmetric] frontier_of_restrict [symmetric])
  done

lemma continuous_map_cases_function:
  assumes contp: "continuous_map X Z p"
    and contf: "continuous_map (subtopology X {x \<in> topspace X. p x \<in> Z closure_of U}) Y f"
    and contg: "continuous_map (subtopology X {x \<in> topspace X. p x \<in> Z closure_of (topspace Z - U)}) Y g"
    and fg: "\<And>x. \<lbrakk>x \<in> topspace X; p x \<in> Z frontier_of U\<rbrakk> \<Longrightarrow> f x = g x"
  shows "continuous_map X Y (\<lambda>x. if p x \<in> U then f x else g x)"
proof (rule continuous_map_cases_alt)
  show "continuous_map (subtopology X (X closure_of {x \<in> topspace X. p x \<in> U})) Y f"
  proof (rule continuous_map_from_subtopology_mono)
    let ?T = "{x \<in> topspace X. p x \<in> Z closure_of U}"
    show "continuous_map (subtopology X ?T) Y f"
      by (simp add: contf)
    show "X closure_of {x \<in> topspace X. p x \<in> U} \<subseteq> ?T"
      by (rule continuous_map_closure_preimage_subset [OF contp])
  qed
  show "continuous_map (subtopology X (X closure_of {x \<in> topspace X. p x \<notin> U})) Y g"
  proof (rule continuous_map_from_subtopology_mono)
    let ?T = "{x \<in> topspace X. p x \<in> Z closure_of (topspace Z - U)}"
    show "continuous_map (subtopology X ?T) Y g"
      by (simp add: contg)
    have "X closure_of {x \<in> topspace X. p x \<notin> U} \<subseteq> X closure_of {x \<in> topspace X. p x \<in> topspace Z - U}"
      apply (rule closure_of_mono)
      using continuous_map_closedin contp by fastforce
    then show "X closure_of {x \<in> topspace X. p x \<notin> U} \<subseteq> ?T"
      by (rule order_trans [OF _ continuous_map_closure_preimage_subset [OF contp]])
  qed
next
  show "f x = g x" if "x \<in> X frontier_of {x \<in> topspace X. p x \<in> U}" for x
    using that continuous_map_frontier_frontier_preimage_subset [OF contp, of U] fg by blast
qed

subsection \<open>Retractions\<close>

definition\<^marker>\<open>tag important\<close> retraction :: "('a::topological_space) set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where "retraction S T r \<longleftrightarrow>
  T \<subseteq> S \<and> continuous_on S r \<and> r ` S \<subseteq> T \<and> (\<forall>x\<in>T. r x = x)"

definition\<^marker>\<open>tag important\<close> retract_of (infixl "retract'_of" 50) where
"T retract_of S  \<longleftrightarrow>  (\<exists>r. retraction S T r)"

lemma retraction_idempotent: "retraction S T r \<Longrightarrow> x \<in> S \<Longrightarrow>  r (r x) = r x"
  unfolding retraction_def by auto

text \<open>Preservation of fixpoints under (more general notion of) retraction\<close>

lemma invertible_fixpoint_property:
  fixes S :: "'a::topological_space set"
    and T :: "'b::topological_space set"
  assumes contt: "continuous_on T i"
    and "i ` T \<subseteq> S"
    and contr: "continuous_on S r"
    and "r ` S \<subseteq> T"
    and ri: "\<And>y. y \<in> T \<Longrightarrow> r (i y) = y"
    and FP: "\<And>f. \<lbrakk>continuous_on S f; f ` S \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>x\<in>S. f x = x"
    and contg: "continuous_on T g"
    and "g ` T \<subseteq> T"
  obtains y where "y \<in> T" and "g y = y"
proof -
  have "\<exists>x\<in>S. (i \<circ> g \<circ> r) x = x"
  proof (rule FP)
    show "continuous_on S (i \<circ> g \<circ> r)"
      by (meson contt contr assms(4) contg assms(8) continuous_on_compose continuous_on_subset)
    show "(i \<circ> g \<circ> r) ` S \<subseteq> S"
      using assms(2,4,8) by force
  qed
  then obtain x where x: "x \<in> S" "(i \<circ> g \<circ> r) x = x" ..
  then have *: "g (r x) \<in> T"
    using assms(4,8) by auto
  have "r ((i \<circ> g \<circ> r) x) = r x"
    using x by auto
  then show ?thesis
    using "*" ri that by auto
qed

lemma homeomorphic_fixpoint_property:
  fixes S :: "'a::topological_space set"
    and T :: "'b::topological_space set"
  assumes "S homeomorphic T"
  shows "(\<forall>f. continuous_on S f \<and> f ` S \<subseteq> S \<longrightarrow> (\<exists>x\<in>S. f x = x)) \<longleftrightarrow>
         (\<forall>g. continuous_on T g \<and> g ` T \<subseteq> T \<longrightarrow> (\<exists>y\<in>T. g y = y))"
         (is "?lhs = ?rhs")
proof -
  obtain r i where r:
      "\<forall>x\<in>S. i (r x) = x" "r ` S = T" "continuous_on S r"
      "\<forall>y\<in>T. r (i y) = y" "i ` T = S" "continuous_on T i"
    using assms unfolding homeomorphic_def homeomorphism_def  by blast
  show ?thesis
  proof
    assume ?lhs
    with r show ?rhs
      by (metis invertible_fixpoint_property[of T i S r] order_refl)
  next
    assume ?rhs
    with r show ?lhs
      by (metis invertible_fixpoint_property[of S r T i] order_refl)
  qed
qed

lemma retract_fixpoint_property:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
    and S :: "'a set"
  assumes "T retract_of S"
    and FP: "\<And>f. \<lbrakk>continuous_on S f; f ` S \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>x\<in>S. f x = x"
    and contg: "continuous_on T g"
    and "g ` T \<subseteq> T"
  obtains y where "y \<in> T" and "g y = y"
proof -
  obtain h where "retraction S T h"
    using assms(1) unfolding retract_of_def ..
  then show ?thesis
    unfolding retraction_def
    using invertible_fixpoint_property[OF continuous_on_id _ _ _ _ FP]
    by (metis assms(4) contg image_ident that)
qed

lemma retraction:
  "retraction S T r \<longleftrightarrow>
    T \<subseteq> S \<and> continuous_on S r \<and> r ` S = T \<and> (\<forall>x \<in> T. r x = x)"
  by (force simp: retraction_def)

lemma retractionE: \<comment> \<open>yields properties normalized wrt. simp -- less likely to loop\<close>
  assumes "retraction S T r"
  obtains "T = r ` S" "r ` S \<subseteq> S" "continuous_on S r" "\<And>x. x \<in> S \<Longrightarrow> r (r x) = r x"
proof (rule that)
  from retraction [of S T r] assms
  have "T \<subseteq> S" "continuous_on S r" "r ` S = T" and "\<forall>x \<in> T. r x = x"
    by simp_all
  then show "T = r ` S" "r ` S \<subseteq> S" "continuous_on S r"
    by simp_all
  from \<open>\<forall>x \<in> T. r x = x\<close> have "r x = x" if "x \<in> T" for x
    using that by simp
  with \<open>r ` S = T\<close> show "r (r x) = r x" if "x \<in> S" for x
    using that by auto
qed

lemma retract_ofE: \<comment> \<open>yields properties normalized wrt. simp -- less likely to loop\<close>
  assumes "T retract_of S"
  obtains r where "T = r ` S" "r ` S \<subseteq> S" "continuous_on S r" "\<And>x. x \<in> S \<Longrightarrow> r (r x) = r x"
proof -
  from assms obtain r where "retraction S T r"
    by (auto simp add: retract_of_def)
  with that show thesis
    by (auto elim: retractionE)
qed

lemma retract_of_imp_extensible:
  assumes "S retract_of T" and "continuous_on S f" and "f ` S \<subseteq> U"
  obtains g where "continuous_on T g" "g ` T \<subseteq> U" "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  from \<open>S retract_of T\<close> obtain r where "retraction T S r"
    by (auto simp add: retract_of_def)
  show thesis
    by (rule that [of "f \<circ> r"])
      (use \<open>continuous_on S f\<close> \<open>f ` S \<subseteq> U\<close> \<open>retraction T S r\<close> in \<open>auto simp: continuous_on_compose2 retraction\<close>)
qed

lemma idempotent_imp_retraction:
  assumes "continuous_on S f" and "f ` S \<subseteq> S" and "\<And>x. x \<in> S \<Longrightarrow> f(f x) = f x"
    shows "retraction S (f ` S) f"
by (simp add: assms retraction)

lemma retraction_subset:
  assumes "retraction S T r" and "T \<subseteq> s'" and "s' \<subseteq> S"
  shows "retraction s' T r"
  unfolding retraction_def
  by (metis assms continuous_on_subset image_mono retraction)

lemma retract_of_subset:
  assumes "T retract_of S" and "T \<subseteq> s'" and "s' \<subseteq> S"
    shows "T retract_of s'"
by (meson assms retract_of_def retraction_subset)

lemma retraction_refl [simp]: "retraction S S (\<lambda>x. x)"
by (simp add: retraction)

lemma retract_of_refl [iff]: "S retract_of S"
  unfolding retract_of_def retraction_def
  using continuous_on_id by blast

lemma retract_of_imp_subset:
   "S retract_of T \<Longrightarrow> S \<subseteq> T"
by (simp add: retract_of_def retraction_def)

lemma retract_of_empty [simp]:
     "({} retract_of S) \<longleftrightarrow> S = {}"  "(S retract_of {}) \<longleftrightarrow> S = {}"
by (auto simp: retract_of_def retraction_def)

lemma retract_of_singleton [iff]: "({x} retract_of S) \<longleftrightarrow> x \<in> S"
  unfolding retract_of_def retraction_def by force

lemma retraction_comp:
   "\<lbrakk>retraction S T f; retraction T U g\<rbrakk>
        \<Longrightarrow> retraction S U (g \<circ> f)"
apply (auto simp: retraction_def intro: continuous_on_compose2)
by blast

lemma retract_of_trans [trans]:
  assumes "S retract_of T" and "T retract_of U"
    shows "S retract_of U"
using assms by (auto simp: retract_of_def intro: retraction_comp)

lemma closedin_retract:
  fixes S :: "'a :: t2_space set"
  assumes "S retract_of T"
    shows "closedin (top_of_set T) S"
proof -
  obtain r where r: "S \<subseteq> T" "continuous_on T r" "r ` T \<subseteq> S" "\<And>x. x \<in> S \<Longrightarrow> r x = x"
    using assms by (auto simp: retract_of_def retraction_def)
  have "S = {x\<in>T. x = r x}"
    using r by auto
  also have "\<dots> = T \<inter> ((\<lambda>x. (x, r x)) -` ({y. \<exists>x. y = (x, x)}))"
    unfolding vimage_def mem_Times_iff fst_conv snd_conv
    using r
    by auto
  also have "closedin (top_of_set T) \<dots>"
    by (rule continuous_closedin_preimage) (auto intro!: closed_diagonal continuous_on_Pair r)
  finally show ?thesis .
qed

lemma closedin_self [simp]: "closedin (top_of_set S) S"
  by simp

lemma retract_of_closed:
    fixes S :: "'a :: t2_space set"
    shows "\<lbrakk>closed T; S retract_of T\<rbrakk> \<Longrightarrow> closed S"
  by (metis closedin_retract closedin_closed_eq)

lemma retract_of_compact:
     "\<lbrakk>compact T; S retract_of T\<rbrakk> \<Longrightarrow> compact S"
  by (metis compact_continuous_image retract_of_def retraction)

lemma retract_of_connected:
    "\<lbrakk>connected T; S retract_of T\<rbrakk> \<Longrightarrow> connected S"
  by (metis Topological_Spaces.connected_continuous_image retract_of_def retraction)

lemma retraction_openin_vimage_iff:
  "openin (top_of_set S) (S \<inter> r -` U) \<longleftrightarrow> openin (top_of_set T) U"
  if retraction: "retraction S T r" and "U \<subseteq> T"
  using retraction apply (rule retractionE)
  apply (rule continuous_right_inverse_imp_quotient_map [where g=r])
  using \<open>U \<subseteq> T\<close> apply (auto elim: continuous_on_subset)
  done

lemma retract_of_Times:
   "\<lbrakk>S retract_of s'; T retract_of t'\<rbrakk> \<Longrightarrow> (S \<times> T) retract_of (s' \<times> t')"
apply (simp add: retract_of_def retraction_def Sigma_mono, clarify)
apply (rename_tac f g)
apply (rule_tac x="\<lambda>z. ((f \<circ> fst) z, (g \<circ> snd) z)" in exI)
apply (rule conjI continuous_intros | erule continuous_on_subset | force)+
done

subsection\<open>Retractions on a topological space\<close>

definition retract_of_space :: "'a set \<Rightarrow> 'a topology \<Rightarrow> bool" (infix "retract'_of'_space" 50)
  where "S retract_of_space X
         \<equiv> S \<subseteq> topspace X \<and> (\<exists>r. continuous_map X (subtopology X S) r \<and> (\<forall>x \<in> S. r x = x))"

lemma retract_of_space_retraction_maps:
   "S retract_of_space X \<longleftrightarrow> S \<subseteq> topspace X \<and> (\<exists>r. retraction_maps X (subtopology X S) r id)"
  by (auto simp: retract_of_space_def retraction_maps_def)

lemma retract_of_space_section_map:
   "S retract_of_space X \<longleftrightarrow> S \<subseteq> topspace X \<and> section_map (subtopology X S) X id"
  unfolding retract_of_space_def retraction_maps_def section_map_def
  by (auto simp: continuous_map_from_subtopology)

lemma retract_of_space_imp_subset:
   "S retract_of_space X \<Longrightarrow> S \<subseteq> topspace X"
  by (simp add: retract_of_space_def)

lemma retract_of_space_topspace:
   "topspace X retract_of_space X"
  using retract_of_space_def by force

lemma retract_of_space_empty [simp]:
   "{} retract_of_space X \<longleftrightarrow> topspace X = {}"
  by (auto simp: continuous_map_def retract_of_space_def)

lemma retract_of_space_singleton [simp]:
  "{a} retract_of_space X \<longleftrightarrow> a \<in> topspace X"
proof -
  have "continuous_map X (subtopology X {a}) (\<lambda>x. a) \<and> (\<lambda>x. a) a = a" if "a \<in> topspace X"
    using that by simp
  then show ?thesis
    by (force simp: retract_of_space_def)
qed

lemma retract_of_space_clopen:
  assumes "openin X S" "closedin X S" "S = {} \<Longrightarrow> topspace X = {}"
  shows "S retract_of_space X"
proof (cases "S = {}")
  case False
  then obtain a where "a \<in> S"
    by blast
  show ?thesis
    unfolding retract_of_space_def
  proof (intro exI conjI)
    show "S \<subseteq> topspace X"
      by (simp add: assms closedin_subset)
    have "continuous_map X X (\<lambda>x. if x \<in> S then x else a)"
    proof (rule continuous_map_cases)
      show "continuous_map (subtopology X (X closure_of {x. x \<in> S})) X (\<lambda>x. x)"
        by (simp add: continuous_map_from_subtopology)
      show "continuous_map (subtopology X (X closure_of {x. x \<notin> S})) X (\<lambda>x. a)"
        using \<open>S \<subseteq> topspace X\<close> \<open>a \<in> S\<close> by force
      show "x = a" if "x \<in> X frontier_of {x. x \<in> S}" for x
        using assms that clopenin_eq_frontier_of by fastforce
    qed
    then show "continuous_map X (subtopology X S) (\<lambda>x. if x \<in> S then x else a)"
      using \<open>S \<subseteq> topspace X\<close> \<open>a \<in> S\<close>  by (auto simp: continuous_map_in_subtopology)
  qed auto
qed (use assms in auto)

lemma retract_of_space_disjoint_union:
  assumes "openin X S" "openin X T" and ST: "disjnt S T" "S \<union> T = topspace X" and "S = {} \<Longrightarrow> topspace X = {}"
  shows "S retract_of_space X"
proof (rule retract_of_space_clopen)
  have "S \<inter> T = {}"
    by (meson ST disjnt_def)
  then have "S = topspace X - T"
    using ST by auto
  then show "closedin X S"
    using \<open>openin X T\<close> by blast
qed (auto simp: assms)

lemma retraction_maps_section_image1:
  assumes "retraction_maps X Y r s"
  shows "s ` (topspace Y) retract_of_space X"
  unfolding retract_of_space_section_map
proof
  show "s ` topspace Y \<subseteq> topspace X"
    using assms continuous_map_image_subset_topspace retraction_maps_def by blast
  show "section_map (subtopology X (s ` topspace Y)) X id"
    unfolding section_map_def
    using assms retraction_maps_to_retract_maps by blast
qed

lemma retraction_maps_section_image2:
   "retraction_maps X Y r s
        \<Longrightarrow> subtopology X (s ` (topspace Y)) homeomorphic_space Y"
  using embedding_map_imp_homeomorphic_space homeomorphic_space_sym section_imp_embedding_map
        section_map_def by blast

subsection\<open>Paths and path-connectedness\<close>

definition pathin :: "'a topology \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
   "pathin X g \<equiv> continuous_map (subtopology euclideanreal {0..1}) X g"

lemma pathin_compose:
     "\<lbrakk>pathin X g; continuous_map X Y f\<rbrakk> \<Longrightarrow> pathin Y (f \<circ> g)"
   by (simp add: continuous_map_compose pathin_def)

lemma pathin_subtopology:
     "pathin (subtopology X S) g \<longleftrightarrow> pathin X g \<and> (\<forall>x \<in> {0..1}. g x \<in> S)"
  by (auto simp: pathin_def continuous_map_in_subtopology)

lemma pathin_const:
   "pathin X (\<lambda>x. a) \<longleftrightarrow> a \<in> topspace X"
  by (simp add: pathin_def)
   
lemma path_start_in_topspace: "pathin X g \<Longrightarrow> g 0 \<in> topspace X"
  by (force simp: pathin_def continuous_map)

lemma path_finish_in_topspace: "pathin X g \<Longrightarrow> g 1 \<in> topspace X"
  by (force simp: pathin_def continuous_map)

lemma path_image_subset_topspace: "pathin X g \<Longrightarrow> g ` ({0..1}) \<subseteq> topspace X"
  by (force simp: pathin_def continuous_map)

definition path_connected_space :: "'a topology \<Rightarrow> bool"
  where "path_connected_space X \<equiv> \<forall>x \<in> topspace X. \<forall> y \<in> topspace X. \<exists>g. pathin X g \<and> g 0 = x \<and> g 1 = y"

definition path_connectedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool"
  where "path_connectedin X S \<equiv> S \<subseteq> topspace X \<and> path_connected_space(subtopology X S)"

lemma path_connectedin_absolute [simp]:
     "path_connectedin (subtopology X S) S \<longleftrightarrow> path_connectedin X S"
  by (simp add: path_connectedin_def subtopology_subtopology)

lemma path_connectedin_subset_topspace:
     "path_connectedin X S \<Longrightarrow> S \<subseteq> topspace X"
  by (simp add: path_connectedin_def)

lemma path_connectedin_subtopology:
     "path_connectedin (subtopology X S) T \<longleftrightarrow> path_connectedin X T \<and> T \<subseteq> S"
  by (auto simp: path_connectedin_def subtopology_subtopology inf.absorb2)

lemma path_connectedin:
     "path_connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
        (\<forall>x \<in> S. \<forall>y \<in> S. \<exists>g. pathin X g \<and> g ` {0..1} \<subseteq> S \<and> g 0 = x \<and> g 1 = y)"
  unfolding path_connectedin_def path_connected_space_def pathin_def continuous_map_in_subtopology
  by (intro conj_cong refl ball_cong) (simp_all add: inf.absorb_iff2)

lemma path_connectedin_topspace:
     "path_connectedin X (topspace X) \<longleftrightarrow> path_connected_space X"
  by (simp add: path_connectedin_def)

lemma path_connected_imp_connected_space:
  assumes "path_connected_space X"
  shows "connected_space X"
proof -
  have *: "\<exists>S. connectedin X S \<and> g 0 \<in> S \<and> g 1 \<in> S" if "pathin X g" for g
  proof (intro exI conjI)
    have "continuous_map (subtopology euclideanreal {0..1}) X g"
      using connectedin_absolute that by (simp add: pathin_def)
    then show "connectedin X (g ` {0..1})"
      by (rule connectedin_continuous_map_image) auto
  qed auto
  show ?thesis
    using assms
    by (auto intro: * simp add: path_connected_space_def connected_space_subconnected Ball_def)
qed

lemma path_connectedin_imp_connectedin:
     "path_connectedin X S \<Longrightarrow> connectedin X S"
  by (simp add: connectedin_def path_connected_imp_connected_space path_connectedin_def)

lemma path_connected_space_topspace_empty:
     "topspace X = {} \<Longrightarrow> path_connected_space X"
  by (simp add: path_connected_space_def)

lemma path_connectedin_empty [simp]: "path_connectedin X {}"
  by (simp add: path_connectedin)

lemma path_connectedin_singleton [simp]: "path_connectedin X {a} \<longleftrightarrow> a \<in> topspace X"
proof
  show "path_connectedin X {a} \<Longrightarrow> a \<in> topspace X"
    by (simp add: path_connectedin)
  show "a \<in> topspace X \<Longrightarrow> path_connectedin X {a}"
    unfolding path_connectedin
    using pathin_const by fastforce
qed

lemma path_connectedin_continuous_map_image:
  assumes f: "continuous_map X Y f" and S: "path_connectedin X S"
  shows "path_connectedin Y (f ` S)"
proof -
  have fX: "f ` (topspace X) \<subseteq> topspace Y"
    by (metis f continuous_map_image_subset_topspace)
  show ?thesis
    unfolding path_connectedin
  proof (intro conjI ballI; clarify?)
    fix x
    assume "x \<in> S"
    show "f x \<in> topspace Y"
      by (meson S fX \<open>x \<in> S\<close> image_subset_iff path_connectedin_subset_topspace set_mp)
  next
    fix x y
    assume "x \<in> S" and "y \<in> S"
    then obtain g where g: "pathin X g" "g ` {0..1} \<subseteq> S" "g 0 = x" "g 1 = y"
      using S  by (force simp: path_connectedin)
    show "\<exists>g. pathin Y g \<and> g ` {0..1} \<subseteq> f ` S \<and> g 0 = f x \<and> g 1 = f y"
    proof (intro exI conjI)
      show "pathin Y (f \<circ> g)"
        using \<open>pathin X g\<close> f pathin_compose by auto
    qed (use g in auto)
  qed
qed

lemma path_connectedin_discrete_topology:
  "path_connectedin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U \<and> (\<exists>a. S \<subseteq> {a})"
  apply safe
  using path_connectedin_subset_topspace apply fastforce
   apply (meson connectedin_discrete_topology path_connectedin_imp_connectedin)
  using subset_singletonD by fastforce

lemma path_connected_space_discrete_topology:
   "path_connected_space (discrete_topology U) \<longleftrightarrow> (\<exists>a. U \<subseteq> {a})"
  by (metis path_connectedin_discrete_topology path_connectedin_topspace path_connected_space_topspace_empty
            subset_singletonD topspace_discrete_topology)


lemma homeomorphic_path_connected_space_imp:
     "\<lbrakk>path_connected_space X; X homeomorphic_space Y\<rbrakk> \<Longrightarrow> path_connected_space Y"
  unfolding homeomorphic_space_def homeomorphic_maps_def
  by (metis (no_types, opaque_lifting) continuous_map_closedin continuous_map_image_subset_topspace imageI order_class.order.antisym path_connectedin_continuous_map_image path_connectedin_topspace subsetI)

lemma homeomorphic_path_connected_space:
   "X homeomorphic_space Y \<Longrightarrow> path_connected_space X \<longleftrightarrow> path_connected_space Y"
  by (meson homeomorphic_path_connected_space_imp homeomorphic_space_sym)

lemma homeomorphic_map_path_connectedness:
  assumes "homeomorphic_map X Y f" "U \<subseteq> topspace X"
  shows "path_connectedin Y (f ` U) \<longleftrightarrow> path_connectedin X U"
  unfolding path_connectedin_def
proof (intro conj_cong homeomorphic_path_connected_space)
  show "(f ` U \<subseteq> topspace Y) = (U \<subseteq> topspace X)"
    using assms homeomorphic_imp_surjective_map by blast
next
  assume "U \<subseteq> topspace X"
  show "subtopology Y (f ` U) homeomorphic_space subtopology X U"
    using assms unfolding homeomorphic_eq_everything_map
    by (metis (no_types, opaque_lifting) assms homeomorphic_map_subtopologies homeomorphic_space homeomorphic_space_sym image_mono inf.absorb_iff2)
qed

lemma homeomorphic_map_path_connectedness_eq:
   "homeomorphic_map X Y f \<Longrightarrow> path_connectedin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> path_connectedin Y (f ` U)"
  by (meson homeomorphic_map_path_connectedness path_connectedin_def)

subsection\<open>Connected components\<close>

definition connected_component_of :: "'a topology \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "connected_component_of X x y \<equiv>
        \<exists>T. connectedin X T \<and> x \<in> T \<and> y \<in> T"

abbreviation connected_component_of_set
  where "connected_component_of_set X x \<equiv> Collect (connected_component_of X x)"

definition connected_components_of :: "'a topology \<Rightarrow> ('a set) set"
  where "connected_components_of X \<equiv> connected_component_of_set X ` topspace X"

lemma connected_component_in_topspace:
   "connected_component_of X x y \<Longrightarrow> x \<in> topspace X \<and> y \<in> topspace X"
  by (meson connected_component_of_def connectedin_subset_topspace in_mono)

lemma connected_component_of_refl:
   "connected_component_of X x x \<longleftrightarrow> x \<in> topspace X"
  by (meson connected_component_in_topspace connected_component_of_def connectedin_sing insertI1)

lemma connected_component_of_sym:
   "connected_component_of X x y \<longleftrightarrow> connected_component_of X y x"
  by (meson connected_component_of_def)

lemma connected_component_of_trans:
   "\<lbrakk>connected_component_of X x y; connected_component_of X y z\<rbrakk>
        \<Longrightarrow> connected_component_of X x z"
  unfolding connected_component_of_def
  using connectedin_Un by blast

lemma connected_component_of_mono:
   "\<lbrakk>connected_component_of (subtopology X S) x y; S \<subseteq> T\<rbrakk>
        \<Longrightarrow> connected_component_of (subtopology X T) x y"
  by (metis connected_component_of_def connectedin_subtopology inf.absorb_iff2 subtopology_subtopology)

lemma connected_component_of_set:
   "connected_component_of_set X x = {y. \<exists>T. connectedin X T \<and> x \<in> T \<and> y \<in> T}"
  by (meson connected_component_of_def)

lemma connected_component_of_subset_topspace:
   "connected_component_of_set X x \<subseteq> topspace X"
  using connected_component_in_topspace by force

lemma connected_component_of_eq_empty:
   "connected_component_of_set X x = {} \<longleftrightarrow> (x \<notin> topspace X)"
  using connected_component_in_topspace connected_component_of_refl by fastforce

lemma connected_space_iff_connected_component:
   "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. connected_component_of X x y)"
  by (simp add: connected_component_of_def connected_space_subconnected)

lemma connected_space_imp_connected_component_of:
   "\<lbrakk>connected_space X; a \<in> topspace X; b \<in> topspace X\<rbrakk>
    \<Longrightarrow> connected_component_of X a b"
  by (simp add: connected_space_iff_connected_component)

lemma connected_space_connected_component_set:
   "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. connected_component_of_set X x = topspace X)"
  using connected_component_of_subset_topspace connected_space_iff_connected_component by fastforce

lemma connected_component_of_maximal:
   "\<lbrakk>connectedin X S; x \<in> S\<rbrakk> \<Longrightarrow> S \<subseteq> connected_component_of_set X x"
  by (meson Ball_Collect connected_component_of_def)

lemma connected_component_of_equiv:
   "connected_component_of X x y \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and> connected_component_of X x = connected_component_of X y"
  apply (simp add: connected_component_in_topspace fun_eq_iff)
  by (meson connected_component_of_refl connected_component_of_sym connected_component_of_trans)

lemma connected_component_of_disjoint:
   "disjnt (connected_component_of_set X x) (connected_component_of_set X y)
    \<longleftrightarrow> ~(connected_component_of X x y)"
  using connected_component_of_equiv unfolding disjnt_iff by force

lemma connected_component_of_eq:
   "connected_component_of X x = connected_component_of X y \<longleftrightarrow>
        (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        connected_component_of X x y"
  by (metis Collect_empty_eq_bot connected_component_of_eq_empty connected_component_of_equiv)

lemma connectedin_connected_component_of:
   "connectedin X (connected_component_of_set X x)"
proof -
  have "connected_component_of_set X x = \<Union> {T. connectedin X T \<and> x \<in> T}"
    by (auto simp: connected_component_of_def)
  then show ?thesis
    apply (rule ssubst)
    by (blast intro: connectedin_Union)
qed


lemma Union_connected_components_of:
   "\<Union>(connected_components_of X) = topspace X"
  unfolding connected_components_of_def
  apply (rule equalityI)
  apply (simp add: SUP_least connected_component_of_subset_topspace)
  using connected_component_of_refl by fastforce

lemma connected_components_of_maximal:
   "\<lbrakk>C \<in> connected_components_of X; connectedin X S; ~disjnt C S\<rbrakk> \<Longrightarrow> S \<subseteq> C"
  unfolding connected_components_of_def disjnt_def
  apply clarify
  by (metis Int_emptyI connected_component_of_def connected_component_of_trans mem_Collect_eq)

lemma pairwise_disjoint_connected_components_of:
   "pairwise disjnt (connected_components_of X)"
  unfolding connected_components_of_def pairwise_def
  apply clarify
  by (metis connected_component_of_disjoint connected_component_of_equiv)

lemma complement_connected_components_of_Union:
   "C \<in> connected_components_of X
      \<Longrightarrow> topspace X - C = \<Union> (connected_components_of X - {C})"
  apply (rule equalityI)
  using Union_connected_components_of apply fastforce
  by (metis Diff_cancel Diff_subset Union_connected_components_of cSup_singleton diff_Union_pairwise_disjoint equalityE insert_subsetI pairwise_disjoint_connected_components_of)

lemma nonempty_connected_components_of:
   "C \<in> connected_components_of X \<Longrightarrow> C \<noteq> {}"
  unfolding connected_components_of_def
  by (metis (no_types, lifting) connected_component_of_eq_empty imageE)

lemma connected_components_of_subset:
   "C \<in> connected_components_of X \<Longrightarrow> C \<subseteq> topspace X"
  using Union_connected_components_of by fastforce

lemma connectedin_connected_components_of:
  assumes "C \<in> connected_components_of X"
  shows "connectedin X C"
proof -
  have "C \<in> connected_component_of_set X ` topspace X"
    using assms connected_components_of_def by blast
then show ?thesis
  using connectedin_connected_component_of by fastforce
qed

lemma connected_component_in_connected_components_of:
   "connected_component_of_set X a \<in> connected_components_of X \<longleftrightarrow> a \<in> topspace X"
  apply (rule iffI)
  using connected_component_of_eq_empty nonempty_connected_components_of apply fastforce
  by (simp add: connected_components_of_def)

lemma connected_space_iff_components_eq:
   "connected_space X \<longleftrightarrow> (\<forall>C \<in> connected_components_of X. \<forall>C' \<in> connected_components_of X. C = C')"
  apply (rule iffI)
  apply (force simp: connected_components_of_def connected_space_connected_component_set image_iff)
  by (metis connected_component_in_connected_components_of connected_component_of_refl connected_space_iff_connected_component mem_Collect_eq)

lemma connected_components_of_eq_empty:
   "connected_components_of X = {} \<longleftrightarrow> topspace X = {}"
  by (simp add: connected_components_of_def)

lemma connected_components_of_empty_space:
   "topspace X = {} \<Longrightarrow> connected_components_of X = {}"
  by (simp add: connected_components_of_eq_empty)

lemma connected_components_of_subset_sing:
   "connected_components_of X \<subseteq> {S} \<longleftrightarrow> connected_space X \<and> (topspace X = {} \<or> topspace X = S)"
proof (cases "topspace X = {}")
  case True
  then show ?thesis
    by (simp add: connected_components_of_empty_space connected_space_topspace_empty)
next
  case False
  then show ?thesis
    by (metis (no_types, opaque_lifting) Union_connected_components_of ccpo_Sup_singleton
        connected_components_of_eq_empty connected_space_iff_components_eq insertI1 singletonD
        subsetI subset_singleton_iff)
qed

lemma connected_space_iff_components_subset_singleton:
   "connected_space X \<longleftrightarrow> (\<exists>a. connected_components_of X \<subseteq> {a})"
  by (simp add: connected_components_of_subset_sing)

lemma connected_components_of_eq_singleton:
   "connected_components_of X = {S}
\<longleftrightarrow> connected_space X \<and> topspace X \<noteq> {} \<and> S = topspace X"
  by (metis ccpo_Sup_singleton connected_components_of_subset_sing insert_not_empty subset_singleton_iff)

lemma connected_components_of_connected_space:
   "connected_space X \<Longrightarrow> connected_components_of X = (if topspace X = {} then {} else {topspace X})"
  by (simp add: connected_components_of_eq_empty connected_components_of_eq_singleton)

lemma exists_connected_component_of_superset:
  assumes "connectedin X S" and ne: "topspace X \<noteq> {}"
  shows "\<exists>C. C \<in> connected_components_of X \<and> S \<subseteq> C"
proof (cases "S = {}")
  case True
  then show ?thesis
    using ne connected_components_of_def by blast
next
  case False
  then show ?thesis
    by (meson all_not_in_conv assms(1) connected_component_in_connected_components_of connected_component_of_maximal connectedin_subset_topspace in_mono)
qed

lemma closedin_connected_components_of:
  assumes "C \<in> connected_components_of X"
  shows   "closedin X C"
proof -
  obtain x where "x \<in> topspace X" and x: "C = connected_component_of_set X x"
    using assms by (auto simp: connected_components_of_def)
  have "connected_component_of_set X x \<subseteq> topspace X"
    by (simp add: connected_component_of_subset_topspace)
  moreover have "X closure_of connected_component_of_set X x \<subseteq> connected_component_of_set X x"
  proof (rule connected_component_of_maximal)
    show "connectedin X (X closure_of connected_component_of_set X x)"
      by (simp add: connectedin_closure_of connectedin_connected_component_of)
    show "x \<in> X closure_of connected_component_of_set X x"
      by (simp add: \<open>x \<in> topspace X\<close> closure_of connected_component_of_refl)
  qed
  ultimately
  show ?thesis
    using closure_of_subset_eq x by auto
qed

lemma closedin_connected_component_of:
   "closedin X (connected_component_of_set X x)"
  by (metis closedin_connected_components_of closedin_empty connected_component_in_connected_components_of connected_component_of_eq_empty)

lemma connected_component_of_eq_overlap:
   "connected_component_of_set X x = connected_component_of_set X y \<longleftrightarrow>
      (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
      ~(connected_component_of_set X x \<inter> connected_component_of_set X y = {})"
  using connected_component_of_equiv by fastforce

lemma connected_component_of_nonoverlap:
   "connected_component_of_set X x \<inter> connected_component_of_set X y = {} \<longleftrightarrow>
     (x \<notin> topspace X) \<or> (y \<notin> topspace X) \<or>
     ~(connected_component_of_set X x = connected_component_of_set X y)"
  by (metis connected_component_of_eq_empty connected_component_of_eq_overlap inf.idem)

lemma connected_component_of_overlap:
   "~(connected_component_of_set X x \<inter> connected_component_of_set X y = {}) \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and>
    connected_component_of_set X x = connected_component_of_set X y"
  by (meson connected_component_of_nonoverlap)

end