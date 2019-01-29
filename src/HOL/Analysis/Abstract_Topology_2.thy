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

(* FIXME: move elsewhere *)

lemma approachable_lt_le: "(\<exists>(d::real) > 0. \<forall>x. f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI)
  apply auto
  done

lemma approachable_lt_le2:  \<comment> \<open>like the above, but pushes aside an extra formula\<close>
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
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({0<..<2} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y > (0::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> A" using indicator_eq_0_iff by force
    hence "x \<in> interior A" using U interiorI by auto
    thus ?thesis using fr unfolding frontier_def by simp
  next
    assume x: "x \<notin> A"
    hence "indicator A x \<in> ({-1<..<1} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({-1<..<1} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
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
    hence "continuous_on U (indicator A)" by (simp add: continuous_on_const indicator_eq_1_iff)
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
  "closedin (subtopology euclidean T) S \<longleftrightarrow> S \<subseteq> T \<and> (\<forall>x. x islimpt S \<and> x \<in> T \<longrightarrow> x \<in> S)"
  apply (simp add: closedin_closed, safe)
   apply (simp add: closed_limpt islimpt_subset)
  apply (rule_tac x="closure S" in exI, simp)
  apply (force simp: closure_def)
  done

lemma closedin_closed_eq: "closed S \<Longrightarrow> closedin (subtopology euclidean S) T \<longleftrightarrow> closed T \<and> T \<subseteq> S"
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
  "closedin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    closedin (subtopology euclidean T) S"
  by (meson closedin_limpt subset_iff)

lemma openin_subset_trans:
  "openin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    openin (subtopology euclidean T) S"
  by (auto simp: openin_open)

lemma closedin_compact:
   "\<lbrakk>compact S; closedin (subtopology euclidean S) T\<rbrakk> \<Longrightarrow> compact T"
by (metis closedin_closed compact_Int_closed)

lemma closedin_compact_eq:
  fixes S :: "'a::t2_space set"
  shows
   "compact S
         \<Longrightarrow> (closedin (subtopology euclidean S) T \<longleftrightarrow>
              compact T \<and> T \<subseteq> S)"
by (metis closedin_imp_subset closedin_compact closed_subset compact_imp_closed)


subsection \<open>Closure\<close>

lemma closure_openin_Int_closure:
  assumes ope: "openin (subtopology euclidean U) S" and "T \<subseteq> U"
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
  shows "\<lbrakk>openin (subtopology euclidean U) S; x \<in> S; x islimpt U\<rbrakk> \<Longrightarrow> infinite S"
  by (clarsimp simp add: openin_open islimpt_eq_acc_point inf_commute)

lemma closure_Int_ballI:
  assumes "\<And>U. \<lbrakk>openin (subtopology euclidean S) U; U \<noteq> {}\<rbrakk> \<Longrightarrow> T \<inter> U \<noteq> {}"
  shows "S \<subseteq> closure T"
proof (clarsimp simp: closure_iff_nhds_not_empty)
  fix x and A and V
  assume "x \<in> S" "V \<subseteq> A" "open V" "x \<in> V" "T \<inter> A = {}"
  then have "openin (subtopology euclidean S) (A \<inter> V \<inter> S)"
    by (auto simp: openin_open intro!: exI[where x="V"])
  moreover have "A \<inter> V \<inter> S \<noteq> {}" using \<open>x \<in> V\<close> \<open>V \<subseteq> A\<close> \<open>x \<in> S\<close>
    by auto
  ultimately have "T \<inter> (A \<inter> V \<inter> S) \<noteq> {}"
    by (rule assms)
  with \<open>T \<inter> A = {}\<close> show False by auto
qed


subsection \<open>Frontier\<close>

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
  shows "openin (subtopology euclidean u) s
         \<Longrightarrow> openin (subtopology euclidean u) (s - {a})"
by (metis Int_Diff open_delete openin_open)

lemma compact_eq_openin_cover:
  "compact S \<longleftrightarrow>
    (\<forall>C. (\<forall>c\<in>C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D))"
proof safe
  fix C
  assume "compact S" and "\<forall>c\<in>C. openin (subtopology euclidean S) c" and "S \<subseteq> \<Union>C"
  then have "\<forall>c\<in>{T. open T \<and> S \<inter> T \<in> C}. open c" and "S \<subseteq> \<Union>{T. open T \<and> S \<inter> T \<in> C}"
    unfolding openin_open by force+
  with \<open>compact S\<close> obtain D where "D \<subseteq> {T. open T \<and> S \<inter> T \<in> C}" and "finite D" and "S \<subseteq> \<Union>D"
    by (meson compactE)
  then have "image (\<lambda>T. S \<inter> T) D \<subseteq> C \<and> finite (image (\<lambda>T. S \<inter> T) D) \<and> S \<subseteq> \<Union>(image (\<lambda>T. S \<inter> T) D)"
    by auto
  then show "\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D" ..
next
  assume 1: "\<forall>C. (\<forall>c\<in>C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>C \<longrightarrow>
        (\<exists>D\<subseteq>C. finite D \<and> S \<subseteq> \<Union>D)"
  show "compact S"
  proof (rule compactI)
    fix C
    let ?C = "image (\<lambda>T. S \<inter> T) C"
    assume "\<forall>t\<in>C. open t" and "S \<subseteq> \<Union>C"
    then have "(\<forall>c\<in>?C. openin (subtopology euclidean S) c) \<and> S \<subseteq> \<Union>?C"
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
        apply (rule subset_trans, clarsimp)
        apply (frule subsetD [OF \<open>D \<subseteq> ?C\<close>, THEN f_inv_into_f])
        apply (erule rev_bexI, fast)
        done
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

subsection%unimportant \<open>Equality of continuous functions on closure and related results\<close>

lemma continuous_closedin_preimage_constant:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "continuous_on S f \<Longrightarrow> closedin (subtopology euclidean S) {x \<in> S. f x = a}"
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

subsection%unimportant \<open>A function constant on a set\<close>

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


subsection%unimportant \<open>Continuity relative to a union.\<close>

lemma continuous_on_Un_local:
    "\<lbrakk>closedin (subtopology euclidean (s \<union> t)) s; closedin (subtopology euclidean (s \<union> t)) t;
      continuous_on s f; continuous_on t f\<rbrakk>
     \<Longrightarrow> continuous_on (s \<union> t) f"
  unfolding continuous_on closedin_limpt
  by (metis Lim_trivial_limit Lim_within_union Un_iff trivial_limit_within)

lemma continuous_on_cases_local:
     "\<lbrakk>closedin (subtopology euclidean (s \<union> t)) s; closedin (subtopology euclidean (s \<union> t)) t;
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
  have 1: "closedin (subtopology euclidean s) (s \<inter> h -` atMost a)"
    by (rule continuous_closedin_preimage [OF h closed_atMost])
  have 2: "closedin (subtopology euclidean s) (s \<inter> h -` atLeast a)"
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
by (auto simp: continuous_on_id intro: continuous_on_cases_le [where h = id, simplified])


subsection%unimportant\<open>Inverse function property for open/closed maps\<close>

lemma continuous_on_inverse_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
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
    and oo: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
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
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
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
    and oo: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_closed_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_imp_open_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "openin (subtopology euclidean S) U"
  shows "openin (subtopology euclidean T) (f ` U)"
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
    and oo: "closedin (subtopology euclidean S) U"
  shows "closedin (subtopology euclidean T) (f ` U)"
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

subsection%unimportant \<open>Seperability\<close>

lemma subset_second_countable:
  obtains \<B> :: "'a:: second_countable_topology set set"
    where "countable \<B>"
          "{} \<notin> \<B>"
          "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
          "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>"
      and opeB: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
      and \<B>:    "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
  proof -
    obtain \<C> :: "'a set set"
      where "countable \<C>" and ope: "\<And>C. C \<in> \<C> \<Longrightarrow> open C"
        and \<C>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<C> \<and> S = \<Union>U"
      by (metis univ_second_countable that)
    show ?thesis
    proof
      show "countable ((\<lambda>C. S \<inter> C) ` \<C>)"
        by (simp add: \<open>countable \<C>\<close>)
      show "\<And>C. C \<in> (\<inter>) S ` \<C> \<Longrightarrow> openin (subtopology euclidean S) C"
        using ope by auto
      show "\<And>T. openin (subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>\<subseteq>(\<inter>) S ` \<C>. T = \<Union>\<U>"
        by (metis \<C> image_mono inf_Sup openin_open)
    qed
  qed
  show ?thesis
  proof
    show "countable (\<B> - {{}})"
      using \<open>countable \<B>\<close> by blast
    show "\<And>C. \<lbrakk>C \<in> \<B> - {{}}\<rbrakk> \<Longrightarrow> openin (subtopology euclidean S) C"
      by (simp add: \<open>\<And>C. C \<in> \<B> \<Longrightarrow> openin (subtopology euclidean S) C\<close>)
    show "\<exists>\<U>\<subseteq>\<B> - {{}}. T = \<Union>\<U>" if "openin (subtopology euclidean S) T" for T
      using \<B> [OF that]
      apply clarify
      apply (rule_tac x="\<U> - {{}}" in exI, auto)
        done
  qed auto
qed

lemma Lindelof_openin:
  fixes \<F> :: "'a::second_countable_topology set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> openin (subtopology euclidean U) S"
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


subsection%unimportant\<open>Closed Maps\<close>

lemma continuous_imp_closed_map:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::t2_space"
  assumes "closedin (subtopology euclidean S) U"
          "continuous_on S f" "f ` S = T" "compact S"
    shows "closedin (subtopology euclidean T) (f ` U)"
  by (metis assms closedin_compact_eq compact_continuous_image continuous_on_subset subset_image_iff)

lemma closed_map_restrict:
  assumes cloU: "closedin (subtopology euclidean (S \<inter> f -` T')) U"
    and cc: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
    and "T' \<subseteq> T"
  shows "closedin (subtopology euclidean T') (f ` U)"
proof -
  obtain V where "closed V" "U = S \<inter> f -` T' \<inter> V"
    using cloU by (auto simp: closedin_closed)
  with cc [of "S \<inter> V"] \<open>T' \<subseteq> T\<close> show ?thesis
    by (fastforce simp add: closedin_closed)
qed

subsection%unimportant\<open>Open Maps\<close>

lemma open_map_restrict:
  assumes opeU: "openin (subtopology euclidean (S \<inter> f -` T')) U"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
    and "T' \<subseteq> T"
  shows "openin (subtopology euclidean T') (f ` U)"
proof -
  obtain V where "open V" "U = S \<inter> f -` T' \<inter> V"
    using opeU by (auto simp: openin_open)
  with oo [of "S \<inter> V"] \<open>T' \<subseteq> T\<close> show ?thesis
    by (fastforce simp add: openin_open)
qed


subsection%unimportant\<open>Quotient maps\<close>

lemma quotient_map_imp_continuous_open:
  assumes T: "f ` S \<subseteq> T"
      and ope: "\<And>U. U \<subseteq> T
              \<Longrightarrow> (openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
                   openin (subtopology euclidean T) U)"
    shows "continuous_on S f"
proof -
  have [simp]: "S \<inter> f -` f ` S = S" by auto
  show ?thesis
    using ope [OF T]
    apply (simp add: continuous_on_open)
    by (meson ope openin_imp_subset openin_trans)
qed

lemma quotient_map_imp_continuous_closed:
  assumes T: "f ` S \<subseteq> T"
      and ope: "\<And>U. U \<subseteq> T
                  \<Longrightarrow> (closedin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
                       closedin (subtopology euclidean T) U)"
    shows "continuous_on S f"
proof -
  have [simp]: "S \<inter> f -` f ` S = S" by auto
  show ?thesis
    using ope [OF T]
    apply (simp add: continuous_on_closed)
    by (metis (no_types, lifting) ope closedin_imp_subset closedin_trans)
qed

lemma open_map_imp_quotient_map:
  assumes contf: "continuous_on S f"
      and T: "T \<subseteq> f ` S"
      and ope: "\<And>T. openin (subtopology euclidean S) T
                   \<Longrightarrow> openin (subtopology euclidean (f ` S)) (f ` T)"
    shows "openin (subtopology euclidean S) (S \<inter> f -` T) =
           openin (subtopology euclidean (f ` S)) T"
proof -
  have "T = f ` (S \<inter> f -` T)"
    using T by blast
  then show ?thesis
    using "ope" contf continuous_on_open by metis
qed

lemma closed_map_imp_quotient_map:
  assumes contf: "continuous_on S f"
      and T: "T \<subseteq> f ` S"
      and ope: "\<And>T. closedin (subtopology euclidean S) T
              \<Longrightarrow> closedin (subtopology euclidean (f ` S)) (f ` T)"
    shows "openin (subtopology euclidean S) (S \<inter> f -` T) \<longleftrightarrow>
           openin (subtopology euclidean (f ` S)) T"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have *: "closedin (subtopology euclidean S) (S - (S \<inter> f -` T))"
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
    shows "openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (subtopology euclidean T) U"
          (is "?lhs = ?rhs")
proof -
  have f: "\<And>Z. openin (subtopology euclidean (f ` S)) Z \<Longrightarrow>
                openin (subtopology euclidean S) (S \<inter> f -` Z)"
  and  g: "\<And>Z. openin (subtopology euclidean (g ` T)) Z \<Longrightarrow>
                openin (subtopology euclidean T) (T \<inter> g -` Z)"
    using contf contg by (auto simp: continuous_on_open)
  show ?thesis
  proof
    have "T \<inter> g -` (g ` T \<inter> (S \<inter> f -` U)) = {x \<in> T. f (g x) \<in> U}"
      using imf img by blast
    also have "... = U"
      using U by auto
    finally have eq: "T \<inter> g -` (g ` T \<inter> (S \<inter> f -` U)) = U" .
    assume ?lhs
    then have *: "openin (subtopology euclidean (g ` T)) (g ` T \<inter> (S \<inter> f -` U))"
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
    shows "openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (subtopology euclidean (f ` S)) U"
apply (rule continuous_right_inverse_imp_quotient_map)
using assms apply force+
done

lemma continuous_imp_quotient_map:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::t2_space"
  assumes "continuous_on S f" "f ` S = T" "compact S" "U \<subseteq> T"
    shows "openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (subtopology euclidean T) U"
  by (metis (no_types, lifting) assms closed_map_imp_quotient_map continuous_imp_closed_map)

subsection%unimportant\<open>Pasting functions together\<close>

text\<open>on open sets\<close>

lemma pasting_lemma:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes clo: "\<And>i. i \<in> I \<Longrightarrow> openin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_on S g"
proof (clarsimp simp: continuous_openin_preimage_eq)
  fix U :: "'b set"
  assume "open U"
  have S: "\<And>i. i \<in> I \<Longrightarrow> (T i) \<subseteq> S"
    using clo openin_imp_subset by blast
  have *: "(S \<inter> g -` U) = (\<Union>i \<in> I. T i \<inter> f i -` U)"
    using S f g by fastforce
  show "openin (subtopology euclidean S) (S \<inter> g -` U)"
    apply (subst *)
    apply (rule openin_Union, clarify)
    using \<open>open U\<close> clo cont continuous_openin_preimage_gen openin_trans by blast
qed

lemma pasting_lemma_exists:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes S: "S \<subseteq> (\<Union>i \<in> I. T i)"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> openin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_on S g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> S \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_on S (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma [OF clo cont])
     apply (blast intro: f)+
    apply (metis (mono_tags, lifting) S UN_iff subsetCE someI)
    done
next
  fix x i
  assume "i \<in> I" "x \<in> S \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed

text\<open>Likewise on closed sets, with a finiteness assumption\<close>

lemma pasting_lemma_closed:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "finite I"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_on S g"
proof (clarsimp simp: continuous_closedin_preimage_eq)
  fix U :: "'b set"
  assume "closed U"
  have S: "\<And>i. i \<in> I \<Longrightarrow> (T i) \<subseteq> S"
    using clo closedin_imp_subset by blast
  have *: "(S \<inter> g -` U) = (\<Union>i \<in> I. T i \<inter> f i -` U)"
    using S f g by fastforce
  show "closedin (subtopology euclidean S) (S \<inter> g -` U)"
    apply (subst *)
    apply (rule closedin_Union)
    using \<open>finite I\<close> apply simp
    apply (blast intro: \<open>closed U\<close> continuous_closedin_preimage cont clo closedin_trans)
    done
qed

lemma pasting_lemma_exists_closed:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "finite I"
      and S: "S \<subseteq> (\<Union>i \<in> I. T i)"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_on S g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> S \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_on S (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma_closed [OF \<open>finite I\<close> clo cont])
     apply (blast intro: f)+
    apply (metis (mono_tags, lifting) S UN_iff subsetCE someI)
    done
next
  fix x i
  assume "i \<in> I" "x \<in> S \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed


subsection \<open>Retractions\<close>

definition%important retraction :: "('a::topological_space) set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where "retraction S T r \<longleftrightarrow>
  T \<subseteq> S \<and> continuous_on S r \<and> r ` S \<subseteq> T \<and> (\<forall>x\<in>T. r x = x)"

definition%important retract_of (infixl "retract'_of" 50) where
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

lemma retractionE: \<comment> \<open>yields properties normalized wrt. simp – less likely to loop\<close>
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

lemma retract_ofE: \<comment> \<open>yields properties normalized wrt. simp – less likely to loop\<close>
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
    shows "closedin (subtopology euclidean T) S"
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

lemma closedin_self [simp]: "closedin (subtopology euclidean S) S"
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

lemma retraction_imp_quotient_map:
  "openin (subtopology euclidean S) (S \<inter> r -` U) \<longleftrightarrow> openin (subtopology euclidean T) U"
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

end