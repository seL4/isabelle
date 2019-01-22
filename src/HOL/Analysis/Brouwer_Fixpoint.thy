(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light) and LCP
*)

(* At the moment this is just Brouwer's fixpoint theorem. The proof is from  *)
(* Kuhn: "some combinatorial lemmas in topology", IBM J. v4. (1960) p. 518   *)
(* See "http://www.research.ibm.com/journal/rd/045/ibmrd0405K.pdf".          *)
(*                                                                           *)
(* The script below is quite messy, but at least we avoid formalizing any    *)
(* topological machinery; we don't even use barycentric subdivision; this is *)
(* the big advantage of Kuhn's proof over the usual Sperner's lemma one.     *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)

section \<open>Brouwer's Fixed Point Theorem\<close>

theory Brouwer_Fixpoint
  imports
    Path_Connected
    Homeomorphism
    Continuous_Extension
begin

(* FIXME mv topology euclidean space *)
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
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
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
  fixes S :: "'a::euclidean_space set"
    and T :: "'b::euclidean_space set"
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
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
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
by (simp add: continuous_on_id retraction)

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
  fixes S :: "'a :: real_normed_vector set"
  assumes "S retract_of T"
    shows "closedin (subtopology euclidean T) S"
proof -
  obtain r where "S \<subseteq> T" "continuous_on T r" "r ` T \<subseteq> S" "\<And>x. x \<in> S \<Longrightarrow> r x = x"
    using assms by (auto simp: retract_of_def retraction_def)
  then have S: "S = {x \<in> T. (norm(r x - x)) = 0}" by auto
  show ?thesis
    apply (subst S)
    apply (rule continuous_closedin_preimage_constant)
    by (simp add: \<open>continuous_on T r\<close> continuous_on_diff continuous_on_id continuous_on_norm)
qed

lemma closedin_self [simp]:
    fixes S :: "'a :: real_normed_vector set"
    shows "closedin (subtopology euclidean S) S"
  by (simp add: closedin_retract)

lemma retract_of_contractible:
  assumes "contractible T" "S retract_of T"
    shows "contractible S"
using assms
apply (clarsimp simp add: retract_of_def contractible_def retraction_def homotopic_with)
apply (rule_tac x="r a" in exI)
apply (rule_tac x="r \<circ> h" in exI)
apply (intro conjI continuous_intros continuous_on_compose)
apply (erule continuous_on_subset | force)+
done

lemma retract_of_compact:
     "\<lbrakk>compact T; S retract_of T\<rbrakk> \<Longrightarrow> compact S"
  by (metis compact_continuous_image retract_of_def retraction)

lemma retract_of_closed:
    fixes S :: "'a :: real_normed_vector set"
    shows "\<lbrakk>closed T; S retract_of T\<rbrakk> \<Longrightarrow> closed S"
  by (metis closedin_retract closedin_closed_eq)

lemma retract_of_connected:
    "\<lbrakk>connected T; S retract_of T\<rbrakk> \<Longrightarrow> connected S"
  by (metis Topological_Spaces.connected_continuous_image retract_of_def retraction)

lemma retract_of_path_connected:
    "\<lbrakk>path_connected T; S retract_of T\<rbrakk> \<Longrightarrow> path_connected S"
  by (metis path_connected_continuous_image retract_of_def retraction)

lemma retract_of_simply_connected:
    "\<lbrakk>simply_connected T; S retract_of T\<rbrakk> \<Longrightarrow> simply_connected S"
apply (simp add: retract_of_def retraction_def, clarify)
apply (rule simply_connected_retraction_gen)
apply (force simp: continuous_on_id elim!: continuous_on_subset)+
done

lemma retract_of_homotopically_trivial:
  assumes ts: "T retract_of S"
      and hom: "\<And>f g. \<lbrakk>continuous_on U f; f ` U \<subseteq> S;
                       continuous_on U g; g ` U \<subseteq> S\<rbrakk>
                       \<Longrightarrow> homotopic_with (\<lambda>x. True) U S f g"
      and "continuous_on U f" "f ` U \<subseteq> T"
      and "continuous_on U g" "g ` U \<subseteq> T"
    shows "homotopic_with (\<lambda>x. True) U T f g"
proof -
  obtain r where "r ` S \<subseteq> S" "continuous_on S r" "\<forall>x\<in>S. r (r x) = r x" "T = r ` S"
    using ts by (auto simp: retract_of_def retraction)
  then obtain k where "Retracts S r T k"
    unfolding Retracts_def
    by (metis continuous_on_subset dual_order.trans image_iff image_mono)
  then show ?thesis
    apply (rule Retracts.homotopically_trivial_retraction_gen)
    using assms
    apply (force simp: hom)+
    done
qed

lemma retract_of_homotopically_trivial_null:
  assumes ts: "T retract_of S"
      and hom: "\<And>f. \<lbrakk>continuous_on U f; f ` U \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>c. homotopic_with (\<lambda>x. True) U S f (\<lambda>x. c)"
      and "continuous_on U f" "f ` U \<subseteq> T"
  obtains c where "homotopic_with (\<lambda>x. True) U T f (\<lambda>x. c)"
proof -
  obtain r where "r ` S \<subseteq> S" "continuous_on S r" "\<forall>x\<in>S. r (r x) = r x" "T = r ` S"
    using ts by (auto simp: retract_of_def retraction)
  then obtain k where "Retracts S r T k"
    unfolding Retracts_def
    by (metis continuous_on_subset dual_order.trans image_iff image_mono)
  then show ?thesis
    apply (rule Retracts.homotopically_trivial_retraction_null_gen)
    apply (rule TrueI refl assms that | assumption)+
    done
qed

lemma retraction_imp_quotient_map:
  "openin (subtopology euclidean S) (S \<inter> r -` U) \<longleftrightarrow> openin (subtopology euclidean T) U"
  if retraction: "retraction S T r" and "U \<subseteq> T"
  using retraction apply (rule retractionE)
  apply (rule continuous_right_inverse_imp_quotient_map [where g=r])
  using \<open>U \<subseteq> T\<close> apply (auto elim: continuous_on_subset)
  done

lemma retract_of_locally_compact:
    fixes S :: "'a :: {heine_borel,real_normed_vector} set"
    shows  "\<lbrakk> locally compact S; T retract_of S\<rbrakk> \<Longrightarrow> locally compact T"
  by (metis locally_compact_closedin closedin_retract)

lemma retract_of_Times:
   "\<lbrakk>S retract_of s'; T retract_of t'\<rbrakk> \<Longrightarrow> (S \<times> T) retract_of (s' \<times> t')"
apply (simp add: retract_of_def retraction_def Sigma_mono, clarify)
apply (rename_tac f g)
apply (rule_tac x="\<lambda>z. ((f \<circ> fst) z, (g \<circ> snd) z)" in exI)
apply (rule conjI continuous_intros | erule continuous_on_subset | force)+
done

lemma homotopic_into_retract:
   "\<lbrakk>f ` S \<subseteq> T; g ` S \<subseteq> T; T retract_of U; homotopic_with (\<lambda>x. True) S U f g\<rbrakk>
        \<Longrightarrow> homotopic_with (\<lambda>x. True) S T f g"
apply (subst (asm) homotopic_with_def)
apply (simp add: homotopic_with retract_of_def retraction_def, clarify)
apply (rule_tac x="r \<circ> h" in exI)
apply (rule conjI continuous_intros | erule continuous_on_subset | force simp: image_subset_iff)+
done

lemma retract_of_locally_connected:
  assumes "locally connected T" "S retract_of T"
  shows "locally connected S"
  using assms
  by (auto simp: idempotent_imp_retraction intro!: retraction_imp_quotient_map elim!: locally_connected_quotient_image retract_ofE)

lemma retract_of_locally_path_connected:
  assumes "locally path_connected T" "S retract_of T"
  shows "locally path_connected S"
  using assms
  by (auto simp: idempotent_imp_retraction intro!: retraction_imp_quotient_map elim!: locally_path_connected_quotient_image retract_ofE)

text \<open>A few simple lemmas about deformation retracts\<close>

lemma deformation_retract_imp_homotopy_eqv:
  fixes S :: "'a::euclidean_space set"
  assumes "homotopic_with (\<lambda>x. True) S S id r" and r: "retraction S T r"
  shows "S homotopy_eqv T"
proof -
  have "homotopic_with (\<lambda>x. True) S S (id \<circ> r) id"
    by (simp add: assms(1) homotopic_with_symD)
  moreover have "homotopic_with (\<lambda>x. True) T T (r \<circ> id) id"
    using r unfolding retraction_def
    by (metis (no_types, lifting) comp_id continuous_on_id' homotopic_with_equal homotopic_with_symD id_def image_id order_refl)
  ultimately
  show ?thesis
    unfolding homotopy_eqv_def
    by (metis continuous_on_id' id_def image_id r retraction_def)
qed

lemma deformation_retract:
  fixes S :: "'a::euclidean_space set"
    shows "(\<exists>r. homotopic_with (\<lambda>x. True) S S id r \<and> retraction S T r) \<longleftrightarrow>
           T retract_of S \<and> (\<exists>f. homotopic_with (\<lambda>x. True) S S id f \<and> f ` S \<subseteq> T)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: retract_of_def retraction_def)
next
  assume ?rhs
  then show ?lhs
    apply (clarsimp simp add: retract_of_def retraction_def)
    apply (rule_tac x=r in exI, simp)
     apply (rule homotopic_with_trans, assumption)
     apply (rule_tac f = "r \<circ> f" and g="r \<circ> id" in homotopic_with_eq)
        apply (rule_tac Y=S in homotopic_compose_continuous_left)
         apply (auto simp: homotopic_with_sym)
    done
qed

lemma deformation_retract_of_contractible_sing:
  fixes S :: "'a::euclidean_space set"
  assumes "contractible S" "a \<in> S"
  obtains r where "homotopic_with (\<lambda>x. True) S S id r" "retraction S {a} r"
proof -
  have "{a} retract_of S"
    by (simp add: \<open>a \<in> S\<close>)
  moreover have "homotopic_with (\<lambda>x. True) S S id (\<lambda>x. a)"
      using assms
      by (auto simp: contractible_def continuous_on_const continuous_on_id homotopic_into_contractible image_subset_iff)
  moreover have "(\<lambda>x. a) ` S \<subseteq> {a}"
    by (simp add: image_subsetI)
  ultimately show ?thesis
    using that deformation_retract  by metis
qed


lemma continuous_on_compact_surface_projection_aux:
  fixes S :: "'a::t2_space set"
  assumes "compact S" "S \<subseteq> T" "image q T \<subseteq> S"
      and contp: "continuous_on T p"
      and "\<And>x. x \<in> S \<Longrightarrow> q x = x"
      and [simp]: "\<And>x. x \<in> T \<Longrightarrow> q(p x) = q x"
      and "\<And>x. x \<in> T \<Longrightarrow> p(q x) = p x"
    shows "continuous_on T q"
proof -
  have *: "image p T = image p S"
    using assms by auto (metis imageI subset_iff)
  have contp': "continuous_on S p"
    by (rule continuous_on_subset [OF contp \<open>S \<subseteq> T\<close>])
  have "continuous_on (p ` T) q"
    by (simp add: "*" assms(1) assms(2) assms(5) continuous_on_inv contp' rev_subsetD)
  then have "continuous_on T (q \<circ> p)"
    by (rule continuous_on_compose [OF contp])
  then show ?thesis
    by (rule continuous_on_eq [of _ "q \<circ> p"]) (simp add: o_def)
qed

lemma continuous_on_compact_surface_projection:
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S"
      and S: "S \<subseteq> V - {0}" and "cone V"
      and iff: "\<And>x k. x \<in> V - {0} \<Longrightarrow> 0 < k \<and> (k *\<^sub>R x) \<in> S \<longleftrightarrow> d x = k"
  shows "continuous_on (V - {0}) (\<lambda>x. d x *\<^sub>R x)"
proof (rule continuous_on_compact_surface_projection_aux [OF \<open>compact S\<close> S])
  show "(\<lambda>x. d x *\<^sub>R x) ` (V - {0}) \<subseteq> S"
    using iff by auto
  show "continuous_on (V - {0}) (\<lambda>x. inverse(norm x) *\<^sub>R x)"
    by (intro continuous_intros) force
  show "\<And>x. x \<in> S \<Longrightarrow> d x *\<^sub>R x = x"
    by (metis S zero_less_one local.iff scaleR_one subset_eq)
  show "d (x /\<^sub>R norm x) *\<^sub>R (x /\<^sub>R norm x) = d x *\<^sub>R x" if "x \<in> V - {0}" for x
    using iff [of "inverse(norm x) *\<^sub>R x" "norm x * d x", symmetric] iff that \<open>cone V\<close>
    by (simp add: field_simps cone_def zero_less_mult_iff)
  show "d x *\<^sub>R x /\<^sub>R norm (d x *\<^sub>R x) = x /\<^sub>R norm x" if "x \<in> V - {0}" for x
  proof -
    have "0 < d x"
      using local.iff that by blast
    then show ?thesis
      by simp
  qed
qed

subsection \<open>Absolute Retracts, Absolute Neighbourhood Retracts and Euclidean Neighbourhood Retracts\<close>

text \<open>Absolute retracts (AR), absolute neighbourhood retracts (ANR) and also Euclidean neighbourhood
retracts (ENR). We define AR and ANR by specializing the standard definitions for a set to embedding
in spaces of higher dimension.

John Harrison writes: "This turns out to be sufficient (since any set in \<open>\<real>\<^sup>n\<close> can be
embedded as a closed subset of a convex subset of \<open>\<real>\<^sup>n\<^sup>+\<^sup>1\<close>) to derive the usual
definitions, but we need to split them into two implications because of the lack of type
quantifiers. Then ENR turns out to be equivalent to ANR plus local compactness."\<close>

definition%important AR :: "'a::topological_space set \<Rightarrow> bool" where
"AR S \<equiv> \<forall>U. \<forall>S'::('a * real) set.
  S homeomorphic S' \<and> closedin (subtopology euclidean U) S' \<longrightarrow> S' retract_of U"

definition%important ANR :: "'a::topological_space set \<Rightarrow> bool" where
"ANR S \<equiv> \<forall>U. \<forall>S'::('a * real) set.
  S homeomorphic S' \<and> closedin (subtopology euclidean U) S'
  \<longrightarrow> (\<exists>T. openin (subtopology euclidean U) T \<and> S' retract_of T)"

definition%important ENR :: "'a::topological_space set \<Rightarrow> bool" where
"ENR S \<equiv> \<exists>U. open U \<and> S retract_of U"

text \<open>First, show that we do indeed get the "usual" properties of ARs and ANRs.\<close>

lemma AR_imp_absolute_extensor:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "AR S" and contf: "continuous_on T f" and "f ` T \<subseteq> S"
      and cloUT: "closedin (subtopology euclidean U) T"
  obtains g where "continuous_on U g" "g ` U \<subseteq> S" "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
proof -
  have "aff_dim S < int (DIM('b \<times> real))"
    using aff_dim_le_DIM [of S] by simp
  then obtain C and S' :: "('b * real) set"
          where C: "convex C" "C \<noteq> {}"
            and cloCS: "closedin (subtopology euclidean C) S'"
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
      apply (intro continuous_on_compose f')
       using continuous_on_subset contr f' apply blast
      by (meson \<open>homeomorphism S S' g h\<close> \<open>r ` C \<subseteq> S'\<close> continuous_on_subset \<open>f' ` U \<subseteq> C\<close> homeomorphism_def image_mono)
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
      and clo: "closedin (subtopology euclidean U) S'"
    shows "S' retract_of U"
proof -
  obtain g h where hom: "homeomorphism S S' g h"
    using assms by (force simp: homeomorphic_def)
  have h: "continuous_on S' h" " h ` S' \<subseteq> S"
    using hom homeomorphism_def apply blast
    apply (metis hom equalityE homeomorphism_def)
    done
  obtain h' where h': "continuous_on U h'" "h' ` U \<subseteq> S"
              and h'h: "\<And>x. x \<in> S' \<Longrightarrow> h' x = h x"
    by (blast intro: AR_imp_absolute_extensor [OF \<open>AR S\<close> h clo])
  have [simp]: "S' \<subseteq> U" using clo closedin_limpt by blast
  show ?thesis
  proof (simp add: retraction_def retract_of_def, intro exI conjI)
    show "continuous_on U (g \<circ> h')"
      apply (intro continuous_on_compose h')
      apply (meson hom continuous_on_subset h' homeomorphism_cont1)
      done
    show "(g \<circ> h') ` U \<subseteq> S'"
      using h'  by clarsimp (metis hom subsetD homeomorphism_def imageI)
    show "\<forall>x\<in>S'. (g \<circ> h') x = x"
      by clarsimp (metis h'h hom homeomorphism_def)
  qed
qed

lemma AR_imp_absolute_retract_UNIV:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "AR S" and hom: "S homeomorphic S'"
      and clo: "closed S'"
    shows "S' retract_of UNIV"
apply (rule AR_imp_absolute_retract [OF \<open>AR S\<close> hom])
using clo closed_closedin by auto

lemma absolute_extensor_imp_AR:
  fixes S :: "'a::euclidean_space set"
  assumes "\<And>f :: 'a * real \<Rightarrow> 'a.
           \<And>U T. \<lbrakk>continuous_on T f;  f ` T \<subseteq> S;
                  closedin (subtopology euclidean U) T\<rbrakk>
                 \<Longrightarrow> \<exists>g. continuous_on U g \<and> g ` U \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)"
  shows "AR S"
proof (clarsimp simp: AR_def)
  fix U and T :: "('a * real) set"
  assume "S homeomorphic T" and clo: "closedin (subtopology euclidean U) T"
  then obtain g h where hom: "homeomorphism S T g h"
    by (force simp: homeomorphic_def)
  have h: "continuous_on T h" " h ` T \<subseteq> S"
    using hom homeomorphism_def apply blast
    apply (metis hom equalityE homeomorphism_def)
    done
  obtain h' where h': "continuous_on U h'" "h' ` U \<subseteq> S"
              and h'h: "\<forall>x\<in>T. h' x = h x"
    using assms [OF h clo] by blast
  have [simp]: "T \<subseteq> U"
    using clo closedin_imp_subset by auto
  show "T retract_of U"
  proof (simp add: retraction_def retract_of_def, intro exI conjI)
    show "continuous_on U (g \<circ> h')"
      apply (intro continuous_on_compose h')
      apply (meson hom continuous_on_subset h' homeomorphism_cont1)
      done
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
               closedin (subtopology euclidean U) T \<longrightarrow>
                (\<exists>g. continuous_on U g \<and> g ` U \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)))"
apply (rule iffI)
 apply (metis AR_imp_absolute_extensor)
apply (simp add: absolute_extensor_imp_AR)
done

lemma AR_imp_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "AR S \<and> closedin (subtopology euclidean U) S"
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
      and cloUT: "closedin (subtopology euclidean U) T"
  obtains V g where "T \<subseteq> V" "openin (subtopology euclidean U) V"
                    "continuous_on V g"
                    "g ` V \<subseteq> S" "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
proof -
  have "aff_dim S < int (DIM('b \<times> real))"
    using aff_dim_le_DIM [of S] by simp
  then obtain C and S' :: "('b * real) set"
          where C: "convex C" "C \<noteq> {}"
            and cloCS: "closedin (subtopology euclidean C) S'"
            and hom: "S homeomorphic S'"
    by (metis that homeomorphic_closedin_convex)
  then obtain D where opD: "openin (subtopology euclidean C) D" and "S' retract_of D"
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
    show ope: "openin (subtopology euclidean U) (U \<inter> f' -` D)"
      using  \<open>f' ` U \<subseteq> C\<close> by (auto simp: opD contf' continuous_openin_preimage)
    have conth: "continuous_on (r ` f' ` (U \<inter> f' -` D)) h"
      apply (rule continuous_on_subset [of S'])
      using homeomorphism_def homgh apply blast
      using \<open>r ` D \<subseteq> S'\<close> by blast
    show "continuous_on (U \<inter> f' -` D) (h \<circ> r \<circ> f')"
      apply (intro continuous_on_compose conth
                   continuous_on_subset [OF contr] continuous_on_subset [OF contf'], auto)
      done
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
      and clo: "closedin (subtopology euclidean U) S'"
  obtains V where "openin (subtopology euclidean U) V" "S' retract_of V"
proof -
  obtain g h where hom: "homeomorphism S S' g h"
    using assms by (force simp: homeomorphic_def)
  have h: "continuous_on S' h" " h ` S' \<subseteq> S"
    using hom homeomorphism_def apply blast
    apply (metis hom equalityE homeomorphism_def)
    done
    from ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> h clo]
  obtain V h' where "S' \<subseteq> V" and opUV: "openin (subtopology euclidean U) V"
                and h': "continuous_on V h'" "h' ` V \<subseteq> S"
                and h'h:"\<And>x. x \<in> S' \<Longrightarrow> h' x = h x"
    by (blast intro: ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> h clo])
  have "S' retract_of V"
  proof (simp add: retraction_def retract_of_def, intro exI conjI \<open>S' \<subseteq> V\<close>)
    show "continuous_on V (g \<circ> h')"
      apply (intro continuous_on_compose h')
      apply (meson hom continuous_on_subset h' homeomorphism_cont1)
      done
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
                  closedin (subtopology euclidean U) T\<rbrakk>
                 \<Longrightarrow> \<exists>V g. T \<subseteq> V \<and> openin (subtopology euclidean U) V \<and>
                       continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)"
  shows "ANR S"
proof (clarsimp simp: ANR_def)
  fix U and T :: "('a * real) set"
  assume "S homeomorphic T" and clo: "closedin (subtopology euclidean U) T"
  then obtain g h where hom: "homeomorphism S T g h"
    by (force simp: homeomorphic_def)
  have h: "continuous_on T h" " h ` T \<subseteq> S"
    using hom homeomorphism_def apply blast
    apply (metis hom equalityE homeomorphism_def)
    done
  obtain V h' where "T \<subseteq> V" and opV: "openin (subtopology euclidean U) V"
                and h': "continuous_on V h'" "h' ` V \<subseteq> S"
              and h'h: "\<forall>x\<in>T. h' x = h x"
    using assms [OF h clo] by blast
  have [simp]: "T \<subseteq> U"
    using clo closedin_imp_subset by auto
  have "T retract_of V"
  proof (simp add: retraction_def retract_of_def, intro exI conjI \<open>T \<subseteq> V\<close>)
    show "continuous_on V (g \<circ> h')"
      apply (intro continuous_on_compose h')
      apply (meson hom continuous_on_subset h' homeomorphism_cont1)
      done
    show "(g \<circ> h') ` V \<subseteq> T"
      using h'  by clarsimp (metis hom subsetD homeomorphism_def imageI)
    show "\<forall>x\<in>T. (g \<circ> h') x = x"
      by clarsimp (metis h'h hom homeomorphism_def)
  qed
  then show "\<exists>V. openin (subtopology euclidean U) V \<and> T retract_of V"
    using opV by blast
qed

lemma ANR_eq_absolute_neighbourhood_extensor:
  fixes S :: "'a::euclidean_space set"
  shows "ANR S \<longleftrightarrow>
         (\<forall>f :: 'a * real \<Rightarrow> 'a.
          \<forall>U T. continuous_on T f \<longrightarrow> f ` T \<subseteq> S \<longrightarrow>
                closedin (subtopology euclidean U) T \<longrightarrow>
               (\<exists>V g. T \<subseteq> V \<and> openin (subtopology euclidean U) V \<and>
                       continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x \<in> T. g x = f x)))"
apply (rule iffI)
 apply (metis ANR_imp_absolute_neighbourhood_extensor)
apply (simp add: absolute_neighbourhood_extensor_imp_ANR)
done

lemma ANR_imp_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S" "closedin (subtopology euclidean U) S"
  obtains V where "openin (subtopology euclidean U) V" "S retract_of V"
using ANR_imp_absolute_neighbourhood_retract assms homeomorphic_refl by blast

lemma ANR_imp_absolute_closed_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ANR S" "S homeomorphic S'" and US': "closedin (subtopology euclidean U) S'"
  obtains V W
    where "openin (subtopology euclidean U) V"
          "closedin (subtopology euclidean U) W"
          "S' \<subseteq> V" "V \<subseteq> W" "S' retract_of W"
proof -
  obtain Z where "openin (subtopology euclidean U) Z" and S'Z: "S' retract_of Z"
    by (blast intro: assms ANR_imp_absolute_neighbourhood_retract)
  then have UUZ: "closedin (subtopology euclidean U) (U - Z)"
    by auto
  have "S' \<inter> (U - Z) = {}"
    using \<open>S' retract_of Z\<close> closedin_retract closedin_subtopology by fastforce
  then obtain V W
      where "openin (subtopology euclidean U) V"
        and "openin (subtopology euclidean U) W"
        and "S' \<subseteq> V" "U - Z \<subseteq> W" "V \<inter> W = {}"
      using separation_normal_local [OF US' UUZ]  by auto
  moreover have "S' retract_of U - W"
    apply (rule retract_of_subset [OF S'Z])
    using US' \<open>S' \<subseteq> V\<close> \<open>V \<inter> W = {}\<close> closedin_subset apply fastforce
    using Diff_subset_conv \<open>U - Z \<subseteq> W\<close> by blast
  ultimately show ?thesis
    apply (rule_tac V=V and W = "U-W" in that)
    using openin_imp_subset apply force+
    done
qed

lemma ANR_imp_closed_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set"
  assumes "ANR S" "closedin (subtopology euclidean U) S"
  obtains V W where "openin (subtopology euclidean U) V"
                    "closedin (subtopology euclidean U) W"
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

subsubsection \<open>Analogous properties of ENRs\<close>

lemma ENR_imp_absolute_neighbourhood_retract:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "ENR S" and hom: "S homeomorphic S'"
      and "S' \<subseteq> U"
  obtains V where "openin (subtopology euclidean U) V" "S' retract_of V"
proof -
  obtain X where "open X" "S retract_of X"
    using \<open>ENR S\<close> by (auto simp: ENR_def)
  then obtain r where "retraction X S r"
    by (auto simp: retract_of_def)
  have "locally compact S'"
    using retract_of_locally_compact open_imp_locally_compact
          homeomorphic_local_compactness \<open>S retract_of X\<close> \<open>open X\<close> hom by blast
  then obtain W where UW: "openin (subtopology euclidean U) W"
                  and WS': "closedin (subtopology euclidean W) S'"
    apply (rule locally_compact_closedin_open)
    apply (rename_tac W)
    apply (rule_tac W = "U \<inter> W" in that, blast)
    by (simp add: \<open>S' \<subseteq> U\<close> closedin_limpt)
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
        apply (rule continuous_on_subset [of S])
         using hom homeomorphism_def apply blast
        apply clarify
        apply (meson \<open>retraction X S r\<close> subsetD imageI retraction_def)
        done
    qed
    show "(f \<circ> r \<circ> h) ` (W \<inter> h -` X) \<subseteq> S'"
      using \<open>retraction X S r\<close> hom
      by (auto simp: retraction_def homeomorphism_def)
    show "\<forall>x\<in>S'. (f \<circ> r \<circ> h) x = x"
      using \<open>retraction X S r\<close> hom by (auto simp: retraction_def homeomorphism_def hg)
  qed
  then show ?thesis
    apply (rule_tac V = "W \<inter> h -` X" in that)
     apply (rule openin_trans [OF _ UW])
     using \<open>continuous_on W h\<close> \<open>open X\<close> continuous_openin_preimage_eq apply blast+
     done
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
apply (rule homeomorphic_ENR_iff_ENR)
using assms homeomorphic_sym linear_homeomorphic_image by auto

text \<open>Some relations among the concepts. We also relate AR to being a retract of UNIV, which is
often a more convenient proxy in the closed case.\<close>

lemma AR_imp_ANR: "AR S \<Longrightarrow> ANR S"
  using ANR_def AR_def by fastforce

lemma ENR_imp_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "ENR S \<Longrightarrow> ANR S"
apply (simp add: ANR_def)
by (metis ENR_imp_absolute_neighbourhood_retract closedin_imp_subset)

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
    apply (simp add: ANR_def)
    apply (drule_tac x=UNIV in spec)
    apply (drule_tac x=T in spec, clarsimp)
    apply (meson ENR_def ENR_homeomorphic_ENR open_openin)
    done
qed


lemma AR_ANR:
  fixes S :: "'a::euclidean_space set"
  shows "AR S \<longleftrightarrow> ANR S \<and> contractible S \<and> S \<noteq> {}"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  obtain C and S' :: "('a * real) set"
    where "convex C" "C \<noteq> {}" "closedin (subtopology euclidean C) S'" "S homeomorphic S'"
      apply (rule homeomorphic_closedin_convex [of S, where 'n = "'a * real"])
      using aff_dim_le_DIM [of S] by auto
  with \<open>AR S\<close> have "contractible S"
    apply (simp add: AR_def)
    apply (drule_tac x=C in spec)
    apply (drule_tac x="S'" in spec, simp)
    using convex_imp_contractible homeomorphic_contractible_eq retract_of_contractible by fastforce
  with \<open>AR S\<close> show ?rhs
    apply (auto simp: AR_imp_ANR)
    apply (force simp: AR_def)
    done
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
            and WT: "closedin (subtopology euclidean W) T"
         for W T and f :: "'a \<times> real \<Rightarrow> 'a"
  proof -
    obtain U g
      where "T \<subseteq> U" and WU: "openin (subtopology euclidean W) U"
        and contg: "continuous_on U g"
        and "g ` U \<subseteq> S" and gf: "\<And>x. x \<in> T \<Longrightarrow> g x = f x"
      using iffD1 [OF ANR_eq_absolute_neighbourhood_extensor \<open>ANR S\<close>, rule_format, OF f WT]
      by auto
    have WWU: "closedin (subtopology euclidean W) (W - U)"
      using WU closedin_diff by fastforce
    moreover have "(W - U) \<inter> T = {}"
      using \<open>T \<subseteq> U\<close> by auto
    ultimately obtain V V'
      where WV': "openin (subtopology euclidean W) V'"
        and WV: "openin (subtopology euclidean W) V"
        and "W - U \<subseteq> V'" "T \<subseteq> V" "V' \<inter> V = {}"
      using separation_normal_local [of W "W-U" T] WT by blast
    then have WVT: "T \<inter> (W - V) = {}"
      by auto
    have WWV: "closedin (subtopology euclidean W) (W - V)"
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
        apply (rule continuous_on_compose2 [OF conth continuous_on_Pair])
          apply (rule continuous_on_subset [OF contj Diff_subset])
         apply (rule continuous_on_subset [OF contg])
         apply (metis Diff_subset_conv Un_commute \<open>W - U \<subseteq> V'\<close>)
        using j \<open>g ` U \<subseteq> S\<close> \<open>W - U \<subseteq> V'\<close> apply fastforce
        done
      show "continuous_on W (\<lambda>x. if x \<in> W - V then a else h (j x, g x))"
        apply (subst Weq)
        apply (rule continuous_on_cases_local)
            apply (simp_all add: Weq [symmetric] WWV continuous_on_const *)
          using WV' closedin_diff apply fastforce
         apply (auto simp: j0 j1)
        done
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
  assumes "ANR T" "S retract_of T"
  shows "ANR S"
using assms
apply (simp add: ANR_eq_absolute_neighbourhood_extensor retract_of_def retraction_def)
apply (clarsimp elim!: all_forward)
apply (erule impCE, metis subset_trans)
apply (clarsimp elim!: ex_forward)
apply (rule_tac x="r \<circ> g" in exI)
by (metis comp_apply continuous_on_compose continuous_on_subset subsetD imageI image_comp image_mono subset_trans)

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
apply (rule absolute_extensor_imp_AR)
apply (rule Dugundji, assumption+)
by blast

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
  assumes "closedin (subtopology euclidean U) S"
          "closedin (subtopology euclidean U) T"
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
  have US': "closedin (subtopology euclidean U) S'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} S - setdist {x} T" "{..0}"]
    by (simp add: S'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have UT': "closedin (subtopology euclidean U) T'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} T - setdist {x} S" "{..0}"]
    by (simp add: T'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have "S \<subseteq> S'"
    using S'_def \<open>S \<subseteq> U\<close> setdist_sing_in_set by fastforce
  have "T \<subseteq> T'"
    using T'_def \<open>T \<subseteq> U\<close> setdist_sing_in_set by fastforce
  have "S \<inter> T \<subseteq> W" "W \<subseteq> U"
    using \<open>S \<subseteq> U\<close> by (auto simp: W_def setdist_sing_in_set)
  have "(S \<inter> T) retract_of W"
    apply (rule AR_imp_absolute_retract [OF \<open>AR(S \<inter> T)\<close>])
     apply (simp add: homeomorphic_refl)
    apply (rule closedin_subset_trans [of U])
    apply (simp_all add: assms closedin_Int \<open>S \<inter> T \<subseteq> W\<close> \<open>W \<subseteq> U\<close>)
    done
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
  then have cloUW: "closedin (subtopology euclidean U) W"
    using closedin_Int US' UT' by blast
  define r where "r \<equiv> \<lambda>x. if x \<in> W then r0 x else x"
  have "r ` (W \<union> S) \<subseteq> S" "r ` (W \<union> T) \<subseteq> T"
    using \<open>r0 ` W \<subseteq> S \<inter> T\<close> r_def by auto
  have contr: "continuous_on (W \<union> (S \<union> T)) r"
  unfolding r_def
  proof (rule continuous_on_cases_local [OF _ _ contr0 continuous_on_id])
    show "closedin (subtopology euclidean (W \<union> (S \<union> T))) W"
      using \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> \<open>W \<subseteq> U\<close> \<open>closedin (subtopology euclidean U) W\<close> closedin_subset_trans by fastforce
    show "closedin (subtopology euclidean (W \<union> (S \<union> T))) (S \<union> T)"
      by (meson \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> \<open>W \<subseteq> U\<close> assms closedin_Un closedin_subset_trans sup.bounded_iff sup.cobounded2)
    show "\<And>x. x \<in> W \<and> x \<notin> W \<or> x \<in> S \<union> T \<and> x \<in> W \<Longrightarrow> r0 x = x"
      by (auto simp: ST)
  qed
  have cloUWS: "closedin (subtopology euclidean U) (W \<union> S)"
    by (simp add: cloUW assms closedin_Un)
  obtain g where contg: "continuous_on U g"
             and "g ` U \<subseteq> S" and geqr: "\<And>x. x \<in> W \<union> S \<Longrightarrow> g x = r x"
    apply (rule AR_imp_absolute_extensor [OF \<open>AR S\<close> _ _ cloUWS])
      apply (rule continuous_on_subset [OF contr])
      using \<open>r ` (W \<union> S) \<subseteq> S\<close> apply auto
    done
  have cloUWT: "closedin (subtopology euclidean U) (W \<union> T)"
    by (simp add: cloUW assms closedin_Un)
  obtain h where conth: "continuous_on U h"
             and "h ` U \<subseteq> T" and heqr: "\<And>x. x \<in> W \<union> T \<Longrightarrow> h x = r x"
    apply (rule AR_imp_absolute_extensor [OF \<open>AR T\<close> _ _ cloUWT])
      apply (rule continuous_on_subset [OF contr])
      using \<open>r ` (W \<union> T) \<subseteq> T\<close> apply auto
    done
  have "U = S' \<union> T'"
    by (force simp: S'_def T'_def)
  then have cont: "continuous_on U (\<lambda>x. if x \<in> S' then g x else h x)"
    apply (rule ssubst)
    apply (rule continuous_on_cases_local)
    using US' UT' \<open>S' \<inter> T' = W\<close> \<open>U = S' \<union> T'\<close>
          contg conth continuous_on_subset geqr heqr apply auto
    done
  have UST: "(\<lambda>x. if x \<in> S' then g x else h x) ` U \<subseteq> S \<union> T"
    using \<open>g ` U \<subseteq> S\<close> \<open>h ` U \<subseteq> T\<close> by auto
  show ?thesis
    apply (simp add: retract_of_def retraction_def \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close>)
    apply (rule_tac x="\<lambda>x. if x \<in> S' then g x else h x" in exI)
    apply (intro conjI cont UST)
    by (metis IntI ST Un_iff \<open>S \<subseteq> S'\<close> \<open>S' \<inter> T' = W\<close> \<open>T \<subseteq> T'\<close> subsetD geqr heqr r0 r_def)
qed


lemma AR_closed_Un_local:
  fixes S :: "'a::euclidean_space set"
  assumes STS: "closedin (subtopology euclidean (S \<union> T)) S"
      and STT: "closedin (subtopology euclidean (S \<union> T)) T"
      and "AR S" "AR T" "AR(S \<inter> T)"
    shows "AR(S \<union> T)"
proof -
  have "C retract_of U"
       if hom: "S \<union> T homeomorphic C" and UC: "closedin (subtopology euclidean U) C"
       for U and C :: "('a * real) set"
  proof -
    obtain f g where hom: "homeomorphism (S \<union> T) C f g"
      using hom by (force simp: homeomorphic_def)
    have US: "closedin (subtopology euclidean U) (C \<inter> g -` S)"
      apply (rule closedin_trans [OF _ UC])
      apply (rule continuous_closedin_preimage_gen [OF _ _ STS])
      using hom homeomorphism_def apply blast
      apply (metis hom homeomorphism_def set_eq_subset)
      done
    have UT: "closedin (subtopology euclidean U) (C \<inter> g -` T)"
      apply (rule closedin_trans [OF _ UC])
      apply (rule continuous_closedin_preimage_gen [OF _ _ STT])
      using hom homeomorphism_def apply blast
      apply (metis hom homeomorphism_def set_eq_subset)
      done
    have ARS: "AR (C \<inter> g -` S)"
      apply (rule AR_homeomorphic_AR [OF \<open>AR S\<close>])
      apply (simp add: homeomorphic_def)
      apply (rule_tac x=g in exI)
      apply (rule_tac x=f in exI)
      using hom apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    have ART: "AR (C \<inter> g -` T)"
      apply (rule AR_homeomorphic_AR [OF \<open>AR T\<close>])
      apply (simp add: homeomorphic_def)
      apply (rule_tac x=g in exI)
      apply (rule_tac x=f in exI)
      using hom apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    have ARI: "AR ((C \<inter> g -` S) \<inter> (C \<inter> g -` T))"
      apply (rule AR_homeomorphic_AR [OF \<open>AR (S \<inter> T)\<close>])
      apply (simp add: homeomorphic_def)
      apply (rule_tac x=g in exI)
      apply (rule_tac x=f in exI)
      using hom
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
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
  assumes US: "closedin (subtopology euclidean U) S"
      and UT: "closedin (subtopology euclidean U) T"
      and "ANR S" "ANR T" "ANR(S \<inter> T)"
  obtains V where "openin (subtopology euclidean U) V" "(S \<union> T) retract_of V"
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
  have cloUS': "closedin (subtopology euclidean U) S'"
    using continuous_closedin_preimage [of U "\<lambda>x. setdist {x} S - setdist {x} T" "{..0}"]
    by (simp add: S'_def vimage_def Collect_conj_eq continuous_on_diff continuous_on_setdist)
  have cloUT': "closedin (subtopology euclidean U) T'"
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
  then have cloUW: "closedin (subtopology euclidean U) W"
    using closedin_Int cloUS' cloUT' by blast
  obtain W' W0 where "openin (subtopology euclidean W) W'"
                 and cloWW0: "closedin (subtopology euclidean W) W0"
                 and "S \<inter> T \<subseteq> W'" "W' \<subseteq> W0"
                 and ret: "(S \<inter> T) retract_of W0"
    apply (rule ANR_imp_closed_neighbourhood_retract [OF \<open>ANR(S \<inter> T)\<close>])
    apply (rule closedin_subset_trans [of U, OF _ ST_W \<open>W \<subseteq> U\<close>])
    apply (blast intro: assms)+
    done
  then obtain U0 where opeUU0: "openin (subtopology euclidean U) U0"
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
    show "closedin (subtopology euclidean (W0 \<union> (S \<union> T))) W0"
      apply (rule closedin_subset_trans [of U])
      using cloWW0 cloUW closedin_trans \<open>W0 \<subseteq> U\<close> \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> apply blast+
      done
    show "closedin (subtopology euclidean (W0 \<union> (S \<union> T))) (S \<union> T)"
      by (meson \<open>S \<subseteq> U\<close> \<open>T \<subseteq> U\<close> \<open>W0 \<subseteq> U\<close> assms closedin_Un closedin_subset_trans sup.bounded_iff sup.cobounded2)
    show "\<And>x. x \<in> W0 \<and> x \<notin> W0 \<or> x \<in> S \<union> T \<and> x \<in> W0 \<Longrightarrow> r0 x = x"
      using ST cloWW0 closedin_subset by fastforce
  qed
  have cloS'WS: "closedin (subtopology euclidean S') (W0 \<union> S)"
    by (meson closedin_subset_trans US cloUS' \<open>S \<subseteq> S'\<close> \<open>W \<subseteq> S'\<close> cloUW cloWW0 
              closedin_Un closedin_imp_subset closedin_trans)
  obtain W1 g where "W0 \<union> S \<subseteq> W1" and contg: "continuous_on W1 g"
                and opeSW1: "openin (subtopology euclidean S') W1"
                and "g ` W1 \<subseteq> S" and geqr: "\<And>x. x \<in> W0 \<union> S \<Longrightarrow> g x = r x"
    apply (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> _ \<open>r ` (W0 \<union> S) \<subseteq> S\<close> cloS'WS])
     apply (rule continuous_on_subset [OF contr], blast+)
    done
  have cloT'WT: "closedin (subtopology euclidean T') (W0 \<union> T)"
    by (meson closedin_subset_trans UT cloUT' \<open>T \<subseteq> T'\<close> \<open>W \<subseteq> T'\<close> cloUW cloWW0 
              closedin_Un closedin_imp_subset closedin_trans)
  obtain W2 h where "W0 \<union> T \<subseteq> W2" and conth: "continuous_on W2 h"
                and opeSW2: "openin (subtopology euclidean T') W2"
                and "h ` W2 \<subseteq> T" and heqr: "\<And>x. x \<in> W0 \<union> T \<Longrightarrow> h x = r x"
    apply (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR T\<close> _ \<open>r ` (W0 \<union> T) \<subseteq> T\<close> cloT'WT])
     apply (rule continuous_on_subset [OF contr], blast+)
    done
  have "S' \<inter> T' = W"
    by (force simp: S'_def T'_def W_def)
  obtain O1 O2 where "open O1" "W1 = S' \<inter> O1" "open O2" "W2 = T' \<inter> O2"
    using opeSW1 opeSW2 by (force simp: openin_open)
  show ?thesis
  proof
    have eq: "W1 - (W - U0) \<union> (W2 - (W - U0)) =
         ((U - T') \<inter> O1 \<union> (U - S') \<inter> O2 \<union> U \<inter> O1 \<inter> O2) - (W - U0)"
     using \<open>U0 \<inter> W \<subseteq> W0\<close> \<open>W0 \<union> S \<subseteq> W1\<close> \<open>W0 \<union> T \<subseteq> W2\<close>
      by (auto simp: \<open>S' \<union> T' = U\<close> [symmetric] \<open>S' \<inter> T' = W\<close> [symmetric] \<open>W1 = S' \<inter> O1\<close> \<open>W2 = T' \<inter> O2\<close>)
    show "openin (subtopology euclidean U) (W1 - (W - U0) \<union> (W2 - (W - U0)))"
      apply (subst eq)
      apply (intro openin_Un openin_Int_open openin_diff closedin_diff cloUW opeUU0 cloUS' cloUT' \<open>open O1\<close> \<open>open O2\<close>, simp_all)
      done
    have cloW1: "closedin (subtopology euclidean (W1 - (W - U0) \<union> (W2 - (W - U0)))) (W1 - (W - U0))"
      using cloUS' apply (simp add: closedin_closed)
      apply (erule ex_forward)
      using U0 \<open>W0 \<union> S \<subseteq> W1\<close>
      apply (auto simp: \<open>W1 = S' \<inter> O1\<close> \<open>W2 = T' \<inter> O2\<close> \<open>S' \<union> T' = U\<close> [symmetric]\<open>S' \<inter> T' = W\<close> [symmetric])
      done
    have cloW2: "closedin (subtopology euclidean (W1 - (W - U0) \<union> (W2 - (W - U0)))) (W2 - (W - U0))"
      using cloUT' apply (simp add: closedin_closed)
      apply (erule ex_forward)
      using U0 \<open>W0 \<union> T \<subseteq> W2\<close>
      apply (auto simp: \<open>W1 = S' \<inter> O1\<close> \<open>W2 = T' \<inter> O2\<close> \<open>S' \<union> T' = U\<close> [symmetric]\<open>S' \<inter> T' = W\<close> [symmetric])
      done
    have *: "\<forall>x\<in>S \<union> T. (if x \<in> S' then g x else h x) = x"
      using ST \<open>S' \<inter> T' = W\<close> cloT'WT closedin_subset geqr heqr 
      apply (auto simp: r_def, fastforce)
      using \<open>S \<subseteq> S'\<close> \<open>T \<subseteq> T'\<close> \<open>W0 \<union> S \<subseteq> W1\<close> \<open>W1 = S' \<inter> O1\<close>  by auto
    have "\<exists>r. continuous_on (W1 - (W - U0) \<union> (W2 - (W - U0))) r \<and>
              r ` (W1 - (W - U0) \<union> (W2 - (W - U0))) \<subseteq> S \<union> T \<and> 
              (\<forall>x\<in>S \<union> T. r x = x)"
      apply (rule_tac x = "\<lambda>x. if  x \<in> S' then g x else h x" in exI)
      apply (intro conjI *)
      apply (rule continuous_on_cases_local 
                  [OF cloW1 cloW2 continuous_on_subset [OF contg] continuous_on_subset [OF conth]])
      using \<open>W1 = S' \<inter> O1\<close> \<open>W2 = T' \<inter> O2\<close> \<open>S' \<inter> T' = W\<close>
            \<open>g ` W1 \<subseteq> S\<close> \<open>h ` W2 \<subseteq> T\<close> apply auto
      using \<open>U0 \<inter> W \<subseteq> W0\<close> \<open>W0 \<union> S \<subseteq> W1\<close> apply (fastforce simp add: geqr heqr)+
      done
    then show "S \<union> T retract_of W1 - (W - U0) \<union> (W2 - (W - U0))"
      using  \<open>W0 \<union> S \<subseteq> W1\<close> \<open>W0 \<union> T \<subseteq> W2\<close> ST opeUU0 U0
      by (auto simp: retract_of_def retraction_def)
  qed
qed


lemma ANR_closed_Un_local:
  fixes S :: "'a::euclidean_space set"
  assumes STS: "closedin (subtopology euclidean (S \<union> T)) S"
      and STT: "closedin (subtopology euclidean (S \<union> T)) T"
      and "ANR S" "ANR T" "ANR(S \<inter> T)" 
    shows "ANR(S \<union> T)"
proof -
  have "\<exists>T. openin (subtopology euclidean U) T \<and> C retract_of T"
       if hom: "S \<union> T homeomorphic C" and UC: "closedin (subtopology euclidean U) C"
       for U and C :: "('a * real) set"
  proof -
    obtain f g where hom: "homeomorphism (S \<union> T) C f g"
      using hom by (force simp: homeomorphic_def)
    have US: "closedin (subtopology euclidean U) (C \<inter> g -` S)"
      apply (rule closedin_trans [OF _ UC])
      apply (rule continuous_closedin_preimage_gen [OF _ _ STS])
      using hom [unfolded homeomorphism_def] apply blast
      apply (metis hom homeomorphism_def set_eq_subset)
      done
    have UT: "closedin (subtopology euclidean U) (C \<inter> g -` T)"
      apply (rule closedin_trans [OF _ UC])
      apply (rule continuous_closedin_preimage_gen [OF _ _ STT])
      using hom [unfolded homeomorphism_def] apply blast
      apply (metis hom homeomorphism_def set_eq_subset)
      done
    have ANRS: "ANR (C \<inter> g -` S)"
      apply (rule ANR_homeomorphic_ANR [OF \<open>ANR S\<close>])
      apply (simp add: homeomorphic_def)
      apply (rule_tac x=g in exI)
      apply (rule_tac x=f in exI)
      using hom apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    have ANRT: "ANR (C \<inter> g -` T)"
      apply (rule ANR_homeomorphic_ANR [OF \<open>ANR T\<close>])
      apply (simp add: homeomorphic_def)
      apply (rule_tac x=g in exI)
      apply (rule_tac x=f in exI)
      using hom apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
    have ANRI: "ANR ((C \<inter> g -` S) \<inter> (C \<inter> g -` T))"
      apply (rule ANR_homeomorphic_ANR [OF \<open>ANR (S \<inter> T)\<close>])
      apply (simp add: homeomorphic_def)
      apply (rule_tac x=g in exI)
      apply (rule_tac x=f in exI)
      using hom
      apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
      apply (rule_tac x="f x" in image_eqI, auto)
      done
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
  assumes "ANR T" and opeTS: "openin (subtopology euclidean T) S"
  shows "ANR S"
proof (clarsimp simp only: ANR_eq_absolute_neighbourhood_extensor)
  fix f :: "'a \<times> real \<Rightarrow> 'a" and U C
  assume contf: "continuous_on C f" and fim: "f ` C \<subseteq> S"
     and cloUC: "closedin (subtopology euclidean U) C"
  have "f ` C \<subseteq> T"
    using fim opeTS openin_imp_subset by blast
  obtain W g where "C \<subseteq> W"
               and UW: "openin (subtopology euclidean U) W"
               and contg: "continuous_on W g"
               and gim: "g ` W \<subseteq> T"
               and geq: "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
    apply (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR T\<close> contf \<open>f ` C \<subseteq> T\<close> cloUC])
    using fim by auto
  show "\<exists>V g. C \<subseteq> V \<and> openin (subtopology euclidean U) V \<and> continuous_on V g \<and> g ` V \<subseteq> S \<and> (\<forall>x\<in>C. g x = f x)"
  proof (intro exI conjI)
    show "C \<subseteq> W \<inter> g -` S"
      using \<open>C \<subseteq> W\<close> fim geq by blast
    show "openin (subtopology euclidean U) (W \<inter> g -` S)"
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
    assumes "ENR T" and opeTS: "openin (subtopology euclidean T) S"
    shows "ENR S"
  using assms apply (simp add: ENR_ANR)
  using ANR_openin locally_open_subset by blast

lemma ANR_neighborhood_retract:
    fixes S :: "'a::euclidean_space set"
    assumes "ANR U" "S retract_of T" "openin (subtopology euclidean U) T"
    shows "ANR S"
  using ANR_openin ANR_retract_of_ANR assms by blast

lemma ENR_neighborhood_retract:
    fixes S :: "'a::euclidean_space set"
    assumes "ENR U" "S retract_of T" "openin (subtopology euclidean U) T"
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
apply (simp add: ENR_convex_closed closed_cbox)
by (simp add: open_box open_imp_ENR)

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
       and UT: "closedin (subtopology euclidean U) T"
       and "S homeomorphic T"
    apply (rule homeomorphic_closedin_convex [of S])
    using aff_dim_le_DIM [of S] apply auto
    done
  then have "locally path_connected T"
    by (meson ANR_imp_absolute_neighbourhood_retract
        assms convex_imp_locally_path_connected locally_open_subset retract_of_locally_path_connected)
  then have S: "locally path_connected S"
      if "openin (subtopology euclidean U) V" "T retract_of V" "U \<noteq> {}" for V
    using \<open>S homeomorphic T\<close> homeomorphic_locally homeomorphic_path_connectedness by blast
  show ?thesis
    using assms
    apply (clarsimp simp: ANR_def)
    apply (drule_tac x=U in spec)
    apply (drule_tac x=T in spec)
    using \<open>S homeomorphic T\<close> \<open>U \<noteq> {}\<close> UT  apply (blast intro: S)
    done
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
     and cloUC: "closedin (subtopology euclidean U) C"
  have contf1: "continuous_on C (fst \<circ> f)"
    by (simp add: \<open>continuous_on C f\<close> continuous_on_fst)
  obtain W1 g where "C \<subseteq> W1"
               and UW1: "openin (subtopology euclidean U) W1"
               and contg: "continuous_on W1 g"
               and gim: "g ` W1 \<subseteq> S"
               and geq: "\<And>x. x \<in> C \<Longrightarrow> g x = (fst \<circ> f) x"
    apply (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR S\<close> contf1 _ cloUC])
    using fim apply auto
    done
  have contf2: "continuous_on C (snd \<circ> f)"
    by (simp add: \<open>continuous_on C f\<close> continuous_on_snd)
  obtain W2 h where "C \<subseteq> W2"
               and UW2: "openin (subtopology euclidean U) W2"
               and conth: "continuous_on W2 h"
               and him: "h ` W2 \<subseteq> T"
               and heq: "\<And>x. x \<in> C \<Longrightarrow> h x = (snd \<circ> f) x"
    apply (rule ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR T\<close> contf2 _ cloUC])
    using fim apply auto
    done
  show "\<exists>V g. C \<subseteq> V \<and>
               openin (subtopology euclidean U) V \<and>
               continuous_on V g \<and> g ` V \<subseteq> S \<times> T \<and> (\<forall>x\<in>C. g x = f x)"
  proof (intro exI conjI)
    show "C \<subseteq> W1 \<inter> W2"
      by (simp add: \<open>C \<subseteq> W1\<close> \<open>C \<subseteq> W2\<close>)
    show "openin (subtopology euclidean U) (W1 \<inter> W2)"
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

subsection \<open>Kuhn Simplices\<close>

lemma bij_betw_singleton_eq:
  assumes f: "bij_betw f A B" and g: "bij_betw g A B" and a: "a \<in> A"
  assumes eq: "(\<And>x. x \<in> A \<Longrightarrow> x \<noteq> a \<Longrightarrow> f x = g x)"
  shows "f a = g a"
proof -
  have "f ` (A - {a}) = g ` (A - {a})"
    by (intro image_cong) (simp_all add: eq)
  then have "B - {f a} = B - {g a}"
    using f g a  by (auto simp: bij_betw_def inj_on_image_set_diff set_eq_iff)
  moreover have "f a \<in> B" "g a \<in> B"
    using f g a by (auto simp: bij_betw_def)
  ultimately show ?thesis
    by auto
qed

lemma swap_image:
  "Fun.swap i j f ` A = (if i \<in> A then (if j \<in> A then f ` A else f ` ((A - {i}) \<union> {j}))
                                  else (if j \<in> A then f ` ((A - {j}) \<union> {i}) else f ` A))"
  by (auto simp: swap_def cong: image_cong_simp)

lemmas swap_apply1 = swap_apply(1)
lemmas swap_apply2 = swap_apply(2)

lemma pointwise_minimal_pointwise_maximal:
  fixes s :: "(nat \<Rightarrow> nat) set"
  assumes "finite s"
    and "s \<noteq> {}"
    and "\<forall>x\<in>s. \<forall>y\<in>s. x \<le> y \<or> y \<le> x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. a \<le> x"
    and "\<exists>a\<in>s. \<forall>x\<in>s. x \<le> a"
  using assms
proof (induct s rule: finite_ne_induct)
  case (insert b s)
  assume *: "\<forall>x\<in>insert b s. \<forall>y\<in>insert b s. x \<le> y \<or> y \<le> x"
  then obtain u l where "l \<in> s" "\<forall>b\<in>s. l \<le> b" "u \<in> s" "\<forall>b\<in>s. b \<le> u"
    using insert by auto
  with * show "\<exists>a\<in>insert b s. \<forall>x\<in>insert b s. a \<le> x" "\<exists>a\<in>insert b s. \<forall>x\<in>insert b s. x \<le> a"
    using *[rule_format, of b u] *[rule_format, of b l] by (metis insert_iff order.trans)+
qed auto

(* FIXME mv *)
lemma brouwer_compactness_lemma:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "compact s"
    and "continuous_on s f"
    and "\<not> (\<exists>x\<in>s. f x = 0)"
  obtains d where "0 < d" and "\<forall>x\<in>s. d \<le> norm (f x)"
proof (cases "s = {}")
  case True
  show thesis
    by (rule that [of 1]) (auto simp: True)
next
  case False
  have "continuous_on s (norm \<circ> f)"
    by (rule continuous_intros continuous_on_norm assms(2))+
  with False obtain x where x: "x \<in> s" "\<forall>y\<in>s. (norm \<circ> f) x \<le> (norm \<circ> f) y"
    using continuous_attains_inf[OF assms(1), of "norm \<circ> f"]
    unfolding o_def
    by auto
  have "(norm \<circ> f) x > 0"
    using assms(3) and x(1)
    by auto
  then show ?thesis
    by (rule that) (insert x(2), auto simp: o_def)
qed

lemma kuhn_labelling_lemma:
  fixes P Q :: "'a::euclidean_space \<Rightarrow> bool"
  assumes "\<forall>x. P x \<longrightarrow> P (f x)"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i\<in>Basis. Q i \<longrightarrow> 0 \<le> x\<bullet>i \<and> x\<bullet>i \<le> 1)"
  shows "\<exists>l. (\<forall>x.\<forall>i\<in>Basis. l x i \<le> (1::nat)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x\<bullet>i \<le> f x\<bullet>i) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f x\<bullet>i \<le> x\<bullet>i)"
proof -
  { fix x i
    let ?R = "\<lambda>y. (P x \<and> Q i \<and> x \<bullet> i = 0 \<longrightarrow> y = (0::nat)) \<and>
        (P x \<and> Q i \<and> x \<bullet> i = 1 \<longrightarrow> y = 1) \<and>
        (P x \<and> Q i \<and> y = 0 \<longrightarrow> x \<bullet> i \<le> f x \<bullet> i) \<and>
        (P x \<and> Q i \<and> y = 1 \<longrightarrow> f x \<bullet> i \<le> x \<bullet> i)"
    { assume "P x" "Q i" "i \<in> Basis" with assms have "0 \<le> f x \<bullet> i \<and> f x \<bullet> i \<le> 1" by auto }
    then have "i \<in> Basis \<Longrightarrow> ?R 0 \<or> ?R 1" by auto }
  then show ?thesis
    unfolding all_conj_distrib[symmetric] Ball_def (* FIXME: shouldn't this work by metis? *)
    by (subst choice_iff[symmetric])+ blast
qed


subsubsection \<open>The key "counting" observation, somewhat abstracted\<close>

lemma kuhn_counting_lemma:
  fixes bnd compo compo' face S F
  defines "nF s == card {f\<in>F. face f s \<and> compo' f}"
  assumes [simp, intro]: "finite F" \<comment> \<open>faces\<close> and [simp, intro]: "finite S" \<comment> \<open>simplices\<close>
    and "\<And>f. f \<in> F \<Longrightarrow> bnd f \<Longrightarrow> card {s\<in>S. face f s} = 1"
    and "\<And>f. f \<in> F \<Longrightarrow> \<not> bnd f \<Longrightarrow> card {s\<in>S. face f s} = 2"
    and "\<And>s. s \<in> S \<Longrightarrow> compo s \<Longrightarrow> nF s = 1"
    and "\<And>s. s \<in> S \<Longrightarrow> \<not> compo s \<Longrightarrow> nF s = 0 \<or> nF s = 2"
    and "odd (card {f\<in>F. compo' f \<and> bnd f})"
  shows "odd (card {s\<in>S. compo s})"
proof -
  have "(\<Sum>s | s \<in> S \<and> \<not> compo s. nF s) + (\<Sum>s | s \<in> S \<and> compo s. nF s) = (\<Sum>s\<in>S. nF s)"
    by (subst sum.union_disjoint[symmetric]) (auto intro!: sum.cong)
  also have "\<dots> = (\<Sum>s\<in>S. card {f \<in> {f\<in>F. compo' f \<and> bnd f}. face f s}) +
                  (\<Sum>s\<in>S. card {f \<in> {f\<in>F. compo' f \<and> \<not> bnd f}. face f s})"
    unfolding sum.distrib[symmetric]
    by (subst card_Un_disjoint[symmetric])
       (auto simp: nF_def intro!: sum.cong arg_cong[where f=card])
  also have "\<dots> = 1 * card {f\<in>F. compo' f \<and> bnd f} + 2 * card {f\<in>F. compo' f \<and> \<not> bnd f}"
    using assms(4,5) by (fastforce intro!: arg_cong2[where f="(+)"] sum_multicount)
  finally have "odd ((\<Sum>s | s \<in> S \<and> \<not> compo s. nF s) + card {s\<in>S. compo s})"
    using assms(6,8) by simp
  moreover have "(\<Sum>s | s \<in> S \<and> \<not> compo s. nF s) =
    (\<Sum>s | s \<in> S \<and> \<not> compo s \<and> nF s = 0. nF s) + (\<Sum>s | s \<in> S \<and> \<not> compo s \<and> nF s = 2. nF s)"
    using assms(7) by (subst sum.union_disjoint[symmetric]) (fastforce intro!: sum.cong)+
  ultimately show ?thesis
    by auto
qed

subsubsection \<open>The odd/even result for faces of complete vertices, generalized\<close>

lemma kuhn_complete_lemma:
  assumes [simp]: "finite simplices"
    and face: "\<And>f s. face f s \<longleftrightarrow> (\<exists>a\<in>s. f = s - {a})"
    and card_s[simp]:  "\<And>s. s \<in> simplices \<Longrightarrow> card s = n + 2"
    and rl_bd: "\<And>s. s \<in> simplices \<Longrightarrow> rl ` s \<subseteq> {..Suc n}"
    and bnd: "\<And>f s. s \<in> simplices \<Longrightarrow> face f s \<Longrightarrow> bnd f \<Longrightarrow> card {s\<in>simplices. face f s} = 1"
    and nbnd: "\<And>f s. s \<in> simplices \<Longrightarrow> face f s \<Longrightarrow> \<not> bnd f \<Longrightarrow> card {s\<in>simplices. face f s} = 2"
    and odd_card: "odd (card {f. (\<exists>s\<in>simplices. face f s) \<and> rl ` f = {..n} \<and> bnd f})"
  shows "odd (card {s\<in>simplices. (rl ` s = {..Suc n})})"
proof (rule kuhn_counting_lemma)
  have finite_s[simp]: "\<And>s. s \<in> simplices \<Longrightarrow> finite s"
    by (metis add_is_0 zero_neq_numeral card_infinite assms(3))

  let ?F = "{f. \<exists>s\<in>simplices. face f s}"
  have F_eq: "?F = (\<Union>s\<in>simplices. \<Union>a\<in>s. {s - {a}})"
    by (auto simp: face)
  show "finite ?F"
    using \<open>finite simplices\<close> unfolding F_eq by auto

  show "card {s \<in> simplices. face f s} = 1" if "f \<in> ?F" "bnd f" for f
    using bnd that by auto

  show "card {s \<in> simplices. face f s} = 2" if "f \<in> ?F" "\<not> bnd f" for f
    using nbnd that by auto

  show "odd (card {f \<in> {f. \<exists>s\<in>simplices. face f s}. rl ` f = {..n} \<and> bnd f})"
    using odd_card by simp

  fix s assume s[simp]: "s \<in> simplices"
  let ?S = "{f \<in> {f. \<exists>s\<in>simplices. face f s}. face f s \<and> rl ` f = {..n}}"
  have "?S = (\<lambda>a. s - {a}) ` {a\<in>s. rl ` (s - {a}) = {..n}}"
    using s by (fastforce simp: face)
  then have card_S: "card ?S = card {a\<in>s. rl ` (s - {a}) = {..n}}"
    by (auto intro!: card_image inj_onI)

  { assume rl: "rl ` s = {..Suc n}"
    then have inj_rl: "inj_on rl s"
      by (intro eq_card_imp_inj_on) auto
    moreover obtain a where "rl a = Suc n" "a \<in> s"
      by (metis atMost_iff image_iff le_Suc_eq rl)
    ultimately have n: "{..n} = rl ` (s - {a})"
      by (auto simp: inj_on_image_set_diff rl)
    have "{a\<in>s. rl ` (s - {a}) = {..n}} = {a}"
      using inj_rl \<open>a \<in> s\<close> by (auto simp: n inj_on_image_eq_iff[OF inj_rl])
    then show "card ?S = 1"
      unfolding card_S by simp }

  { assume rl: "rl ` s \<noteq> {..Suc n}"
    show "card ?S = 0 \<or> card ?S = 2"
    proof cases
      assume *: "{..n} \<subseteq> rl ` s"
      with rl rl_bd[OF s] have rl_s: "rl ` s = {..n}"
        by (auto simp: atMost_Suc subset_insert_iff split: if_split_asm)
      then have "\<not> inj_on rl s"
        by (intro pigeonhole) simp
      then obtain a b where ab: "a \<in> s" "b \<in> s" "rl a = rl b" "a \<noteq> b"
        by (auto simp: inj_on_def)
      then have eq: "rl ` (s - {a}) = rl ` s"
        by auto
      with ab have inj: "inj_on rl (s - {a})"
        by (intro eq_card_imp_inj_on) (auto simp: rl_s card_Diff_singleton_if)

      { fix x assume "x \<in> s" "x \<notin> {a, b}"
        then have "rl ` s - {rl x} = rl ` ((s - {a}) - {x})"
          by (auto simp: eq inj_on_image_set_diff[OF inj])
        also have "\<dots> = rl ` (s - {x})"
          using ab \<open>x \<notin> {a, b}\<close> by auto
        also assume "\<dots> = rl ` s"
        finally have False
          using \<open>x\<in>s\<close> by auto }
      moreover
      { fix x assume "x \<in> {a, b}" with ab have "x \<in> s \<and> rl ` (s - {x}) = rl ` s"
          by (simp add: set_eq_iff image_iff Bex_def) metis }
      ultimately have "{a\<in>s. rl ` (s - {a}) = {..n}} = {a, b}"
        unfolding rl_s[symmetric] by fastforce
      with \<open>a \<noteq> b\<close> show "card ?S = 0 \<or> card ?S = 2"
        unfolding card_S by simp
    next
      assume "\<not> {..n} \<subseteq> rl ` s"
      then have "\<And>x. rl ` (s - {x}) \<noteq> {..n}"
        by auto
      then show "card ?S = 0 \<or> card ?S = 2"
        unfolding card_S by simp
    qed }
qed fact

locale kuhn_simplex =
  fixes p n and base upd and s :: "(nat \<Rightarrow> nat) set"
  assumes base: "base \<in> {..< n} \<rightarrow> {..< p}"
  assumes base_out: "\<And>i. n \<le> i \<Longrightarrow> base i = p"
  assumes upd: "bij_betw upd {..< n} {..< n}"
  assumes s_pre: "s = (\<lambda>i j. if j \<in> upd`{..< i} then Suc (base j) else base j) ` {.. n}"
begin

definition "enum i j = (if j \<in> upd`{..< i} then Suc (base j) else base j)"

lemma s_eq: "s = enum ` {.. n}"
  unfolding s_pre enum_def[abs_def] ..

lemma upd_space: "i < n \<Longrightarrow> upd i < n"
  using upd by (auto dest!: bij_betwE)

lemma s_space: "s \<subseteq> {..< n} \<rightarrow> {.. p}"
proof -
  { fix i assume "i \<le> n" then have "enum i \<in> {..< n} \<rightarrow> {.. p}"
    proof (induct i)
      case 0 then show ?case
        using base by (auto simp: Pi_iff less_imp_le enum_def)
    next
      case (Suc i) with base show ?case
        by (auto simp: Pi_iff Suc_le_eq less_imp_le enum_def intro: upd_space)
    qed }
  then show ?thesis
    by (auto simp: s_eq)
qed

lemma inj_upd: "inj_on upd {..< n}"
  using upd by (simp add: bij_betw_def)

lemma inj_enum: "inj_on enum {.. n}"
proof -
  { fix x y :: nat assume "x \<noteq> y" "x \<le> n" "y \<le> n"
    with upd have "upd ` {..< x} \<noteq> upd ` {..< y}"
      by (subst inj_on_image_eq_iff[where C="{..< n}"]) (auto simp: bij_betw_def)
    then have "enum x \<noteq> enum y"
      by (auto simp: enum_def fun_eq_iff) }
  then show ?thesis
    by (auto simp: inj_on_def)
qed

lemma enum_0: "enum 0 = base"
  by (simp add: enum_def[abs_def])

lemma base_in_s: "base \<in> s"
  unfolding s_eq by (subst enum_0[symmetric]) auto

lemma enum_in: "i \<le> n \<Longrightarrow> enum i \<in> s"
  unfolding s_eq by auto

lemma one_step:
  assumes a: "a \<in> s" "j < n"
  assumes *: "\<And>a'. a' \<in> s \<Longrightarrow> a' \<noteq> a \<Longrightarrow> a' j = p'"
  shows "a j \<noteq> p'"
proof
  assume "a j = p'"
  with * a have "\<And>a'. a' \<in> s \<Longrightarrow> a' j = p'"
    by auto
  then have "\<And>i. i \<le> n \<Longrightarrow> enum i j = p'"
    unfolding s_eq by auto
  from this[of 0] this[of n] have "j \<notin> upd ` {..< n}"
    by (auto simp: enum_def fun_eq_iff split: if_split_asm)
  with upd \<open>j < n\<close> show False
    by (auto simp: bij_betw_def)
qed

lemma upd_inj: "i < n \<Longrightarrow> j < n \<Longrightarrow> upd i = upd j \<longleftrightarrow> i = j"
  using upd by (auto simp: bij_betw_def inj_on_eq_iff)

lemma upd_surj: "upd ` {..< n} = {..< n}"
  using upd by (auto simp: bij_betw_def)

lemma in_upd_image: "A \<subseteq> {..< n} \<Longrightarrow> i < n \<Longrightarrow> upd i \<in> upd ` A \<longleftrightarrow> i \<in> A"
  using inj_on_image_mem_iff[of upd "{..< n}"] upd
  by (auto simp: bij_betw_def)

lemma enum_inj: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i = enum j \<longleftrightarrow> i = j"
  using inj_enum by (auto simp: inj_on_eq_iff)

lemma in_enum_image: "A \<subseteq> {.. n} \<Longrightarrow> i \<le> n \<Longrightarrow> enum i \<in> enum ` A \<longleftrightarrow> i \<in> A"
  using inj_on_image_mem_iff[OF inj_enum] by auto

lemma enum_mono: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i \<le> enum j \<longleftrightarrow> i \<le> j"
  by (auto simp: enum_def le_fun_def in_upd_image Ball_def[symmetric])

lemma enum_strict_mono: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> enum i < enum j \<longleftrightarrow> i < j"
  using enum_mono[of i j] enum_inj[of i j] by (auto simp: le_less)

lemma chain: "a \<in> s \<Longrightarrow> b \<in> s \<Longrightarrow> a \<le> b \<or> b \<le> a"
  by (auto simp: s_eq enum_mono)

lemma less: "a \<in> s \<Longrightarrow> b \<in> s \<Longrightarrow> a i < b i \<Longrightarrow> a < b"
  using chain[of a b] by (auto simp: less_fun_def le_fun_def not_le[symmetric])

lemma enum_0_bot: "a \<in> s \<Longrightarrow> a = enum 0 \<longleftrightarrow> (\<forall>a'\<in>s. a \<le> a')"
  unfolding s_eq by (auto simp: enum_mono Ball_def)

lemma enum_n_top: "a \<in> s \<Longrightarrow> a = enum n \<longleftrightarrow> (\<forall>a'\<in>s. a' \<le> a)"
  unfolding s_eq by (auto simp: enum_mono Ball_def)

lemma enum_Suc: "i < n \<Longrightarrow> enum (Suc i) = (enum i)(upd i := Suc (enum i (upd i)))"
  by (auto simp: fun_eq_iff enum_def upd_inj)

lemma enum_eq_p: "i \<le> n \<Longrightarrow> n \<le> j \<Longrightarrow> enum i j = p"
  by (induct i) (auto simp: enum_Suc enum_0 base_out upd_space not_less[symmetric])

lemma out_eq_p: "a \<in> s \<Longrightarrow> n \<le> j \<Longrightarrow> a j = p"
  unfolding s_eq by (auto simp: enum_eq_p)

lemma s_le_p: "a \<in> s \<Longrightarrow> a j \<le> p"
  using out_eq_p[of a j] s_space by (cases "j < n") auto

lemma le_Suc_base: "a \<in> s \<Longrightarrow> a j \<le> Suc (base j)"
  unfolding s_eq by (auto simp: enum_def)

lemma base_le: "a \<in> s \<Longrightarrow> base j \<le> a j"
  unfolding s_eq by (auto simp: enum_def)

lemma enum_le_p: "i \<le> n \<Longrightarrow> j < n \<Longrightarrow> enum i j \<le> p"
  using enum_in[of i] s_space by auto

lemma enum_less: "a \<in> s \<Longrightarrow> i < n \<Longrightarrow> enum i < a \<longleftrightarrow> enum (Suc i) \<le> a"
  unfolding s_eq by (auto simp: enum_strict_mono enum_mono)

lemma ksimplex_0:
  "n = 0 \<Longrightarrow> s = {(\<lambda>x. p)}"
  using s_eq enum_def base_out by auto

lemma replace_0:
  assumes "j < n" "a \<in> s" and p: "\<forall>x\<in>s - {a}. x j = 0" and "x \<in> s"
  shows "x \<le> a"
proof cases
  assume "x \<noteq> a"
  have "a j \<noteq> 0"
    using assms by (intro one_step[where a=a]) auto
  with less[OF \<open>x\<in>s\<close> \<open>a\<in>s\<close>, of j] p[rule_format, of x] \<open>x \<in> s\<close> \<open>x \<noteq> a\<close>
  show ?thesis
    by auto
qed simp

lemma replace_1:
  assumes "j < n" "a \<in> s" and p: "\<forall>x\<in>s - {a}. x j = p" and "x \<in> s"
  shows "a \<le> x"
proof cases
  assume "x \<noteq> a"
  have "a j \<noteq> p"
    using assms by (intro one_step[where a=a]) auto
  with enum_le_p[of _ j] \<open>j < n\<close> \<open>a\<in>s\<close>
  have "a j < p"
    by (auto simp: less_le s_eq)
  with less[OF \<open>a\<in>s\<close> \<open>x\<in>s\<close>, of j] p[rule_format, of x] \<open>x \<in> s\<close> \<open>x \<noteq> a\<close>
  show ?thesis
    by auto
qed simp

end

locale kuhn_simplex_pair = s: kuhn_simplex p n b_s u_s s + t: kuhn_simplex p n b_t u_t t
  for p n b_s u_s s b_t u_t t
begin

lemma enum_eq:
  assumes l: "i \<le> l" "l \<le> j" and "j + d \<le> n"
  assumes eq: "s.enum ` {i .. j} = t.enum ` {i + d .. j + d}"
  shows "s.enum l = t.enum (l + d)"
using l proof (induct l rule: dec_induct)
  case base
  then have s: "s.enum i \<in> t.enum ` {i + d .. j + d}" and t: "t.enum (i + d) \<in> s.enum ` {i .. j}"
    using eq by auto
  from t \<open>i \<le> j\<close> \<open>j + d \<le> n\<close> have "s.enum i \<le> t.enum (i + d)"
    by (auto simp: s.enum_mono)
  moreover from s \<open>i \<le> j\<close> \<open>j + d \<le> n\<close> have "t.enum (i + d) \<le> s.enum i"
    by (auto simp: t.enum_mono)
  ultimately show ?case
    by auto
next
  case (step l)
  moreover from step.prems \<open>j + d \<le> n\<close> have
      "s.enum l < s.enum (Suc l)"
      "t.enum (l + d) < t.enum (Suc l + d)"
    by (simp_all add: s.enum_strict_mono t.enum_strict_mono)
  moreover have
      "s.enum (Suc l) \<in> t.enum ` {i + d .. j + d}"
      "t.enum (Suc l + d) \<in> s.enum ` {i .. j}"
    using step \<open>j + d \<le> n\<close> eq by (auto simp: s.enum_inj t.enum_inj)
  ultimately have "s.enum (Suc l) = t.enum (Suc (l + d))"
    using \<open>j + d \<le> n\<close>
    by (intro antisym s.enum_less[THEN iffD1] t.enum_less[THEN iffD1])
       (auto intro!: s.enum_in t.enum_in)
  then show ?case by simp
qed

lemma ksimplex_eq_bot:
  assumes a: "a \<in> s" "\<And>a'. a' \<in> s \<Longrightarrow> a \<le> a'"
  assumes b: "b \<in> t" "\<And>b'. b' \<in> t \<Longrightarrow> b \<le> b'"
  assumes eq: "s - {a} = t - {b}"
  shows "s = t"
proof cases
  assume "n = 0" with s.ksimplex_0 t.ksimplex_0 show ?thesis by simp
next
  assume "n \<noteq> 0"
  have "s.enum 0 = (s.enum (Suc 0)) (u_s 0 := s.enum (Suc 0) (u_s 0) - 1)"
       "t.enum 0 = (t.enum (Suc 0)) (u_t 0 := t.enum (Suc 0) (u_t 0) - 1)"
    using \<open>n \<noteq> 0\<close> by (simp_all add: s.enum_Suc t.enum_Suc)
  moreover have e0: "a = s.enum 0" "b = t.enum 0"
    using a b by (simp_all add: s.enum_0_bot t.enum_0_bot)
  moreover
  { fix j assume "0 < j" "j \<le> n"
    moreover have "s - {a} = s.enum ` {Suc 0 .. n}" "t - {b} = t.enum ` {Suc 0 .. n}"
      unfolding s.s_eq t.s_eq e0 by (auto simp: s.enum_inj t.enum_inj)
    ultimately have "s.enum j = t.enum j"
      using enum_eq[of "1" j n 0] eq by auto }
  note enum_eq = this
  then have "s.enum (Suc 0) = t.enum (Suc 0)"
    using \<open>n \<noteq> 0\<close> by auto
  moreover
  { fix j assume "Suc j < n"
    with enum_eq[of "Suc j"] enum_eq[of "Suc (Suc j)"]
    have "u_s (Suc j) = u_t (Suc j)"
      using s.enum_Suc[of "Suc j"] t.enum_Suc[of "Suc j"]
      by (auto simp: fun_eq_iff split: if_split_asm) }
  then have "\<And>j. 0 < j \<Longrightarrow> j < n \<Longrightarrow> u_s j = u_t j"
    by (auto simp: gr0_conv_Suc)
  with \<open>n \<noteq> 0\<close> have "u_t 0 = u_s 0"
    by (intro bij_betw_singleton_eq[OF t.upd s.upd, of 0]) auto
  ultimately have "a = b"
    by simp
  with assms show "s = t"
    by auto
qed

lemma ksimplex_eq_top:
  assumes a: "a \<in> s" "\<And>a'. a' \<in> s \<Longrightarrow> a' \<le> a"
  assumes b: "b \<in> t" "\<And>b'. b' \<in> t \<Longrightarrow> b' \<le> b"
  assumes eq: "s - {a} = t - {b}"
  shows "s = t"
proof (cases n)
  assume "n = 0" with s.ksimplex_0 t.ksimplex_0 show ?thesis by simp
next
  case (Suc n')
  have "s.enum n = (s.enum n') (u_s n' := Suc (s.enum n' (u_s n')))"
       "t.enum n = (t.enum n') (u_t n' := Suc (t.enum n' (u_t n')))"
    using Suc by (simp_all add: s.enum_Suc t.enum_Suc)
  moreover have en: "a = s.enum n" "b = t.enum n"
    using a b by (simp_all add: s.enum_n_top t.enum_n_top)
  moreover
  { fix j assume "j < n"
    moreover have "s - {a} = s.enum ` {0 .. n'}" "t - {b} = t.enum ` {0 .. n'}"
      unfolding s.s_eq t.s_eq en by (auto simp: s.enum_inj t.enum_inj Suc)
    ultimately have "s.enum j = t.enum j"
      using enum_eq[of "0" j n' 0] eq Suc by auto }
  note enum_eq = this
  then have "s.enum n' = t.enum n'"
    using Suc by auto
  moreover
  { fix j assume "j < n'"
    with enum_eq[of j] enum_eq[of "Suc j"]
    have "u_s j = u_t j"
      using s.enum_Suc[of j] t.enum_Suc[of j]
      by (auto simp: Suc fun_eq_iff split: if_split_asm) }
  then have "\<And>j. j < n' \<Longrightarrow> u_s j = u_t j"
    by (auto simp: gr0_conv_Suc)
  then have "u_t n' = u_s n'"
    by (intro bij_betw_singleton_eq[OF t.upd s.upd, of n']) (auto simp: Suc)
  ultimately have "a = b"
    by simp
  with assms show "s = t"
    by auto
qed

end

inductive ksimplex for p n :: nat where
  ksimplex: "kuhn_simplex p n base upd s \<Longrightarrow> ksimplex p n s"

lemma finite_ksimplexes: "finite {s. ksimplex p n s}"
proof (rule finite_subset)
  { fix a s assume "ksimplex p n s" "a \<in> s"
    then obtain b u where "kuhn_simplex p n b u s" by (auto elim: ksimplex.cases)
    then interpret kuhn_simplex p n b u s .
    from s_space \<open>a \<in> s\<close> out_eq_p[OF \<open>a \<in> s\<close>]
    have "a \<in> (\<lambda>f x. if n \<le> x then p else f x) ` ({..< n} \<rightarrow>\<^sub>E {.. p})"
      by (auto simp: image_iff subset_eq Pi_iff split: if_split_asm
               intro!: bexI[of _ "restrict a {..< n}"]) }
  then show "{s. ksimplex p n s} \<subseteq> Pow ((\<lambda>f x. if n \<le> x then p else f x) ` ({..< n} \<rightarrow>\<^sub>E {.. p}))"
    by auto
qed (simp add: finite_PiE)

lemma ksimplex_card:
  assumes "ksimplex p n s" shows "card s = Suc n"
using assms proof cases
  case (ksimplex u b)
  then interpret kuhn_simplex p n u b s .
  show ?thesis
    by (simp add: card_image s_eq inj_enum)
qed

lemma simplex_top_face:
  assumes "0 < p" "\<forall>x\<in>s'. x n = p"
  shows "ksimplex p n s' \<longleftrightarrow> (\<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> s' = s - {a})"
  using assms
proof safe
  fix s a assume "ksimplex p (Suc n) s" and a: "a \<in> s" and na: "\<forall>x\<in>s - {a}. x n = p"
  then show "ksimplex p n (s - {a})"
  proof cases
    case (ksimplex base upd)
    then interpret kuhn_simplex p "Suc n" base upd "s" .

    have "a n < p"
      using one_step[of a n p] na \<open>a\<in>s\<close> s_space by (auto simp: less_le)
    then have "a = enum 0"
      using \<open>a \<in> s\<close> na by (subst enum_0_bot) (auto simp: le_less intro!: less[of a _ n])
    then have s_eq: "s - {a} = enum ` Suc ` {.. n}"
      using s_eq by (simp add: atMost_Suc_eq_insert_0 insert_ident zero_notin_Suc_image in_enum_image subset_eq)
    then have "enum 1 \<in> s - {a}"
      by auto
    then have "upd 0 = n"
      using \<open>a n < p\<close> \<open>a = enum 0\<close> na[rule_format, of "enum 1"]
      by (auto simp: fun_eq_iff enum_Suc split: if_split_asm)
    then have "bij_betw upd (Suc ` {..< n}) {..< n}"
      using upd
      by (subst notIn_Un_bij_betw3[where b=0])
         (auto simp: lessThan_Suc[symmetric] lessThan_Suc_eq_insert_0)
    then have "bij_betw (upd\<circ>Suc) {..<n} {..<n}"
      by (rule bij_betw_trans[rotated]) (auto simp: bij_betw_def)

    have "a n = p - 1"
      using enum_Suc[of 0] na[rule_format, OF \<open>enum 1 \<in> s - {a}\<close>] \<open>a = enum 0\<close> by (auto simp: \<open>upd 0 = n\<close>)

    show ?thesis
    proof (rule ksimplex.intros, standard)
      show "bij_betw (upd\<circ>Suc) {..< n} {..< n}" by fact
      show "base(n := p) \<in> {..<n} \<rightarrow> {..<p}" "\<And>i. n\<le>i \<Longrightarrow> (base(n := p)) i = p"
        using base base_out by (auto simp: Pi_iff)

      have "\<And>i. Suc ` {..< i} = {..< Suc i} - {0}"
        by (auto simp: image_iff Ball_def) arith
      then have upd_Suc: "\<And>i. i \<le> n \<Longrightarrow> (upd\<circ>Suc) ` {..< i} = upd ` {..< Suc i} - {n}"
        using \<open>upd 0 = n\<close> upd_inj by (auto simp add: image_iff less_Suc_eq_0_disj)
      have n_in_upd: "\<And>i. n \<in> upd ` {..< Suc i}"
        using \<open>upd 0 = n\<close> by auto

      define f' where "f' i j =
        (if j \<in> (upd\<circ>Suc)`{..< i} then Suc ((base(n := p)) j) else (base(n := p)) j)" for i j
      { fix x i
        assume i [arith]: "i \<le> n"
        with upd_Suc have "(upd \<circ> Suc) ` {..<i} = upd ` {..<Suc i} - {n}" .
        with \<open>a n < p\<close> \<open>a = enum 0\<close> \<open>upd 0 = n\<close> \<open>a n = p - 1\<close>
        have "enum (Suc i) x = f' i x"
          by (auto simp add: f'_def enum_def)  }
      then show "s - {a} = f' ` {.. n}"
        unfolding s_eq image_comp by (intro image_cong) auto
    qed
  qed
next
  assume "ksimplex p n s'" and *: "\<forall>x\<in>s'. x n = p"
  then show "\<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> s' = s - {a}"
  proof cases
    case (ksimplex base upd)
    then interpret kuhn_simplex p n base upd s' .
    define b where "b = base (n := p - 1)"
    define u where "u i = (case i of 0 \<Rightarrow> n | Suc i \<Rightarrow> upd i)" for i

    have "ksimplex p (Suc n) (s' \<union> {b})"
    proof (rule ksimplex.intros, standard)
      show "b \<in> {..<Suc n} \<rightarrow> {..<p}"
        using base \<open>0 < p\<close> unfolding lessThan_Suc b_def by (auto simp: PiE_iff)
      show "\<And>i. Suc n \<le> i \<Longrightarrow> b i = p"
        using base_out by (auto simp: b_def)

      have "bij_betw u (Suc ` {..< n} \<union> {0}) ({..<n} \<union> {u 0})"
        using upd
        by (intro notIn_Un_bij_betw) (auto simp: u_def bij_betw_def image_comp comp_def inj_on_def)
      then show "bij_betw u {..<Suc n} {..<Suc n}"
        by (simp add: u_def lessThan_Suc[symmetric] lessThan_Suc_eq_insert_0)

      define f' where "f' i j = (if j \<in> u`{..< i} then Suc (b j) else b j)" for i j

      have u_eq: "\<And>i. i \<le> n \<Longrightarrow> u ` {..< Suc i} = upd ` {..< i} \<union> { n }"
        by (auto simp: u_def image_iff upd_inj Ball_def split: nat.split) arith

      { fix x have "x \<le> n \<Longrightarrow> n \<notin> upd ` {..<x}"
          using upd_space by (simp add: image_iff neq_iff) }
      note n_not_upd = this

      have *: "f' ` {.. Suc n} = f' ` (Suc ` {.. n} \<union> {0})"
        unfolding atMost_Suc_eq_insert_0 by simp
      also have "\<dots> = (f' \<circ> Suc) ` {.. n} \<union> {b}"
        by (auto simp: f'_def)
      also have "(f' \<circ> Suc) ` {.. n} = s'"
        using \<open>0 < p\<close> base_out[of n]
        unfolding s_eq enum_def[abs_def] f'_def[abs_def] upd_space
        by (intro image_cong) (simp_all add: u_eq b_def fun_eq_iff n_not_upd)
      finally show "s' \<union> {b} = f' ` {.. Suc n}" ..
    qed
    moreover have "b \<notin> s'"
      using * \<open>0 < p\<close> by (auto simp: b_def)
    ultimately show ?thesis by auto
  qed
qed

lemma ksimplex_replace_0:
  assumes s: "ksimplex p n s" and a: "a \<in> s"
  assumes j: "j < n" and p: "\<forall>x\<in>s - {a}. x j = 0"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
  using s
proof cases
  case (ksimplex b_s u_s)

  { fix t b assume "ksimplex p n t"
    then obtain b_t u_t where "kuhn_simplex p n b_t u_t t"
      by (auto elim: ksimplex.cases)
    interpret kuhn_simplex_pair p n b_s u_s s b_t u_t t
      by intro_locales fact+

    assume b: "b \<in> t" "t - {b} = s - {a}"
    with a j p s.replace_0[of _ a] t.replace_0[of _ b] have "s = t"
      by (intro ksimplex_eq_top[of a b]) auto }
  then have "{s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = {s}"
    using s \<open>a \<in> s\<close> by auto
  then show ?thesis
    by simp
qed

lemma ksimplex_replace_1:
  assumes s: "ksimplex p n s" and a: "a \<in> s"
  assumes j: "j < n" and p: "\<forall>x\<in>s - {a}. x j = p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
  using s
proof cases
  case (ksimplex b_s u_s)

  { fix t b assume "ksimplex p n t"
    then obtain b_t u_t where "kuhn_simplex p n b_t u_t t"
      by (auto elim: ksimplex.cases)
    interpret kuhn_simplex_pair p n b_s u_s s b_t u_t t
      by intro_locales fact+

    assume b: "b \<in> t" "t - {b} = s - {a}"
    with a j p s.replace_1[of _ a] t.replace_1[of _ b] have "s = t"
      by (intro ksimplex_eq_bot[of a b]) auto }
  then have "{s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = {s}"
    using s \<open>a \<in> s\<close> by auto
  then show ?thesis
    by simp
qed

lemma card_2_exists: "card s = 2 \<longleftrightarrow> (\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y))"
  by (auto simp: card_Suc_eq eval_nat_numeral)

lemma ksimplex_replace_2:
  assumes s: "ksimplex p n s" and "a \<in> s" and "n \<noteq> 0"
    and lb: "\<forall>j<n. \<exists>x\<in>s - {a}. x j \<noteq> 0"
    and ub: "\<forall>j<n. \<exists>x\<in>s - {a}. x j \<noteq> p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 2"
  using s
proof cases
  case (ksimplex base upd)
  then interpret kuhn_simplex p n base upd s .

  from \<open>a \<in> s\<close> obtain i where "i \<le> n" "a = enum i"
    unfolding s_eq by auto

  from \<open>i \<le> n\<close> have "i = 0 \<or> i = n \<or> (0 < i \<and> i < n)"
    by linarith
  then have "\<exists>!s'. s' \<noteq> s \<and> ksimplex p n s' \<and> (\<exists>b\<in>s'. s - {a} = s'- {b})"
  proof (elim disjE conjE)
    assume "i = 0"
    define rot where [abs_def]: "rot i = (if i + 1 = n then 0 else i + 1)" for i
    let ?upd = "upd \<circ> rot"

    have rot: "bij_betw rot {..< n} {..< n}"
      by (auto simp: bij_betw_def inj_on_def image_iff Ball_def rot_def)
         arith+
    from rot upd have "bij_betw ?upd {..<n} {..<n}"
      by (rule bij_betw_trans)

    define f' where [abs_def]: "f' i j =
      (if j \<in> ?upd`{..< i} then Suc (enum (Suc 0) j) else enum (Suc 0) j)" for i j

    interpret b: kuhn_simplex p n "enum (Suc 0)" "upd \<circ> rot" "f' ` {.. n}"
    proof
      from \<open>a = enum i\<close> ub \<open>n \<noteq> 0\<close> \<open>i = 0\<close>
      obtain i' where "i' \<le> n" "enum i' \<noteq> enum 0" "enum i' (upd 0) \<noteq> p"
        unfolding s_eq by (auto intro: upd_space simp: enum_inj)
      then have "enum 1 \<le> enum i'" "enum i' (upd 0) < p"
        using enum_le_p[of i' "upd 0"] by (auto simp: enum_inj enum_mono upd_space)
      then have "enum 1 (upd 0) < p"
        by (auto simp: le_fun_def intro: le_less_trans)
      then show "enum (Suc 0) \<in> {..<n} \<rightarrow> {..<p}"
        using base \<open>n \<noteq> 0\<close> by (auto simp: enum_0 enum_Suc PiE_iff extensional_def upd_space)

      { fix i assume "n \<le> i" then show "enum (Suc 0) i = p"
        using \<open>n \<noteq> 0\<close> by (auto simp: enum_eq_p) }
      show "bij_betw ?upd {..<n} {..<n}" by fact
    qed (simp add: f'_def)
    have ks_f': "ksimplex p n (f' ` {.. n})"
      by rule unfold_locales

    have b_enum: "b.enum = f'" unfolding f'_def b.enum_def[abs_def] ..
    with b.inj_enum have inj_f': "inj_on f' {.. n}" by simp

    have f'_eq_enum: "f' j = enum (Suc j)" if "j < n" for j
    proof -
      from that have "rot ` {..< j} = {0 <..< Suc j}"
        by (auto simp: rot_def image_Suc_lessThan cong: image_cong_simp)
      with that \<open>n \<noteq> 0\<close> show ?thesis
        by (simp only: f'_def enum_def fun_eq_iff image_comp [symmetric])
          (auto simp add: upd_inj)
    qed
    then have "enum ` Suc ` {..< n} = f' ` {..< n}"
      by (force simp: enum_inj)
    also have "Suc ` {..< n} = {.. n} - {0}"
      by (auto simp: image_iff Ball_def) arith
    also have "{..< n} = {.. n} - {n}"
      by auto
    finally have eq: "s - {a} = f' ` {.. n} - {f' n}"
      unfolding s_eq \<open>a = enum i\<close> \<open>i = 0\<close>
      by (simp add: inj_on_image_set_diff[OF inj_enum] inj_on_image_set_diff[OF inj_f'])

    have "enum 0 < f' 0"
      using \<open>n \<noteq> 0\<close> by (simp add: enum_strict_mono f'_eq_enum)
    also have "\<dots> < f' n"
      using \<open>n \<noteq> 0\<close> b.enum_strict_mono[of 0 n] unfolding b_enum by simp
    finally have "a \<noteq> f' n"
      using \<open>a = enum i\<close> \<open>i = 0\<close> by auto

    { fix t c assume "ksimplex p n t" "c \<in> t" and eq_sma: "s - {a} = t - {c}"
      obtain b u where "kuhn_simplex p n b u t"
        using \<open>ksimplex p n t\<close> by (auto elim: ksimplex.cases)
      then interpret t: kuhn_simplex p n b u t .

      { fix x assume "x \<in> s" "x \<noteq> a"
         then have "x (upd 0) = enum (Suc 0) (upd 0)"
           by (auto simp: \<open>a = enum i\<close> \<open>i = 0\<close> s_eq enum_def enum_inj) }
      then have eq_upd0: "\<forall>x\<in>t-{c}. x (upd 0) = enum (Suc 0) (upd 0)"
        unfolding eq_sma[symmetric] by auto
      then have "c (upd 0) \<noteq> enum (Suc 0) (upd 0)"
        using \<open>n \<noteq> 0\<close> by (intro t.one_step[OF \<open>c\<in>t\<close> ]) (auto simp: upd_space)
      then have "c (upd 0) < enum (Suc 0) (upd 0) \<or> c (upd 0) > enum (Suc 0) (upd 0)"
        by auto
      then have "t = s \<or> t = f' ` {..n}"
      proof (elim disjE conjE)
        assume *: "c (upd 0) < enum (Suc 0) (upd 0)"
        interpret st: kuhn_simplex_pair p n base upd s b u t ..
        { fix x assume "x \<in> t" with * \<open>c\<in>t\<close> eq_upd0[rule_format, of x] have "c \<le> x"
            by (auto simp: le_less intro!: t.less[of _ _ "upd 0"]) }
        note top = this
        have "s = t"
          using \<open>a = enum i\<close> \<open>i = 0\<close> \<open>c \<in> t\<close>
          by (intro st.ksimplex_eq_bot[OF _ _ _ _ eq_sma])
             (auto simp: s_eq enum_mono t.s_eq t.enum_mono top)
        then show ?thesis by simp
      next
        assume *: "c (upd 0) > enum (Suc 0) (upd 0)"
        interpret st: kuhn_simplex_pair p n "enum (Suc 0)" "upd \<circ> rot" "f' ` {.. n}" b u t ..
        have eq: "f' ` {..n} - {f' n} = t - {c}"
          using eq_sma eq by simp
        { fix x assume "x \<in> t" with * \<open>c\<in>t\<close> eq_upd0[rule_format, of x] have "x \<le> c"
            by (auto simp: le_less intro!: t.less[of _ _ "upd 0"]) }
        note top = this
        have "f' ` {..n} = t"
          using \<open>a = enum i\<close> \<open>i = 0\<close> \<open>c \<in> t\<close>
          by (intro st.ksimplex_eq_top[OF _ _ _ _ eq])
             (auto simp: b.s_eq b.enum_mono t.s_eq t.enum_mono b_enum[symmetric] top)
        then show ?thesis by simp
      qed }
    with ks_f' eq \<open>a \<noteq> f' n\<close> \<open>n \<noteq> 0\<close> show ?thesis
      apply (intro ex1I[of _ "f' ` {.. n}"])
      apply auto []
      apply metis
      done
  next
    assume "i = n"
    from \<open>n \<noteq> 0\<close> obtain n' where n': "n = Suc n'"
      by (cases n) auto

    define rot where "rot i = (case i of 0 \<Rightarrow> n' | Suc i \<Rightarrow> i)" for i
    let ?upd = "upd \<circ> rot"

    have rot: "bij_betw rot {..< n} {..< n}"
      by (auto simp: bij_betw_def inj_on_def image_iff Bex_def rot_def n' split: nat.splits)
         arith
    from rot upd have "bij_betw ?upd {..<n} {..<n}"
      by (rule bij_betw_trans)

    define b where "b = base (upd n' := base (upd n') - 1)"
    define f' where [abs_def]: "f' i j = (if j \<in> ?upd`{..< i} then Suc (b j) else b j)" for i j

    interpret b: kuhn_simplex p n b "upd \<circ> rot" "f' ` {.. n}"
    proof
      { fix i assume "n \<le> i" then show "b i = p"
          using base_out[of i] upd_space[of n'] by (auto simp: b_def n') }
      show "b \<in> {..<n} \<rightarrow> {..<p}"
        using base \<open>n \<noteq> 0\<close> upd_space[of n']
        by (auto simp: b_def PiE_def Pi_iff Ball_def upd_space extensional_def n')

      show "bij_betw ?upd {..<n} {..<n}" by fact
    qed (simp add: f'_def)
    have f': "b.enum = f'" unfolding f'_def b.enum_def[abs_def] ..
    have ks_f': "ksimplex p n (b.enum ` {.. n})"
      unfolding f' by rule unfold_locales

    have "0 < n"
      using \<open>n \<noteq> 0\<close> by auto

    { from \<open>a = enum i\<close> \<open>n \<noteq> 0\<close> \<open>i = n\<close> lb upd_space[of n']
      obtain i' where "i' \<le> n" "enum i' \<noteq> enum n" "0 < enum i' (upd n')"
        unfolding s_eq by (auto simp: enum_inj n')
      moreover have "enum i' (upd n') = base (upd n')"
        unfolding enum_def using \<open>i' \<le> n\<close> \<open>enum i' \<noteq> enum n\<close> by (auto simp: n' upd_inj enum_inj)
      ultimately have "0 < base (upd n')"
        by auto }
    then have benum1: "b.enum (Suc 0) = base"
      unfolding b.enum_Suc[OF \<open>0<n\<close>] b.enum_0 by (auto simp: b_def rot_def)

    have [simp]: "\<And>j. Suc j < n \<Longrightarrow> rot ` {..< Suc j} = {n'} \<union> {..< j}"
      by (auto simp: rot_def image_iff Ball_def split: nat.splits)
    have rot_simps: "\<And>j. rot (Suc j) = j" "rot 0 = n'"
      by (simp_all add: rot_def)

    { fix j assume j: "Suc j \<le> n" then have "b.enum (Suc j) = enum j"
        by (induct j) (auto simp: benum1 enum_0 b.enum_Suc enum_Suc rot_simps) }
    note b_enum_eq_enum = this
    then have "enum ` {..< n} = b.enum ` Suc ` {..< n}"
      by (auto simp: image_comp intro!: image_cong)
    also have "Suc ` {..< n} = {.. n} - {0}"
      by (auto simp: image_iff Ball_def) arith
    also have "{..< n} = {.. n} - {n}"
      by auto
    finally have eq: "s - {a} = b.enum ` {.. n} - {b.enum 0}"
      unfolding s_eq \<open>a = enum i\<close> \<open>i = n\<close>
      using inj_on_image_set_diff[OF inj_enum Diff_subset, of "{n}"]
            inj_on_image_set_diff[OF b.inj_enum Diff_subset, of "{0}"]
      by (simp add: comp_def)

    have "b.enum 0 \<le> b.enum n"
      by (simp add: b.enum_mono)
    also have "b.enum n < enum n"
      using \<open>n \<noteq> 0\<close> by (simp add: enum_strict_mono b_enum_eq_enum n')
    finally have "a \<noteq> b.enum 0"
      using \<open>a = enum i\<close> \<open>i = n\<close> by auto

    { fix t c assume "ksimplex p n t" "c \<in> t" and eq_sma: "s - {a} = t - {c}"
      obtain b' u where "kuhn_simplex p n b' u t"
        using \<open>ksimplex p n t\<close> by (auto elim: ksimplex.cases)
      then interpret t: kuhn_simplex p n b' u t .

      { fix x assume "x \<in> s" "x \<noteq> a"
         then have "x (upd n') = enum n' (upd n')"
           by (auto simp: \<open>a = enum i\<close> n' \<open>i = n\<close> s_eq enum_def enum_inj in_upd_image) }
      then have eq_upd0: "\<forall>x\<in>t-{c}. x (upd n') = enum n' (upd n')"
        unfolding eq_sma[symmetric] by auto
      then have "c (upd n') \<noteq> enum n' (upd n')"
        using \<open>n \<noteq> 0\<close> by (intro t.one_step[OF \<open>c\<in>t\<close> ]) (auto simp: n' upd_space[unfolded n'])
      then have "c (upd n') < enum n' (upd n') \<or> c (upd n') > enum n' (upd n')"
        by auto
      then have "t = s \<or> t = b.enum ` {..n}"
      proof (elim disjE conjE)
        assume *: "c (upd n') > enum n' (upd n')"
        interpret st: kuhn_simplex_pair p n base upd s b' u t ..
        { fix x assume "x \<in> t" with * \<open>c\<in>t\<close> eq_upd0[rule_format, of x] have "x \<le> c"
            by (auto simp: le_less intro!: t.less[of _ _ "upd n'"]) }
        note top = this
        have "s = t"
          using \<open>a = enum i\<close> \<open>i = n\<close> \<open>c \<in> t\<close>
          by (intro st.ksimplex_eq_top[OF _ _ _ _ eq_sma])
             (auto simp: s_eq enum_mono t.s_eq t.enum_mono top)
        then show ?thesis by simp
      next
        assume *: "c (upd n') < enum n' (upd n')"
        interpret st: kuhn_simplex_pair p n b "upd \<circ> rot" "f' ` {.. n}" b' u t ..
        have eq: "f' ` {..n} - {b.enum 0} = t - {c}"
          using eq_sma eq f' by simp
        { fix x assume "x \<in> t" with * \<open>c\<in>t\<close> eq_upd0[rule_format, of x] have "c \<le> x"
            by (auto simp: le_less intro!: t.less[of _ _ "upd n'"]) }
        note bot = this
        have "f' ` {..n} = t"
          using \<open>a = enum i\<close> \<open>i = n\<close> \<open>c \<in> t\<close>
          by (intro st.ksimplex_eq_bot[OF _ _ _ _ eq])
             (auto simp: b.s_eq b.enum_mono t.s_eq t.enum_mono bot)
        with f' show ?thesis by simp
      qed }
    with ks_f' eq \<open>a \<noteq> b.enum 0\<close> \<open>n \<noteq> 0\<close> show ?thesis
      apply (intro ex1I[of _ "b.enum ` {.. n}"])
      apply auto []
      apply metis
      done
  next
    assume i: "0 < i" "i < n"
    define i' where "i' = i - 1"
    with i have "Suc i' < n"
      by simp
    with i have Suc_i': "Suc i' = i"
      by (simp add: i'_def)

    let ?upd = "Fun.swap i' i upd"
    from i upd have "bij_betw ?upd {..< n} {..< n}"
      by (subst bij_betw_swap_iff) (auto simp: i'_def)

    define f' where [abs_def]: "f' i j = (if j \<in> ?upd`{..< i} then Suc (base j) else base j)"
      for i j
    interpret b: kuhn_simplex p n base ?upd "f' ` {.. n}"
    proof
      show "base \<in> {..<n} \<rightarrow> {..<p}" by (rule base)
      { fix i assume "n \<le> i" then show "base i = p" by (rule base_out) }
      show "bij_betw ?upd {..<n} {..<n}" by fact
    qed (simp add: f'_def)
    have f': "b.enum = f'" unfolding f'_def b.enum_def[abs_def] ..
    have ks_f': "ksimplex p n (b.enum ` {.. n})"
      unfolding f' by rule unfold_locales

    have "{i} \<subseteq> {..n}"
      using i by auto
    { fix j assume "j \<le> n"
      moreover have "j < i \<or> i = j \<or> i < j" by arith
      moreover note i
      ultimately have "enum j = b.enum j \<longleftrightarrow> j \<noteq> i"
        unfolding enum_def[abs_def] b.enum_def[abs_def]
        by (auto simp: fun_eq_iff swap_image i'_def
                           in_upd_image inj_on_image_set_diff[OF inj_upd]) }
    note enum_eq_benum = this
    then have "enum ` ({.. n} - {i}) = b.enum ` ({.. n} - {i})"
      by (intro image_cong) auto
    then have eq: "s - {a} = b.enum ` {.. n} - {b.enum i}"
      unfolding s_eq \<open>a = enum i\<close>
      using inj_on_image_set_diff[OF inj_enum Diff_subset \<open>{i} \<subseteq> {..n}\<close>]
            inj_on_image_set_diff[OF b.inj_enum Diff_subset \<open>{i} \<subseteq> {..n}\<close>]
      by (simp add: comp_def)

    have "a \<noteq> b.enum i"
      using \<open>a = enum i\<close> enum_eq_benum i by auto

    { fix t c assume "ksimplex p n t" "c \<in> t" and eq_sma: "s - {a} = t - {c}"
      obtain b' u where "kuhn_simplex p n b' u t"
        using \<open>ksimplex p n t\<close> by (auto elim: ksimplex.cases)
      then interpret t: kuhn_simplex p n b' u t .
      have "enum i' \<in> s - {a}" "enum (i + 1) \<in> s - {a}"
        using \<open>a = enum i\<close> i enum_in by (auto simp: enum_inj i'_def)
      then obtain l k where
        l: "t.enum l = enum i'" "l \<le> n" "t.enum l \<noteq> c" and
        k: "t.enum k = enum (i + 1)" "k \<le> n" "t.enum k \<noteq> c"
        unfolding eq_sma by (auto simp: t.s_eq)
      with i have "t.enum l < t.enum k"
        by (simp add: enum_strict_mono i'_def)
      with \<open>l \<le> n\<close> \<open>k \<le> n\<close> have "l < k"
        by (simp add: t.enum_strict_mono)
      { assume "Suc l = k"
        have "enum (Suc (Suc i')) = t.enum (Suc l)"
          using i by (simp add: k \<open>Suc l = k\<close> i'_def)
        then have False
          using \<open>l < k\<close> \<open>k \<le> n\<close> \<open>Suc i' < n\<close>
          by (auto simp: t.enum_Suc enum_Suc l upd_inj fun_eq_iff split: if_split_asm)
             (metis Suc_lessD n_not_Suc_n upd_inj) }
      with \<open>l < k\<close> have "Suc l < k"
        by arith
      have c_eq: "c = t.enum (Suc l)"
      proof (rule ccontr)
        assume "c \<noteq> t.enum (Suc l)"
        then have "t.enum (Suc l) \<in> s - {a}"
          using \<open>l < k\<close> \<open>k \<le> n\<close> by (simp add: t.s_eq eq_sma)
        then obtain j where "t.enum (Suc l) = enum j" "j \<le> n" "enum j \<noteq> enum i"
          unfolding s_eq \<open>a = enum i\<close> by auto
        with i have "t.enum (Suc l) \<le> t.enum l \<or> t.enum k \<le> t.enum (Suc l)"
          by (auto simp: i'_def enum_mono enum_inj l k)
        with \<open>Suc l < k\<close> \<open>k \<le> n\<close> show False
          by (simp add: t.enum_mono)
      qed

      { have "t.enum (Suc (Suc l)) \<in> s - {a}"
          unfolding eq_sma c_eq t.s_eq using \<open>Suc l < k\<close> \<open>k \<le> n\<close> by (auto simp: t.enum_inj)
        then obtain j where eq: "t.enum (Suc (Suc l)) = enum j" and "j \<le> n" "j \<noteq> i"
          by (auto simp: s_eq \<open>a = enum i\<close>)
        moreover have "enum i' < t.enum (Suc (Suc l))"
          unfolding l(1)[symmetric] using \<open>Suc l < k\<close> \<open>k \<le> n\<close> by (auto simp: t.enum_strict_mono)
        ultimately have "i' < j"
          using i by (simp add: enum_strict_mono i'_def)
        with \<open>j \<noteq> i\<close> \<open>j \<le> n\<close> have "t.enum k \<le> t.enum (Suc (Suc l))"
          unfolding i'_def by (simp add: enum_mono k eq)
        then have "k \<le> Suc (Suc l)"
          using \<open>k \<le> n\<close> \<open>Suc l < k\<close> by (simp add: t.enum_mono) }
      with \<open>Suc l < k\<close> have "Suc (Suc l) = k" by simp
      then have "enum (Suc (Suc i')) = t.enum (Suc (Suc l))"
        using i by (simp add: k i'_def)
      also have "\<dots> = (enum i') (u l := Suc (enum i' (u l)), u (Suc l) := Suc (enum i' (u (Suc l))))"
        using \<open>Suc l < k\<close> \<open>k \<le> n\<close> by (simp add: t.enum_Suc l t.upd_inj)
      finally have "(u l = upd i' \<and> u (Suc l) = upd (Suc i')) \<or>
        (u l = upd (Suc i') \<and> u (Suc l) = upd i')"
        using \<open>Suc i' < n\<close> by (auto simp: enum_Suc fun_eq_iff split: if_split_asm)

      then have "t = s \<or> t = b.enum ` {..n}"
      proof (elim disjE conjE)
        assume u: "u l = upd i'"
        have "c = t.enum (Suc l)" unfolding c_eq ..
        also have "t.enum (Suc l) = enum (Suc i')"
          using u \<open>l < k\<close> \<open>k \<le> n\<close> \<open>Suc i' < n\<close> by (simp add: enum_Suc t.enum_Suc l)
        also have "\<dots> = a"
          using \<open>a = enum i\<close> i by (simp add: i'_def)
        finally show ?thesis
          using eq_sma \<open>a \<in> s\<close> \<open>c \<in> t\<close> by auto
      next
        assume u: "u l = upd (Suc i')"
        define B where "B = b.enum ` {..n}"
        have "b.enum i' = enum i'"
          using enum_eq_benum[of i'] i by (auto simp: i'_def gr0_conv_Suc)
        have "c = t.enum (Suc l)" unfolding c_eq ..
        also have "t.enum (Suc l) = b.enum (Suc i')"
          using u \<open>l < k\<close> \<open>k \<le> n\<close> \<open>Suc i' < n\<close>
          by (simp_all add: enum_Suc t.enum_Suc l b.enum_Suc \<open>b.enum i' = enum i'\<close> swap_apply1)
             (simp add: Suc_i')
        also have "\<dots> = b.enum i"
          using i by (simp add: i'_def)
        finally have "c = b.enum i" .
        then have "t - {c} = B - {c}" "c \<in> B"
          unfolding eq_sma[symmetric] eq B_def using i by auto
        with \<open>c \<in> t\<close> have "t = B"
          by auto
        then show ?thesis
          by (simp add: B_def)
      qed }
    with ks_f' eq \<open>a \<noteq> b.enum i\<close> \<open>n \<noteq> 0\<close> \<open>i \<le> n\<close> show ?thesis
      apply (intro ex1I[of _ "b.enum ` {.. n}"])
      apply auto []
      apply metis
      done
  qed
  then show ?thesis
    using s \<open>a \<in> s\<close> by (simp add: card_2_exists Ex1_def) metis
qed

text \<open>Hence another step towards concreteness.\<close>

lemma kuhn_simplex_lemma:
  assumes "\<forall>s. ksimplex p (Suc n) s \<longrightarrow> rl ` s \<subseteq> {.. Suc n}"
    and "odd (card {f. \<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> (f = s - {a}) \<and>
      rl ` f = {..n} \<and> ((\<exists>j\<le>n. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>f. x j = p))})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> rl ` s = {..Suc n}})"
proof (rule kuhn_complete_lemma[OF finite_ksimplexes refl, unfolded mem_Collect_eq,
    where bnd="\<lambda>f. (\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = p)"],
    safe del: notI)

  have *: "\<And>x y. x = y \<Longrightarrow> odd (card x) \<Longrightarrow> odd (card y)"
    by auto
  show "odd (card {f. (\<exists>s\<in>{s. ksimplex p (Suc n) s}. \<exists>a\<in>s. f = s - {a}) \<and>
    rl ` f = {..n} \<and> ((\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{..n}. \<forall>x\<in>f. x j = p))})"
    apply (rule *[OF _ assms(2)])
    apply (auto simp: atLeast0AtMost)
    done

next

  fix s assume s: "ksimplex p (Suc n) s"
  then show "card s = n + 2"
    by (simp add: ksimplex_card)

  fix a assume a: "a \<in> s" then show "rl a \<le> Suc n"
    using assms(1) s by (auto simp: subset_eq)

  let ?S = "{t. ksimplex p (Suc n) t \<and> (\<exists>b\<in>t. s - {a} = t - {b})}"
  { fix j assume j: "j \<le> n" "\<forall>x\<in>s - {a}. x j = 0"
    with s a show "card ?S = 1"
      using ksimplex_replace_0[of p "n + 1" s a j]
      by (subst eq_commute) simp }

  { fix j assume j: "j \<le> n" "\<forall>x\<in>s - {a}. x j = p"
    with s a show "card ?S = 1"
      using ksimplex_replace_1[of p "n + 1" s a j]
      by (subst eq_commute) simp }

  { assume "card ?S \<noteq> 2" "\<not> (\<exists>j\<in>{..n}. \<forall>x\<in>s - {a}. x j = p)"
    with s a show "\<exists>j\<in>{..n}. \<forall>x\<in>s - {a}. x j = 0"
      using ksimplex_replace_2[of p "n + 1" s a]
      by (subst (asm) eq_commute) auto }
qed

subsubsection \<open>Reduced labelling\<close>

definition reduced :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where "reduced n x = (LEAST k. k = n \<or> x k \<noteq> 0)"

lemma reduced_labelling:
  shows "reduced n x \<le> n"
    and "\<forall>i<reduced n x. x i = 0"
    and "reduced n x = n \<or> x (reduced n x) \<noteq> 0"
proof -
  show "reduced n x \<le> n"
    unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) auto
  show "\<forall>i<reduced n x. x i = 0"
    unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) fastforce+
  show "reduced n x = n \<or> x (reduced n x) \<noteq> 0"
    unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) fastforce+
qed

lemma reduced_labelling_unique:
  "r \<le> n \<Longrightarrow> \<forall>i<r. x i = 0 \<Longrightarrow> r = n \<or> x r \<noteq> 0 \<Longrightarrow> reduced n x = r"
 unfolding reduced_def by (rule LeastI2_wellorder[where a=n]) (metis le_less not_le)+

lemma reduced_labelling_zero: "j < n \<Longrightarrow> x j = 0 \<Longrightarrow> reduced n x \<noteq> j"
  using reduced_labelling[of n x] by auto

lemma reduce_labelling_zero[simp]: "reduced 0 x = 0"
  by (rule reduced_labelling_unique) auto

lemma reduced_labelling_nonzero: "j < n \<Longrightarrow> x j \<noteq> 0 \<Longrightarrow> reduced n x \<le> j"
  using reduced_labelling[of n x] by (elim allE[where x=j]) auto

lemma reduced_labelling_Suc: "reduced (Suc n) x \<noteq> Suc n \<Longrightarrow> reduced (Suc n) x = reduced n x"
  using reduced_labelling[of "Suc n" x]
  by (intro reduced_labelling_unique[symmetric]) auto

lemma complete_face_top:
  assumes "\<forall>x\<in>f. \<forall>j\<le>n. x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x\<in>f. \<forall>j\<le>n. x j = p \<longrightarrow> lab x j = 1"
    and eq: "(reduced (Suc n) \<circ> lab) ` f = {..n}"
  shows "((\<exists>j\<le>n. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>f. x j = p)) \<longleftrightarrow> (\<forall>x\<in>f. x n = p)"
proof (safe del: disjCI)
  fix x j assume j: "j \<le> n" "\<forall>x\<in>f. x j = 0"
  { fix x assume "x \<in> f" with assms j have "reduced (Suc n) (lab x) \<noteq> j"
      by (intro reduced_labelling_zero) auto }
  moreover have "j \<in> (reduced (Suc n) \<circ> lab) ` f"
    using j eq by auto
  ultimately show "x n = p"
    by force
next
  fix x j assume j: "j \<le> n" "\<forall>x\<in>f. x j = p" and x: "x \<in> f"
  have "j = n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    { fix x assume "x \<in> f"
      with assms j have "reduced (Suc n) (lab x) \<le> j"
        by (intro reduced_labelling_nonzero) auto
      then have "reduced (Suc n) (lab x) \<noteq> n"
        using \<open>j \<noteq> n\<close> \<open>j \<le> n\<close> by simp }
    moreover
    have "n \<in> (reduced (Suc n) \<circ> lab) ` f"
      using eq by auto
    ultimately show False
      by force
  qed
  moreover have "j \<in> (reduced (Suc n) \<circ> lab) ` f"
    using j eq by auto
  ultimately show "x n = p"
    using j x by auto
qed auto

text \<open>Hence we get just about the nice induction.\<close>

lemma kuhn_induction:
  assumes "0 < p"
    and lab_0: "\<forall>x. \<forall>j\<le>n. (\<forall>j. x j \<le> p) \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and lab_1: "\<forall>x. \<forall>j\<le>n. (\<forall>j. x j \<le> p) \<and> x j = p \<longrightarrow> lab x j = 1"
    and odd: "odd (card {s. ksimplex p n s \<and> (reduced n\<circ>lab) ` s = {..n}})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> (reduced (Suc n)\<circ>lab) ` s = {..Suc n}})"
proof -
  let ?rl = "reduced (Suc n) \<circ> lab" and ?ext = "\<lambda>f v. \<exists>j\<le>n. \<forall>x\<in>f. x j = v"
  let ?ext = "\<lambda>s. (\<exists>j\<le>n. \<forall>x\<in>s. x j = 0) \<or> (\<exists>j\<le>n. \<forall>x\<in>s. x j = p)"
  have "\<forall>s. ksimplex p (Suc n) s \<longrightarrow> ?rl ` s \<subseteq> {..Suc n}"
    by (simp add: reduced_labelling subset_eq)
  moreover
  have "{s. ksimplex p n s \<and> (reduced n \<circ> lab) ` s = {..n}} =
        {f. \<exists>s a. ksimplex p (Suc n) s \<and> a \<in> s \<and> f = s - {a} \<and> ?rl ` f = {..n} \<and> ?ext f}"
  proof (intro set_eqI, safe del: disjCI equalityI disjE)
    fix s assume s: "ksimplex p n s" and rl: "(reduced n \<circ> lab) ` s = {..n}"
    from s obtain u b where "kuhn_simplex p n u b s" by (auto elim: ksimplex.cases)
    then interpret kuhn_simplex p n u b s .
    have all_eq_p: "\<forall>x\<in>s. x n = p"
      by (auto simp: out_eq_p)
    moreover
    { fix x assume "x \<in> s"
      with lab_1[rule_format, of n x] all_eq_p s_le_p[of x]
      have "?rl x \<le> n"
        by (auto intro!: reduced_labelling_nonzero)
      then have "?rl x = reduced n (lab x)"
        by (auto intro!: reduced_labelling_Suc) }
    then have "?rl ` s = {..n}"
      using rl by (simp cong: image_cong)
    moreover
    obtain t a where "ksimplex p (Suc n) t" "a \<in> t" "s = t - {a}"
      using s unfolding simplex_top_face[OF \<open>0 < p\<close> all_eq_p] by auto
    ultimately
    show "\<exists>t a. ksimplex p (Suc n) t \<and> a \<in> t \<and> s = t - {a} \<and> ?rl ` s = {..n} \<and> ?ext s"
      by auto
  next
    fix x s a assume s: "ksimplex p (Suc n) s" and rl: "?rl ` (s - {a}) = {.. n}"
      and a: "a \<in> s" and "?ext (s - {a})"
    from s obtain u b where "kuhn_simplex p (Suc n) u b s" by (auto elim: ksimplex.cases)
    then interpret kuhn_simplex p "Suc n" u b s .
    have all_eq_p: "\<forall>x\<in>s. x (Suc n) = p"
      by (auto simp: out_eq_p)

    { fix x assume "x \<in> s - {a}"
      then have "?rl x \<in> ?rl ` (s - {a})"
        by auto
      then have "?rl x \<le> n"
        unfolding rl by auto
      then have "?rl x = reduced n (lab x)"
        by (auto intro!: reduced_labelling_Suc) }
    then show rl': "(reduced n\<circ>lab) ` (s - {a}) = {..n}"
      unfolding rl[symmetric] by (intro image_cong) auto

    from \<open>?ext (s - {a})\<close>
    have all_eq_p: "\<forall>x\<in>s - {a}. x n = p"
    proof (elim disjE exE conjE)
      fix j assume "j \<le> n" "\<forall>x\<in>s - {a}. x j = 0"
      with lab_0[rule_format, of j] all_eq_p s_le_p
      have "\<And>x. x \<in> s - {a} \<Longrightarrow> reduced (Suc n) (lab x) \<noteq> j"
        by (intro reduced_labelling_zero) auto
      moreover have "j \<in> ?rl ` (s - {a})"
        using \<open>j \<le> n\<close> unfolding rl by auto
      ultimately show ?thesis
        by force
    next
      fix j assume "j \<le> n" and eq_p: "\<forall>x\<in>s - {a}. x j = p"
      show ?thesis
      proof cases
        assume "j = n" with eq_p show ?thesis by simp
      next
        assume "j \<noteq> n"
        { fix x assume x: "x \<in> s - {a}"
          have "reduced n (lab x) \<le> j"
          proof (rule reduced_labelling_nonzero)
            show "lab x j \<noteq> 0"
              using lab_1[rule_format, of j x] x s_le_p[of x] eq_p \<open>j \<le> n\<close> by auto
            show "j < n"
              using \<open>j \<le> n\<close> \<open>j \<noteq> n\<close> by simp
          qed
          then have "reduced n (lab x) \<noteq> n"
            using \<open>j \<le> n\<close> \<open>j \<noteq> n\<close> by simp }
        moreover have "n \<in> (reduced n\<circ>lab) ` (s - {a})"
          unfolding rl' by auto
        ultimately show ?thesis
          by force
      qed
    qed
    show "ksimplex p n (s - {a})"
      unfolding simplex_top_face[OF \<open>0 < p\<close> all_eq_p] using s a by auto
  qed
  ultimately show ?thesis
    using assms by (intro kuhn_simplex_lemma) auto
qed

text \<open>And so we get the final combinatorial result.\<close>

lemma ksimplex_0: "ksimplex p 0 s \<longleftrightarrow> s = {(\<lambda>x. p)}"
proof
  assume "ksimplex p 0 s" then show "s = {(\<lambda>x. p)}"
    by (blast dest: kuhn_simplex.ksimplex_0 elim: ksimplex.cases)
next
  assume s: "s = {(\<lambda>x. p)}"
  show "ksimplex p 0 s"
  proof (intro ksimplex, unfold_locales)
    show "(\<lambda>_. p) \<in> {..<0::nat} \<rightarrow> {..<p}" by auto
    show "bij_betw id {..<0} {..<0}"
      by simp
  qed (auto simp: s)
qed

lemma kuhn_combinatorial:
  assumes "0 < p"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> j < n \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> j < n  \<and> x j = p \<longrightarrow> lab x j = 1"
  shows "odd (card {s. ksimplex p n s \<and> (reduced n\<circ>lab) ` s = {..n}})"
    (is "odd (card (?M n))")
  using assms
proof (induct n)
  case 0 then show ?case
    by (simp add: ksimplex_0 cong: conj_cong)
next
  case (Suc n)
  then have "odd (card (?M n))"
    by force
  with Suc show ?case
    using kuhn_induction[of p n] by (auto simp: comp_def)
qed

lemma kuhn_lemma:
  fixes n p :: nat
  assumes "0 < p"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. label x i = (0::nat) \<or> label x i = 1)"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = 0 \<longrightarrow> label x i = 0)"
    and "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = p \<longrightarrow> label x i = 1)"
  obtains q where "\<forall>i<n. q i < p"
    and "\<forall>i<n. \<exists>r s. (\<forall>j<n. q j \<le> r j \<and> r j \<le> q j + 1) \<and> (\<forall>j<n. q j \<le> s j \<and> s j \<le> q j + 1) \<and> label r i \<noteq> label s i"
proof -
  let ?rl = "reduced n \<circ> label"
  let ?A = "{s. ksimplex p n s \<and> ?rl ` s = {..n}}"
  have "odd (card ?A)"
    using assms by (intro kuhn_combinatorial[of p n label]) auto
  then have "?A \<noteq> {}"
    by (rule odd_card_imp_not_empty)
  then obtain s b u where "kuhn_simplex p n b u s" and rl: "?rl ` s = {..n}"
    by (auto elim: ksimplex.cases)
  interpret kuhn_simplex p n b u s by fact

  show ?thesis
  proof (intro that[of b] allI impI)
    fix i
    assume "i < n"
    then show "b i < p"
      using base by auto
  next
    fix i
    assume "i < n"
    then have "i \<in> {.. n}" "Suc i \<in> {.. n}"
      by auto
    then obtain u v where u: "u \<in> s" "Suc i = ?rl u" and v: "v \<in> s" "i = ?rl v"
      unfolding rl[symmetric] by blast

    have "label u i \<noteq> label v i"
      using reduced_labelling [of n "label u"] reduced_labelling [of n "label v"]
        u(2)[symmetric] v(2)[symmetric] \<open>i < n\<close>
      by auto
    moreover
    have "b j \<le> u j" "u j \<le> b j + 1" "b j \<le> v j" "v j \<le> b j + 1" if "j < n" for j
      using that base_le[OF \<open>u\<in>s\<close>] le_Suc_base[OF \<open>u\<in>s\<close>] base_le[OF \<open>v\<in>s\<close>] le_Suc_base[OF \<open>v\<in>s\<close>]
      by auto
    ultimately show "\<exists>r s. (\<forall>j<n. b j \<le> r j \<and> r j \<le> b j + 1) \<and>
        (\<forall>j<n. b j \<le> s j \<and> s j \<le> b j + 1) \<and> label r i \<noteq> label s i"
      by blast
  qed
qed

subsubsection \<open>Main result for the unit cube\<close>

lemma kuhn_labelling_lemma':
  assumes "(\<forall>x::nat\<Rightarrow>real. P x \<longrightarrow> P (f x))"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i::nat. Q i \<longrightarrow> 0 \<le> x i \<and> x i \<le> 1)"
  shows "\<exists>l. (\<forall>x i. l x i \<le> (1::nat)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 0 \<longrightarrow> l x i = 0) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 1 \<longrightarrow> l x i = 1) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 0 \<longrightarrow> x i \<le> f x i) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 1 \<longrightarrow> f x i \<le> x i)"
proof -
  have and_forall_thm: "\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)"
    by auto
  have *: "\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x"
    by auto
  show ?thesis
    unfolding and_forall_thm
    apply (subst choice_iff[symmetric])+
    apply rule
    apply rule
  proof -
    fix x x'
    let ?R = "\<lambda>y::nat.
      (P x \<and> Q x' \<and> x x' = 0 \<longrightarrow> y = 0) \<and>
      (P x \<and> Q x' \<and> x x' = 1 \<longrightarrow> y = 1) \<and>
      (P x \<and> Q x' \<and> y = 0 \<longrightarrow> x x' \<le> (f x) x') \<and>
      (P x \<and> Q x' \<and> y = 1 \<longrightarrow> (f x) x' \<le> x x')"
    have "0 \<le> f x x' \<and> f x x' \<le> 1" if "P x" "Q x'"
      using assms(2)[rule_format,of "f x" x'] that
      apply (drule_tac assms(1)[rule_format])
      apply auto
      done
    then have "?R 0 \<or> ?R 1"
      by auto
    then show "\<exists>y\<le>1. ?R y"
      by auto
  qed
qed

subsection \<open>Brouwer's fixed point theorem\<close>

text \<open>We start proving Brouwer's fixed point theorem for the unit cube = \<open>cbox 0 One\<close>.\<close>

lemma brouwer_cube:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "continuous_on (cbox 0 One) f"
    and "f ` cbox 0 One \<subseteq> cbox 0 One"
  shows "\<exists>x\<in>cbox 0 One. f x = x"
proof (rule ccontr)
  define n where "n = DIM('a)"
  have n: "1 \<le> n" "0 < n" "n \<noteq> 0"
    unfolding n_def by (auto simp: Suc_le_eq DIM_positive)
  assume "\<not> ?thesis"
  then have *: "\<not> (\<exists>x\<in>cbox 0 One. f x - x = 0)"
    by auto
  obtain d where
      d: "d > 0" "\<And>x. x \<in> cbox 0 One \<Longrightarrow> d \<le> norm (f x - x)"
    apply (rule brouwer_compactness_lemma[OF compact_cbox _ *])
    apply (rule continuous_intros assms)+
    apply blast
    done
  have *: "\<forall>x. x \<in> cbox 0 One \<longrightarrow> f x \<in> cbox 0 One"
    "\<forall>x. x \<in> (cbox 0 One::'a set) \<longrightarrow> (\<forall>i\<in>Basis. True \<longrightarrow> 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1)"
    using assms(2)[unfolded image_subset_iff Ball_def]
    unfolding cbox_def
    by auto
  obtain label :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where label [rule_format]:
    "\<forall>x. \<forall>i\<in>Basis. label x i \<le> 1"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> cbox 0 One \<and> x \<bullet> i = 0 \<longrightarrow> label x i = 0"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> cbox 0 One \<and> x \<bullet> i = 1 \<longrightarrow> label x i = 1"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> cbox 0 One \<and> label x i = 0 \<longrightarrow> x \<bullet> i \<le> f x \<bullet> i"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> cbox 0 One \<and> label x i = 1 \<longrightarrow> f x \<bullet> i \<le> x \<bullet> i"
    using kuhn_labelling_lemma[OF *] by auto
  note label = this [rule_format]
  have lem1: "\<forall>x\<in>cbox 0 One. \<forall>y\<in>cbox 0 One. \<forall>i\<in>Basis. label x i \<noteq> label y i \<longrightarrow>
    \<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y - f x) + norm (y - x)"
  proof safe
    fix x y :: 'a
    assume x: "x \<in> cbox 0 One" and y: "y \<in> cbox 0 One"
    fix i
    assume i: "label x i \<noteq> label y i" "i \<in> Basis"
    have *: "\<And>x y fx fy :: real. x \<le> fx \<and> fy \<le> y \<or> fx \<le> x \<and> y \<le> fy \<Longrightarrow>
      \<bar>fx - x\<bar> \<le> \<bar>fy - fx\<bar> + \<bar>y - x\<bar>" by auto
    have "\<bar>(f x - x) \<bullet> i\<bar> \<le> \<bar>(f y - f x)\<bullet>i\<bar> + \<bar>(y - x)\<bullet>i\<bar>"
    proof (cases "label x i = 0")
      case True
      then have fxy: "\<not> f y \<bullet> i \<le> y \<bullet> i \<Longrightarrow> f x \<bullet> i \<le> x \<bullet> i"
        by (metis True i label(1) label(5) le_antisym less_one not_le_imp_less y)
      show ?thesis
      unfolding inner_simps         
      by (rule *) (auto simp: True i label x y fxy)
    next
      case False
      then show ?thesis
        using label [OF \<open>i \<in> Basis\<close>] i(1) x y
        apply (auto simp: inner_diff_left le_Suc_eq)
        by (metis "*")
    qed
    also have "\<dots> \<le> norm (f y - f x) + norm (y - x)"
      by (simp add: add_mono i(2) norm_bound_Basis_le)
    finally show "\<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y - f x) + norm (y - x)"
      unfolding inner_simps .
  qed
  have "\<exists>e>0. \<forall>x\<in>cbox 0 One. \<forall>y\<in>cbox 0 One. \<forall>z\<in>cbox 0 One. \<forall>i\<in>Basis.
    norm (x - z) < e \<longrightarrow> norm (y - z) < e \<longrightarrow> label x i \<noteq> label y i \<longrightarrow>
      \<bar>(f(z) - z)\<bullet>i\<bar> < d / (real n)"
  proof -
    have d': "d / real n / 8 > 0"
      using d(1) by (simp add: n_def DIM_positive)
    have *: "uniformly_continuous_on (cbox 0 One) f"
      by (rule compact_uniformly_continuous[OF assms(1) compact_cbox])
    obtain e where e:
        "e > 0"
        "\<And>x x'. x \<in> cbox 0 One \<Longrightarrow>
          x' \<in> cbox 0 One \<Longrightarrow>
          norm (x' - x) < e \<Longrightarrow>
          norm (f x' - f x) < d / real n / 8"
      using *[unfolded uniformly_continuous_on_def,rule_format,OF d']
      unfolding dist_norm
      by blast
    show ?thesis
    proof (intro exI conjI ballI impI)
      show "0 < min (e / 2) (d / real n / 8)"
        using d' e by auto
      fix x y z i
      assume as:
        "x \<in> cbox 0 One" "y \<in> cbox 0 One" "z \<in> cbox 0 One"
        "norm (x - z) < min (e / 2) (d / real n / 8)"
        "norm (y - z) < min (e / 2) (d / real n / 8)"
        "label x i \<noteq> label y i"
      assume i: "i \<in> Basis"
      have *: "\<And>z fz x fx n1 n2 n3 n4 d4 d :: real. \<bar>fx - x\<bar> \<le> n1 + n2 \<Longrightarrow>
        \<bar>fx - fz\<bar> \<le> n3 \<Longrightarrow> \<bar>x - z\<bar> \<le> n4 \<Longrightarrow>
        n1 < d4 \<Longrightarrow> n2 < 2 * d4 \<Longrightarrow> n3 < d4 \<Longrightarrow> n4 < d4 \<Longrightarrow>
        (8 * d4 = d) \<Longrightarrow> \<bar>fz - z\<bar> < d"
        by auto
      show "\<bar>(f z - z) \<bullet> i\<bar> < d / real n"
        unfolding inner_simps
      proof (rule *)
        show "\<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y -f x) + norm (y - x)"
          using as(1) as(2) as(6) i lem1 by blast
        show "norm (f x - f z) < d / real n / 8"
          using d' e as by auto
        show "\<bar>f x \<bullet> i - f z \<bullet> i\<bar> \<le> norm (f x - f z)" "\<bar>x \<bullet> i - z \<bullet> i\<bar> \<le> norm (x - z)"
          unfolding inner_diff_left[symmetric]
          by (rule Basis_le_norm[OF i])+
        have tria: "norm (y - x) \<le> norm (y - z) + norm (x - z)"
          using dist_triangle[of y x z, unfolded dist_norm]
          unfolding norm_minus_commute
          by auto
        also have "\<dots> < e / 2 + e / 2"
          using as(4) as(5) by auto
        finally show "norm (f y - f x) < d / real n / 8"
          using as(1) as(2) e(2) by auto
        have "norm (y - z) + norm (x - z) < d / real n / 8 + d / real n / 8"
          using as(4) as(5) by auto
        with tria show "norm (y - x) < 2 * (d / real n / 8)"
          by auto
      qed (use as in auto)
    qed
  qed
  then
  obtain e where e:
    "e > 0"
    "\<And>x y z i. x \<in> cbox 0 One \<Longrightarrow>
      y \<in> cbox 0 One \<Longrightarrow>
      z \<in> cbox 0 One \<Longrightarrow>
      i \<in> Basis \<Longrightarrow>
      norm (x - z) < e \<and> norm (y - z) < e \<and> label x i \<noteq> label y i \<Longrightarrow>
      \<bar>(f z - z) \<bullet> i\<bar> < d / real n"
    by blast
  obtain p :: nat where p: "1 + real n / e \<le> real p"
    using real_arch_simple ..
  have "1 + real n / e > 0"
    using e(1) n by (simp add: add_pos_pos)
  then have "p > 0"
    using p by auto

  obtain b :: "nat \<Rightarrow> 'a" where b: "bij_betw b {..< n} Basis"
    by atomize_elim (auto simp: n_def intro!: finite_same_card_bij)
  define b' where "b' = inv_into {..< n} b"
  then have b': "bij_betw b' Basis {..< n}"
    using bij_betw_inv_into[OF b] by auto
  then have b'_Basis: "\<And>i. i \<in> Basis \<Longrightarrow> b' i \<in> {..< n}"
    unfolding bij_betw_def by (auto simp: set_eq_iff)
  have bb'[simp]:"\<And>i. i \<in> Basis \<Longrightarrow> b (b' i) = i"
    unfolding b'_def
    using b
    by (auto simp: f_inv_into_f bij_betw_def)
  have b'b[simp]:"\<And>i. i < n \<Longrightarrow> b' (b i) = i"
    unfolding b'_def
    using b
    by (auto simp: inv_into_f_eq bij_betw_def)
  have *: "\<And>x :: nat. x = 0 \<or> x = 1 \<longleftrightarrow> x \<le> 1"
    by auto
  have b'': "\<And>j. j < n \<Longrightarrow> b j \<in> Basis"
    using b unfolding bij_betw_def by auto
  have q1: "0 < p" "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow>
    (\<forall>i<n. (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0 \<or>
           (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1)"
    unfolding *
    using \<open>p > 0\<close> \<open>n > 0\<close>
    using label(1)[OF b'']
    by auto
  { fix x :: "nat \<Rightarrow> nat" and i assume "\<forall>i<n. x i \<le> p" "i < n" "x i = p \<or> x i = 0"
    then have "(\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<in> (cbox 0 One::'a set)"
      using b'_Basis
      by (auto simp: cbox_def inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1) }
  note cube = this
  have q2: "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = 0 \<longrightarrow>
      (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0)"
    unfolding o_def using cube \<open>p > 0\<close> by (intro allI impI label(2)) (auto simp: b'')
  have q3: "\<forall>x. (\<forall>i<n. x i \<le> p) \<longrightarrow> (\<forall>i<n. x i = p \<longrightarrow>
      (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1)"
    using cube \<open>p > 0\<close> unfolding o_def by (intro allI impI label(3)) (auto simp: b'')
  obtain q where q:
      "\<forall>i<n. q i < p"
      "\<forall>i<n.
         \<exists>r s. (\<forall>j<n. q j \<le> r j \<and> r j \<le> q j + 1) \<and>
               (\<forall>j<n. q j \<le> s j \<and> s j \<le> q j + 1) \<and>
               (label (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i) \<circ> b) i \<noteq>
               (label (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i) \<circ> b) i"
    by (rule kuhn_lemma[OF q1 q2 q3])
  define z :: 'a where "z = (\<Sum>i\<in>Basis. (real (q (b' i)) / real p) *\<^sub>R i)"
  have "\<exists>i\<in>Basis. d / real n \<le> \<bar>(f z - z)\<bullet>i\<bar>"
  proof (rule ccontr)
    have "\<forall>i\<in>Basis. q (b' i) \<in> {0..p}"
      using q(1) b'
      by (auto intro: less_imp_le simp: bij_betw_def)
    then have "z \<in> cbox 0 One"
      unfolding z_def cbox_def
      using b'_Basis
      by (auto simp: bij_betw_def zero_le_divide_iff divide_le_eq_1)
    then have d_fz_z: "d \<le> norm (f z - z)"
      by (rule d)
    assume "\<not> ?thesis"
    then have as: "\<forall>i\<in>Basis. \<bar>f z \<bullet> i - z \<bullet> i\<bar> < d / real n"
      using \<open>n > 0\<close>
      by (auto simp: not_le inner_diff)
    have "norm (f z - z) \<le> (\<Sum>i\<in>Basis. \<bar>f z \<bullet> i - z \<bullet> i\<bar>)"
      unfolding inner_diff_left[symmetric]
      by (rule norm_le_l1)
    also have "\<dots> < (\<Sum>(i::'a) \<in> Basis. d / real n)"
      by (meson as finite_Basis nonempty_Basis sum_strict_mono)
    also have "\<dots> = d"
      using DIM_positive[where 'a='a] by (auto simp: n_def)
    finally show False
      using d_fz_z by auto
  qed
  then obtain i where i: "i \<in> Basis" "d / real n \<le> \<bar>(f z - z) \<bullet> i\<bar>" ..
  have *: "b' i < n"
    using i and b'[unfolded bij_betw_def]
    by auto
  obtain r s where rs:
    "\<And>j. j < n \<Longrightarrow> q j \<le> r j \<and> r j \<le> q j + 1"
    "\<And>j. j < n \<Longrightarrow> q j \<le> s j \<and> s j \<le> q j + 1"
    "(label (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i) \<circ> b) (b' i) \<noteq>
      (label (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i) \<circ> b) (b' i)"
    using q(2)[rule_format,OF *] by blast
  have b'_im: "\<And>i. i \<in> Basis \<Longrightarrow>  b' i < n"
    using b' unfolding bij_betw_def by auto
  define r' ::'a where "r' = (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i)"
  have "\<And>i. i \<in> Basis \<Longrightarrow> r (b' i) \<le> p"
    apply (rule order_trans)
    apply (rule rs(1)[OF b'_im,THEN conjunct2])
    using q(1)[rule_format,OF b'_im]
    apply (auto simp: Suc_le_eq)
    done
  then have "r' \<in> cbox 0 One"
    unfolding r'_def cbox_def
    using b'_Basis
    by (auto simp: bij_betw_def zero_le_divide_iff divide_le_eq_1)
  define s' :: 'a where "s' = (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i)"
  have "\<And>i. i \<in> Basis \<Longrightarrow> s (b' i) \<le> p"
    using b'_im q(1) rs(2) by fastforce
  then have "s' \<in> cbox 0 One"
    unfolding s'_def cbox_def
    using b'_Basis by (auto simp: bij_betw_def zero_le_divide_iff divide_le_eq_1)
  have "z \<in> cbox 0 One"
    unfolding z_def cbox_def
    using b'_Basis q(1)[rule_format,OF b'_im] \<open>p > 0\<close>
    by (auto simp: bij_betw_def zero_le_divide_iff divide_le_eq_1 less_imp_le)
  {
    have "(\<Sum>i\<in>Basis. \<bar>real (r (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>(i::'a)\<in>Basis. 1)"
      by (rule sum_mono) (use rs(1)[OF b'_im] in force)
    also have "\<dots> < e * real p"
      using p \<open>e > 0\<close> \<open>p > 0\<close>
      by (auto simp: field_simps n_def)
    finally have "(\<Sum>i\<in>Basis. \<bar>real (r (b' i)) - real (q (b' i))\<bar>) < e * real p" .
  }
  moreover
  {
    have "(\<Sum>i\<in>Basis. \<bar>real (s (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>(i::'a)\<in>Basis. 1)"
      by (rule sum_mono) (use rs(2)[OF b'_im] in force)
    also have "\<dots> < e * real p"
      using p \<open>e > 0\<close> \<open>p > 0\<close>
      by (auto simp: field_simps n_def)
    finally have "(\<Sum>i\<in>Basis. \<bar>real (s (b' i)) - real (q (b' i))\<bar>) < e * real p" .
  }
  ultimately
  have "norm (r' - z) < e" and "norm (s' - z) < e"
    unfolding r'_def s'_def z_def
    using \<open>p > 0\<close>
    apply (rule_tac[!] le_less_trans[OF norm_le_l1])
    apply (auto simp: field_simps sum_divide_distrib[symmetric] inner_diff_left)
    done
  then have "\<bar>(f z - z) \<bullet> i\<bar> < d / real n"
    using rs(3) i
    unfolding r'_def[symmetric] s'_def[symmetric] o_def bb'
    by (intro e(2)[OF \<open>r'\<in>cbox 0 One\<close> \<open>s'\<in>cbox 0 One\<close> \<open>z\<in>cbox 0 One\<close>]) auto
  then show False
    using i by auto
qed

text \<open>Next step is to prove it for nonempty interiors.\<close>

lemma brouwer_weak:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "compact S"
    and "convex S"
    and "interior S \<noteq> {}"
    and "continuous_on S f"
    and "f ` S \<subseteq> S"
  obtains x where "x \<in> S" and "f x = x"
proof -
  let ?U = "cbox 0 One :: 'a set"
  have "\<Sum>Basis /\<^sub>R 2 \<in> interior ?U"
  proof (rule interiorI)
    let ?I = "(\<Inter>i\<in>Basis. {x::'a. 0 < x \<bullet> i} \<inter> {x. x \<bullet> i < 1})"
    show "open ?I"
      by (intro open_INT finite_Basis ballI open_Int, auto intro: open_Collect_less simp: continuous_on_inner continuous_on_const continuous_on_id)
    show "\<Sum>Basis /\<^sub>R 2 \<in> ?I"
      by simp
    show "?I \<subseteq> cbox 0 One"
      unfolding cbox_def by force
  qed
  then have *: "interior ?U \<noteq> {}" by fast
  have *: "?U homeomorphic S"
    using homeomorphic_convex_compact[OF convex_box(1) compact_cbox * assms(2,1,3)] .
  have "\<forall>f. continuous_on ?U f \<and> f ` ?U \<subseteq> ?U \<longrightarrow>
    (\<exists>x\<in>?U. f x = x)"
    using brouwer_cube by auto
  then show ?thesis
    unfolding homeomorphic_fixpoint_property[OF *]
    using assms
    by (auto intro: that)
qed

text \<open>Then the particular case for closed balls.\<close>

lemma brouwer_ball:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "e > 0"
    and "continuous_on (cball a e) f"
    and "f ` cball a e \<subseteq> cball a e"
  obtains x where "x \<in> cball a e" and "f x = x"
  using brouwer_weak[OF compact_cball convex_cball, of a e f]
  unfolding interior_cball ball_eq_empty
  using assms by auto

text \<open>And finally we prove Brouwer's fixed point theorem in its general version.\<close>

theorem brouwer:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes S: "compact S" "convex S" "S \<noteq> {}"
    and contf: "continuous_on S f"
    and fim: "f ` S \<subseteq> S"
  obtains x where "x \<in> S" and "f x = x"
proof -
  have "\<exists>e>0. S \<subseteq> cball 0 e"
    using compact_imp_bounded[OF \<open>compact S\<close>]  unfolding bounded_pos
    by auto
  then obtain e where e: "e > 0" "S \<subseteq> cball 0 e"
    by blast
  have "\<exists>x\<in> cball 0 e. (f \<circ> closest_point S) x = x"
  proof (rule_tac brouwer_ball[OF e(1)])
    show "continuous_on (cball 0 e) (f \<circ> closest_point S)"
      apply (rule continuous_on_compose)
      using S compact_eq_bounded_closed continuous_on_closest_point apply blast
      by (meson S contf closest_point_in_set compact_imp_closed continuous_on_subset image_subsetI)
    show "(f \<circ> closest_point S) ` cball 0 e \<subseteq> cball 0 e"
      by clarsimp (metis S fim closest_point_exists(1) compact_eq_bounded_closed e(2) image_subset_iff mem_cball_0 subsetCE)
  qed (use assms in auto)
  then obtain x where x: "x \<in> cball 0 e" "(f \<circ> closest_point S) x = x" ..
  have "x \<in> S"
    by (metis closest_point_in_set comp_apply compact_imp_closed fim image_eqI S(1) S(3) subset_iff x(2))
  then have *: "closest_point S x = x"
    by (rule closest_point_self)
  show thesis
  proof
    show "closest_point S x \<in> S"
      by (simp add: "*" \<open>x \<in> S\<close>)
    show "f (closest_point S x) = closest_point S x"
      using "*" x(2) by auto
  qed
qed

subsection \<open>Applications\<close>

text \<open>So we get the no-retraction theorem.\<close>

corollary no_retraction_cball:
  fixes a :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<not> (frontier (cball a e) retract_of (cball a e))"
proof
  assume *: "frontier (cball a e) retract_of (cball a e)"
  have **: "\<And>xa. a - (2 *\<^sub>R a - xa) = - (a - xa)"
    using scaleR_left_distrib[of 1 1 a] by auto
  obtain x where x: "x \<in> {x. norm (a - x) = e}" "2 *\<^sub>R a - x = x"
  proof (rule retract_fixpoint_property[OF *, of "\<lambda>x. scaleR 2 a - x"])
    show "continuous_on (frontier (cball a e)) ((-) (2 *\<^sub>R a))"
      by (intro continuous_intros)
    show "(-) (2 *\<^sub>R a) ` frontier (cball a e) \<subseteq> frontier (cball a e)"
      by clarsimp (metis "**" dist_norm norm_minus_cancel)
  qed (auto simp: dist_norm intro: brouwer_ball[OF assms])
  then have "scaleR 2 a = scaleR 1 x + scaleR 1 x"
    by (auto simp: algebra_simps)
  then have "a = x"
    unfolding scaleR_left_distrib[symmetric]
    by auto
  then show False
    using x assms by auto
qed

corollary contractible_sphere:
  fixes a :: "'a::euclidean_space"
  shows "contractible(sphere a r) \<longleftrightarrow> r \<le> 0"
proof (cases "0 < r")
  case True
  then show ?thesis
    unfolding contractible_def nullhomotopic_from_sphere_extension
    using no_retraction_cball [OF True, of a]
    by (auto simp: retract_of_def retraction_def)
next
  case False
  then show ?thesis
    unfolding contractible_def nullhomotopic_from_sphere_extension
    using continuous_on_const less_eq_real_def by auto
qed

corollary connected_sphere_eq:
  fixes a :: "'a :: euclidean_space"
  shows "connected(sphere a r) \<longleftrightarrow> 2 \<le> DIM('a) \<or> r \<le> 0"
    (is "?lhs = ?rhs")
proof (cases r "0::real" rule: linorder_cases)
  case less
  then show ?thesis by auto
next
  case equal
  then show ?thesis by auto
next
  case greater
  show ?thesis
  proof
    assume L: ?lhs
    have "False" if 1: "DIM('a) = 1"
    proof -
      obtain x y where xy: "sphere a r = {x,y}" "x \<noteq> y"
        using sphere_1D_doubleton [OF 1 greater]
        by (metis dist_self greater insertI1 less_add_same_cancel1 mem_sphere mult_2 not_le zero_le_dist)
      then have "finite (sphere a r)"
        by auto
      with L \<open>r > 0\<close> xy show "False"
        using connected_finite_iff_sing by auto
    qed
    with greater show ?rhs
      by (metis DIM_ge_Suc0 One_nat_def Suc_1 le_antisym not_less_eq_eq)
  next
    assume ?rhs
    then show ?lhs
      using connected_sphere greater by auto
  qed
qed

corollary path_connected_sphere_eq:
  fixes a :: "'a :: euclidean_space"
  shows "path_connected(sphere a r) \<longleftrightarrow> 2 \<le> DIM('a) \<or> r \<le> 0"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using connected_sphere_eq path_connected_imp_connected by blast
next
  assume R: ?rhs
  then show ?lhs
    by (auto simp: contractible_imp_path_connected contractible_sphere path_connected_sphere)
qed

proposition frontier_subset_retraction:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" and fros: "frontier S \<subseteq> T"
      and contf: "continuous_on (closure S) f"
      and fim: "f ` S \<subseteq> T"
      and fid: "\<And>x. x \<in> T \<Longrightarrow> f x = x"
    shows "S \<subseteq> T"
proof (rule ccontr)
  assume "\<not> S \<subseteq> T"
  then obtain a where "a \<in> S" "a \<notin> T" by blast
  define g where "g \<equiv> \<lambda>z. if z \<in> closure S then f z else z"
  have "continuous_on (closure S \<union> closure(-S)) g"
    unfolding g_def
    apply (rule continuous_on_cases)
    using fros fid frontier_closures
        apply (auto simp: contf continuous_on_id)
    done
  moreover have "closure S \<union> closure(- S) = UNIV"
    using closure_Un by fastforce
  ultimately have contg: "continuous_on UNIV g" by metis
  obtain B where "0 < B" and B: "closure S \<subseteq> ball a B"
    using \<open>bounded S\<close> bounded_subset_ballD by blast
  have notga: "g x \<noteq> a" for x
    unfolding g_def using fros fim \<open>a \<notin> T\<close>
    apply (auto simp: frontier_def)
    using fid interior_subset apply fastforce
    by (simp add: \<open>a \<in> S\<close> closure_def)
  define h where "h \<equiv> (\<lambda>y. a + (B / norm(y - a)) *\<^sub>R (y - a)) \<circ> g"
  have "\<not> (frontier (cball a B) retract_of (cball a B))"
    by (metis no_retraction_cball \<open>0 < B\<close>)
  then have "\<And>k. \<not> retraction (cball a B) (frontier (cball a B)) k"
    by (simp add: retract_of_def)
  moreover have "retraction (cball a B) (frontier (cball a B)) h"
    unfolding retraction_def
  proof (intro conjI ballI)
    show "frontier (cball a B) \<subseteq> cball a B"
      by force
    show "continuous_on (cball a B) h"
      unfolding h_def
      by (intro continuous_intros) (use contg continuous_on_subset notga in auto)
    show "h ` cball a B \<subseteq> frontier (cball a B)"
      using \<open>0 < B\<close> by (auto simp: h_def notga dist_norm)
    show "\<And>x. x \<in> frontier (cball a B) \<Longrightarrow> h x = x"
      apply (auto simp: h_def algebra_simps)
      apply (simp add: vector_add_divide_simps  notga)
      by (metis (no_types, hide_lams) B add.commute dist_commute  dist_norm g_def mem_ball not_less_iff_gr_or_eq  subset_eq)
  qed
  ultimately show False by simp
qed

subsubsection \<open>Punctured affine hulls, etc\<close>

lemma rel_frontier_deformation_retract_of_punctured_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "convex T" "bounded S"
      and arelS: "a \<in> rel_interior S"
      and relS: "rel_frontier S \<subseteq> T"
      and affS: "T \<subseteq> affine hull S"
  obtains r where "homotopic_with (\<lambda>x. True) (T - {a}) (T - {a}) id r"
                  "retraction (T - {a}) (rel_frontier S) r"
proof -
  have "\<exists>d. 0 < d \<and> (a + d *\<^sub>R l) \<in> rel_frontier S \<and>
            (\<forall>e. 0 \<le> e \<and> e < d \<longrightarrow> (a + e *\<^sub>R l) \<in> rel_interior S)"
       if "(a + l) \<in> affine hull S" "l \<noteq> 0" for l
    apply (rule ray_to_rel_frontier [OF \<open>bounded S\<close> arelS])
    apply (rule that)+
    by metis
  then obtain dd
    where dd1: "\<And>l. \<lbrakk>(a + l) \<in> affine hull S; l \<noteq> 0\<rbrakk> \<Longrightarrow> 0 < dd l \<and> (a + dd l *\<^sub>R l) \<in> rel_frontier S"
      and dd2: "\<And>l e. \<lbrakk>(a + l) \<in> affine hull S; e < dd l; 0 \<le> e; l \<noteq> 0\<rbrakk>
                      \<Longrightarrow> (a + e *\<^sub>R l) \<in> rel_interior S"
    by metis+
  have aaffS: "a \<in> affine hull S"
    by (meson arelS subsetD hull_inc rel_interior_subset)
  have "((\<lambda>z. z - a) ` (affine hull S - {a})) = ((\<lambda>z. z - a) ` (affine hull S)) - {0}"
    by auto
  moreover have "continuous_on (((\<lambda>z. z - a) ` (affine hull S)) - {0}) (\<lambda>x. dd x *\<^sub>R x)"
  proof (rule continuous_on_compact_surface_projection)
    show "compact (rel_frontier ((\<lambda>z. z - a) ` S))"
      by (simp add: \<open>bounded S\<close> bounded_translation_minus compact_rel_frontier_bounded)
    have releq: "rel_frontier ((\<lambda>z. z - a) ` S) = (\<lambda>z. z - a) ` rel_frontier S"
      using rel_frontier_translation [of "-a"] add.commute by simp
    also have "\<dots> \<subseteq> (\<lambda>z. z - a) ` (affine hull S) - {0}"
      using rel_frontier_affine_hull arelS rel_frontier_def by fastforce
    finally show "rel_frontier ((\<lambda>z. z - a) ` S) \<subseteq> (\<lambda>z. z - a) ` (affine hull S) - {0}" .
    show "cone ((\<lambda>z. z - a) ` (affine hull S))"
      by (rule subspace_imp_cone)
         (use aaffS in \<open>simp add: subspace_affine image_comp o_def affine_translation_aux [of a]\<close>)
    show "(0 < k \<and> k *\<^sub>R x \<in> rel_frontier ((\<lambda>z. z - a) ` S)) \<longleftrightarrow> (dd x = k)"
         if x: "x \<in> (\<lambda>z. z - a) ` (affine hull S) - {0}" for k x
    proof
      show "dd x = k \<Longrightarrow> 0 < k \<and> k *\<^sub>R x \<in> rel_frontier ((\<lambda>z. z - a) ` S)"
      using dd1 [of x] that image_iff by (fastforce simp add: releq)
    next
      assume k: "0 < k \<and> k *\<^sub>R x \<in> rel_frontier ((\<lambda>z. z - a) ` S)"
      have False if "dd x < k"
      proof -
        have "k \<noteq> 0" "a + k *\<^sub>R x \<in> closure S"
          using k closure_translation [of "-a"]
          by (auto simp: rel_frontier_def cong: image_cong_simp)
        then have segsub: "open_segment a (a + k *\<^sub>R x) \<subseteq> rel_interior S"
          by (metis rel_interior_closure_convex_segment [OF \<open>convex S\<close> arelS])
        have "x \<noteq> 0" and xaffS: "a + x \<in> affine hull S"
          using x by auto
        then have "0 < dd x" and inS: "a + dd x *\<^sub>R x \<in> rel_frontier S"
          using dd1 by auto
        moreover have "a + dd x *\<^sub>R x \<in> open_segment a (a + k *\<^sub>R x)"
          using k \<open>x \<noteq> 0\<close> \<open>0 < dd x\<close>
          apply (simp add: in_segment)
          apply (rule_tac x = "dd x / k" in exI)
          apply (simp add: field_simps that)
          apply (simp add: vector_add_divide_simps algebra_simps)
          apply (metis (no_types) \<open>k \<noteq> 0\<close> divide_inverse_commute inverse_eq_divide mult.left_commute right_inverse)
          done
        ultimately show ?thesis
          using segsub by (auto simp: rel_frontier_def)
      qed
      moreover have False if "k < dd x"
        using x k that rel_frontier_def
        by (fastforce simp: algebra_simps releq dest!: dd2)
      ultimately show "dd x = k"
        by fastforce
    qed
  qed
  ultimately have *: "continuous_on ((\<lambda>z. z - a) ` (affine hull S - {a})) (\<lambda>x. dd x *\<^sub>R x)"
    by auto
  have "continuous_on (affine hull S - {a}) ((\<lambda>x. a + dd x *\<^sub>R x) \<circ> (\<lambda>z. z - a))"
    by (intro * continuous_intros continuous_on_compose)
  with affS have contdd: "continuous_on (T - {a}) ((\<lambda>x. a + dd x *\<^sub>R x) \<circ> (\<lambda>z. z - a))"
    by (blast intro: continuous_on_subset)
  show ?thesis
  proof
    show "homotopic_with (\<lambda>x. True) (T - {a}) (T - {a}) id (\<lambda>x. a + dd (x - a) *\<^sub>R (x - a))"
    proof (rule homotopic_with_linear)
      show "continuous_on (T - {a}) id"
        by (intro continuous_intros continuous_on_compose)
      show "continuous_on (T - {a}) (\<lambda>x. a + dd (x - a) *\<^sub>R (x - a))"
        using contdd by (simp add: o_def)
      show "closed_segment (id x) (a + dd (x - a) *\<^sub>R (x - a)) \<subseteq> T - {a}"
           if "x \<in> T - {a}" for x
      proof (clarsimp simp: in_segment, intro conjI)
        fix u::real assume u: "0 \<le> u" "u \<le> 1"
        have "a + dd (x - a) *\<^sub>R (x - a) \<in> T"
          by (metis DiffD1 DiffD2 add.commute add.right_neutral affS dd1 diff_add_cancel relS singletonI subsetCE that)
        then show "(1 - u) *\<^sub>R x + u *\<^sub>R (a + dd (x - a) *\<^sub>R (x - a)) \<in> T"
          using convexD [OF \<open>convex T\<close>] that u by simp
        have iff: "(1 - u) *\<^sub>R x + u *\<^sub>R (a + d *\<^sub>R (x - a)) = a \<longleftrightarrow>
                  (1 - u + u * d) *\<^sub>R (x - a) = 0" for d
          by (auto simp: algebra_simps)
        have "x \<in> T" "x \<noteq> a" using that by auto
        then have axa: "a + (x - a) \<in> affine hull S"
           by (metis (no_types) add.commute affS diff_add_cancel rev_subsetD)
        then have "\<not> dd (x - a) \<le> 0 \<and> a + dd (x - a) *\<^sub>R (x - a) \<in> rel_frontier S"
          using \<open>x \<noteq> a\<close> dd1 by fastforce
        with \<open>x \<noteq> a\<close> show "(1 - u) *\<^sub>R x + u *\<^sub>R (a + dd (x - a) *\<^sub>R (x - a)) \<noteq> a"
          apply (auto simp: iff)
          using less_eq_real_def mult_le_0_iff not_less u by fastforce
      qed
    qed
    show "retraction (T - {a}) (rel_frontier S) (\<lambda>x. a + dd (x - a) *\<^sub>R (x - a))"
    proof (simp add: retraction_def, intro conjI ballI)
      show "rel_frontier S \<subseteq> T - {a}"
        using arelS relS rel_frontier_def by fastforce
      show "continuous_on (T - {a}) (\<lambda>x. a + dd (x - a) *\<^sub>R (x - a))"
        using contdd by (simp add: o_def)
      show "(\<lambda>x. a + dd (x - a) *\<^sub>R (x - a)) ` (T - {a}) \<subseteq> rel_frontier S"
        apply (auto simp: rel_frontier_def)
        apply (metis Diff_subset add.commute affS dd1 diff_add_cancel eq_iff_diff_eq_0 rel_frontier_def subset_iff)
        by (metis DiffE add.commute affS dd1 diff_add_cancel eq_iff_diff_eq_0 rel_frontier_def rev_subsetD)
      show "a + dd (x - a) *\<^sub>R (x - a) = x" if x: "x \<in> rel_frontier S" for x
      proof -
        have "x \<noteq> a"
          using that arelS by (auto simp: rel_frontier_def)
        have False if "dd (x - a) < 1"
        proof -
          have "x \<in> closure S"
            using x by (auto simp: rel_frontier_def)
          then have segsub: "open_segment a x \<subseteq> rel_interior S"
            by (metis rel_interior_closure_convex_segment [OF \<open>convex S\<close> arelS])
          have  xaffS: "x \<in> affine hull S"
            using affS relS x by auto
          then have "0 < dd (x - a)" and inS: "a + dd (x - a) *\<^sub>R (x - a) \<in> rel_frontier S"
            using dd1 by (auto simp: \<open>x \<noteq> a\<close>)
          moreover have "a + dd (x - a) *\<^sub>R (x - a) \<in> open_segment a x"
            using  \<open>x \<noteq> a\<close> \<open>0 < dd (x - a)\<close>
            apply (simp add: in_segment)
            apply (rule_tac x = "dd (x - a)" in exI)
            apply (simp add: algebra_simps that)
            done
          ultimately show ?thesis
            using segsub by (auto simp: rel_frontier_def)
        qed
        moreover have False if "1 < dd (x - a)"
          using x that dd2 [of "x - a" 1] \<open>x \<noteq> a\<close> closure_affine_hull
          by (auto simp: rel_frontier_def)
        ultimately have "dd (x - a) = 1" \<comment> \<open>similar to another proof above\<close>
          by fastforce
        with that show ?thesis
          by (simp add: rel_frontier_def)
      qed
    qed
  qed
qed

corollary rel_frontier_retract_of_punctured_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "bounded S" "convex S" "a \<in> rel_interior S"
    shows "rel_frontier S retract_of (affine hull S - {a})"
apply (rule rel_frontier_deformation_retract_of_punctured_convex [of S "affine hull S" a])
apply (auto simp: affine_imp_convex rel_frontier_affine_hull retract_of_def assms)
done

corollary rel_boundary_retract_of_punctured_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "compact S" "convex S" "a \<in> rel_interior S"
    shows "(S - rel_interior S) retract_of (affine hull S - {a})"
by (metis assms closure_closed compact_eq_bounded_closed rel_frontier_def
          rel_frontier_retract_of_punctured_affine_hull)

lemma homotopy_eqv_rel_frontier_punctured_convex:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "a \<in> rel_interior S" "convex T" "rel_frontier S \<subseteq> T" "T \<subseteq> affine hull S"
  shows "(rel_frontier S) homotopy_eqv (T - {a})"
  apply (rule rel_frontier_deformation_retract_of_punctured_convex [of S T])
  using assms
  apply auto
  apply (subst homotopy_eqv_sym)
  using deformation_retract_imp_homotopy_eqv by blast

lemma homotopy_eqv_rel_frontier_punctured_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "bounded S" "a \<in> rel_interior S"
    shows "(rel_frontier S) homotopy_eqv (affine hull S - {a})"
apply (rule homotopy_eqv_rel_frontier_punctured_convex)
  using assms rel_frontier_affine_hull  by force+

lemma path_connected_sphere_gen:
  assumes "convex S" "bounded S" "aff_dim S \<noteq> 1"
  shows "path_connected(rel_frontier S)"
proof (cases "rel_interior S = {}")
  case True
  then show ?thesis
    by (simp add: \<open>convex S\<close> convex_imp_path_connected rel_frontier_def)
next
  case False
  then show ?thesis
    by (metis aff_dim_affine_hull affine_affine_hull affine_imp_convex all_not_in_conv assms path_connected_punctured_convex rel_frontier_retract_of_punctured_affine_hull retract_of_path_connected)
qed

lemma connected_sphere_gen:
  assumes "convex S" "bounded S" "aff_dim S \<noteq> 1"
  shows "connected(rel_frontier S)"
  by (simp add: assms path_connected_imp_connected path_connected_sphere_gen)

subsubsection\<open>Borsuk-style characterization of separation\<close>

lemma continuous_on_Borsuk_map:
   "a \<notin> s \<Longrightarrow>  continuous_on s (\<lambda>x. inverse(norm (x - a)) *\<^sub>R (x - a))"
by (rule continuous_intros | force)+

lemma Borsuk_map_into_sphere:
   "(\<lambda>x. inverse(norm (x - a)) *\<^sub>R (x - a)) ` s \<subseteq> sphere 0 1 \<longleftrightarrow> (a \<notin> s)"
  by auto (metis eq_iff_diff_eq_0 left_inverse norm_eq_zero)

lemma Borsuk_maps_homotopic_in_path_component:
  assumes "path_component (- s) a b"
    shows "homotopic_with (\<lambda>x. True) s (sphere 0 1)
                   (\<lambda>x. inverse(norm(x - a)) *\<^sub>R (x - a))
                   (\<lambda>x. inverse(norm(x - b)) *\<^sub>R (x - b))"
proof -
  obtain g where "path g" "path_image g \<subseteq> -s" "pathstart g = a" "pathfinish g = b"
    using assms by (auto simp: path_component_def)
  then show ?thesis
    apply (simp add: path_def path_image_def pathstart_def pathfinish_def homotopic_with_def)
    apply (rule_tac x = "\<lambda>z. inverse(norm(snd z - (g \<circ> fst)z)) *\<^sub>R (snd z - (g \<circ> fst)z)" in exI)
    apply (intro conjI continuous_intros)
    apply (rule continuous_intros | erule continuous_on_subset | fastforce simp: divide_simps sphere_def)+
    done
qed

lemma non_extensible_Borsuk_map:
  fixes a :: "'a :: euclidean_space"
  assumes "compact s" and cin: "c \<in> components(- s)" and boc: "bounded c" and "a \<in> c"
    shows "\<not> (\<exists>g. continuous_on (s \<union> c) g \<and>
                  g ` (s \<union> c) \<subseteq> sphere 0 1 \<and>
                  (\<forall>x \<in> s. g x = inverse(norm(x - a)) *\<^sub>R (x - a)))"
proof -
  have "closed s" using assms by (simp add: compact_imp_closed)
  have "c \<subseteq> -s"
    using assms by (simp add: in_components_subset)
  with \<open>a \<in> c\<close> have "a \<notin> s" by blast
  then have ceq: "c = connected_component_set (- s) a"
    by (metis \<open>a \<in> c\<close> cin components_iff connected_component_eq)
  then have "bounded (s \<union> connected_component_set (- s) a)"
    using \<open>compact s\<close> boc compact_imp_bounded by auto
  with bounded_subset_ballD obtain r where "0 < r" and r: "(s \<union> connected_component_set (- s) a) \<subseteq> ball a r"
    by blast
  { fix g
    assume "continuous_on (s \<union> c) g"
            "g ` (s \<union> c) \<subseteq> sphere 0 1"
       and [simp]: "\<And>x. x \<in> s \<Longrightarrow> g x = (x - a) /\<^sub>R norm (x - a)"
    then have [simp]: "\<And>x. x \<in> s \<union> c \<Longrightarrow> norm (g x) = 1"
      by force
    have cb_eq: "cball a r = (s \<union> connected_component_set (- s) a) \<union>
                      (cball a r - connected_component_set (- s) a)"
      using ball_subset_cball [of a r] r by auto
    have cont1: "continuous_on (s \<union> connected_component_set (- s) a)
                     (\<lambda>x. a + r *\<^sub>R g x)"
      apply (rule continuous_intros)+
      using \<open>continuous_on (s \<union> c) g\<close> ceq by blast
    have cont2: "continuous_on (cball a r - connected_component_set (- s) a)
            (\<lambda>x. a + r *\<^sub>R ((x - a) /\<^sub>R norm (x - a)))"
      by (rule continuous_intros | force simp: \<open>a \<notin> s\<close>)+
    have 1: "continuous_on (cball a r)
             (\<lambda>x. if connected_component (- s) a x
                  then a + r *\<^sub>R g x
                  else a + r *\<^sub>R ((x - a) /\<^sub>R norm (x - a)))"
      apply (subst cb_eq)
      apply (rule continuous_on_cases [OF _ _ cont1 cont2])
        using ceq cin
      apply (auto intro: closed_Un_complement_component
                  simp: \<open>closed s\<close> open_Compl open_connected_component)
      done
    have 2: "(\<lambda>x. a + r *\<^sub>R g x) ` (cball a r \<inter> connected_component_set (- s) a)
             \<subseteq> sphere a r "
      using \<open>0 < r\<close> by (force simp: dist_norm ceq)
    have "retraction (cball a r) (sphere a r)
            (\<lambda>x. if x \<in> connected_component_set (- s) a
                 then a + r *\<^sub>R g x
                 else a + r *\<^sub>R ((x - a) /\<^sub>R norm (x - a)))"
      using  \<open>0 < r\<close>
      apply (simp add: retraction_def dist_norm 1 2, safe)
      apply (force simp: dist_norm abs_if mult_less_0_iff divide_simps \<open>a \<notin> s\<close>)
      using r
      by (auto simp: dist_norm norm_minus_commute)
    then have False
      using no_retraction_cball
             [OF \<open>0 < r\<close>, of a, unfolded retract_of_def, simplified, rule_format,
              of "\<lambda>x. if x \<in> connected_component_set (- s) a
                      then a + r *\<^sub>R g x
                      else a + r *\<^sub>R inverse(norm(x - a)) *\<^sub>R (x - a)"]
      by blast
  }
  then show ?thesis
    by blast
qed

subsubsection  \<open>We continue with ANRs and ENRs\<close>

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
    apply (simp add: retract_of_def retraction_def ahS)
    apply (rule_tac x="closest_point (affine hull S)" in exI)
    apply (auto simp: False closest_point_self affine_imp_convex closest_point_in_set continuous_on_closest_point)
    done
  finally have "rel_frontier S retract_of {x. closest_point (affine hull S) x \<noteq> a}" .
  moreover have "openin (subtopology euclidean UNIV) (UNIV \<inter> closest_point (affine hull S) -` (- {a}))"
    apply (rule continuous_openin_preimage_gen)
    apply (auto simp: False affine_imp_convex continuous_on_closest_point)
    done
  ultimately show ?thesis
    unfolding ENR_def
    apply (rule_tac x = "closest_point (affine hull S) -` (- {a})" in exI)
    apply (simp add: vimage_def)
    done
qed

lemma ANR_rel_frontier_convex:
                 fixes S :: "'a::euclidean_space set"
  assumes "bounded S" "convex S"
    shows "ANR(rel_frontier S)"
by (simp add: ENR_imp_ANR ENR_rel_frontier_convex assms)
    
lemma ENR_closedin_Un_local:
  fixes S :: "'a::euclidean_space set"
  shows "\<lbrakk>ENR S; ENR T; ENR(S \<inter> T);
          closedin (subtopology euclidean (S \<union> T)) S; closedin (subtopology euclidean (S \<union> T)) T\<rbrakk>
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
  assumes clS: "closedin (subtopology euclidean (S \<union> T)) S"
      and clT: "closedin (subtopology euclidean (S \<union> T)) T"
      and Un: "(S \<union> T) retract_of U" and Int: "(S \<inter> T) retract_of T"
    shows "S retract_of U"
proof -
  obtain r where r: "continuous_on T r" "r ` T \<subseteq> S \<inter> T" "\<forall>x\<in>S \<inter> T. r x = x"
    using Int by (auto simp: retraction_def retract_of_def)
  have "S retract_of S \<union> T"
    unfolding retraction_def retract_of_def
  proof (intro exI conjI)
    show "continuous_on (S \<union> T) (\<lambda>x. if x \<in> S then x else r x)"
      apply (rule continuous_on_cases_local [OF clS clT])
      using r by (auto simp: continuous_on_id)
  qed (use r in auto)
  also have "\<dots> retract_of U"
    by (rule Un)
  finally show ?thesis .
qed

lemma AR_from_Un_Int_local:
  fixes S :: "'a::euclidean_space set"
  assumes clS: "closedin (subtopology euclidean (S \<union> T)) S"
      and clT: "closedin (subtopology euclidean (S \<union> T)) T"
      and Un: "AR(S \<union> T)" and Int: "AR(S \<inter> T)"
    shows "AR S"
  apply (rule AR_retract_of_AR [OF Un])
  by (meson AR_imp_retract clS clT closedin_closed_subset local.Int retract_from_Un_Int retract_of_refl sup_ge2)

lemma AR_from_Un_Int_local':
  fixes S :: "'a::euclidean_space set"
  assumes "closedin (subtopology euclidean (S \<union> T)) S"
      and "closedin (subtopology euclidean (S \<union> T)) T"
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
  assumes clS: "closedin (subtopology euclidean (S \<union> T)) S"
      and clT: "closedin (subtopology euclidean (S \<union> T)) T"
      and Un: "ANR(S \<union> T)" and Int: "ANR(S \<inter> T)"
    shows "ANR S"
proof -
  obtain V where clo: "closedin (subtopology euclidean (S \<union> T)) (S \<inter> T)"
             and ope: "openin (subtopology euclidean (S \<union> T)) V"
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
    show "closedin (subtopology euclidean (S \<union> V \<inter> T)) S"
      using clS closedin_subset_trans inf.boundedE by blast
    show "closedin (subtopology euclidean (S \<union> V \<inter> T)) (V \<inter> T)"
      using clT Vsup by (auto simp: closedin_closed)
    show "continuous_on (V \<inter> T) r"
      by (meson Int_lower1 continuous_on_subset r)
  qed (use req continuous_on_id in auto)
  with rim have "S retract_of S \<union> V"
    unfolding retraction_def retract_of_def
    apply (rule_tac x="\<lambda>x. if x \<in> S then x else r x" in exI)
    apply (auto simp: eq')
    done
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
            by (metis (no_types, hide_lams) Suc.prems(2) closed_Int subsetD imageE insert.prems insertI1 insertI2)
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

subsubsection\<open>Original ANR material, now for ENRs\<close>

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
    apply (clarsimp simp: ENR_def)
    apply (rule_tac x="ball 0 r \<inter> U" in exI, auto)
    using r retract_of_imp_subset retract_of_subset by fastforce
next
  assume ?rhs
  then show ?lhs
    using ENR_def by blast
qed

lemma absolute_retract_imp_AR_gen:
  fixes S :: "'a::euclidean_space set" and S' :: "'b::euclidean_space set"
  assumes "S retract_of T" "convex T" "T \<noteq> {}" "S homeomorphic S'" "closedin (subtopology euclidean U) S'"
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
  apply auto
   apply (meson assms compact_AR homeomorphic_AR_iff_AR homeomorphic_compactness)+
  done

lemma absolute_retract_from_Un_Int:
  fixes S :: "'a::euclidean_space set"
  assumes "(S \<union> T) retract_of UNIV" "(S \<inter> T) retract_of UNIV" "closed S" "closed T"
  shows "S retract_of UNIV"
  using AR_from_Un_Int assms retract_of_UNIV by auto

lemma ENR_from_Un_Int_gen:
  fixes S :: "'a::euclidean_space set"
  assumes "closedin (subtopology euclidean (S \<union> T)) S" "closedin (subtopology euclidean (S \<union> T)) T" "ENR(S \<union> T)" "ENR(S \<inter> T)"
  shows "ENR S"
  apply (simp add: ENR_ANR)
  using ANR_from_Un_Int_local ENR_ANR assms locally_compact_closedin by blast


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

subsubsection\<open>Finally, spheres are ANRs and ENRs\<close>

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
    apply (rule frontier_retract_of_punctured_universe)
    using assms by auto
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

corollary%unimportant ANR_sphere:
  fixes a :: "'a::euclidean_space"
  shows "ANR(sphere a r)"
  by (simp add: ENR_imp_ANR ENR_sphere)

subsubsection\<open>Spheres are connected, etc\<close>

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

subsubsection\<open>Borsuk homotopy extension theorem\<close>

text\<open>It's only this late so we can use the concept of retraction,
  saying that the domain sets or range set are ENRs.\<close>

theorem Borsuk_homotopy_extension_homotopic:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes cloTS: "closedin (subtopology euclidean T) S"
      and anr: "(ANR S \<and> ANR T) \<or> ANR U"
      and contf: "continuous_on T f"
      and "f ` T \<subseteq> U"
      and "homotopic_with (\<lambda>x. True) S U f g"
   obtains g' where "homotopic_with (\<lambda>x. True) T U f g'"
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
  have clo0T: "closedin (subtopology euclidean ({0..1} \<times> T)) ({0::real} \<times> T)"
    by (simp add: closedin_subtopology_refl closedin_Times)
  moreover have cloT1S: "closedin (subtopology euclidean ({0..1} \<times> T)) ({0..1} \<times> S)"
    by (simp add: closedin_subtopology_refl closedin_Times assms)
  ultimately have clo0TB:"closedin (subtopology euclidean ({0..1} \<times> T)) B"
    by (auto simp: B_def)
  have cloBS: "closedin (subtopology euclidean B) ({0..1} \<times> S)"
    by (metis (no_types) Un_subset_iff B_def closedin_subset_trans [OF cloT1S] clo0TB closedin_imp_subset closedin_self)
  moreover have cloBT: "closedin (subtopology euclidean B) ({0} \<times> T)"
    using \<open>S \<subseteq> T\<close> closedin_subset_trans [OF clo0T]
    by (metis B_def Un_upper1 clo0TB closedin_closed inf_le1)
  moreover have "continuous_on ({0} \<times> T) (f \<circ> snd)"
    apply (rule continuous_intros)+
    apply (simp add: contf)
    done
  ultimately have conth': "continuous_on B h'"
    apply (simp add: h'_def B_def Un_commute [of "{0} \<times> T"])
    apply (auto intro!: continuous_on_cases_local conth)
    done
  have "image h' B \<subseteq> U"
    using \<open>f ` T \<subseteq> U\<close> him by (auto simp: h'_def B_def)
  obtain V k where "B \<subseteq> V" and opeTV: "openin (subtopology euclidean ({0..1} \<times> T)) V"
               and contk: "continuous_on V k" and kim: "k ` V \<subseteq> U"
               and keq: "\<And>x. x \<in> B \<Longrightarrow> k x = h' x"
  using anr
  proof
    assume ST: "ANR S \<and> ANR T"
    have eq: "({0} \<times> T \<inter> {0..1} \<times> S) = {0::real} \<times> S"
      using \<open>S \<subseteq> T\<close> by auto
    have "ANR B"
      apply (simp add: B_def)
      apply (rule ANR_closed_Un_local)
          apply (metis cloBT B_def)
         apply (metis Un_commute cloBS B_def)
        apply (simp_all add: ANR_Times convex_imp_ANR ANR_singleton ST eq)
      done
    note Vk = that
    have *: thesis if "openin (subtopology euclidean ({0..1::real} \<times> T)) V"
                      "retraction V B r" for V r
      using that
      apply (clarsimp simp add: retraction_def)
      apply (rule Vk [of V "h' \<circ> r"], assumption+)
        apply (metis continuous_on_compose conth' continuous_on_subset) 
      using \<open>h' ` B \<subseteq> U\<close> apply force+
      done
    show thesis
        apply (rule ANR_imp_neighbourhood_retract [OF \<open>ANR B\<close> clo0TB])
        apply (auto simp: ANR_Times ANR_singleton ST retract_of_def *)
        done
  next
    assume "ANR U"
    with ANR_imp_absolute_neighbourhood_extensor \<open>h' ` B \<subseteq> U\<close> clo0TB conth' that
    show ?thesis by blast
  qed
  define S' where "S' \<equiv> {x. \<exists>u::real. u \<in> {0..1} \<and> (u, x::'a) \<in> {0..1} \<times> T - V}"
  have "closedin (subtopology euclidean T) S'"
    unfolding S'_def
    apply (rule closedin_compact_projection, blast)
    using closedin_self opeTV by blast
  have S'_def: "S' = {x. \<exists>u::real.  (u, x::'a) \<in> {0..1} \<times> T - V}"
    by (auto simp: S'_def)
  have cloTS': "closedin (subtopology euclidean T) S'"
    using S'_def \<open>closedin (subtopology euclidean T) S'\<close> by blast
  have "S \<inter> S' = {}"
    using S'_def B_def \<open>B \<subseteq> V\<close> by force
  obtain a :: "'a \<Rightarrow> real" where conta: "continuous_on T a"
      and "\<And>x. x \<in> T \<Longrightarrow> a x \<in> closed_segment 1 0"
      and a1: "\<And>x. x \<in> S \<Longrightarrow> a x = 1"
      and a0: "\<And>x. x \<in> S' \<Longrightarrow> a x = 0"
    apply (rule Urysohn_local [OF cloTS cloTS' \<open>S \<inter> S' = {}\<close>, of 1 0], blast)
    done
  then have ain: "\<And>x. x \<in> T \<Longrightarrow> a x \<in> {0..1}"
    using closed_segment_eq_real_ivl by auto
  have inV: "(u * a t, t) \<in> V" if "t \<in> T" "0 \<le> u" "u \<le> 1" for t u
  proof (rule ccontr)
    assume "(u * a t, t) \<notin> V"
    with ain [OF \<open>t \<in> T\<close>] have "a t = 0"
      apply simp
      apply (rule a0)
      by (metis (no_types, lifting) Diff_iff S'_def SigmaI atLeastAtMost_iff mem_Collect_eq mult_le_one mult_nonneg_nonneg that)
    show False
      using B_def \<open>(u * a t, t) \<notin> V\<close> \<open>B \<subseteq> V\<close> \<open>a t = 0\<close> that by auto
  qed
  show ?thesis
  proof
    show hom: "homotopic_with (\<lambda>x. True) T U f (\<lambda>x. k (a x, x))"
    proof (simp add: homotopic_with, intro exI conjI)
      show "continuous_on ({0..1} \<times> T) (k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z)))"
        apply (intro continuous_on_compose continuous_intros)
        apply (rule continuous_on_subset [OF conta], force)
        apply (rule continuous_on_subset [OF contk])
        apply (force intro: inV)
        done
      show "(k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z))) ` ({0..1} \<times> T) \<subseteq> U"
        using inV kim by auto
      show "\<forall>x\<in>T. (k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z))) (0, x) = f x"
        by (simp add: B_def h'_def keq)
      show "\<forall>x\<in>T. (k \<circ> (\<lambda>z. (fst z *\<^sub>R (a \<circ> snd) z, snd z))) (1, x) = k (a x, x)"
        by auto
    qed
  show "continuous_on T (\<lambda>x. k (a x, x))"
    using hom homotopic_with_imp_continuous by blast
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


corollary%unimportant nullhomotopic_into_ANR_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "closed S"
      and contf: "continuous_on S f"
      and "ANR T"
      and fim: "f ` S \<subseteq> T"
      and "S \<noteq> {}"
   shows "(\<exists>c. homotopic_with (\<lambda>x. True) S T f (\<lambda>x. c)) \<longleftrightarrow>
          (\<exists>g. continuous_on UNIV g \<and> range g \<subseteq> T \<and> (\<forall>x \<in> S. g x = f x))"
       (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain c where c: "homotopic_with (\<lambda>x. True) S T (\<lambda>x. c) f"
    by (blast intro: homotopic_with_symD)
  have "closedin (subtopology euclidean UNIV) S"
    using \<open>closed S\<close> closed_closedin by fastforce
  then obtain g where "continuous_on UNIV g" "range g \<subseteq> T"
                      "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    apply (rule Borsuk_homotopy_extension_homotopic [OF _ _ continuous_on_const _ c, where T=UNIV])
    using \<open>ANR T\<close> \<open>S \<noteq> {}\<close> c homotopic_with_imp_subset1 apply fastforce+
    done
  then show ?rhs by blast
next
  assume ?rhs
  then obtain g where "continuous_on UNIV g" "range g \<subseteq> T" "\<And>x. x\<in>S \<Longrightarrow> g x = f x"
    by blast
  then obtain c where "homotopic_with (\<lambda>h. True) UNIV T g (\<lambda>x. c)"
    using nullhomotopic_from_contractible [of UNIV g T] contractible_UNIV by blast
  then show ?lhs
    apply (rule_tac x=c in exI)
    apply (rule homotopic_with_eq [of _ _ _ g "\<lambda>x. c"])
    apply (rule homotopic_with_subset_left)
    apply (auto simp: \<open>\<And>x. x \<in> S \<Longrightarrow> g x = f x\<close>)
    done
qed

corollary%unimportant nullhomotopic_into_rel_frontier_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "closed S"
      and contf: "continuous_on S f"
      and "convex T" "bounded T"
      and fim: "f ` S \<subseteq> rel_frontier T"
      and "S \<noteq> {}"
   shows "(\<exists>c. homotopic_with (\<lambda>x. True) S (rel_frontier T) f (\<lambda>x. c)) \<longleftrightarrow>
          (\<exists>g. continuous_on UNIV g \<and> range g \<subseteq> rel_frontier T \<and> (\<forall>x \<in> S. g x = f x))"
by (simp add: nullhomotopic_into_ANR_extension assms ANR_rel_frontier_convex)

corollary%unimportant nullhomotopic_into_sphere_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes "closed S" and contf: "continuous_on S f"
      and "S \<noteq> {}" and fim: "f ` S \<subseteq> sphere a r"
    shows "((\<exists>c. homotopic_with (\<lambda>x. True) S (sphere a r) f (\<lambda>x. c)) \<longleftrightarrow>
           (\<exists>g. continuous_on UNIV g \<and> range g \<subseteq> sphere a r \<and> (\<forall>x \<in> S. g x = f x)))"
           (is "?lhs = ?rhs")
proof (cases "r = 0")
  case True with fim show ?thesis
    apply auto
    using fim continuous_on_const apply fastforce
    by (metis contf contractible_sing nullhomotopic_into_contractible)
next
  case False
  then have eq: "sphere a r = rel_frontier (cball a r)" by simp
  show ?thesis
    using fim unfolding eq
    apply (rule nullhomotopic_into_rel_frontier_extension [OF \<open>closed S\<close> contf convex_cball bounded_cball])
    apply (rule \<open>S \<noteq> {}\<close>)
    done
qed

proposition%unimportant Borsuk_map_essential_bounded_component:
  fixes a :: "'a :: euclidean_space"
  assumes "compact S" and "a \<notin> S"
   shows "bounded (connected_component_set (- S) a) \<longleftrightarrow>
          \<not>(\<exists>c. homotopic_with (\<lambda>x. True) S (sphere 0 1)
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
      apply (rule non_extensible_Borsuk_map [OF \<open>compact S\<close> componentsI _ aincc])
      using  \<open>a \<notin> S\<close> that by auto
    obtain g where "range g \<subseteq> sphere 0 1" "continuous_on UNIV g"
                        "\<And>x. x \<in> S \<Longrightarrow> g x = (x - a) /\<^sub>R norm (x - a)"
      using notr
      by (auto simp: nullhomotopic_into_sphere_extension
                 [OF \<open>closed S\<close> continuous_on_Borsuk_map [OF \<open>a \<notin> S\<close>] False s01])
    with \<open>a \<notin> S\<close> show  "\<not> ?lhs"
      apply (clarsimp simp: Borsuk_map_into_sphere [of a S, symmetric] dest!: nog)
      apply (drule_tac x=g in spec)
      using continuous_on_subset by fastforce 
  next
    assume "\<not> ?lhs"
    then obtain b where b: "b \<in> connected_component_set (- S) a" and "r \<le> norm b"
      using bounded_iff linear by blast
    then have bnot: "b \<notin> ball 0 r"
      by simp
    have "homotopic_with (\<lambda>x. True) S (sphere 0 1) (\<lambda>x. (x - a) /\<^sub>R norm (x - a))
                                                   (\<lambda>x. (x - b) /\<^sub>R norm (x - b))"
      apply (rule Borsuk_maps_homotopic_in_path_component)
      using \<open>closed S\<close> b open_Compl open_path_connected_component apply fastforce
      done
    moreover
    obtain c where "homotopic_with (\<lambda>x. True) (ball 0 r) (sphere 0 1)
                                   (\<lambda>x. inverse (norm (x - b)) *\<^sub>R (x - b)) (\<lambda>x. c)"
    proof (rule nullhomotopic_from_contractible)
      show "contractible (ball (0::'a) r)"
        by (metis convex_imp_contractible convex_ball)
      show "continuous_on (ball 0 r) (\<lambda>x. inverse(norm (x - b)) *\<^sub>R (x - b))"
        by (rule continuous_on_Borsuk_map [OF bnot])
      show "(\<lambda>x. (x - b) /\<^sub>R norm (x - b)) ` ball 0 r \<subseteq> sphere 0 1"
        using bnot Borsuk_map_into_sphere by blast
    qed blast
    ultimately have "homotopic_with (\<lambda>x. True) S (sphere 0 1)
                         (\<lambda>x. (x - a) /\<^sub>R norm (x - a)) (\<lambda>x. c)"
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
      and hom: "homotopic_with (\<lambda>x. True) S (sphere 0 1)
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
    show "closedin (subtopology euclidean ?T) S"
      by (simp add: \<open>compact S\<close> closed_subset compact_imp_closed)
    show "continuous_on ?T (\<lambda>x. (x - b) /\<^sub>R norm (x - b))"
      by (simp add: \<open>b \<notin> S\<close> notcc continuous_on_Borsuk_map)
    show "(\<lambda>x. (x - b) /\<^sub>R norm (x - b)) ` ?T \<subseteq> sphere 0 1"
      by (simp add: \<open>b \<notin> S\<close> notcc Borsuk_map_into_sphere)
    show "homotopic_with (\<lambda>x. True) S (sphere 0 1)
             (\<lambda>x. (x - b) /\<^sub>R norm (x - b)) (\<lambda>x. (x - a) /\<^sub>R norm (x - a))"
      by (simp add: hom homotopic_with_symD)
    qed (auto simp: ANR_sphere intro: that)
  ultimately show False by blast
qed


lemma Borsuk_maps_homotopic_in_connected_component_eq:
  fixes a :: "'a :: euclidean_space"
  assumes S: "compact S" "a \<notin> S" "b \<notin> S" and 2: "2 \<le> DIM('a)"
    shows "(homotopic_with (\<lambda>x. True) S (sphere 0 1)
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

subsubsection\<open>More extension theorems\<close>

lemma extension_from_clopen:
  assumes ope: "openin (subtopology euclidean S) T"
      and clo: "closedin (subtopology euclidean S) T"
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
      apply (rule continuous_on_cases_local)
      using Seq clo ope by (auto simp: contf continuous_on_const intro: continuous_on_cases_local)
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
  obtain T g where ope: "openin (subtopology euclidean S) T"
               and clo: "closedin (subtopology euclidean S) T"
               and "C \<subseteq> T" and contg: "continuous_on T g" and gim: "g ` T \<subseteq> U"
               and gf: "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
    using S
  proof
    assume "locally connected S"
    show ?thesis
      by (metis C \<open>locally connected S\<close> openin_components_locally_connected closedin_component contf fim order_refl that)
  next
    assume "compact S"
    then obtain W g where "C \<subseteq> W" and opeW: "openin (subtopology euclidean S) W"
                 and contg: "continuous_on W g"
                 and gim: "g ` W \<subseteq> U" and gf: "\<And>x. x \<in> C \<Longrightarrow> g x = f x"
      using ANR_imp_absolute_neighbourhood_extensor [of U C f S] C \<open>ANR U\<close> closedin_component contf fim by blast
    then obtain V where "open V" and V: "W = S \<inter> V"
      by (auto simp: openin_open)
    moreover have "locally compact S"
      by (simp add: \<open>compact S\<close> closed_imp_locally_compact compact_imp_closed)
    ultimately obtain K where opeK: "openin (subtopology euclidean S) K" and "compact K" "C \<subseteq> K" "K \<subseteq> V"
      by (metis C Int_subset_iff \<open>C \<subseteq> W\<close> \<open>compact S\<close> compact_components Sura_Bura_clopen_subset)
    show ?thesis
    proof
      show "closedin (subtopology euclidean S) K"
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
      and ope: "openin (subtopology euclidean (S \<times> T)) U"
  obtains V where "openin (subtopology euclidean T) V" "a \<in> V" "S \<times> V \<subseteq> U"
proof -
  let ?W = "{y. \<exists>x. x \<in> S \<and> (x, y) \<in> (S \<times> T - U)}"
  have "U \<subseteq> S \<times> T" "closedin (subtopology euclidean (S \<times> T)) (S \<times> T - U)"
    using ope by (auto simp: openin_closedin_eq)
  then have "closedin (subtopology euclidean T) ?W"
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
      and ope: "openin (subtopology euclidean (S \<times> T')) U"
  obtains V where "openin (subtopology euclidean T') V" "T \<subseteq> V" "S \<times> V \<subseteq> U"
proof -
  have "\<And>x. x \<in> T \<Longrightarrow> \<exists>V. openin (subtopology euclidean T') V \<and> x \<in> V \<and> S \<times> V \<subseteq> U"
    using assms by (auto intro:  tube_lemma [OF \<open>compact S\<close>])
  then obtain F where F: "\<And>x. x \<in> T \<Longrightarrow> openin (subtopology euclidean T') (F x) \<and> x \<in> F x \<and> S \<times> F x \<subseteq> U"
    by metis
  show ?thesis
  proof
    show "openin (subtopology euclidean T') (\<Union>(F ` T))"
      using F by blast
    show "T \<subseteq> \<Union>(F ` T)"
      using F by blast
    show "S \<times> \<Union>(F ` T) \<subseteq> U"
      using F by auto
  qed
qed

proposition%unimportant homotopic_neighbourhood_extension:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes contf: "continuous_on S f" and fim: "f ` S \<subseteq> U"
      and contg: "continuous_on S g" and gim: "g ` S \<subseteq> U"
      and clo: "closedin (subtopology euclidean S) T"
      and "ANR U" and hom: "homotopic_with (\<lambda>x. True) T U f g"
    obtains V where "T \<subseteq> V" "openin (subtopology euclidean S) V"
                    "homotopic_with (\<lambda>x. True) V U f g"
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
    show "closedin (subtopology euclidean (?S0 \<union> (?S1 \<union> {0..1} \<times> T))) ?S0"
         "closedin (subtopology euclidean (?S1 \<union> {0..1} \<times> T)) ?S1"
      using \<open>T \<subseteq> S\<close> by (force intro: closedin_Times closedin_subset_trans [of "{0..1} \<times> S"])+
    show "closedin (subtopology euclidean (?S0 \<union> (?S1 \<union> {0..1} \<times> T))) (?S1 \<union> {0..1} \<times> T)"
         "closedin (subtopology euclidean (?S1 \<union> {0..1} \<times> T)) ({0..1} \<times> T)"
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
  moreover have "closedin (subtopology euclidean ({0..1::real} \<times> S)) ({0,1} \<times> S \<union> {0..1::real} \<times> T)"
    by (intro closedin_Times closedin_Un clo) (simp_all add: closed_subset)
  ultimately
  obtain W k where W: "({0,1} \<times> S) \<union> ({0..1} \<times> T) \<subseteq> W"
               and opeW: "openin (subtopology euclidean ({0..1} \<times> S)) W"
               and contk: "continuous_on W k"
               and kim: "k ` W \<subseteq> U"
               and kh': "\<And>x. x \<in> ({0,1} \<times> S) \<union> ({0..1} \<times> T) \<Longrightarrow> k x = h' x"
    by (metis ANR_imp_absolute_neighbourhood_extensor [OF \<open>ANR U\<close>, of "({0,1} \<times> S) \<union> ({0..1} \<times> T)" h' "{0..1} \<times> S"])
  obtain T' where opeT': "openin (subtopology euclidean S) T'" 
              and "T \<subseteq> T'" and TW: "{0..1} \<times> T' \<subseteq> W"
    using tube_lemma_gen [of "{0..1::real}" T S W] W \<open>T \<subseteq> S\<close> opeW by auto
  moreover have "homotopic_with (\<lambda>x. True) T' U f g"
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
proposition%unimportant homotopic_on_clopen_Union:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> closedin (subtopology euclidean (\<Union>\<F>)) S"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> openin (subtopology euclidean (\<Union>\<F>)) S"
      and "\<And>S. S \<in> \<F> \<Longrightarrow> homotopic_with (\<lambda>x. True) S T f g"
  shows "homotopic_with (\<lambda>x. True) (\<Union>\<F>) T f g"
proof -
  obtain \<V> where "\<V> \<subseteq> \<F>" "countable \<V>" and eqU: "\<Union>\<V> = \<Union>\<F>"
    using Lindelof_openin assms by blast
  show ?thesis
  proof (cases "\<V> = {}")
    case True
    then show ?thesis
      by (metis Union_empty eqU homotopic_on_empty)
  next
    case False
    then obtain V :: "nat \<Rightarrow> 'a set" where V: "range V = \<V>"
      using range_from_nat_into \<open>countable \<V>\<close> by metis
    with \<open>\<V> \<subseteq> \<F>\<close> have clo: "\<And>n. closedin (subtopology euclidean (\<Union>\<F>)) (V n)"
                  and ope: "\<And>n. openin (subtopology euclidean (\<Union>\<F>)) (V n)"
                  and hom: "\<And>n. homotopic_with (\<lambda>x. True) (V n) T f g"
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
      show "{0..1} \<times> \<Union>(V ` UNIV) \<subseteq> (\<Union>i. {0..1::real} \<times> (V i - (\<Union>m<i. V m)))"
        by (force simp: Ball_def dest: wop)
      show "openin (subtopology euclidean ({0..1} \<times> \<Union>(V ` UNIV))) 
                   ({0..1::real} \<times> (V i - (\<Union>m<i. V m)))" for i
      proof (intro openin_Times openin_subtopology_self openin_diff)
        show "openin (subtopology euclidean (\<Union>(V ` UNIV))) (V i)"
          using ope V eqU by auto
        show "closedin (subtopology euclidean (\<Union>(V ` UNIV))) (\<Union>m<i. V m)"
          using V clo eqU by (force intro: closedin_Union)
      qed
      show "continuous_on ({0..1} \<times> (V i - (\<Union>m<i. V m))) (h i)" for i
        by (rule continuous_on_subset [OF conth]) auto
      show "\<And>i j x. x \<in> {0..1} \<times> \<Union>(V ` UNIV) \<inter>
                    {0..1} \<times> (V i - (\<Union>m<i. V m)) \<inter> {0..1} \<times> (V j - (\<Union>m<j. V m))
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
  shows "homotopic_with (\<lambda>x. True) S T f g \<longleftrightarrow>
         (continuous_on S f \<and> f ` S \<subseteq> T \<and> continuous_on S g \<and> g ` S \<subseteq> T) \<and>
         (\<forall>C \<in> components S. homotopic_with (\<lambda>x. True) C T f g)"
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
    have "\<exists>U. C \<subseteq> U \<and> closedin (subtopology euclidean S) U \<and>
              openin (subtopology euclidean S) U \<and>
              homotopic_with (\<lambda>x. True) U T f g" if C: "C \<in> components S" for C
    proof -
      have "C \<subseteq> S"
        by (simp add: in_components_subset that)
      show ?thesis
        using S
      proof
        assume "locally connected S"
        show ?thesis
        proof (intro exI conjI)
          show "closedin (subtopology euclidean S) C"
            by (simp add: closedin_component that)
          show "openin (subtopology euclidean S) C"
            by (simp add: \<open>locally connected S\<close> openin_components_locally_connected that)
          show "homotopic_with (\<lambda>x. True) C T f g"
            by (simp add: R that)
        qed auto
      next
        assume "compact S"
        have hom: "homotopic_with (\<lambda>x. True) C T f g"
          using R that by blast
        obtain U where "C \<subseteq> U" and opeU: "openin (subtopology euclidean S) U"
                  and hom: "homotopic_with (\<lambda>x. True) U T f g"
          using homotopic_neighbourhood_extension [OF contf fim contg gim _ \<open>ANR T\<close> hom]
            \<open>C \<in> components S\<close> closedin_component by blast
        then obtain V where "open V" and V: "U = S \<inter> V"
          by (auto simp: openin_open)
        moreover have "locally compact S"
          by (simp add: \<open>compact S\<close> closed_imp_locally_compact compact_imp_closed)
        ultimately obtain K where opeK: "openin (subtopology euclidean S) K" and "compact K" "C \<subseteq> K" "K \<subseteq> V"
          by (metis C Int_subset_iff Sura_Bura_clopen_subset \<open>C \<subseteq> U\<close> \<open>compact S\<close> compact_components)
        show ?thesis
        proof (intro exI conjI)
          show "closedin (subtopology euclidean S) K"
            by (meson \<open>compact K\<close> \<open>compact S\<close> closedin_compact_eq opeK openin_imp_subset)
          show "homotopic_with (\<lambda>x. True) K T f g"
            using V \<open>K \<subseteq> V\<close> hom homotopic_with_subset_left opeK openin_imp_subset by fastforce
        qed (use opeK \<open>C \<subseteq> K\<close> in auto)
      qed
    qed
    then obtain \<phi> where \<phi>: "\<And>C. C \<in> components S \<Longrightarrow> C \<subseteq> \<phi> C"
                  and clo\<phi>: "\<And>C. C \<in> components S \<Longrightarrow> closedin (subtopology euclidean S) (\<phi> C)"
                  and ope\<phi>: "\<And>C. C \<in> components S \<Longrightarrow> openin (subtopology euclidean S) (\<phi> C)"
                  and hom\<phi>: "\<And>C. C \<in> components S \<Longrightarrow> homotopic_with (\<lambda>x. True) (\<phi> C) T f g"
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
      apply (rule homotopic_on_clopen_Union)
      using Seq clo\<phi> ope\<phi> hom\<phi> by auto
  qed
  ultimately show ?thesis by blast
qed


lemma cohomotopically_trivial_on_components:
  fixes S :: "'a :: euclidean_space set" and T :: "'b :: euclidean_space set"
  assumes S: "locally connected S \<or> compact S" and "ANR T"
  shows
   "(\<forall>f g. continuous_on S f \<longrightarrow> f ` S \<subseteq> T \<longrightarrow> continuous_on S g \<longrightarrow> g ` S \<subseteq> T \<longrightarrow>
           homotopic_with (\<lambda>x. True) S T f g)
    \<longleftrightarrow>
    (\<forall>C\<in>components S.
        \<forall>f g. continuous_on C f \<longrightarrow> f ` C \<subseteq> T \<longrightarrow> continuous_on C g \<longrightarrow> g ` C \<subseteq> T \<longrightarrow>
              homotopic_with (\<lambda>x. True) C T f g)"
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
    have "homotopic_with (\<lambda>x. True) C T f' g'"
      using L [OF contf' f'im contg' g'im] homotopic_with_subset_left C in_components_subset by fastforce
    then show "homotopic_with (\<lambda>x. True) C T f g"
      using f'f g'g homotopic_with_eq by force
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
  proof clarify
    fix f g
    assume contf: "continuous_on S f" and fim: "f ` S \<subseteq> T"
      and contg: "continuous_on S g" and gim: "g ` S \<subseteq> T"
    moreover have "homotopic_with (\<lambda>x. True) C T f g" if "C \<in> components S" for C
      using R [OF that]
      by (meson contf contg continuous_on_subset fim gim image_mono in_components_subset order.trans that)
    ultimately show "homotopic_with (\<lambda>x. True) S T f g"
      by (subst homotopic_on_components_eq [OF S \<open>ANR T\<close>]) auto
  qed
qed

subsubsection\<open>The complement of a set and path-connectedness\<close>

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
    apply (clarsimp simp: connected_iff_connected_component_eq)
    apply (rule cobounded_unique_unbounded_component [OF _ 2])
      apply (simp add: \<open>compact S\<close> compact_imp_bounded)
     apply (meson ComplI S componentsI unbounded_components_complement_absolute_retract)+
    done
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
