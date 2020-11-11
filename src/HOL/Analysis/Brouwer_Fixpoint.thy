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
  imports Homeomorphism Derivative
begin

subsection \<open>Retractions\<close>

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

lemma retract_of_path_connected:
    "\<lbrakk>path_connected T; S retract_of T\<rbrakk> \<Longrightarrow> path_connected S"
  by (metis path_connected_continuous_image retract_of_def retraction)

lemma retract_of_simply_connected:
    "\<lbrakk>simply_connected T; S retract_of T\<rbrakk> \<Longrightarrow> simply_connected S"
apply (simp add: retract_of_def retraction_def, clarify)
apply (rule simply_connected_retraction_gen)
apply (force elim!: continuous_on_subset)+
done

lemma retract_of_homotopically_trivial:
  assumes ts: "T retract_of S"
      and hom: "\<And>f g. \<lbrakk>continuous_on U f; f ` U \<subseteq> S;
                       continuous_on U g; g ` U \<subseteq> S\<rbrakk>
                       \<Longrightarrow> homotopic_with_canon (\<lambda>x. True) U S f g"
      and "continuous_on U f" "f ` U \<subseteq> T"
      and "continuous_on U g" "g ` U \<subseteq> T"
    shows "homotopic_with_canon (\<lambda>x. True) U T f g"
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
                     \<Longrightarrow> \<exists>c. homotopic_with_canon (\<lambda>x. True) U S f (\<lambda>x. c)"
      and "continuous_on U f" "f ` U \<subseteq> T"
  obtains c where "homotopic_with_canon (\<lambda>x. True) U T f (\<lambda>x. c)"
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

lemma retraction_openin_vimage_iff:
  "openin (top_of_set S) (S \<inter> r -` U) \<longleftrightarrow> openin (top_of_set T) U"
  if retraction: "retraction S T r" and "U \<subseteq> T"
  using retraction apply (rule retractionE)
  apply (rule continuous_right_inverse_imp_quotient_map [where g=r])
  using \<open>U \<subseteq> T\<close> apply (auto elim: continuous_on_subset)
  done

lemma retract_of_locally_compact:
    fixes S :: "'a :: {heine_borel,real_normed_vector} set"
    shows  "\<lbrakk> locally compact S; T retract_of S\<rbrakk> \<Longrightarrow> locally compact T"
  by (metis locally_compact_closedin closedin_retract)

lemma homotopic_into_retract:
   "\<lbrakk>f ` S \<subseteq> T; g ` S \<subseteq> T; T retract_of U; homotopic_with_canon (\<lambda>x. True) S U f g\<rbrakk>
        \<Longrightarrow> homotopic_with_canon (\<lambda>x. True) S T f g"
apply (subst (asm) homotopic_with_def)
apply (simp add: homotopic_with retract_of_def retraction_def, clarify)
apply (rule_tac x="r \<circ> h" in exI)
apply (rule conjI continuous_intros | erule continuous_on_subset | force simp: image_subset_iff)+
done

lemma retract_of_locally_connected:
  assumes "locally connected T" "S retract_of T"
  shows "locally connected S"
  using assms
  by (auto simp: idempotent_imp_retraction intro!: retraction_openin_vimage_iff elim!: locally_connected_quotient_image retract_ofE)

lemma retract_of_locally_path_connected:
  assumes "locally path_connected T" "S retract_of T"
  shows "locally path_connected S"
  using assms
  by (auto simp: idempotent_imp_retraction intro!: retraction_openin_vimage_iff elim!: locally_path_connected_quotient_image retract_ofE)

text \<open>A few simple lemmas about deformation retracts\<close>

lemma deformation_retract_imp_homotopy_eqv:
  fixes S :: "'a::euclidean_space set"
  assumes "homotopic_with_canon (\<lambda>x. True) S S id r" and r: "retraction S T r"
  shows "S homotopy_eqv T"
proof -
  have "homotopic_with_canon (\<lambda>x. True) S S (id \<circ> r) id"
    by (simp add: assms(1) homotopic_with_symD)
  moreover have "homotopic_with_canon (\<lambda>x. True) T T (r \<circ> id) id"
    using r unfolding retraction_def
    by (metis eq_id_iff homotopic_with_id2 topspace_euclidean_subtopology)
  ultimately
  show ?thesis
    unfolding homotopy_equivalent_space_def 
    by (metis (no_types, lifting) continuous_map_subtopology_eu continuous_on_id' id_def image_id r retraction_def)
qed

lemma deformation_retract:
  fixes S :: "'a::euclidean_space set"
    shows "(\<exists>r. homotopic_with_canon (\<lambda>x. True) S S id r \<and> retraction S T r) \<longleftrightarrow>
           T retract_of S \<and> (\<exists>f. homotopic_with_canon (\<lambda>x. True) S S id f \<and> f ` S \<subseteq> T)"
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
        apply (rule_tac Y=S in homotopic_with_compose_continuous_left)
         apply (auto simp: homotopic_with_sym)
    done
qed

lemma deformation_retract_of_contractible_sing:
  fixes S :: "'a::euclidean_space set"
  assumes "contractible S" "a \<in> S"
  obtains r where "homotopic_with_canon (\<lambda>x. True) S S id r" "retraction S {a} r"
proof -
  have "{a} retract_of S"
    by (simp add: \<open>a \<in> S\<close>)
  moreover have "homotopic_with_canon (\<lambda>x. True) S S id (\<lambda>x. a)"
      using assms
      by (auto simp: contractible_def homotopic_into_contractible image_subset_iff)
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
    by (metis add_is_0 zero_neq_numeral card.infinite assms(3))

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
      using s_eq by (simp add: atMost_Suc_eq_insert_0 insert_ident in_enum_image subset_eq)
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
          by (simp_all add: enum_Suc t.enum_Suc l b.enum_Suc \<open>b.enum i' = enum i'\<close>)
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
    using s \<open>a \<in> s\<close> by (simp add: card_2_iff' Ex1_def) metis
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
    unfolding n_def by (auto simp: Suc_le_eq)
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
      using d(1) by (simp add: n_def)
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
      by (auto simp: cbox_def bij_betw_def zero_le_divide_iff divide_le_eq_1) }
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
      by (intro open_INT finite_Basis ballI open_Int, auto intro: open_Collect_less simp: continuous_on_inner)
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
    using less_eq_real_def by auto
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
    using fros fid frontier_closures by (auto simp: contf)
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
  obtains r where "homotopic_with_canon (\<lambda>x. True) (T - {a}) (T - {a}) id r"
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
    show "homotopic_with_canon (\<lambda>x. True) (T - {a}) (T - {a}) id (\<lambda>x. a + dd (x - a) *\<^sub>R (x - a))"
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
  using deformation_retract_imp_homotopy_eqv homotopy_equivalent_space_sym by blast

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
    shows "homotopic_with_canon (\<lambda>x. True) s (sphere 0 1)
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

subsubsection \<open>Proving surjectivity via Brouwer fixpoint theorem\<close>

lemma brouwer_surjective:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "compact T"
    and "convex T"
    and "T \<noteq> {}"
    and "continuous_on T f"
    and "\<And>x y. \<lbrakk>x\<in>S; y\<in>T\<rbrakk> \<Longrightarrow> x + (y - f y) \<in> T"
    and "x \<in> S"
  shows "\<exists>y\<in>T. f y = x"
proof -
  have *: "\<And>x y. f y = x \<longleftrightarrow> x + (y - f y) = y"
    by (auto simp add: algebra_simps)
  show ?thesis
    unfolding *
    apply (rule brouwer[OF assms(1-3), of "\<lambda>y. x + (y - f y)"])
    apply (intro continuous_intros)
    using assms
    apply auto
    done
qed

lemma brouwer_surjective_cball:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "continuous_on (cball a e) f"
    and "e > 0"
    and "x \<in> S"
    and "\<And>x y. \<lbrakk>x\<in>S; y\<in>cball a e\<rbrakk> \<Longrightarrow> x + (y - f y) \<in> cball a e"
  shows "\<exists>y\<in>cball a e. f y = x"
  apply (rule brouwer_surjective)
  apply (rule compact_cball convex_cball)+
  unfolding cball_eq_empty
  using assms
  apply auto
  done

subsubsection \<open>Inverse function theorem\<close>

text \<open>See Sussmann: "Multidifferential calculus", Theorem 2.1.1\<close>

lemma sussmann_open_mapping:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
  assumes "open S"
    and contf: "continuous_on S f"
    and "x \<in> S"
    and derf: "(f has_derivative f') (at x)"
    and "bounded_linear g'" "f' \<circ> g' = id"
    and "T \<subseteq> S"
    and x: "x \<in> interior T"
  shows "f x \<in> interior (f ` T)"
proof -
  interpret f': bounded_linear f'
    using assms unfolding has_derivative_def by auto
  interpret g': bounded_linear g'
    using assms by auto
  obtain B where B: "0 < B" "\<forall>x. norm (g' x) \<le> norm x * B"
    using bounded_linear.pos_bounded[OF assms(5)] by blast
  hence *: "1 / (2 * B) > 0" by auto
  obtain e0 where e0:
      "0 < e0"
      "\<forall>y. norm (y - x) < e0 \<longrightarrow> norm (f y - f x - f' (y - x)) \<le> 1 / (2 * B) * norm (y - x)"
    using derf unfolding has_derivative_at_alt
    using * by blast
  obtain e1 where e1: "0 < e1" "cball x e1 \<subseteq> T"
    using mem_interior_cball x by blast
  have *: "0 < e0 / B" "0 < e1 / B" using e0 e1 B by auto
  obtain e where e: "0 < e" "e < e0 / B" "e < e1 / B"
    using field_lbound_gt_zero[OF *] by blast
  have lem: "\<exists>y\<in>cball (f x) e. f (x + g' (y - f x)) = z" if "z\<in>cball (f x) (e / 2)" for z
  proof (rule brouwer_surjective_cball)
    have z: "z \<in> S" if as: "y \<in>cball (f x) e" "z = x + (g' y - g' (f x))" for y z
    proof-
      have "dist x z = norm (g' (f x) - g' y)"
        unfolding as(2) and dist_norm by auto
      also have "\<dots> \<le> norm (f x - y) * B"
        by (metis B(2) g'.diff)
      also have "\<dots> \<le> e * B"
        by (metis B(1) dist_norm mem_cball mult_le_cancel_iff1 that(1))
      also have "\<dots> \<le> e1"
        using B(1) e(3) pos_less_divide_eq by fastforce
      finally have "z \<in> cball x e1"
        by force
      then show "z \<in> S"
        using e1 assms(7) by auto
    qed
    show "continuous_on (cball (f x) e) (\<lambda>y. f (x + g' (y - f x)))"
      unfolding g'.diff
    proof (rule continuous_on_compose2 [OF _ _ order_refl, of _ _ f])
      show "continuous_on ((\<lambda>y. x + (g' y - g' (f x))) ` cball (f x) e) f"
        by (rule continuous_on_subset[OF contf]) (use z in blast)
      show "continuous_on (cball (f x) e) (\<lambda>y. x + (g' y - g' (f x)))"
        by (intro continuous_intros linear_continuous_on[OF \<open>bounded_linear g'\<close>])
    qed
  next
    fix y z
    assume y: "y \<in> cball (f x) (e / 2)" and z: "z \<in> cball (f x) e"
    have "norm (g' (z - f x)) \<le> norm (z - f x) * B"
      using B by auto
    also have "\<dots> \<le> e * B"
      by (metis B(1) z dist_norm mem_cball norm_minus_commute mult_le_cancel_iff1)
    also have "\<dots> < e0"
      using B(1) e(2) pos_less_divide_eq by blast
    finally have *: "norm (x + g' (z - f x) - x) < e0"
      by auto
    have **: "f x + f' (x + g' (z - f x) - x) = z"
      using assms(6)[unfolded o_def id_def,THEN cong]
      by auto
    have "norm (f x - (y + (z - f (x + g' (z - f x))))) \<le>
          norm (f (x + g' (z - f x)) - z) + norm (f x - y)"
      using norm_triangle_ineq[of "f (x + g'(z - f x)) - z" "f x - y"]
      by (auto simp add: algebra_simps)
    also have "\<dots> \<le> 1 / (B * 2) * norm (g' (z - f x)) + norm (f x - y)"
      using e0(2)[rule_format, OF *]
      by (simp only: algebra_simps **) auto
    also have "\<dots> \<le> 1 / (B * 2) * norm (g' (z - f x)) + e/2"
      using y by (auto simp: dist_norm)
    also have "\<dots> \<le> 1 / (B * 2) * B * norm (z - f x) + e/2"
      using * B by (auto simp add: field_simps)
    also have "\<dots> \<le> 1 / 2 * norm (z - f x) + e/2"
      by auto
    also have "\<dots> \<le> e/2 + e/2"
      using B(1) \<open>norm (z - f x) * B \<le> e * B\<close> by auto
    finally show "y + (z - f (x + g' (z - f x))) \<in> cball (f x) e"
      by (auto simp: dist_norm)
  qed (use e that in auto) 
  show ?thesis
    unfolding mem_interior
  proof (intro exI conjI subsetI)
    fix y
    assume "y \<in> ball (f x) (e / 2)"
    then have *: "y \<in> cball (f x) (e / 2)"
      by auto
    obtain z where z: "z \<in> cball (f x) e" "f (x + g' (z - f x)) = y"
      using lem * by blast
    then have "norm (g' (z - f x)) \<le> norm (z - f x) * B"
      using B
      by (auto simp add: field_simps)
    also have "\<dots> \<le> e * B"
      by (metis B(1) dist_norm mem_cball norm_minus_commute mult_le_cancel_iff1 z(1))
    also have "\<dots> \<le> e1"
      using e B unfolding less_divide_eq by auto
    finally have "x + g'(z - f x) \<in> T"
      by (metis add_diff_cancel diff_diff_add dist_norm e1(2) mem_cball norm_minus_commute subset_eq)
    then show "y \<in> f ` T"
      using z by auto
  qed (use e in auto)
qed

text \<open>Hence the following eccentric variant of the inverse function theorem.
  This has no continuity assumptions, but we do need the inverse function.
  We could put \<open>f' \<circ> g = I\<close> but this happens to fit with the minimal linear
  algebra theory I've set up so far.\<close>

lemma has_derivative_inverse_strong:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "open S"
    and "x \<in> S"
    and contf: "continuous_on S f"
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and derf: "(f has_derivative f') (at x)"
    and id: "f' \<circ> g' = id"
  shows "(g has_derivative g') (at (f x))"
proof -
  have linf: "bounded_linear f'"
    using derf unfolding has_derivative_def by auto
  then have ling: "bounded_linear g'"
    unfolding linear_conv_bounded_linear[symmetric]
    using id right_inverse_linear by blast
  moreover have "g' \<circ> f' = id"
    using id linf ling
    unfolding linear_conv_bounded_linear[symmetric]
    using linear_inverse_left
    by auto
  moreover have *: "\<And>T. \<lbrakk>T \<subseteq> S; x \<in> interior T\<rbrakk> \<Longrightarrow> f x \<in> interior (f ` T)"
    apply (rule sussmann_open_mapping)
    apply (rule assms ling)+
    apply auto
    done
  have "continuous (at (f x)) g"
    unfolding continuous_at Lim_at
  proof (rule, rule)
    fix e :: real
    assume "e > 0"
    then have "f x \<in> interior (f ` (ball x e \<inter> S))"
      using *[rule_format,of "ball x e \<inter> S"] \<open>x \<in> S\<close>
      by (auto simp add: interior_open[OF open_ball] interior_open[OF assms(1)])
    then obtain d where d: "0 < d" "ball (f x) d \<subseteq> f ` (ball x e \<inter> S)"
      unfolding mem_interior by blast
    show "\<exists>d>0. \<forall>y. 0 < dist y (f x) \<and> dist y (f x) < d \<longrightarrow> dist (g y) (g (f x)) < e"
    proof (intro exI allI impI conjI)
      fix y
      assume "0 < dist y (f x) \<and> dist y (f x) < d"
      then have "g y \<in> g ` f ` (ball x e \<inter> S)"
        by (metis d(2) dist_commute mem_ball rev_image_eqI subset_iff)
      then show "dist (g y) (g (f x)) < e"
        using gf[OF \<open>x \<in> S\<close>]
        by (simp add: assms(4) dist_commute image_iff)
    qed (use d in auto)
  qed
  moreover have "f x \<in> interior (f ` S)"
    apply (rule sussmann_open_mapping)
    apply (rule assms ling)+
    using interior_open[OF assms(1)] and \<open>x \<in> S\<close>
    apply auto
    done
  moreover have "f (g y) = y" if "y \<in> interior (f ` S)" for y
    by (metis gf imageE interiorE subsetD that)
  ultimately show ?thesis using assms
    by (metis has_derivative_inverse_basic_x open_interior)
qed

text \<open>A rewrite based on the other domain.\<close>

lemma has_derivative_inverse_strong_x:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "open S"
    and "g y \<in> S"
    and "continuous_on S f"
    and "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and "(f has_derivative f') (at (g y))"
    and "f' \<circ> g' = id"
    and "f (g y) = y"
  shows "(g has_derivative g') (at y)"
  using has_derivative_inverse_strong[OF assms(1-6)]
  unfolding assms(7)
  by simp

text \<open>On a region.\<close>

theorem has_derivative_inverse_on:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'n"
  assumes "open S"
    and derf: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative f'(x)) (at x)"
    and "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and "f' x \<circ> g' x = id"
    and "x \<in> S"
  shows "(g has_derivative g'(x)) (at (f x))"
proof (rule has_derivative_inverse_strong[where g'="g' x" and f=f])
  show "continuous_on S f"
  unfolding continuous_on_eq_continuous_at[OF \<open>open S\<close>]
  using derf has_derivative_continuous by blast
qed (use assms in auto)


end
