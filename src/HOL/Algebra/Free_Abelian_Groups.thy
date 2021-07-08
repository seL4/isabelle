section\<open>Free Abelian Groups\<close>

theory Free_Abelian_Groups
  imports
    Product_Groups FiniteProduct "HOL-Cardinals.Cardinal_Arithmetic"
   "HOL-Library.Countable_Set" "HOL-Library.Poly_Mapping" "HOL-Library.Equipollence"

begin

(*Move? But where?*)
lemma eqpoll_Fpow:
  assumes "infinite A" shows "Fpow A \<approx> A"
  unfolding eqpoll_iff_card_of_ordIso
  by (metis assms card_of_Fpow_infinite)

lemma infinite_iff_card_of_countable: "\<lbrakk>countable B; infinite B\<rbrakk> \<Longrightarrow> infinite A \<longleftrightarrow> ( |B| \<le>o |A| )"
  unfolding infinite_iff_countable_subset card_of_ordLeq countable_def
  by (force intro: card_of_ordLeqI ordLeq_transitive)

lemma iso_imp_eqpoll_carrier: "G \<cong> H \<Longrightarrow> carrier G \<approx> carrier H"
  by (auto simp: is_iso_def iso_def eqpoll_def)

subsection\<open>Generalised finite product\<close>

definition
  gfinprod :: "[('b, 'm) monoid_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b"
  where "gfinprod G f A =
   (if finite {x \<in> A. f x \<noteq> \<one>\<^bsub>G\<^esub>} then finprod G f {x \<in> A. f x \<noteq> \<one>\<^bsub>G\<^esub>} else \<one>\<^bsub>G\<^esub>)"

context comm_monoid begin

lemma gfinprod_closed [simp]:
  "f \<in> A \<rightarrow> carrier G \<Longrightarrow> gfinprod G f A \<in> carrier G"
  unfolding gfinprod_def
  by (auto simp: image_subset_iff_funcset intro: finprod_closed)

lemma gfinprod_cong:
  "\<lbrakk>A = B; f \<in> B \<rightarrow> carrier G;
    \<And>i. i \<in> B =simp=> f i = g i\<rbrakk> \<Longrightarrow> gfinprod G f A = gfinprod G g B"
  unfolding gfinprod_def
  by (auto simp: simp_implies_def cong: conj_cong intro: finprod_cong)

lemma gfinprod_eq_finprod [simp]: "\<lbrakk>finite A; f \<in> A \<rightarrow> carrier G\<rbrakk> \<Longrightarrow> gfinprod G f A = finprod G f A"
  by (auto simp: gfinprod_def intro: finprod_mono_neutral_cong_left)

lemma gfinprod_insert [simp]:
  assumes "finite {x \<in> A. f x \<noteq> \<one>\<^bsub>G\<^esub>}" "f \<in> A \<rightarrow> carrier G" "f i \<in> carrier G"
  shows "gfinprod G f (insert i A) = (if i \<in> A then gfinprod G f A else f i \<otimes> gfinprod G f A)"
proof -
  have f: "f \<in> {x \<in> A. f x \<noteq> \<one>} \<rightarrow> carrier G"
    using assms by (auto simp: image_subset_iff_funcset)
  have "{x. x = i \<and> f x \<noteq> \<one> \<or> x \<in> A \<and> f x \<noteq> \<one>} = (if f i = \<one> then {x \<in> A. f x \<noteq> \<one>} else insert i {x \<in> A. f x \<noteq> \<one>})"
    by auto
  then show ?thesis
    using assms
    unfolding gfinprod_def by (simp add: conj_disj_distribR insert_absorb f split: if_split_asm)
qed

lemma gfinprod_distrib:
  assumes fin: "finite {x \<in> A. f x \<noteq> \<one>\<^bsub>G\<^esub>}" "finite {x \<in> A. g x \<noteq> \<one>\<^bsub>G\<^esub>}"
     and "f \<in> A \<rightarrow> carrier G" "g \<in> A \<rightarrow> carrier G"
  shows "gfinprod G (\<lambda>i. f i \<otimes> g i) A = gfinprod G f A \<otimes> gfinprod G g A"
proof -
  have "finite {x \<in> A. f x \<otimes> g x \<noteq> \<one>}"
    by (auto intro: finite_subset [OF _ finite_UnI [OF fin]])
  then have "gfinprod G (\<lambda>i. f i \<otimes> g i) A = gfinprod G (\<lambda>i. f i \<otimes> g i) ({i \<in> A. f i \<noteq> \<one>\<^bsub>G\<^esub>} \<union> {i \<in> A. g i \<noteq> \<one>\<^bsub>G\<^esub>})"
    unfolding gfinprod_def
    using assms by (force intro: finprod_mono_neutral_cong)
  also have "\<dots> = gfinprod G f A \<otimes> gfinprod G g A"
  proof -
    have "finprod G f ({i \<in> A. f i \<noteq> \<one>\<^bsub>G\<^esub>} \<union> {i \<in> A. g i \<noteq> \<one>\<^bsub>G\<^esub>}) = gfinprod G f A"
      "finprod G g ({i \<in> A. f i \<noteq> \<one>\<^bsub>G\<^esub>} \<union> {i \<in> A. g i \<noteq> \<one>\<^bsub>G\<^esub>}) = gfinprod G g A"
      using assms by (auto simp: gfinprod_def intro: finprod_mono_neutral_cong_right)
    moreover have "(\<lambda>i. f i \<otimes> g i) \<in> {i \<in> A. f i \<noteq> \<one>} \<union> {i \<in> A. g i \<noteq> \<one>} \<rightarrow> carrier G"
      using assms by (force simp: image_subset_iff_funcset)
    ultimately show ?thesis
      using assms
      apply simp
      apply (subst finprod_multf, auto)
      done
  qed
  finally show ?thesis .
qed

lemma gfinprod_mono_neutral_cong_left:
  assumes "A \<subseteq> B"
    and 1: "\<And>i. i \<in> B - A \<Longrightarrow> h i = \<one>"
    and gh: "\<And>x. x \<in> A \<Longrightarrow> g x = h x"
    and h: "h \<in> B \<rightarrow> carrier G"
  shows "gfinprod G g A = gfinprod G h B"
proof (cases "finite {x \<in> B. h x \<noteq> \<one>}")
  case True
  then have "finite {x \<in> A. h x \<noteq> \<one>}"
    apply (rule rev_finite_subset)
    using \<open>A \<subseteq> B\<close> by auto
  with True assms show ?thesis
    apply (simp add: gfinprod_def cong: conj_cong)
    apply (auto intro!: finprod_mono_neutral_cong_left)
    done
next
  case False
  have "{x \<in> B. h x \<noteq> \<one>} \<subseteq> {x \<in> A. h x \<noteq> \<one>}"
    using 1 by auto
  with False have "infinite {x \<in> A. h x \<noteq> \<one>}"
    using infinite_super by blast
  with False assms show ?thesis
    by (simp add: gfinprod_def cong: conj_cong)
qed

lemma gfinprod_mono_neutral_cong_right:
  assumes "A \<subseteq> B" "\<And>i. i \<in> B - A \<Longrightarrow> g i = \<one>" "\<And>x. x \<in> A \<Longrightarrow> g x = h x" "g \<in> B \<rightarrow> carrier G"
  shows "gfinprod G g B = gfinprod G h A"
  using assms  by (auto intro!: gfinprod_mono_neutral_cong_left [symmetric])

lemma gfinprod_mono_neutral_cong:
  assumes [simp]: "finite B" "finite A"
    and *: "\<And>i. i \<in> B - A \<Longrightarrow> h i = \<one>" "\<And>i. i \<in> A - B \<Longrightarrow> g i = \<one>"
    and gh: "\<And>x. x \<in> A \<inter> B \<Longrightarrow> g x = h x"
    and g: "g \<in> A \<rightarrow> carrier G"
    and h: "h \<in> B \<rightarrow> carrier G"
 shows "gfinprod G g A = gfinprod G h B"
proof-
  have "gfinprod G g A = gfinprod G g (A \<inter> B)"
    by (rule gfinprod_mono_neutral_cong_right) (use assms in auto)
  also have "\<dots> = gfinprod G h (A \<inter> B)"
    by (rule gfinprod_cong) (use assms in auto)
  also have "\<dots> = gfinprod G h B"
    by (rule gfinprod_mono_neutral_cong_left) (use assms in auto)
  finally show ?thesis .
qed

end

lemma (in comm_group) hom_group_sum:
  assumes hom: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> hom (A i) G" and grp: "\<And>i. i \<in> I \<Longrightarrow> group (A i)"
  shows "(\<lambda>x. gfinprod G (\<lambda>i. (f i) (x i)) I) \<in> hom (sum_group I A) G"
  unfolding hom_def
proof (intro CollectI conjI ballI)
  show "(\<lambda>x. gfinprod G (\<lambda>i. f i (x i)) I) \<in> carrier (sum_group I A) \<rightarrow> carrier G"
    using assms
    by (force simp: hom_def carrier_sum_group intro: gfinprod_closed simp flip: image_subset_iff_funcset)
next
  fix x y
  assume x: "x \<in> carrier (sum_group I A)" and y: "y \<in> carrier (sum_group I A)"
  then have finx: "finite {i \<in> I. x i \<noteq> \<one>\<^bsub>A i\<^esub>}" and finy: "finite {i \<in> I. y i \<noteq> \<one>\<^bsub>A i\<^esub>}"
    using assms by (auto simp: carrier_sum_group)
  have finfx: "finite {i \<in> I. f i (x i) \<noteq> \<one>}"
    using assms by (auto simp: is_group hom_one [OF hom] intro: finite_subset [OF _ finx])
  have finfy: "finite {i \<in> I. f i (y i) \<noteq> \<one>}"
    using assms by (auto simp: is_group hom_one [OF hom] intro: finite_subset [OF _ finy])
  have carr: "f i (x i) \<in> carrier G"  "f i (y i) \<in> carrier G" if "i \<in> I" for i
    using hom_carrier [OF hom] that x y assms
    by (fastforce simp add: carrier_sum_group)+
  have lam: "(\<lambda>i. f i ( x i \<otimes>\<^bsub>A i\<^esub> y i)) \<in> I \<rightarrow> carrier G"
    using x y assms by (auto simp: hom_def carrier_sum_group PiE_def Pi_def)
  have lam': "(\<lambda>i. f i (if i \<in> I then x i \<otimes>\<^bsub>A i\<^esub> y i else undefined)) \<in> I \<rightarrow> carrier G"
    by (simp add: lam Pi_cong)
  with lam x y assms
  show "gfinprod G (\<lambda>i. f i ((x \<otimes>\<^bsub>sum_group I A\<^esub> y) i)) I
      = gfinprod G (\<lambda>i. f i (x i)) I \<otimes> gfinprod G (\<lambda>i. f i (y i)) I"
    by (simp add: carrier_sum_group PiE_def Pi_def hom_mult [OF hom]
                  gfinprod_distrib finfx finfy carr cong: gfinprod_cong)
qed

subsection\<open>Free Abelian groups on a set, using the "frag" type constructor.          \<close>

definition free_Abelian_group :: "'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 int) monoid"
  where "free_Abelian_group S = \<lparr>carrier = {c. Poly_Mapping.keys c \<subseteq> S}, monoid.mult = (+), one  = 0\<rparr>"

lemma group_free_Abelian_group [simp]: "group (free_Abelian_group S)"
proof -
  have "\<And>x. Poly_Mapping.keys x \<subseteq> S \<Longrightarrow> x \<in> Units (free_Abelian_group S)"
    unfolding free_Abelian_group_def Units_def
    by clarsimp (metis eq_neg_iff_add_eq_0 neg_eq_iff_add_eq_0 keys_minus)
  then show ?thesis
    unfolding free_Abelian_group_def
    by unfold_locales (auto simp: dest: subsetD [OF keys_add])
qed

lemma carrier_free_Abelian_group_iff [simp]:
  shows "x \<in> carrier (free_Abelian_group S) \<longleftrightarrow> Poly_Mapping.keys x \<subseteq> S"
  by (auto simp: free_Abelian_group_def)

lemma one_free_Abelian_group [simp]: "\<one>\<^bsub>free_Abelian_group S\<^esub> = 0"
  by (auto simp: free_Abelian_group_def)

lemma mult_free_Abelian_group [simp]: "x \<otimes>\<^bsub>free_Abelian_group S\<^esub> y = x + y"
  by (auto simp: free_Abelian_group_def)

lemma inv_free_Abelian_group [simp]: "Poly_Mapping.keys x \<subseteq> S \<Longrightarrow> inv\<^bsub>free_Abelian_group S\<^esub> x = -x"
  by (rule group.inv_equality [OF group_free_Abelian_group]) auto

lemma abelian_free_Abelian_group: "comm_group(free_Abelian_group S)"
  apply (rule group.group_comm_groupI [OF group_free_Abelian_group])
  by (simp add: free_Abelian_group_def)

lemma pow_free_Abelian_group [simp]:
  fixes n::nat
  shows "Group.pow (free_Abelian_group S) x n = frag_cmul (int n) x"
  by (induction n) (auto simp: nat_pow_def free_Abelian_group_def frag_cmul_distrib)

lemma int_pow_free_Abelian_group [simp]:
  fixes n::int
  assumes "Poly_Mapping.keys x \<subseteq> S"
  shows "Group.pow (free_Abelian_group S) x n = frag_cmul n x"
proof (induction n)
  case (nonneg n)
  then show ?case
    by (simp add: int_pow_int)
next
  case (neg n)
  have "x [^]\<^bsub>free_Abelian_group S\<^esub> - int (Suc n)
     = inv\<^bsub>free_Abelian_group S\<^esub> (x [^]\<^bsub>free_Abelian_group S\<^esub> int (Suc n))"
    by (rule group.int_pow_neg [OF group_free_Abelian_group]) (use assms in \<open>simp add: free_Abelian_group_def\<close>)
  also have "\<dots> = frag_cmul (- int (Suc n)) x"
    by (metis assms inv_free_Abelian_group pow_free_Abelian_group int_pow_int minus_frag_cmul
              order_trans keys_cmul)
  finally show ?case .
qed

lemma frag_of_in_free_Abelian_group [simp]:
   "frag_of x \<in> carrier(free_Abelian_group S) \<longleftrightarrow> x \<in> S"
  by simp

lemma free_Abelian_group_induct:
  assumes major: "Poly_Mapping.keys x \<subseteq> S"
      and minor: "P(0)"
           "\<And>x y. \<lbrakk>Poly_Mapping.keys x \<subseteq> S; Poly_Mapping.keys y \<subseteq> S; P x; P y\<rbrakk> \<Longrightarrow> P(x-y)"
           "\<And>a. a \<in> S \<Longrightarrow> P(frag_of a)"
         shows "P x"
proof -
  have "Poly_Mapping.keys x \<subseteq> S \<and> P x"
    using major
  proof (induction x rule: frag_induction)
    case (diff a b)
    then show ?case
      by (meson Un_least minor(2) order.trans keys_diff)
  qed (auto intro: minor)
  then show ?thesis ..
qed

lemma sum_closed_free_Abelian_group:
    "(\<And>i. i \<in> I \<Longrightarrow> x i \<in> carrier (free_Abelian_group S)) \<Longrightarrow> sum x I \<in> carrier (free_Abelian_group S)"
  apply (induction I rule: infinite_finite_induct, auto)
  by (metis (no_types, opaque_lifting) UnE subsetCE keys_add)


lemma (in comm_group) free_Abelian_group_universal:
  fixes f :: "'c \<Rightarrow> 'a"
  assumes "f ` S \<subseteq> carrier G"
  obtains h where "h \<in> hom (free_Abelian_group S) G" "\<And>x. x \<in> S \<Longrightarrow> h(frag_of x) = f x"
proof
  have fin: "Poly_Mapping.keys u \<subseteq> S \<Longrightarrow> finite {x \<in> S. f x [^] poly_mapping.lookup u x \<noteq> \<one>}" for u :: "'c \<Rightarrow>\<^sub>0 int"
    apply (rule finite_subset [OF _ finite_keys [of u]])
    unfolding keys.rep_eq by force
  define h :: "('c \<Rightarrow>\<^sub>0 int) \<Rightarrow> 'a"
    where "h \<equiv> \<lambda>x. gfinprod G (\<lambda>a. f a [^] poly_mapping.lookup x a) S"
  show "h \<in> hom (free_Abelian_group S) G"
  proof (rule homI)
    fix x y
    assume xy: "x \<in> carrier (free_Abelian_group S)" "y \<in> carrier (free_Abelian_group S)"
    then show "h (x \<otimes>\<^bsub>free_Abelian_group S\<^esub> y) = h x \<otimes> h y"
      using assms unfolding h_def free_Abelian_group_def
      by (simp add: fin gfinprod_distrib image_subset_iff Poly_Mapping.lookup_add int_pow_mult cong: gfinprod_cong)
  qed (use assms in \<open>force simp: free_Abelian_group_def h_def intro: gfinprod_closed\<close>)
  show "h(frag_of x) = f x" if "x \<in> S" for x
  proof -
    have fin: "(\<lambda>a. f x [^] (1::int)) \<in> {x} \<rightarrow> carrier G" "f x [^] (1::int) \<in> carrier G"
      using assms that by force+
    show ?thesis
      by (cases " f x [^] (1::int) = \<one>") (use assms that in \<open>auto simp: h_def gfinprod_def finprod_singleton\<close>)
  qed
qed

lemma eqpoll_free_Abelian_group_infinite:
  assumes "infinite A" shows "carrier(free_Abelian_group A) \<approx> A"
proof (rule lepoll_antisym)
  have "carrier (free_Abelian_group A) \<lesssim> {f::'a\<Rightarrow>int. f ` A \<subseteq> UNIV \<and> {x. f x \<noteq> 0} \<subseteq> A \<and> finite {x. f x \<noteq> 0}}"
    unfolding lepoll_def
    by (rule_tac x="Poly_Mapping.lookup" in exI) (auto simp: poly_mapping_eqI lookup_not_eq_zero_eq_in_keys inj_onI)
  also have "\<dots> \<lesssim> Fpow (A \<times> (UNIV::int set))"
    by (rule lepoll_restricted_funspace)
  also have "\<dots> \<approx> A \<times> (UNIV::int set)"
  proof (rule eqpoll_Fpow)
    show "infinite (A \<times> (UNIV::int set))"
      using assms finite_cartesian_productD1 by fastforce
  qed
  also have "\<dots> \<approx> A"
    unfolding eqpoll_iff_card_of_ordIso
  proof -
    have "|A \<times> (UNIV::int set)| <=o |A|"
      by (simp add: assms card_of_Times_ordLeq_infinite flip: infinite_iff_card_of_countable)
    moreover have "|A| \<le>o |A \<times> (UNIV::int set)|"
      by simp
    ultimately have "|A| *c |(UNIV::int set)| =o |A|"
      by (simp add: cprod_def ordIso_iff_ordLeq)
    then show "|A \<times> (UNIV::int set)| =o |A|"
      by (metis Times_cprod ordIso_transitive)
  qed
  finally show "carrier (free_Abelian_group A) \<lesssim> A" .
  have "inj_on frag_of A"
    by (simp add: frag_of_eq inj_on_def)
  moreover have "frag_of ` A \<subseteq> carrier (free_Abelian_group A)"
    by (simp add: image_subsetI)
  ultimately show "A \<lesssim> carrier (free_Abelian_group A)"
    by (force simp: lepoll_def)
qed

proposition (in comm_group) eqpoll_homomorphisms_from_free_Abelian_group:
   "{f. f \<in> extensional (carrier(free_Abelian_group S)) \<and> f \<in> hom (free_Abelian_group S) G}
    \<approx> (S \<rightarrow>\<^sub>E carrier G)"  (is "?lhs \<approx> ?rhs")
  unfolding eqpoll_def bij_betw_def
proof (intro exI conjI)
  let ?f = "\<lambda>f. restrict (f \<circ> frag_of) S"
  show "inj_on ?f ?lhs"
  proof (clarsimp simp: inj_on_def)
    fix g h
    assume
      g: "g \<in> extensional (carrier (free_Abelian_group S))" "g \<in> hom (free_Abelian_group S) G"
      and h: "h \<in> extensional (carrier (free_Abelian_group S))" "h \<in> hom (free_Abelian_group S) G"
      and eq: "restrict (g \<circ> frag_of) S = restrict (h \<circ> frag_of) S"
    have 0: "0 \<in> carrier (free_Abelian_group S)"
      by simp
    interpret hom_g: group_hom "free_Abelian_group S" G g
      using g by (auto simp: group_hom_def group_hom_axioms_def is_group)
    interpret hom_h: group_hom "free_Abelian_group S" G h
      using h by (auto simp: group_hom_def group_hom_axioms_def is_group)
    have "Poly_Mapping.keys c \<subseteq> S \<Longrightarrow> Poly_Mapping.keys c \<subseteq> S \<and> g c = h c" for c
    proof (induction c rule: frag_induction)
      case zero
      show ?case
        using hom_g.hom_one hom_h.hom_one by auto
    next
      case (one x)
      then show ?case
        using eq by (simp add: fun_eq_iff) (metis comp_def)
    next
      case (diff a b)
      then show ?case
        using hom_g.hom_mult hom_h.hom_mult hom_g.hom_inv hom_h.hom_inv
        apply (auto simp: dest: subsetD [OF keys_diff])
        by (metis keys_minus uminus_add_conv_diff)
    qed
    then show "g = h"
      by (meson g h carrier_free_Abelian_group_iff extensionalityI)
  qed
  have "f \<in> (\<lambda>f. restrict (f \<circ> frag_of) S) `
            {f \<in> extensional (carrier (free_Abelian_group S)). f \<in> hom (free_Abelian_group S) G}"
    if f: "f \<in> S \<rightarrow>\<^sub>E carrier G"
    for f :: "'c \<Rightarrow> 'a"
  proof -
    obtain h where h: "h \<in> hom (free_Abelian_group S) G" "\<And>x. x \<in> S \<Longrightarrow> h(frag_of x) = f x"
    proof (rule free_Abelian_group_universal)
      show "f ` S \<subseteq> carrier G"
        using f by blast
    qed auto
    let ?h = "restrict h (carrier (free_Abelian_group S))"
    show ?thesis
    proof
      show "f = restrict (?h \<circ> frag_of) S"
        using f by (force simp: h)
      show "?h \<in> {f \<in> extensional (carrier (free_Abelian_group S)). f \<in> hom (free_Abelian_group S) G}"
        using h by (auto simp: hom_def dest!: subsetD [OF keys_add])
    qed
  qed
  then show "?f ` ?lhs = S \<rightarrow>\<^sub>E carrier G"
    by (auto simp: hom_def Ball_def Pi_def)
qed

lemma hom_frag_minus:
  assumes "h \<in> hom (free_Abelian_group S) (free_Abelian_group T)" "Poly_Mapping.keys a \<subseteq> S"
  shows "h (-a) = - (h a)"
proof -
  have "Poly_Mapping.keys (h a) \<subseteq> T"
    by (meson assms carrier_free_Abelian_group_iff hom_in_carrier)
  then show ?thesis
    by (metis (no_types) assms carrier_free_Abelian_group_iff group_free_Abelian_group group_hom.hom_inv group_hom_axioms_def group_hom_def inv_free_Abelian_group)
qed

lemma hom_frag_add:
  assumes "h \<in> hom (free_Abelian_group S) (free_Abelian_group T)" "Poly_Mapping.keys a \<subseteq> S" "Poly_Mapping.keys b \<subseteq> S"
  shows "h (a+b) = h a + h b"
proof -
  have "Poly_Mapping.keys (h a) \<subseteq> T"
    by (meson assms carrier_free_Abelian_group_iff hom_in_carrier)
  moreover
  have "Poly_Mapping.keys (h b) \<subseteq> T"
    by (meson assms carrier_free_Abelian_group_iff hom_in_carrier)
  ultimately show ?thesis
    using assms hom_mult by fastforce
qed

lemma hom_frag_diff:
  assumes "h \<in> hom (free_Abelian_group S) (free_Abelian_group T)" "Poly_Mapping.keys a \<subseteq> S" "Poly_Mapping.keys b \<subseteq> S"
  shows "h (a-b) = h a - h b"
  by (metis (no_types, lifting) assms diff_conv_add_uminus hom_frag_add hom_frag_minus keys_minus)


proposition isomorphic_free_Abelian_groups:
   "free_Abelian_group S \<cong> free_Abelian_group T \<longleftrightarrow> S \<approx> T"  (is "(?FS \<cong> ?FT) = ?rhs")
proof
  interpret S: group "?FS"
    by simp
  interpret T: group "?FT"
    by simp
  interpret G2: comm_group "integer_mod_group 2"
    by (rule abelian_integer_mod_group)
  let ?Two = "{0..<2::int}"
  have [simp]: "\<not> ?Two \<subseteq> {a}" for a
    by (simp add: subset_iff) presburger
  assume L: "?FS \<cong> ?FT"
  let ?HS = "{h \<in> extensional (carrier ?FS). h \<in> hom ?FS (integer_mod_group 2)}"
  let ?HT = "{h \<in> extensional (carrier ?FT). h \<in> hom ?FT (integer_mod_group 2)}"
  have "S \<rightarrow>\<^sub>E ?Two \<approx> ?HS"
    apply (rule eqpoll_sym)
    using G2.eqpoll_homomorphisms_from_free_Abelian_group by (simp add: carrier_integer_mod_group)
  also have "\<dots> \<approx> ?HT"
  proof -
    obtain f g where "group_isomorphisms ?FS ?FT f g"
      using L S.iso_iff_group_isomorphisms by (force simp: is_iso_def)
    then have f: "f \<in> hom ?FS ?FT"
      and g: "g \<in> hom ?FT ?FS"
      and gf: "\<forall>x \<in> carrier ?FS. g(f x) = x"
      and fg: "\<forall>y \<in> carrier ?FT. f(g y) = y"
      by (auto simp: group_isomorphisms_def)
    let ?f = "\<lambda>h. restrict (h \<circ> g) (carrier ?FT)"
    let ?g = "\<lambda>h. restrict (h \<circ> f) (carrier ?FS)"
    show ?thesis
    proof (rule lepoll_antisym)
      show "?HS \<lesssim> ?HT"
        unfolding lepoll_def
      proof (intro exI conjI)
        show "inj_on ?f ?HS"
          apply (rule inj_on_inverseI [where g = ?g])
          using hom_in_carrier [OF f]
          by (auto simp: gf fun_eq_iff carrier_integer_mod_group Ball_def Pi_def extensional_def)
        show "?f ` ?HS \<subseteq> ?HT"
        proof clarsimp
          fix h
          assume h: "h \<in> hom ?FS (integer_mod_group 2)"
          have "h \<circ> g \<in> hom ?FT (integer_mod_group 2)"
            by (rule hom_compose [OF g h])
          moreover have "restrict (h \<circ> g) (carrier ?FT) x = (h \<circ> g) x" if "x \<in> carrier ?FT" for x
            using g that by (simp add: hom_def)
          ultimately show "restrict (h \<circ> g) (carrier ?FT) \<in> hom ?FT (integer_mod_group 2)"
            using T.hom_restrict by fastforce
        qed
      qed
    next
      show "?HT \<lesssim> ?HS"
        unfolding lepoll_def
      proof (intro exI conjI)
        show "inj_on ?g ?HT"
          apply (rule inj_on_inverseI [where g = ?f])
          using hom_in_carrier [OF g]
          by (auto simp: fg fun_eq_iff carrier_integer_mod_group Ball_def Pi_def extensional_def)
        show "?g ` ?HT \<subseteq> ?HS"
        proof clarsimp
          fix k
          assume k: "k \<in> hom ?FT (integer_mod_group 2)"
          have "k \<circ> f \<in> hom ?FS (integer_mod_group 2)"
            by (rule hom_compose [OF f k])
          moreover have "restrict (k \<circ> f) (carrier ?FS) x = (k \<circ> f) x" if "x \<in> carrier ?FS" for x
            using f that by (simp add: hom_def)
          ultimately show "restrict (k \<circ> f) (carrier ?FS) \<in> hom ?FS (integer_mod_group 2)"
            using S.hom_restrict by fastforce
        qed
      qed
    qed
  qed
  also have "\<dots> \<approx> T \<rightarrow>\<^sub>E ?Two"
    using G2.eqpoll_homomorphisms_from_free_Abelian_group by (simp add: carrier_integer_mod_group)
  finally have *: "S \<rightarrow>\<^sub>E ?Two \<approx> T \<rightarrow>\<^sub>E ?Two" .
  then have "finite (S \<rightarrow>\<^sub>E ?Two) \<longleftrightarrow> finite (T \<rightarrow>\<^sub>E ?Two)"
    by (rule eqpoll_finite_iff)
  then have "finite S \<longleftrightarrow> finite T"
    by (auto simp: finite_funcset_iff)
  then consider "finite S" "finite T" | "~ finite S" "~ finite T"
    by blast
  then show ?rhs
  proof cases
    case 1
    with * have "2 ^ card S = (2::nat) ^ card T"
      by (simp add: card_PiE finite_PiE eqpoll_iff_card)
    then have "card S = card T"
      by auto
    then show ?thesis
      using eqpoll_iff_card 1 by blast
  next
    case 2
    have "carrier (free_Abelian_group S) \<approx> carrier (free_Abelian_group T)"
      using L by (simp add: iso_imp_eqpoll_carrier)
    then show ?thesis
      using 2 eqpoll_free_Abelian_group_infinite eqpoll_sym eqpoll_trans by metis
  qed
next
  assume ?rhs
  then obtain f g where f: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T \<and> g(f x) = x"
                    and g: "\<And>y. y \<in> T \<Longrightarrow> g y \<in> S \<and> f(g y) = y"
    using eqpoll_iff_bijections by metis
  interpret S: comm_group "?FS"
    by (simp add: abelian_free_Abelian_group)
  interpret T: comm_group "?FT"
    by (simp add: abelian_free_Abelian_group)
  have "(frag_of \<circ> f) ` S \<subseteq> carrier (free_Abelian_group T)"
    using f by auto
  then obtain h where h: "h \<in> hom (free_Abelian_group S) (free_Abelian_group T)"
    and h_frag: "\<And>x. x \<in> S \<Longrightarrow> h (frag_of x) = (frag_of \<circ> f) x"
    using T.free_Abelian_group_universal [of "frag_of \<circ> f" S] by blast
  interpret hhom: group_hom "free_Abelian_group S" "free_Abelian_group T" h
    by (simp add: h group_hom_axioms_def group_hom_def)
  have "(frag_of \<circ> g) ` T \<subseteq> carrier (free_Abelian_group S)"
    using g by auto
  then obtain k where k: "k \<in> hom (free_Abelian_group T) (free_Abelian_group S)"
    and k_frag: "\<And>x. x \<in> T \<Longrightarrow> k (frag_of x) = (frag_of \<circ> g) x"
    using S.free_Abelian_group_universal [of "frag_of \<circ> g" T] by blast
  interpret khom: group_hom "free_Abelian_group T" "free_Abelian_group S" k
    by (simp add: k group_hom_axioms_def group_hom_def)
  have kh: "Poly_Mapping.keys x \<subseteq> S \<Longrightarrow> Poly_Mapping.keys x \<subseteq> S \<and> k (h x) = x" for x
  proof (induction rule: frag_induction)
    case zero
    then show ?case
      apply auto
      by (metis group_free_Abelian_group h hom_one k one_free_Abelian_group)
  next
    case (one x)
    then show ?case
      by (auto simp: h_frag k_frag f)
  next
    case (diff a b)
    with keys_diff have "Poly_Mapping.keys (a - b) \<subseteq> S"
      by (metis Un_least order_trans)
    with diff hhom.hom_closed show ?case
      by (simp add: hom_frag_diff [OF h] hom_frag_diff [OF k])
  qed
  have hk: "Poly_Mapping.keys y \<subseteq> T \<Longrightarrow> Poly_Mapping.keys y \<subseteq> T \<and> h (k y) = y" for y
  proof (induction rule: frag_induction)
    case zero
    then show ?case
      apply auto
      by (metis group_free_Abelian_group h hom_one k one_free_Abelian_group)
  next
    case (one y)
    then show ?case
      by (auto simp: h_frag k_frag g)
  next
    case (diff a b)
    with keys_diff have "Poly_Mapping.keys (a - b) \<subseteq> T"
      by (metis Un_least order_trans)
    with diff khom.hom_closed show ?case
      by (simp add: hom_frag_diff [OF h] hom_frag_diff [OF k])
  qed
  have "h \<in> iso ?FS ?FT"
    unfolding iso_def bij_betw_iff_bijections mem_Collect_eq
  proof (intro conjI exI ballI h)
    fix x
    assume x: "x \<in> carrier (free_Abelian_group S)"
    show "h x \<in> carrier (free_Abelian_group T)"
      by (meson x h hom_in_carrier)
    show "k (h x) = x"
      using x by (simp add: kh)
  next
    fix y
    assume y: "y \<in> carrier (free_Abelian_group T)"
    show "k y \<in> carrier (free_Abelian_group S)"
      by (meson y k hom_in_carrier)
    show "h (k y) = y"
      using y by (simp add: hk)
  qed
  then show "?FS \<cong> ?FT"
    by (auto simp: is_iso_def)
qed

lemma isomorphic_group_integer_free_Abelian_group_singleton:
  "integer_group \<cong> free_Abelian_group {x}"
proof -
  have "(\<lambda>n. frag_cmul n (frag_of x)) \<in> iso integer_group (free_Abelian_group {x})"
  proof (rule isoI [OF homI])
    show "bij_betw (\<lambda>n. frag_cmul n (frag_of x)) (carrier integer_group) (carrier (free_Abelian_group {x}))"
      apply (rule bij_betwI [where g = "\<lambda>y. Poly_Mapping.lookup y x"])
      by (auto simp: integer_group_def in_keys_iff intro!: poly_mapping_eqI)
  qed (auto simp: frag_cmul_distrib)
  then show ?thesis
    unfolding is_iso_def
    by blast
qed

lemma group_hom_free_Abelian_groups_id:
  "id \<in> hom (free_Abelian_group S) (free_Abelian_group T) \<longleftrightarrow> S \<subseteq> T"
proof -
  have "x \<in> T" if ST: "\<And>c:: 'a \<Rightarrow>\<^sub>0 int. Poly_Mapping.keys c \<subseteq> S \<longrightarrow> Poly_Mapping.keys c \<subseteq> T" and "x \<in> S" for x
    using ST [of "frag_of x"] \<open>x \<in> S\<close> by simp
  then show ?thesis
    by (auto simp: hom_def free_Abelian_group_def Pi_def)
qed

proposition iso_free_Abelian_group_sum:
  assumes "pairwise (\<lambda>i j. disjnt (S i) (S j)) I"
  shows "(\<lambda>f. sum' f I) \<in> iso (sum_group I (\<lambda>i. free_Abelian_group(S i))) (free_Abelian_group (\<Union>(S ` I)))"
    (is "?h \<in> iso ?G ?H")
proof (rule isoI)
  show hom: "?h \<in> hom ?G ?H"
  proof (rule homI)
    show "?h c \<in> carrier ?H" if "c \<in> carrier ?G" for c
      using that
      apply (simp add: sum.G_def carrier_sum_group)
      apply (rule order_trans [OF keys_sum])
      apply (auto simp: free_Abelian_group_def)
      done
    show "?h (x \<otimes>\<^bsub>?G\<^esub> y) = ?h x \<otimes>\<^bsub>?H\<^esub> ?h y"
      if "x \<in> carrier ?G" "y \<in> carrier ?G"  for x y
      using that by (simp add: sum.finite_Collect_op carrier_sum_group sum.distrib')
  qed
  interpret GH: group_hom "?G" "?H" "?h"
    using hom by (simp add: group_hom_def group_hom_axioms_def)
  show "bij_betw ?h (carrier ?G) (carrier ?H)"
    unfolding bij_betw_def
  proof (intro conjI subset_antisym)
    show "?h ` carrier ?G \<subseteq> carrier ?H"
      apply (clarsimp simp: sum.G_def carrier_sum_group simp del: carrier_free_Abelian_group_iff)
      by (force simp: PiE_def Pi_iff intro!: sum_closed_free_Abelian_group)
    have *: "poly_mapping.lookup (Abs_poly_mapping (\<lambda>j. if j \<in> S i then poly_mapping.lookup x j else 0)) k
           = (if k \<in> S i then poly_mapping.lookup x k else 0)" if "i \<in> I" for i k and x :: "'b \<Rightarrow>\<^sub>0 int"
      using that by (auto simp: conj_commute cong: conj_cong)
    have eq: "Abs_poly_mapping (\<lambda>j. if j \<in> S i then poly_mapping.lookup x j else 0) = 0
     \<longleftrightarrow> (\<forall>c \<in> S i. poly_mapping.lookup x c = 0)" if "i \<in> I" for i and x :: "'b \<Rightarrow>\<^sub>0 int"
      apply (auto simp: poly_mapping_eq_iff fun_eq_iff)
      apply (simp add: * Abs_poly_mapping_inverse conj_commute cong: conj_cong)
      apply (force dest!: spec split: if_split_asm)
      done
    have "x \<in> ?h ` {x \<in> \<Pi>\<^sub>E i\<in>I. {c. Poly_Mapping.keys c \<subseteq> S i}. finite {i \<in> I. x i \<noteq> 0}}"
      if x: "Poly_Mapping.keys x \<subseteq> \<Union> (S ` I)" for x :: "'b \<Rightarrow>\<^sub>0 int"
    proof -
      let ?f = "(\<lambda>i c. if c \<in> S i then Poly_Mapping.lookup x c else 0)"
      define J where "J \<equiv> {i \<in> I. \<exists>c\<in>S i. c \<in> Poly_Mapping.keys x}"
      have "J \<subseteq> (\<lambda>c. THE i. i \<in> I \<and> c \<in> S i) ` Poly_Mapping.keys x"
      proof (clarsimp simp: J_def)
        show "i \<in> (\<lambda>c. THE i. i \<in> I \<and> c \<in> S i) ` Poly_Mapping.keys x"
          if "i \<in> I" "c \<in> S i" "c \<in> Poly_Mapping.keys x" for i c
        proof
          show "i = (THE i. i \<in> I \<and> c \<in> S i)"
            using assms that by (auto simp: pairwise_def disjnt_def intro: the_equality [symmetric])
        qed (simp add: that)
      qed
      then have fin: "finite J"
        using finite_subset finite_keys by blast
      have [simp]: "Poly_Mapping.keys (Abs_poly_mapping (?f i)) = {k. ?f i k \<noteq> 0}" if "i \<in> I" for i
        by (simp add: eq_onp_def keys.abs_eq conj_commute cong: conj_cong)
      have [simp]: "Poly_Mapping.lookup (Abs_poly_mapping (?f i)) c = ?f i c" if "i \<in> I" for i c
        by (auto simp: Abs_poly_mapping_inverse conj_commute cong: conj_cong)
      show ?thesis
      proof
        have "poly_mapping.lookup x c = poly_mapping.lookup (?h (\<lambda>i\<in>I. Abs_poly_mapping (?f i))) c"
          for c
        proof (cases "c \<in> Poly_Mapping.keys x")
          case True
          then obtain i where "i \<in> I" "c \<in> S i" "?f i c \<noteq> 0"
            using x by (auto simp: in_keys_iff)
          then have 1: "poly_mapping.lookup (sum' (\<lambda>j. Abs_poly_mapping (?f j)) (I - {i})) c = 0"
            using assms
            apply (simp add: sum.G_def Poly_Mapping.lookup_sum pairwise_def disjnt_def)
            apply (force simp: eq split: if_split_asm intro!: comm_monoid_add_class.sum.neutral)
            done
          have 2: "poly_mapping.lookup x c = poly_mapping.lookup (Abs_poly_mapping (?f i)) c"
            by (auto simp: \<open>c \<in> S i\<close> Abs_poly_mapping_inverse conj_commute cong: conj_cong)
          have "finite {i \<in> I. Abs_poly_mapping (?f i) \<noteq> 0}"
            by (rule finite_subset [OF _ fin]) (use \<open>i \<in> I\<close> J_def eq in \<open>auto simp: in_keys_iff\<close>)
          with \<open>i \<in> I\<close> have "?h (\<lambda>j\<in>I. Abs_poly_mapping (?f j)) = Abs_poly_mapping (?f i) + sum' (\<lambda>j. Abs_poly_mapping (?f j)) (I - {i})"
            by (simp add: sum_diff1')
          then show ?thesis
            by (simp add: 1 2 Poly_Mapping.lookup_add)
        next
          case False
          then have "poly_mapping.lookup x c = 0"
            using keys.rep_eq by force
          then show ?thesis
            unfolding sum.G_def by (simp add: lookup_sum * comm_monoid_add_class.sum.neutral)
        qed
        then show "x = ?h (\<lambda>i\<in>I. Abs_poly_mapping (?f i))"
          by (rule poly_mapping_eqI)
        have "(\<lambda>i. Abs_poly_mapping (?f i)) \<in> (\<Pi> i\<in>I. {c. Poly_Mapping.keys c \<subseteq> S i})"
          by (auto simp: PiE_def Pi_def in_keys_iff)
        then show "(\<lambda>i\<in>I. Abs_poly_mapping (?f i))
                 \<in> {x \<in> \<Pi>\<^sub>E i\<in>I. {c. Poly_Mapping.keys c \<subseteq> S i}. finite {i \<in> I. x i \<noteq> 0}}"
          using fin unfolding J_def by (force simp add: eq in_keys_iff cong: conj_cong)
      qed
    qed
    then show "carrier ?H \<subseteq> ?h ` carrier ?G"
      by (simp add: carrier_sum_group) (auto simp: free_Abelian_group_def)
    show "inj_on ?h (carrier (sum_group I (\<lambda>i. free_Abelian_group (S i))))"
      unfolding GH.inj_on_one_iff
    proof clarify
      fix x
      assume "x \<in> carrier ?G" "?h x = \<one>\<^bsub>?H\<^esub>"
      then have eq0: "sum' x I = 0"
        and xs: "\<And>i. i \<in> I \<Longrightarrow> Poly_Mapping.keys (x i) \<subseteq> S i" and xext: "x \<in> extensional I"
        and fin: "finite {i \<in> I. x i \<noteq> 0}"
        by (simp_all add: carrier_sum_group PiE_def Pi_def)
      have "x i = 0" if "i \<in> I" for i
      proof -
        have "sum' x (insert i (I - {i})) = 0"
          using eq0 that by (simp add: insert_absorb)
        moreover have "Poly_Mapping.keys (sum' x (I - {i})) = {}"
        proof -
          have "x i = - sum' x (I - {i})"
            by (metis (mono_tags, lifting) diff_zero eq0 fin sum_diff1' minus_diff_eq that)
          then have "Poly_Mapping.keys (x i) = Poly_Mapping.keys (sum' x (I - {i}))"
            by simp
          then have "Poly_Mapping.keys (sum' x (I - {i})) \<subseteq> S i"
            using that xs by metis
          moreover
          have "Poly_Mapping.keys (sum' x (I - {i})) \<subseteq> (\<Union>j \<in> I - {i}. S j)"
          proof -
            have "Poly_Mapping.keys (sum' x (I - {i})) \<subseteq> (\<Union>i\<in>{j \<in> I. j \<noteq> i \<and> x j \<noteq> 0}. Poly_Mapping.keys (x i))"
              using keys_sum [of x "{j \<in> I. j \<noteq> i \<and> x j \<noteq> 0}"] by (simp add: sum.G_def)
            also have "\<dots> \<subseteq> \<Union> (S ` (I - {i}))"
              using xs by force
            finally show ?thesis .
          qed
          moreover have "A = {}" if "A \<subseteq> S i" "A \<subseteq> \<Union> (S ` (I - {i}))" for A
            using assms that \<open>i \<in> I\<close>
            by (force simp: pairwise_def disjnt_def image_def subset_iff)
          ultimately show ?thesis
            by metis
        qed
        then have [simp]: "sum' x (I - {i}) = 0"
          by (auto simp: sum.G_def)
        have "sum' x (insert i (I - {i})) = x i"
          by (subst sum.insert' [OF finite_subset [OF _ fin]]) auto
        ultimately show ?thesis
          by metis
      qed
      with xext [unfolded extensional_def]
      show "x = \<one>\<^bsub>sum_group I (\<lambda>i. free_Abelian_group (S i))\<^esub>"
        by (force simp: free_Abelian_group_def)
    qed
  qed
qed

lemma isomorphic_free_Abelian_group_Union:
  "pairwise disjnt I \<Longrightarrow> free_Abelian_group(\<Union> I) \<cong> sum_group I free_Abelian_group"
  using iso_free_Abelian_group_sum [of "\<lambda>X. X" I]
  by (metis SUP_identity_eq empty_iff group.iso_sym group_free_Abelian_group is_iso_def sum_group)

lemma isomorphic_sum_integer_group:
   "sum_group I (\<lambda>i. integer_group) \<cong> free_Abelian_group I"
proof -
  have "sum_group I (\<lambda>i. integer_group) \<cong> sum_group I (\<lambda>i. free_Abelian_group {i})"
    by (rule iso_sum_groupI) (auto simp: isomorphic_group_integer_free_Abelian_group_singleton)
  also have "\<dots> \<cong> free_Abelian_group I"
    using iso_free_Abelian_group_sum [of "\<lambda>x. {x}" I] by (auto simp: is_iso_def)
  finally show ?thesis .
qed

end
