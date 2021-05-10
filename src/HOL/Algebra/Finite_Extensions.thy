(*  Title:      HOL/Algebra/Finite_Extensions.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Finite_Extensions
  imports Embedded_Algebras Polynomials Polynomial_Divisibility
    
begin

section \<open>Finite Extensions\<close>

subsection \<open>Definitions\<close>

definition (in ring) transcendental :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "transcendental K x \<longleftrightarrow> inj_on (\<lambda>p. eval p x) (carrier (K[X]))"

abbreviation (in ring) algebraic :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "algebraic K x \<equiv> \<not> transcendental K x"

definition (in ring) Irr :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "Irr K x = (THE p. p \<in> carrier (K[X]) \<and> pirreducible K p \<and> eval p x = \<zero> \<and> lead_coeff p = \<one>)"

inductive_set (in ring) simple_extension :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  for K and x where
    zero [simp, intro]: "\<zero> \<in> simple_extension K x" |
    lin:  "\<lbrakk> k1 \<in> simple_extension K x; k2 \<in> K \<rbrakk> \<Longrightarrow> (k1 \<otimes> x) \<oplus> k2 \<in> simple_extension K x"

fun (in ring) finite_extension :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set"
  where "finite_extension K xs = foldr (\<lambda>x K'. simple_extension K' x) xs K"


subsection \<open>Basic Properties\<close>

lemma (in ring) transcendental_consistent:
  assumes "subring K R" shows "transcendental = ring.transcendental (R \<lparr> carrier := K \<rparr>)"
  unfolding transcendental_def ring.transcendental_def[OF subring_is_ring[OF assms]]
            univ_poly_consistent[OF assms] eval_consistent[OF assms] ..

lemma (in ring) algebraic_consistent:
  assumes "subring K R" shows "algebraic = ring.algebraic (R \<lparr> carrier := K \<rparr>)"
  unfolding over_def transcendental_consistent[OF assms] ..

lemma (in ring) eval_transcendental:
  assumes "(transcendental over K) x" "p \<in> carrier (K[X])" "eval p x = \<zero>" shows "p = []"
proof -
  have "[] \<in> carrier (K[X])" and "eval [] x = \<zero>"
    by (auto simp add: univ_poly_def)
  thus ?thesis
    using assms unfolding over_def transcendental_def inj_on_def by auto
qed

lemma (in ring) transcendental_imp_trivial_ker:
  shows "(transcendental over K) x \<Longrightarrow> a_kernel (K[X]) R (\<lambda>p. eval p x) = { [] }"
  using eval_transcendental unfolding a_kernel_def' by (auto simp add: univ_poly_def)

lemma (in ring) non_trivial_ker_imp_algebraic:
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) \<noteq> { [] } \<Longrightarrow> (algebraic over K) x"
  using transcendental_imp_trivial_ker unfolding over_def by auto

lemma (in domain) trivial_ker_imp_transcendental:
  assumes "subring K R" and "x \<in> carrier R"
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) = { [] } \<Longrightarrow> (transcendental over K) x"
  using ring_hom_ring.trivial_ker_imp_inj[OF eval_ring_hom[OF assms]]
  unfolding transcendental_def over_def by (simp add: univ_poly_zero)

lemma (in domain) algebraic_imp_non_trivial_ker:
  assumes "subring K R" and "x \<in> carrier R"
  shows "(algebraic over K) x \<Longrightarrow> a_kernel (K[X]) R (\<lambda>p. eval p x) \<noteq> { [] }"
  using trivial_ker_imp_transcendental[OF assms] unfolding over_def by auto

lemma (in domain) algebraicE:
  assumes "subring K R" and "x \<in> carrier R" "(algebraic over K) x"
  obtains p where "p \<in> carrier (K[X])" "p \<noteq> []" "eval p x = \<zero>"
proof -
  have "[] \<in> a_kernel (K[X]) R (\<lambda>p. eval p x)"
    unfolding a_kernel_def' univ_poly_def by auto
  then obtain p where "p \<in> carrier (K[X])" "p \<noteq> []" "eval p x = \<zero>"
    using algebraic_imp_non_trivial_ker[OF assms] unfolding a_kernel_def' by blast
  thus thesis using that by auto
qed

lemma (in ring) algebraicI:
  assumes "p \<in> carrier (K[X])" "p \<noteq> []" and "eval p x = \<zero>" shows "(algebraic over K) x"
  using assms non_trivial_ker_imp_algebraic unfolding a_kernel_def' by auto

lemma (in ring) transcendental_mono:
  assumes "K \<subseteq> K'" "(transcendental over K') x" shows "(transcendental over K) x"
proof -
  have "carrier (K[X]) \<subseteq> carrier (K'[X])"
    using assms(1) unfolding univ_poly_def polynomial_def by auto
  thus ?thesis
    using assms unfolding over_def transcendental_def by (metis inj_on_subset)
qed

corollary (in ring) algebraic_mono:
  assumes "K \<subseteq> K'" "(algebraic over K) x" shows "(algebraic over K') x"
  using transcendental_mono[OF assms(1)] assms(2) unfolding over_def by blast 

lemma (in domain) zero_is_algebraic:
  assumes "subring K R" shows "(algebraic over K) \<zero>"
  using algebraicI[OF var_closed(1)[OF assms]] unfolding var_def by auto

lemma (in domain) algebraic_self:
  assumes "subring K R" and "k \<in> K" shows "(algebraic over K) k"
proof (rule algebraicI[of "[ \<one>, \<ominus> k ]"])
  show "[ \<one>, \<ominus> k ] \<in> carrier (K [X])" and "[ \<one>, \<ominus> k ] \<noteq> []"
    using subringE(2-3,5)[OF assms(1)] assms(2) unfolding univ_poly_def polynomial_def by auto
  have "k \<in> carrier R"
    using subringE(1)[OF assms(1)] assms(2) by auto
  thus "eval [ \<one>, \<ominus> k ] k = \<zero>"
    by (auto, algebra)
qed

lemma (in domain) ker_diff_carrier:
  assumes "subring K R"
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) \<noteq> carrier (K[X])"
proof -
  have "eval [ \<one> ] x \<noteq> \<zero>" and "[ \<one> ] \<in> carrier (K[X])"
    using subringE(3)[OF assms] unfolding univ_poly_def polynomial_def by auto
  thus ?thesis
    unfolding a_kernel_def' by blast
qed


subsection \<open>Minimal Polynomial\<close>

lemma (in domain) minimal_polynomial_is_unique:
  assumes "subfield K R" and "x \<in> carrier R" "(algebraic over K) x"
  shows "\<exists>!p \<in> carrier (K[X]). pirreducible K p \<and> eval p x = \<zero> \<and> lead_coeff p = \<one>"
    (is "\<exists>!p. ?minimal_poly p")
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  let ?ker_gen = "\<lambda>p. p \<in> carrier (K[X]) \<and> pirreducible K p \<and> lead_coeff p = \<one> \<and>
                    a_kernel (K[X]) R (\<lambda>p. eval p x) = PIdl\<^bsub>K[X]\<^esub> p"

  obtain p where p: "?ker_gen p" and unique: "\<And>q. ?ker_gen q \<Longrightarrow> q = p"
    using exists_unique_pirreducible_gen[OF assms(1) eval_ring_hom[OF _ assms(2)]
          algebraic_imp_non_trivial_ker[OF _ assms(2-3)]
          ker_diff_carrier] subfieldE(1)[OF assms(1)] by auto
  hence "?minimal_poly p"
    using UP.cgenideal_self p unfolding a_kernel_def' by auto
  moreover have "\<And>q. ?minimal_poly q \<Longrightarrow> q = p"
  proof -
    fix q assume q: "?minimal_poly q"
    then have "q \<in> PIdl\<^bsub>K[X]\<^esub> p"
      using p unfolding a_kernel_def' by auto
    hence "p \<sim>\<^bsub>K[X]\<^esub> q"
      using cgenideal_pirreducible[OF assms(1)] p q by simp
    hence "a_kernel (K[X]) R (\<lambda>p. eval p x) = PIdl\<^bsub>K[X]\<^esub> q"
      using UP.associated_iff_same_ideal q p by simp
    thus "q = p"
      using unique q by simp
  qed
  ultimately show ?thesis by blast
qed

lemma (in domain) IrrE:
  assumes "subfield K R" and "x \<in> carrier R" "(algebraic over K) x"
  shows "Irr K x \<in> carrier (K[X])" and "pirreducible K (Irr K x)"
    and "lead_coeff (Irr K x) = \<one>" and "eval (Irr K x) x = \<zero>"
  using theI'[OF minimal_polynomial_is_unique[OF assms]] unfolding Irr_def by auto

lemma (in domain) Irr_generates_ker:
  assumes "subfield K R" and "x \<in> carrier R" "(algebraic over K) x"
  shows "a_kernel (K[X]) R (\<lambda>p. eval p x) = PIdl\<^bsub>K[X]\<^esub> (Irr K x)"
proof -
  obtain q
    where q: "q \<in> carrier (K[X])" "pirreducible K q"
      and ker: "a_kernel (K[X]) R (\<lambda>p. eval p x) = PIdl\<^bsub>K[X]\<^esub> q"
    using exists_unique_pirreducible_gen[OF assms(1) eval_ring_hom[OF _ assms(2)]
          algebraic_imp_non_trivial_ker[OF _ assms(2-3)]
          ker_diff_carrier] subfieldE(1)[OF assms(1)] by auto
  have "Irr K x \<in> PIdl\<^bsub>K[X]\<^esub> q"
    using IrrE(1,4)[OF assms] ker unfolding a_kernel_def' by auto
  thus ?thesis
    using cgenideal_pirreducible[OF assms(1) q(1-2) IrrE(2)[OF assms]] q(1) IrrE(1)[OF assms]
          cring.associated_iff_same_ideal[OF univ_poly_is_cring[OF subfieldE(1)[OF assms(1)]]]
    unfolding ker
    by simp
qed

lemma (in domain) Irr_minimal:
  assumes "subfield K R" and "x \<in> carrier R" "(algebraic over K) x"
    and "p \<in> carrier (K[X])" "eval p x = \<zero>" shows "(Irr K x) pdivides p"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  have "p \<in> PIdl\<^bsub>K[X]\<^esub> (Irr K x)"
    using Irr_generates_ker[OF assms(1-3)] assms(4-5) unfolding a_kernel_def' by auto
  hence "(Irr K x) divides\<^bsub>K[X]\<^esub> p"
    using UP.to_contain_is_to_divide IrrE(1)[OF assms(1-3)]
    by (meson UP.cgenideal_ideal UP.cgenideal_minimal assms(4))
  thus ?thesis
    unfolding pdivides_iff_shell[OF assms(1) IrrE(1)[OF assms(1-3)] assms(4)] .
qed

lemma (in domain) rupture_of_Irr:
  assumes "subfield K R" and "x \<in> carrier R" "(algebraic over K) x" shows "field (Rupt K (Irr K x))"
  using rupture_is_field_iff_pirreducible[OF assms(1)] IrrE(1-2)[OF assms] by simp


subsection \<open>Simple Extensions\<close>

lemma (in ring) simple_extension_consistent:
  assumes "subring K R" shows "ring.simple_extension (R \<lparr> carrier := K \<rparr>) = simple_extension"
proof -
  interpret K: ring "R \<lparr> carrier := K \<rparr>"
    using subring_is_ring[OF assms] .

  have "\<And>K' x. K.simple_extension  K' x \<subseteq> simple_extension K' x"
  proof
    fix K' x a show "a \<in> K.simple_extension  K' x \<Longrightarrow> a \<in> simple_extension K' x"
      by (induction rule: K.simple_extension.induct) (auto simp add: simple_extension.lin)
  qed
  moreover
  have "\<And>K' x. simple_extension K' x \<subseteq> K.simple_extension  K' x"
  proof
    fix K' x a assume a: "a \<in> simple_extension K' x" thus "a \<in> K.simple_extension  K' x"
      using K.simple_extension.zero K.simple_extension.lin
      by (induction rule: simple_extension.induct) (simp)+
  qed
  ultimately show ?thesis by blast
qed

lemma (in ring) mono_simple_extension:
  assumes "K \<subseteq> K'" shows "simple_extension K x \<subseteq> simple_extension K' x"
proof
  fix a assume "a \<in> simple_extension K x" thus "a \<in> simple_extension K' x"
  proof (induct a rule: simple_extension.induct, simp)
    case lin thus ?case using simple_extension.lin assms by blast
  qed
qed

lemma (in ring) simple_extension_incl:
  assumes "K \<subseteq> carrier R" and "x \<in> carrier R" shows "K \<subseteq> simple_extension K x"
proof
  fix k assume "k \<in> K" thus "k \<in> simple_extension K x"
    using simple_extension.lin[OF simple_extension.zero, of k K x] assms by auto
qed

lemma (in ring) simple_extension_mem:
  assumes "subring K R" and "x \<in> carrier R" shows "x \<in> simple_extension K x"
proof -
  have "\<one> \<in> simple_extension K x"
    using simple_extension_incl[OF _ assms(2)] subringE(1,3)[OF assms(1)] by auto
  thus ?thesis
    using simple_extension.lin[OF _ subringE(2)[OF assms(1)], of \<one> x] assms(2) by auto
qed

lemma (in ring) simple_extension_carrier:
  assumes "x \<in> carrier R" shows "simple_extension (carrier R) x = carrier R"
proof
  show "carrier R \<subseteq> simple_extension (carrier R) x"
    using simple_extension_incl[OF _ assms] by auto
next
  show "simple_extension (carrier R) x \<subseteq> carrier R"
  proof
    fix a assume "a \<in> simple_extension (carrier R) x" thus "a \<in> carrier R"
      by (induct a rule: simple_extension.induct) (auto simp add: assms)
  qed
qed

lemma (in ring) simple_extension_in_carrier:
  assumes "K \<subseteq> carrier R" and "x \<in> carrier R" shows "simple_extension K x \<subseteq> carrier R"
  using mono_simple_extension[OF assms(1), of x] simple_extension_carrier[OF assms(2)] by auto 

lemma (in ring) simple_extension_subring_incl:
  assumes "subring K' R" and "K \<subseteq> K'" "x \<in> K'" shows "simple_extension K x \<subseteq> K'"
  using ring.simple_extension_in_carrier[OF subring_is_ring[OF assms(1)]] assms(2-3)
  unfolding simple_extension_consistent[OF assms(1)] by simp

lemma (in ring) simple_extension_as_eval_img:
  assumes "K \<subseteq> carrier R" "x \<in> carrier R"
  shows "simple_extension K x = (\<lambda>p. eval p x) ` carrier (K[X])"
proof
  show "simple_extension K x \<subseteq> (\<lambda>p. eval p x) ` carrier (K[X])"
  proof
    fix a assume "a \<in> simple_extension K x" thus "a \<in> (\<lambda>p. eval p x) ` carrier (K[X])"
    proof (induction rule: simple_extension.induct)
      case zero
      have "polynomial K []" and "eval [] x = \<zero>"
        unfolding polynomial_def by simp+
      thus ?case
        unfolding univ_poly_carrier by force
    next
      case (lin k1 k2)
      then obtain p where p: "p \<in> carrier (K[X])" "polynomial K p" "eval p x = k1"
        by (auto simp add: univ_poly_carrier)
      hence "set p \<subseteq> carrier R" and "k2 \<in> carrier R"
        using assms(1) lin(2) unfolding polynomial_def by auto
      hence "eval (normalize (p @ [ k2 ])) x = k1 \<otimes> x \<oplus> k2"
        using eval_append_aux[of p k2 x] eval_normalize[of "p @ [ k2 ]" x] assms(2) p(3) by auto
      moreover have "set (p @ [k2]) \<subseteq> K"
        using polynomial_incl[OF p(2)] \<open>k2 \<in> K\<close> by auto
      then have "local.normalize (p @ [k2]) \<in> carrier (K [X])"
        using normalize_gives_polynomial univ_poly_carrier by blast
      ultimately show ?case
        unfolding univ_poly_carrier by force
    qed
  qed
next
  show "(\<lambda>p. eval p x) ` carrier (K[X]) \<subseteq> simple_extension K x"
  proof
    fix a assume "a \<in> (\<lambda>p. eval p x) ` carrier (K[X])"
    then obtain p where p: "set p \<subseteq> K" "eval p x = a"
      using polynomial_incl unfolding univ_poly_def by auto
    thus "a \<in> simple_extension K x"
    proof (induct "length p" arbitrary: p a)
      case 0 thus ?case
        using simple_extension.zero by simp
    next
      case (Suc n)
      obtain p' k where p: "p = p' @ [ k ]"
        using Suc(2) by (metis list.size(3) nat.simps(3) rev_exhaust)
      hence "a = (eval p' x) \<otimes> x \<oplus> k"
        using eval_append_aux[of p' k x] Suc(3-4) assms unfolding p by auto
      moreover have "eval p' x \<in> simple_extension K x"
        using Suc(1-3) unfolding p by auto
      ultimately show ?case
        using simple_extension.lin Suc(3) unfolding p by auto
    qed
  qed
qed

corollary (in domain) simple_extension_is_subring:
  assumes "subring K R" "x \<in> carrier R" shows "subring (simple_extension K x) R"
  using ring_hom_ring.img_is_subring[OF eval_ring_hom[OF assms]
        ring.carrier_is_subring[OF univ_poly_is_ring[OF assms(1)]]]
        simple_extension_as_eval_img[OF subringE(1)[OF assms(1)] assms(2)]
  by simp

corollary (in domain) simple_extension_minimal:
  assumes "subring K R" "x \<in> carrier R"
  shows "simple_extension K x = \<Inter> { K'. subring K' R \<and> K \<subseteq> K' \<and> x \<in> K' }"
  using simple_extension_is_subring[OF assms] simple_extension_mem[OF assms]
        simple_extension_incl[OF subringE(1)[OF assms(1)] assms(2)] simple_extension_subring_incl
  by blast

corollary (in domain) simple_extension_isomorphism:
  assumes "subring K R" "x \<in> carrier R"
  shows "(K[X]) Quot (a_kernel (K[X]) R (\<lambda>p. eval p x)) \<simeq> R \<lparr> carrier := simple_extension K x \<rparr>"
  using ring_hom_ring.FactRing_iso_set_aux[OF eval_ring_hom[OF assms]]
        simple_extension_as_eval_img[OF subringE(1)[OF assms(1)] assms(2)]
  unfolding is_ring_iso_def by auto

corollary (in domain) simple_extension_of_algebraic:
  assumes "subfield K R" and "x \<in> carrier R" "(algebraic over K) x"
  shows "Rupt K (Irr K x) \<simeq> R \<lparr> carrier := simple_extension K x \<rparr>"
  using simple_extension_isomorphism[OF subfieldE(1)[OF assms(1)] assms(2)]
  unfolding Irr_generates_ker[OF assms] rupture_def by simp

corollary (in domain) simple_extension_of_transcendental:
  assumes "subring K R" and "x \<in> carrier R" "(transcendental over K) x"
  shows "K[X] \<simeq> R \<lparr> carrier := simple_extension K x \<rparr>"
  using simple_extension_isomorphism[OF _ assms(2), of K] assms(1)
        ring_iso_trans[OF ring.FactRing_zeroideal(2)[OF univ_poly_is_ring]]
  unfolding transcendental_imp_trivial_ker[OF assms(3)] univ_poly_zero
  by auto

proposition (in domain) simple_extension_subfield_imp_algebraic:
  assumes "subring K R" "x \<in> carrier R"
  shows "subfield (simple_extension K x) R \<Longrightarrow> (algebraic over K) x"
proof -
  assume simple_ext: "subfield (simple_extension K x) R" show "(algebraic over K) x"
  proof (rule ccontr)
    assume "\<not> (algebraic over K) x" then have "(transcendental over K) x"
      unfolding over_def by simp
    then obtain h where h: "h \<in> ring_iso (R \<lparr> carrier := simple_extension K x \<rparr>) (K[X])"
      using ring_iso_sym[OF univ_poly_is_ring simple_extension_of_transcendental] assms
      unfolding is_ring_iso_def by blast
    then interpret Hom: ring_hom_ring "R \<lparr> carrier := simple_extension K x \<rparr>" "K[X]" h
      using subring_is_ring[OF simple_extension_is_subring[OF assms]]
            univ_poly_is_ring[OF assms(1)] assms h
      by (auto simp add: ring_hom_ring_def ring_hom_ring_axioms_def ring_iso_def)
    have "field (K[X])"
      using field.ring_iso_imp_img_field[OF subfield_iff(2)[OF simple_ext] h]
      unfolding Hom.hom_one Hom.hom_zero by simp
    moreover have "\<not> field (K[X])"
      using univ_poly_not_field[OF assms(1)] .
    ultimately show False by simp
  qed
qed

proposition (in domain) simple_extension_is_subfield:
  assumes "subfield K R" "x \<in> carrier R"
  shows "subfield (simple_extension K x) R \<longleftrightarrow> (algebraic over K) x"
proof
  assume alg: "(algebraic over K) x"
  then obtain h where h: "h \<in> ring_iso (Rupt K (Irr K x)) (R \<lparr> carrier := simple_extension K x \<rparr>)"
    using simple_extension_of_algebraic[OF assms] unfolding is_ring_iso_def by blast
  have rupt_field: "field (Rupt K (Irr K x))" and "ring (R \<lparr> carrier := simple_extension K x \<rparr>)"
    using subring_is_ring[OF simple_extension_is_subring[OF subfieldE(1)]]
          rupture_of_Irr[OF assms alg] assms by simp+
  then interpret Hom: ring_hom_ring "Rupt K (Irr K x)" "R \<lparr> carrier := simple_extension K x \<rparr>" h
    using h cring.axioms(1)[OF domain.axioms(1)[OF field.axioms(1)]]
    by (auto simp add: ring_hom_ring_def ring_hom_ring_axioms_def ring_iso_def)
  show "subfield (simple_extension K x) R"
    using field.ring_iso_imp_img_field[OF rupt_field h] subfield_iff(1)[OF _
          simple_extension_in_carrier[OF subfieldE(3)[OF assms(1)] assms(2)]]
    by simp
next
  assume simple_ext: "subfield (simple_extension K x) R" thus "(algebraic over K) x"
    using simple_extension_subfield_imp_algebraic[OF subfieldE(1)[OF assms(1)] assms(2)] by simp
qed


subsection \<open>Link between dimension of K-algebras and algebraic extensions\<close>

lemma (in domain) exp_base_independent:
  assumes "subfield K R" "x \<in> carrier R" "(algebraic over K) x"
  shows "independent K (exp_base x (degree (Irr K x)))"
proof -
  have "\<And>n. n \<le> degree (Irr K x) \<Longrightarrow> independent K (exp_base x n)"
  proof -
    fix n show "n \<le> degree (Irr K x) \<Longrightarrow> independent K (exp_base x n)"
    proof (induct n, simp add: exp_base_def)
      case (Suc n)
      have "x [^] n \<notin> Span K (exp_base x n)"
      proof (rule ccontr)
        assume "\<not> x [^] n \<notin> Span K (exp_base x n)"
        then obtain a Ks
          where Ks: "a \<in> K - { \<zero> }" "set Ks \<subseteq> K" "length Ks = n" "combine (a # Ks) (exp_base x (Suc n)) = \<zero>"
          using Span_mem_imp_non_trivial_combine[OF assms(1) exp_base_closed[OF assms(2), of n]]
          by (auto simp add: exp_base_def)
        hence "eval (a # Ks) x = \<zero>"
          using combine_eq_eval by (auto simp add: exp_base_def)
        moreover have "(a # Ks) \<in> carrier (K[X]) - { [] }"
          unfolding univ_poly_def polynomial_def using Ks(1-2) by auto
        ultimately have "degree (Irr K x) \<le> n"
          using pdivides_imp_degree_le[OF subfieldE(1)[OF assms(1)]
                IrrE(1)[OF assms] _ _  Irr_minimal[OF assms, of "a # Ks"]] Ks(3) by auto
        from \<open>Suc n \<le> degree (Irr K x)\<close> and this show False by simp
      qed
      thus ?case
        using independent.li_Cons assms(2) Suc by (auto simp add: exp_base_def)
    qed
  qed
  thus ?thesis
    by simp
qed

lemma (in ring) Span_eq_eval_img:
  assumes "subfield K R" "x \<in> carrier R"
  shows "Span K (exp_base x n) = (\<lambda>p. eval p x) ` { p \<in> carrier (K[X]). length p \<le> n }"
    (is "?Span = ?eval_img")
proof
  show "?Span \<subseteq> ?eval_img"
  proof
    fix u assume "u \<in> Span K (exp_base x n)"
    then obtain Ks where Ks: "set Ks \<subseteq> K" "length Ks = n" "u = combine Ks (exp_base x n)"
      using Span_eq_combine_set_length_version[OF assms(1) exp_base_closed[OF assms(2)]]
      by (auto simp add: exp_base_def)
    hence "u = eval (normalize Ks) x"
      using combine_eq_eval eval_normalize[OF _ assms(2)] subfieldE(3)[OF assms(1)] by auto
    moreover have "normalize Ks \<in> carrier (K[X])"
      using normalize_gives_polynomial[OF Ks(1)] unfolding univ_poly_def by auto
    moreover have "length (normalize Ks) \<le> n"
      using normalize_length_le[of Ks] Ks(2) by auto
    ultimately show "u \<in> ?eval_img" by auto
  qed
next
  show "?eval_img \<subseteq> ?Span"
  proof
    fix u assume "u \<in> ?eval_img"
    then obtain p where p: "p \<in> carrier (K[X])" "length p \<le> n" "u = eval p x"
      by blast
    hence "combine p (exp_base x (length p)) = u"
      using combine_eq_eval by auto
    moreover have set_p: "set p \<subseteq> K"
      using polynomial_incl[of K p] p(1) unfolding univ_poly_carrier by auto
    hence "set p \<subseteq> carrier R"
      using subfieldE(3)[OF assms(1)] by auto 
    moreover have "drop (n - length p) (exp_base x n) = exp_base x (length p)"
      using p(2) drop_exp_base by auto
    ultimately have "combine ((replicate (n - length p) \<zero>) @ p) (exp_base x n) = u"
      using combine_prepend_replicate[OF _ exp_base_closed[OF assms(2), of n]] by auto
    moreover have "set ((replicate (n - length p) \<zero>) @ p) \<subseteq> K"
      using subringE(2)[OF subfieldE(1)[OF assms(1)]] set_p by auto
    ultimately show "u \<in> ?Span"
      using Span_eq_combine_set[OF assms(1) exp_base_closed[OF assms(2), of n]] by blast
  qed
qed

lemma (in domain) Span_exp_base:
  assumes "subfield K R" "x \<in> carrier R" "(algebraic over K) x"
  shows "Span K (exp_base x (degree (Irr K x))) = simple_extension K x"
  unfolding simple_extension_as_eval_img[OF subfieldE(3)[OF assms(1)] assms(2)]
            Span_eq_eval_img[OF assms(1-2)]
proof (auto)
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .
  note hom_simps = ring_hom_memE[OF eval_is_hom[OF subfieldE(1)[OF assms(1)] assms(2)]]

  fix p assume p: "p \<in> carrier (K[X])"
  have Irr: "Irr K x \<in> carrier (K[X])" "Irr K x \<noteq> []"
    using IrrE(1-2)[OF assms] unfolding ring_irreducible_def univ_poly_zero by auto 
  then obtain q r
    where q: "q \<in> carrier (K[X])" and r: "r \<in> carrier (K[X])"
      and dvd: "p = Irr K x \<otimes>\<^bsub>K [X]\<^esub> q \<oplus>\<^bsub>K [X]\<^esub> r" "r = [] \<or> degree r < degree (Irr K x)"
    using subfield_long_division_theorem_shell[OF assms(1) p Irr(1)] unfolding univ_poly_zero by auto
  hence "eval p x = (eval (Irr K x) x) \<otimes> (eval q x) \<oplus> (eval r x)"
    using hom_simps(2-3) Irr(1) by simp
  hence "eval p x = eval r x"
    using hom_simps(1) q r unfolding IrrE(4)[OF assms] by simp
  moreover have "length r < length (Irr K x)"
    using dvd(2) Irr(2) by auto
  ultimately
  show "eval p x \<in> (\<lambda>p. local.eval p x) ` { p \<in> carrier (K [X]). length p \<le> length (Irr K x) - Suc 0 }"
    using r by auto
qed

corollary (in domain) dimension_simple_extension:
  assumes "subfield K R" "x \<in> carrier R" "(algebraic over K) x"
  shows "dimension (degree (Irr K x)) K (simple_extension K x)"
  using dimension_independent[OF exp_base_independent[OF assms]] Span_exp_base[OF assms]
  by (simp add: exp_base_def)

lemma (in ring) finite_dimension_imp_algebraic:
  assumes "subfield K R" "subring F R" and "finite_dimension K F"
  shows "x \<in> F \<Longrightarrow> (algebraic over K) x"
proof -
  let ?Us = "\<lambda>n. map (\<lambda>i. x [^] i) (rev [0..< Suc n])"

  assume x: "x \<in> F" then have in_carrier: "x \<in> carrier R"
    using subringE[OF assms(2)] by auto
  obtain n where n: "dimension n K F"
    using assms(3) by auto
  have set_Us: "set (?Us n) \<subseteq> F"
    using x subringE(3,6)[OF assms(2)] by (induct n) (auto)
  hence "set (?Us n) \<subseteq> carrier R"
    using subringE(1)[OF assms(2)] by auto
  moreover have "dependent K (?Us n)"
    using independent_length_le_dimension[OF assms(1) n _ set_Us] by auto
  ultimately
  obtain Ks where Ks: "length Ks = Suc n" "combine Ks (?Us n) = \<zero>" "set Ks \<subseteq> K" "set Ks \<noteq> { \<zero> }"
    using dependent_imp_non_trivial_combine[OF assms(1), of "?Us n"] by auto
  have "set Ks \<subseteq> carrier R"
    using subring_props(1)[OF assms(1)] Ks(3) by auto 
  hence "eval (normalize Ks) x = \<zero>"
    using combine_eq_eval[of Ks] eval_normalize[OF _ in_carrier] Ks(1-2) by (simp add: exp_base_def)
  moreover have "normalize Ks = [] \<Longrightarrow> set Ks \<subseteq> { \<zero> }"
    by (induct Ks) (auto, meson list.discI,
                    metis all_not_in_conv list.discI list.sel(3) singletonD subset_singletonD)
  hence "normalize Ks \<noteq> []"
    using Ks(1,4) by (metis list.size(3) nat.distinct(1) set_empty subset_singleton_iff)
  moreover have "normalize Ks \<in> carrier (K[X])"
    using normalize_gives_polynomial[OF Ks(3)] unfolding univ_poly_def by auto
  ultimately show ?thesis
    using algebraicI by auto
qed

corollary (in domain) simple_extension_dim:
  assumes "subfield K R" "x \<in> carrier R" "(algebraic over K) x"
  shows "(dim over K) (simple_extension K x) = degree (Irr K x)"
  using dimI[OF assms(1) dimension_simple_extension[OF assms]] .

corollary (in domain) finite_dimension_simple_extension:
  assumes "subfield K R" "x \<in> carrier R"
  shows "finite_dimension K (simple_extension K x) \<longleftrightarrow> (algebraic over K) x"
  using finite_dimensionI[OF dimension_simple_extension[OF assms]]
        finite_dimension_imp_algebraic[OF _ simple_extension_is_subring[OF subfieldE(1)]]
        simple_extension_mem[OF subfieldE(1)] assms
  by auto


subsection \<open>Finite Extensions\<close>

lemma (in ring) finite_extension_consistent:
  assumes "subring K R" shows "ring.finite_extension (R \<lparr> carrier := K \<rparr>) = finite_extension"
proof -
  have "\<And>K' xs. ring.finite_extension (R \<lparr> carrier := K \<rparr>) K' xs = finite_extension K' xs"
  proof -
    fix K' xs show "ring.finite_extension (R \<lparr> carrier := K \<rparr>) K' xs = finite_extension K' xs"
      using ring.finite_extension.simps[OF subring_is_ring[OF assms]]
            simple_extension_consistent[OF assms] by (induct xs) (auto)
  qed
  thus ?thesis by blast
qed

lemma (in ring) mono_finite_extension:
  assumes "K \<subseteq> K'" shows "finite_extension K xs \<subseteq> finite_extension K' xs"
  using mono_simple_extension assms by (induct xs) (auto)

lemma (in ring) finite_extension_carrier:
  assumes "set xs \<subseteq> carrier R" shows "finite_extension (carrier R) xs = carrier R"
  using assms simple_extension_carrier by (induct xs) (auto)

lemma (in ring) finite_extension_in_carrier:
  assumes "K \<subseteq> carrier R" and "set xs \<subseteq> carrier R" shows "finite_extension K xs \<subseteq> carrier R"
  using assms simple_extension_in_carrier by (induct xs) (auto)

lemma (in ring) finite_extension_subring_incl:
  assumes "subring K' R" and "K \<subseteq> K'" "set xs \<subseteq> K'" shows "finite_extension K xs \<subseteq> K'"
  using ring.finite_extension_in_carrier[OF subring_is_ring[OF assms(1)]] assms(2-3)
  unfolding finite_extension_consistent[OF assms(1)] by simp

lemma (in ring) finite_extension_incl_aux:
  assumes "K \<subseteq> carrier R" and "x \<in> carrier R" "set xs \<subseteq> carrier R"
  shows "finite_extension K xs \<subseteq> finite_extension K (x # xs)"
  using simple_extension_incl[OF finite_extension_in_carrier[OF assms(1,3)] assms(2)] by simp

lemma (in ring) finite_extension_incl:
  assumes "K \<subseteq> carrier R" and "set xs \<subseteq> carrier R" shows "K \<subseteq> finite_extension K xs"
  using finite_extension_incl_aux[OF assms(1)] assms(2) by (induct xs) (auto)

lemma (in ring) finite_extension_as_eval_img:
  assumes "K \<subseteq> carrier R" and "x \<in> carrier R" "set xs \<subseteq> carrier R"
  shows "finite_extension K (x # xs) = (\<lambda>p. eval p x) ` carrier ((finite_extension K xs) [X])"
  using simple_extension_as_eval_img[OF finite_extension_in_carrier[OF assms(1,3)] assms(2)] by simp

lemma (in domain) finite_extension_is_subring:
  assumes "subring K R" "set xs \<subseteq> carrier R" shows "subring (finite_extension K xs) R"
  using assms simple_extension_is_subring by (induct xs) (auto)

corollary (in domain) finite_extension_mem:
  assumes subring: "subring K R"
  shows "set xs \<subseteq> carrier R \<Longrightarrow> set xs \<subseteq> finite_extension K xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons(2) have a: "a \<in> carrier R" and xs: "set xs \<subseteq> carrier R" by auto
  show ?case
  proof
    fix x assume "x \<in> set (a # xs)"
    then consider "x = a" | "x \<in> set xs" by auto
    then show "x \<in> finite_extension K (a # xs)"
    proof cases
      case 1
      with a have "x \<in> carrier R" by simp
      with xs have "x \<in> finite_extension K (x # xs)"
        using simple_extension_mem[OF finite_extension_is_subring[OF subring]] by simp
      with 1 show ?thesis by simp
    next
      case 2
      with Cons have *: "x \<in> finite_extension K xs" by auto
      from a xs have "finite_extension K xs \<subseteq> finite_extension K (a # xs)"
        by (rule finite_extension_incl_aux[OF subringE(1)[OF subring]])
      with * show ?thesis by auto
    qed
  qed
qed

corollary (in domain) finite_extension_minimal:
  assumes "subring K R" "set xs \<subseteq> carrier R"
  shows "finite_extension K xs = \<Inter> { K'. subring K' R \<and> K \<subseteq> K' \<and> set xs \<subseteq> K' }"
  using finite_extension_is_subring[OF assms] finite_extension_mem[OF assms]
        finite_extension_incl[OF subringE(1)[OF assms(1)] assms(2)] finite_extension_subring_incl
  by blast

corollary (in domain) finite_extension_same_set:
  assumes "subring K R" "set xs \<subseteq> carrier R" "set xs = set ys"
  shows "finite_extension K xs = finite_extension K ys"
  using finite_extension_minimal[OF assms(1)] assms(2-3) by auto

text \<open>The reciprocal is also true, but it is more subtle.\<close>
proposition (in domain) finite_extension_is_subfield:
  assumes "subfield K R" "set xs \<subseteq> carrier R"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x) \<Longrightarrow> subfield (finite_extension K xs) R"
  using simple_extension_is_subfield algebraic_mono assms
  by (induct xs) (auto, metis finite_extension.simps finite_extension_incl subring_props(1))

proposition (in domain) finite_extension_finite_dimension:
  assumes "subfield K R" "set xs \<subseteq> carrier R"
  shows "(\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x) \<Longrightarrow> finite_dimension K (finite_extension K xs)"
    and "finite_dimension K (finite_extension K xs) \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x)"
proof -
  show "finite_dimension K (finite_extension K xs) \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x)"
    using finite_dimension_imp_algebraic[OF assms(1)
          finite_extension_is_subring[OF subfieldE(1)[OF assms(1)] assms(2)]]
          finite_extension_mem[OF subfieldE(1)[OF assms(1)] assms(2)] by auto
next
  show "(\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x) \<Longrightarrow> finite_dimension K (finite_extension K xs)"
    using assms(2)
  proof (induct xs, simp add: finite_dimensionI[OF dimension_one[OF assms(1)]])
    case (Cons x xs)
    hence "finite_dimension K (finite_extension K xs)"
      by auto
    moreover have "(algebraic over (finite_extension K xs)) x"
      using algebraic_mono[OF finite_extension_incl[OF subfieldE(3)[OF assms(1)]]] Cons(2-3) by auto
    moreover have "subfield (finite_extension K xs) R"
      using finite_extension_is_subfield[OF assms(1)] Cons(2-3) by auto
    ultimately show ?case
      using telescopic_base_dim(1)[OF assms(1) _ _ 
            finite_dimensionI[OF dimension_simple_extension, of _ x]] Cons(3) by auto
  qed
qed

corollary (in domain) finite_extesion_mem_imp_algebraic:
  assumes "subfield K R" "set xs \<subseteq> carrier R" and "\<And>x. x \<in> set xs \<Longrightarrow> (algebraic over K) x"
  shows "y \<in> finite_extension K xs \<Longrightarrow> (algebraic over K) y"
  using finite_dimension_imp_algebraic[OF assms(1)
        finite_extension_is_subring[OF subfieldE(1)[OF assms(1)] assms(2)]]
        finite_extension_finite_dimension(1)[OF assms(1-2)] assms(3) by auto

corollary (in domain) simple_extesion_mem_imp_algebraic:
  assumes "subfield K R" "x \<in> carrier R" "(algebraic over K) x"
  shows "y \<in> simple_extension K x \<Longrightarrow> (algebraic over K) y"
  using finite_extesion_mem_imp_algebraic[OF assms(1), of "[ x ]"] assms(2-3) by auto


subsection \<open>Arithmetic of algebraic numbers\<close>

text \<open>We show that the set of algebraic numbers of a field
      over a subfield K is a subfield itself.\<close>

lemma (in field) subfield_of_algebraics:
  assumes "subfield K R" shows "subfield { x \<in> carrier R. (algebraic over K) x } R"
proof -
  let ?set_of_algebraics = "{ x \<in> carrier R. (algebraic over K) x }"

  show ?thesis
  proof (rule subfieldI'[OF subringI])
    show "?set_of_algebraics \<subseteq> carrier R" and "\<one> \<in> ?set_of_algebraics"
      using algebraic_self[OF _ subringE(3)] subfieldE(1)[OF assms(1)] by auto
  next
    fix x y assume x: "x \<in> ?set_of_algebraics" and y: "y \<in> ?set_of_algebraics"
    have "\<ominus> x \<in> simple_extension K x"
      using subringE(5)[OF simple_extension_is_subring[OF subfieldE(1)]]
            simple_extension_mem[OF subfieldE(1)] assms(1) x by auto
    thus "\<ominus> x \<in> ?set_of_algebraics"
      using simple_extesion_mem_imp_algebraic[OF assms] x by auto

    have "x \<oplus> y \<in> finite_extension K [ x, y ]" and "x \<otimes> y \<in> finite_extension K [ x, y ]"
      using subringE(6-7)[OF finite_extension_is_subring[OF subfieldE(1)[OF assms(1)]], of "[ x, y ]"]
            finite_extension_mem[OF subfieldE(1)[OF assms(1)], of "[ x, y ]"] x y by auto
    thus "x \<oplus> y \<in> ?set_of_algebraics" and "x \<otimes> y \<in> ?set_of_algebraics"
      using finite_extesion_mem_imp_algebraic[OF assms, of "[ x, y ]"] x y by auto
  next
    fix z assume z: "z \<in> ?set_of_algebraics - { \<zero> }"
    have "inv z \<in> simple_extension K z"
      using subfield_m_inv(1)[of "simple_extension K z"]
            simple_extension_is_subfield[OF assms, of z]
            simple_extension_mem[OF subfieldE(1)] assms(1) z by auto
    thus "inv z \<in> ?set_of_algebraics"
      using simple_extesion_mem_imp_algebraic[OF assms] field_Units z by auto
  qed
qed

end