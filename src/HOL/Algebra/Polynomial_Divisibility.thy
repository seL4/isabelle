(*  Title:      HOL/Algebra/Polynomial_Divisibility.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Polynomial_Divisibility
  imports Polynomials Embedded_Algebras "HOL-Library.Multiset"
    
begin

section \<open>Divisibility of Polynomials\<close>

subsection \<open>Definitions\<close>

abbreviation poly_ring :: "_ \<Rightarrow> ('a  list) ring"
  where "poly_ring R \<equiv> univ_poly R (carrier R)"

abbreviation pirreducible :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("pirreducible\<index>")
  where "pirreducible\<^bsub>R\<^esub> K p \<equiv> ring_irreducible\<^bsub>(univ_poly R K)\<^esub> p"

abbreviation pprime :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" ("pprime\<index>")
  where "pprime\<^bsub>R\<^esub> K p \<equiv> ring_prime\<^bsub>(univ_poly R K)\<^esub> p"

definition pdivides :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "pdivides\<index>" 65)
  where "p pdivides\<^bsub>R\<^esub> q = p divides\<^bsub>(univ_poly R (carrier R))\<^esub> q"

definition rupture :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> (('a list) set) ring" ("Rupt\<index>")
  where "Rupt\<^bsub>R\<^esub> K p = (K[X]\<^bsub>R\<^esub>) Quot (PIdl\<^bsub>K[X]\<^bsub>R\<^esub>\<^esub> p)"

abbreviation (in ring) rupture_surj :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a list) set"
  where "rupture_surj K p \<equiv> (\<lambda>q. (PIdl\<^bsub>K[X]\<^esub> p) +>\<^bsub>K[X]\<^esub> q)"


subsection \<open>Basic Properties\<close>

lemma (in ring) carrier_polynomial_shell [intro]:
  assumes "subring K R" and "p \<in> carrier (K[X])" shows "p \<in> carrier (poly_ring R)"
  using carrier_polynomial[OF assms(1), of p] assms(2) unfolding sym[OF univ_poly_carrier] by simp

lemma (in domain) pdivides_zero:
  assumes "subring K R" and "p \<in> carrier (K[X])" shows "p pdivides []"
  using ring.divides_zero[OF univ_poly_is_ring[OF carrier_is_subring]
         carrier_polynomial_shell[OF assms]]
  unfolding univ_poly_zero pdivides_def .

lemma (in domain) zero_pdivides_zero: "[] pdivides []"
  using pdivides_zero[OF carrier_is_subring] univ_poly_carrier by blast

lemma (in domain) zero_pdivides:
  shows "[] pdivides p \<longleftrightarrow> p = []"
  using ring.zero_divides[OF univ_poly_is_ring[OF carrier_is_subring]]
  unfolding univ_poly_zero pdivides_def .

lemma (in domain) pprime_iff_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])"
  shows "pprime K p \<longleftrightarrow> pirreducible K p"
  using principal_domain.primeness_condition[OF univ_poly_is_principal] assms by simp

lemma (in domain) pirreducibleE:
  assumes "subring K R" "p \<in> carrier (K[X])" "pirreducible K p"
  shows "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p = q \<otimes>\<^bsub>K[X]\<^esub> r \<Longrightarrow> q \<in> Units (K[X]) \<or> r \<in> Units (K[X])"
  using domain.ring_irreducibleE[OF univ_poly_is_domain[OF assms(1)] _ assms(3)] assms(2)
  by (auto simp add: univ_poly_zero)

lemma (in domain) pirreducibleI:
  assumes "subring K R" "p \<in> carrier (K[X])" "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p = q \<otimes>\<^bsub>K[X]\<^esub> r \<Longrightarrow> q \<in> Units (K[X]) \<or> r \<in> Units (K[X])"
  shows "pirreducible K p"
  using domain.ring_irreducibleI[OF univ_poly_is_domain[OF assms(1)] _ assms(4)] assms(2-3,5)
  by (auto simp add: univ_poly_zero)

lemma (in domain) univ_poly_carrier_units_incl:
  shows "Units ((carrier R) [X]) \<subseteq> { [ k ] | k. k \<in> carrier R - { \<zero> } }"
proof
  fix p assume "p \<in> Units ((carrier R) [X])"
  then obtain q
    where p: "polynomial (carrier R) p" and q: "polynomial (carrier R) q" and pq: "poly_mult p q = [ \<one> ]"
    unfolding Units_def univ_poly_def by auto
  hence not_nil: "p \<noteq> []" and "q \<noteq> []"
    using poly_mult_integral[OF carrier_is_subring p q] poly_mult_zero[OF polynomial_incl[OF p]] by auto
  hence "degree p = 0"
    using poly_mult_degree_eq[OF carrier_is_subring p q] unfolding pq by simp
  hence "length p = 1"
    using not_nil by (metis One_nat_def Suc_pred length_greater_0_conv)
  then obtain k where k: "p = [ k ]"
    by (metis One_nat_def length_0_conv length_Suc_conv)
  hence "k \<in> carrier R - { \<zero> }"
    using p unfolding polynomial_def by auto 
  thus "p \<in> { [ k ] | k. k \<in> carrier R - { \<zero> } }"
    unfolding k by blast
qed

lemma (in field) univ_poly_carrier_units:
  "Units ((carrier R) [X]) = { [ k ] | k. k \<in> carrier R - { \<zero> } }"
proof
  show "Units ((carrier R) [X]) \<subseteq> { [ k ] | k. k \<in> carrier R - { \<zero> } }"
    using univ_poly_carrier_units_incl by simp
next
  show "{ [ k ] | k. k \<in> carrier R - { \<zero> } } \<subseteq> Units ((carrier R) [X])"
  proof (auto)
    fix k assume k: "k \<in> carrier R" "k \<noteq> \<zero>"
    hence inv_k: "inv k \<in> carrier R" "inv k \<noteq> \<zero>" and "k \<otimes> inv k = \<one>" "inv k \<otimes> k = \<one>"
      using subfield_m_inv[OF carrier_is_subfield, of k] by auto
    hence "poly_mult [ k ] [ inv k ] = [ \<one> ]" and "poly_mult [ inv k ] [ k ] = [ \<one> ]"
      by (auto simp add: k)
    moreover have "polynomial (carrier R) [ k ]" and "polynomial (carrier R) [ inv k ]"
      using const_is_polynomial k inv_k by auto
    ultimately show "[ k ] \<in> Units ((carrier R) [X])"
      unfolding Units_def univ_poly_def by (auto simp del: poly_mult.simps)
  qed
qed

lemma (in domain) univ_poly_units_incl:
  assumes "subring K R" shows "Units (K[X]) \<subseteq> { [ k ] | k. k \<in> K - { \<zero> } }"
  using domain.univ_poly_carrier_units_incl[OF subring_is_domain[OF assms]]
        univ_poly_consistent[OF assms] by auto

lemma (in ring) univ_poly_units:
  assumes "subfield K R" shows "Units (K[X]) = { [ k ] | k. k \<in> K - { \<zero> } }"
  using field.univ_poly_carrier_units[OF subfield_iff(2)[OF assms]]
        univ_poly_consistent[OF subfieldE(1)[OF assms]] by auto

lemma (in domain) univ_poly_units':
  assumes "subfield K R" shows "p \<in> Units (K[X]) \<longleftrightarrow> p \<in> carrier (K[X]) \<and> p \<noteq> [] \<and> degree p = 0"
  unfolding univ_poly_units[OF assms] sym[OF univ_poly_carrier] polynomial_def
  by (auto, metis hd_in_set le_0_eq le_Suc_eq length_0_conv length_Suc_conv list.sel(1) subsetD)

corollary (in domain) rupture_one_not_zero:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p > 0"
  shows "\<one>\<^bsub>Rupt K p\<^esub> \<noteq> \<zero>\<^bsub>Rupt K p\<^esub>"
proof (rule ccontr)
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] . 

  assume "\<not> \<one>\<^bsub>Rupt K p\<^esub> \<noteq> \<zero>\<^bsub>Rupt K p\<^esub>"
  then have "PIdl\<^bsub>K[X]\<^esub> p +>\<^bsub>K[X]\<^esub> \<one>\<^bsub>K[X]\<^esub> = PIdl\<^bsub>K[X]\<^esub> p"
    unfolding rupture_def FactRing_def by simp
  hence "\<one>\<^bsub>K[X]\<^esub> \<in> PIdl\<^bsub>K[X]\<^esub> p"
    using ideal.rcos_const_imp_mem[OF UP.cgenideal_ideal[OF assms(2)]] by auto
  then obtain q where "q \<in> carrier (K[X])" and "\<one>\<^bsub>K[X]\<^esub> = q \<otimes>\<^bsub>K[X]\<^esub> p"
    using assms(2) unfolding cgenideal_def by auto
  hence "p \<in> Units (K[X])"
    unfolding Units_def using assms(2) UP.m_comm by auto
  hence "degree p = 0"
    unfolding univ_poly_units[OF assms(1)] by auto
  with \<open>degree p > 0\<close> show False
    by simp
qed

corollary (in ring) pirreducible_degree:
  assumes "subfield K R" "p \<in> carrier (K[X])" "pirreducible K p"
  shows "degree p \<ge> 1"
proof (rule ccontr)
  assume "\<not> degree p \<ge> 1" then have "length p \<le> 1"
    by simp
  moreover have "p \<noteq> []" and "p \<notin> Units (K[X])"
    using assms(3) by (auto simp add: ring_irreducible_def irreducible_def univ_poly_zero)
  ultimately obtain k where k: "p = [ k ]"
    by (metis append_butlast_last_id butlast_take diff_is_0_eq le_refl self_append_conv2 take0 take_all)
  hence "k \<in> K" and "k \<noteq> \<zero>"
    using assms(2) by (auto simp add: polynomial_def univ_poly_def)
  hence "p \<in> Units (K[X])"
    using univ_poly_units[OF assms(1)] unfolding k by auto
  from \<open>p \<in> Units (K[X])\<close> and \<open>p \<notin> Units (K[X])\<close> show False by simp
qed

corollary (in domain) univ_poly_not_field:
  assumes "subring K R" shows "\<not> field (K[X])"
proof -
  have "X \<in> carrier (K[X]) - { \<zero>\<^bsub>(K[X])\<^esub> }" and "X \<notin> { [ k ] | k. k \<in> K - { \<zero> } }"
    using var_closed(1)[OF assms] unfolding univ_poly_zero var_def by auto 
  thus ?thesis
    using field.field_Units[of "K[X]"] univ_poly_units_incl[OF assms] by blast 
qed

lemma (in domain) rupture_is_field_iff_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])"
  shows "field (Rupt K p) \<longleftrightarrow> pirreducible K p"
proof
  assume "pirreducible K p" thus "field (Rupt K p)"
    using principal_domain.field_iff_prime[OF univ_poly_is_principal[OF assms(1)]] assms(2)
          pprime_iff_pirreducible[OF assms] pirreducibleE(1)[OF subfieldE(1)[OF assms(1)]]
    by (simp add: univ_poly_zero rupture_def)
next
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  assume field: "field (Rupt K p)"
  have "p \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p \<noteq> []" then have p: "p = []"
      by simp
    hence "Rupt K p \<simeq> (K[X])"
      using UP.FactRing_zeroideal(1) UP.genideal_zero
            UP.cgenideal_eq_genideal[OF UP.zero_closed]
      by (simp add: rupture_def univ_poly_zero)
    then obtain h where h: "h \<in> ring_iso (Rupt K p) (K[X])"
      unfolding is_ring_iso_def by blast
    moreover have "ring (Rupt K p)"
      using field by (simp add: cring_def domain_def field_def) 
    ultimately interpret R: ring_hom_ring "Rupt K p" "K[X]" h
      unfolding ring_hom_ring_def ring_hom_ring_axioms_def ring_iso_def
      using UP.ring_axioms by simp
    have "field (K[X])"
      using field.ring_iso_imp_img_field[OF field h] by simp
    thus False
      using univ_poly_not_field[OF subfieldE(1)[OF assms(1)]] by simp
  qed
  thus "pirreducible K p"
    using UP.field_iff_prime pprime_iff_pirreducible[OF assms] assms(2) field
    by (simp add: univ_poly_zero rupture_def)
qed

lemma (in domain) rupture_surj_hom:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "(rupture_surj K p) \<in> ring_hom (K[X]) (Rupt K p)"
    and "ring_hom_ring (K[X]) (Rupt K p) (rupture_surj K p)"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .
  interpret I: ideal "PIdl\<^bsub>K[X]\<^esub> p" "K[X]"
    using UP.cgenideal_ideal[OF assms(2)] .
  show "(rupture_surj K p) \<in> ring_hom (K[X]) (Rupt K p)"
   and "ring_hom_ring (K[X]) (Rupt K p) (rupture_surj K p)"
    using ring_hom_ring.intro[OF UP.ring_axioms I.quotient_is_ring] I.rcos_ring_hom
    unfolding symmetric[OF ring_hom_ring_axioms_def] rupture_def by auto
qed

corollary (in domain) rupture_surj_norm_is_hom:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "((rupture_surj K p) \<circ> poly_of_const) \<in> ring_hom (R \<lparr> carrier := K \<rparr>) (Rupt K p)"
  using ring_hom_trans[OF canonical_embedding_is_hom[OF assms(1)] rupture_surj_hom(1)[OF assms]] .

lemma (in domain) norm_map_in_poly_ring_carrier:
  assumes "p \<in> carrier (poly_ring R)" and "\<And>a. a \<in> carrier R \<Longrightarrow> f a \<in> carrier (poly_ring R)"
  shows "ring.normalize (poly_ring R) (map f p) \<in> carrier (poly_ring (poly_ring R))"
proof -
  have "set p \<subseteq> carrier R"
    using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence "set (map f p) \<subseteq> carrier (poly_ring R)"
    using assms(2) by auto
  thus ?thesis
    using ring.normalize_gives_polynomial[OF univ_poly_is_ring[OF carrier_is_subring]]
    unfolding univ_poly_carrier by simp
qed

lemma (in domain) map_in_poly_ring_carrier:
  assumes "p \<in> carrier (poly_ring R)" and "\<And>a. a \<in> carrier R \<Longrightarrow> f a \<in> carrier (poly_ring R)"
    and "\<And>a. a \<noteq> \<zero> \<Longrightarrow> f a \<noteq> []"
  shows "map f p \<in> carrier (poly_ring (poly_ring R))"
proof -
  interpret UP: ring "poly_ring R"
    using univ_poly_is_ring[OF carrier_is_subring] .
  have "lead_coeff p \<noteq> \<zero>" if "p \<noteq> []"
    using that assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence "ring.normalize (poly_ring R) (map f p) = map f p"
    by (cases p) (simp_all add: assms(3) univ_poly_zero)
  thus ?thesis
    using norm_map_in_poly_ring_carrier[of p f] assms(1-2) by simp
qed

lemma (in domain) map_norm_in_poly_ring_carrier:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "map poly_of_const p \<in> carrier (poly_ring (K[X]))"
  using domain.map_in_poly_ring_carrier[OF subring_is_domain[OF assms(1)]]
proof -
  have "\<And>a. a \<in> K \<Longrightarrow> poly_of_const a \<in> carrier (K[X])"
   and "\<And>a. a \<noteq> \<zero> \<Longrightarrow> poly_of_const a \<noteq> []"
    using ring_hom_memE(1)[OF canonical_embedding_is_hom[OF assms(1)]]
    by (auto simp: poly_of_const_def)
  thus ?thesis
    using domain.map_in_poly_ring_carrier[OF subring_is_domain[OF assms(1)]] assms(2)
    unfolding univ_poly_consistent[OF assms(1)] by simp
qed

lemma (in domain) polynomial_rupture:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "(ring.eval (Rupt K p)) (map ((rupture_surj K p) \<circ> poly_of_const) p) (rupture_surj K p X) = \<zero>\<^bsub>Rupt K p\<^esub>"
proof -
  let ?surj = "rupture_surj K p"

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .
  interpret Hom: ring_hom_ring "K[X]" "Rupt K p" ?surj
    using rupture_surj_hom(2)[OF assms] .

  have "(Hom.S.eval) (map (?surj \<circ> poly_of_const) p) (?surj X) = ?surj ((UP.eval) (map poly_of_const p) X)"
    using Hom.eval_hom[OF UP.carrier_is_subring var_closed(1)[OF assms(1)]
          map_norm_in_poly_ring_carrier[OF assms]] by simp
  also have " ... = ?surj p"
    unfolding sym[OF eval_rewrite[OF assms]] ..
  also have " ... = \<zero>\<^bsub>Rupt K p\<^esub>"
    using UP.a_rcos_zero[OF UP.cgenideal_ideal[OF assms(2)] UP.cgenideal_self[OF assms(2)]]
    unfolding rupture_def FactRing_def by simp
  finally show ?thesis .
qed


subsection \<open>Division\<close>

definition (in ring) long_divides :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> bool"
  where "long_divides p q t \<longleftrightarrow>
           \<comment> \<open>i\<close>   (t \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)) \<and>
           \<comment> \<open>ii\<close>  (p = (q \<otimes>\<^bsub>poly_ring R\<^esub> (fst t)) \<oplus>\<^bsub>poly_ring R\<^esub> (snd t)) \<and>
           \<comment> \<open>iii\<close> (snd t = [] \<or> degree (snd t) < degree q)"

definition (in ring) long_division :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)"
  where "long_division p q = (THE t. long_divides p q t)"

definition (in ring) pdiv :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "pdiv" 65)
  where "p pdiv q = (if q = [] then [] else fst (long_division p q))"

definition (in ring) pmod :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "pmod" 65)
  where "p pmod q = (if q = [] then p else snd (long_division p q))"


lemma (in ring) long_dividesI:
  assumes "b \<in> carrier (poly_ring R)" and "r \<in> carrier (poly_ring R)"
      and "p = (q \<otimes>\<^bsub>poly_ring R\<^esub> b) \<oplus>\<^bsub>poly_ring R\<^esub> r" and "r = [] \<or> degree r < degree q"
    shows "long_divides p q (b, r)"
  using assms unfolding long_divides_def by auto 

lemma (in domain) exists_long_division:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  obtains b r where "b \<in> carrier (K[X])" and "r \<in> carrier (K[X])" and "long_divides p q (b, r)"
  using subfield_long_division_theorem_shell[OF assms(1-3)] assms(4)
        carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]]
  unfolding long_divides_def univ_poly_zero univ_poly_add univ_poly_mult by auto

lemma (in domain) exists_unique_long_division:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "\<exists>!t. long_divides p q t"
proof -
  let ?padd   = "\<lambda>a b. a \<oplus>\<^bsub>poly_ring R\<^esub> b"
  let ?pmult  = "\<lambda>a b. a \<otimes>\<^bsub>poly_ring R\<^esub> b"
  let ?pminus = "\<lambda>a b. a \<ominus>\<^bsub>poly_ring R\<^esub> b"

  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  obtain b r where ldiv: "long_divides p q (b, r)"
    using exists_long_division[OF assms] by metis

  moreover have "(b, r) = (b', r')" if "long_divides p q (b', r')" for b' r'
  proof -
    have q: "q \<in> carrier (poly_ring R)" "q \<noteq> []"
      using assms(3-4) carrier_polynomial[OF subfieldE(1)[OF assms(1)]]
      unfolding univ_poly_carrier by auto 
    hence in_carrier: "q \<in> carrier (poly_ring R)"
      "b  \<in> carrier (poly_ring R)" "r  \<in> carrier (poly_ring R)"
      "b' \<in> carrier (poly_ring R)" "r' \<in> carrier (poly_ring R)" 
      using assms(3) that ldiv unfolding long_divides_def by auto
    have "?pminus (?padd (?pmult q b) r) r' = ?pminus (?padd (?pmult q b') r') r'"
      using ldiv and that unfolding long_divides_def by auto
    hence eq: "?padd (?pmult q (?pminus b b')) (?pminus r r') = \<zero>\<^bsub>poly_ring R\<^esub>"
      using in_carrier by algebra
    have "b = b'"
    proof (rule ccontr)
      assume "b \<noteq> b'"
      hence pminus: "?pminus b b' \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>" "?pminus b b' \<in> carrier (poly_ring R)"
        using in_carrier(2,4) by (metis UP.add.inv_closed UP.l_neg UP.minus_eq UP.minus_unique, algebra)
      hence degree_ge: "degree (?pmult q (?pminus b b')) \<ge> degree q"
        using poly_mult_degree_eq[OF carrier_is_subring, of q "?pminus b b'"] q
        unfolding univ_poly_zero univ_poly_carrier univ_poly_mult by simp

      have "?pminus b b' = \<zero>\<^bsub>poly_ring R\<^esub>" if "?pminus r r' = \<zero>\<^bsub>poly_ring R\<^esub>"
        using eq pminus(2) q UP.integral univ_poly_zero unfolding that by auto 
      hence "?pminus r r' \<noteq> []"
        using pminus(1) unfolding univ_poly_zero by blast
      moreover have "?pminus r r' = []" if "r = []" and "r' = []"
        using univ_poly_a_inv_def'[OF carrier_is_subring UP.zero_closed] that
        unfolding a_minus_def univ_poly_add univ_poly_zero by auto
      ultimately have "r \<noteq> [] \<or> r' \<noteq> []"
        by blast
      hence "max (degree r) (degree r') < degree q"
        using ldiv and that unfolding long_divides_def by auto
      moreover have "degree (?pminus r r') \<le> max (degree r) (degree r')"
        using poly_add_degree[of r "map (a_inv R) r'"]
        unfolding a_minus_def univ_poly_add univ_poly_a_inv_def'[OF carrier_is_subring in_carrier(5)]
        by auto
      ultimately have degree_lt: "degree (?pminus r r') < degree q"
        by linarith
      have is_poly: "polynomial (carrier R) (?pmult q (?pminus b b'))" "polynomial (carrier R) (?pminus r r')"
        using in_carrier pminus(2) unfolding univ_poly_carrier by algebra+
      
      have "degree (?padd (?pmult q (?pminus b b')) (?pminus r r')) = degree (?pmult q (?pminus b b'))"
        using poly_add_degree_eq[OF carrier_is_subring is_poly] degree_ge degree_lt
        unfolding univ_poly_carrier sym[OF univ_poly_add[of R "carrier R"]] max_def by simp
      hence "degree (?padd (?pmult q (?pminus b b')) (?pminus r r')) > 0"
        using degree_ge degree_lt by simp
      moreover have "degree (?padd (?pmult q (?pminus b b')) (?pminus r r')) = 0"
        using eq unfolding univ_poly_zero by simp
      ultimately show False by simp
    qed
    hence "?pminus r r' = \<zero>\<^bsub>poly_ring R\<^esub>"
      using in_carrier eq by algebra
    hence "r = r'"
      using in_carrier by (metis UP.add.inv_closed UP.add.right_cancel UP.minus_eq UP.r_neg)
    with \<open>b = b'\<close> show ?thesis
      by simp
  qed

  ultimately show ?thesis
    by auto
qed

lemma (in domain) long_divisionE:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "long_divides p q (p pdiv q, p pmod q)"
  using theI'[OF exists_unique_long_division[OF assms]] assms(4)
  unfolding pmod_def pdiv_def long_division_def by auto

lemma (in domain) long_divisionI:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "long_divides p q (b, r) \<Longrightarrow> (b, r) = (p pdiv q, p pmod q)"
  using exists_unique_long_division[OF assms] long_divisionE[OF assms] by metis

lemma (in domain) long_division_closed:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pdiv q \<in> carrier (K[X])" and "p pmod q \<in> carrier (K[X])"
proof -
  have "p pdiv q \<in> carrier (K[X]) \<and> p pmod q \<in> carrier (K[X])"
    using assms univ_poly_zero_closed[of R] long_divisionI[of K] exists_long_division[OF assms]
    by (cases "q = []") (simp add: pdiv_def pmod_def, metis Pair_inject)+
  thus "p pdiv q \<in> carrier (K[X])" and "p pmod q \<in> carrier (K[X])"
    by auto
qed

lemma (in domain) pdiv_pmod:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p = (q \<otimes>\<^bsub>K[X]\<^esub> (p pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (p pmod q)"
proof (cases)
  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .
  assume "q = []" thus ?thesis
    using assms(2) unfolding pdiv_def pmod_def sym[OF univ_poly_zero[of R K]] by simp
next
  assume "q \<noteq> []" thus ?thesis
    using long_divisionE[OF assms] unfolding long_divides_def univ_poly_mult univ_poly_add by simp
qed

lemma (in domain) pmod_degree:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "p pmod q = [] \<or> degree (p pmod q) < degree q"
  using long_divisionE[OF assms] unfolding long_divides_def by auto

lemma (in domain) pmod_const:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])" and "degree q > degree p" 
  shows "p pdiv q = []" and "p pmod q = p"
proof -
  have "p pdiv q = [] \<and> p pmod q = p"
  proof (cases)
    interpret UP: ring "K[X]"
      using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .

    assume "q \<noteq> []"
    have "p = (q \<otimes>\<^bsub>K[X]\<^esub> []) \<oplus>\<^bsub>K[X]\<^esub> p"
      using assms(2-3) unfolding sym[OF univ_poly_zero[of R K]] by simp
    moreover have "([], p) \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)"
      using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)] assms(2)] by auto
    ultimately have "long_divides p q ([], p)"
      using assms(4) unfolding long_divides_def univ_poly_mult univ_poly_add by auto
    with \<open>q \<noteq> []\<close> show ?thesis
      using long_divisionI[OF assms(1-3)] by auto
  qed (simp add: pmod_def pdiv_def)
  thus "p pdiv q = []" and "p pmod q = p"
    by auto
qed

lemma (in domain) long_division_zero:
  assumes "subfield K R" and "q \<in> carrier (K[X])" shows "[] pdiv q = []" and "[] pmod q = []"
proof -
  interpret UP: ring "poly_ring R"
    using univ_poly_is_ring[OF carrier_is_subring] .

  have "[] pdiv q = [] \<and> [] pmod q = []"
  proof (cases)
    assume "q \<noteq> []"
    have "q \<in> carrier (poly_ring R)"
      using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)] assms(2)] .
    hence "long_divides [] q ([], [])"
      unfolding long_divides_def sym[OF univ_poly_zero[of R "carrier R"]] by auto
    with \<open>q \<noteq> []\<close> show ?thesis
      using long_divisionI[OF assms(1) univ_poly_zero_closed assms(2)] by simp
  qed (simp add: pmod_def pdiv_def)
  thus "[] pdiv q = []" and "[] pmod q = []"
    by auto
qed

lemma (in domain) long_division_a_inv:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "((\<ominus>\<^bsub>K[X]\<^esub> p) pdiv q) = \<ominus>\<^bsub>K[X]\<^esub> (p pdiv q)" (is "?pdiv")
    and "((\<ominus>\<^bsub>K[X]\<^esub> p) pmod q) = \<ominus>\<^bsub>K[X]\<^esub> (p pmod q)" (is "?pmod")
proof -
  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .

  have "?pdiv \<and> ?pmod"
  proof (cases)
    assume "q = []" thus ?thesis
      unfolding pmod_def pdiv_def sym[OF univ_poly_zero[of R K]] by simp
  next
    assume not_nil: "q \<noteq> []"
    have "\<ominus>\<^bsub>K[X]\<^esub> p = \<ominus>\<^bsub>K[X]\<^esub> ((q \<otimes>\<^bsub>K[X]\<^esub> (p pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (p pmod q))"
      using pdiv_pmod[OF assms] by simp
    hence "\<ominus>\<^bsub>K[X]\<^esub> p = (q \<otimes>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q))) \<oplus>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> (p pmod q))"
      using assms(2-3) long_division_closed[OF assms] by algebra
    moreover have "\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q) \<in> carrier (K[X])" "\<ominus>\<^bsub>K[X]\<^esub> (p pmod q) \<in> carrier (K[X])"
      using long_division_closed[OF assms] by algebra+
    hence "(\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q), \<ominus>\<^bsub>K[X]\<^esub> (p pmod q)) \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)"
      using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
    moreover have "\<ominus>\<^bsub>K[X]\<^esub> (p pmod q) = [] \<or> degree (\<ominus>\<^bsub>K[X]\<^esub> (p pmod q)) < degree q"
      using univ_poly_a_inv_length[OF subfieldE(1)[OF assms(1)]
            long_division_closed(2)[OF assms]] pmod_degree[OF assms not_nil]
      by auto
    ultimately have "long_divides (\<ominus>\<^bsub>K[X]\<^esub> p) q (\<ominus>\<^bsub>K[X]\<^esub> (p pdiv q), \<ominus>\<^bsub>K[X]\<^esub> (p pmod q))"
      unfolding long_divides_def univ_poly_mult univ_poly_add by simp
    thus ?thesis
      using long_divisionI[OF assms(1) UP.a_inv_closed[OF assms(2)] assms(3) not_nil] by simp
  qed
  thus ?pdiv and ?pmod
    by auto
qed

lemma (in domain) long_division_add:
  assumes "subfield K R" and "a \<in> carrier (K[X])" "b \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "(a \<oplus>\<^bsub>K[X]\<^esub> b) pdiv q = (a pdiv q) \<oplus>\<^bsub>K[X]\<^esub> (b pdiv q)" (is "?pdiv")
    and "(a \<oplus>\<^bsub>K[X]\<^esub> b) pmod q = (a pmod q) \<oplus>\<^bsub>K[X]\<^esub> (b pmod q)" (is "?pmod")
proof -
  let ?pdiv_add = "(a pdiv q) \<oplus>\<^bsub>K[X]\<^esub> (b pdiv q)"
  let ?pmod_add = "(a pmod q) \<oplus>\<^bsub>K[X]\<^esub> (b pmod q)"

  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .

  have "?pdiv \<and> ?pmod"
  proof (cases)
    assume "q = []" thus ?thesis
      using assms(2-3) unfolding pmod_def pdiv_def sym[OF univ_poly_zero[of R K]] by simp
  next
    note in_carrier = long_division_closed[OF assms(1,2,4)]
                      long_division_closed[OF assms(1,3,4)]

    assume "q \<noteq> []"
    have "a \<oplus>\<^bsub>K[X]\<^esub> b = ((q \<otimes>\<^bsub>K[X]\<^esub> (a pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (a pmod q)) \<oplus>\<^bsub>K[X]\<^esub>
                         ((q \<otimes>\<^bsub>K[X]\<^esub> (b pdiv q)) \<oplus>\<^bsub>K[X]\<^esub> (b pmod q))"
      using assms(2-3)[THEN pdiv_pmod[OF assms(1) _ assms(4)]] by simp
    hence "a \<oplus>\<^bsub>K[X]\<^esub> b = (q \<otimes>\<^bsub>K[X]\<^esub> ?pdiv_add) \<oplus>\<^bsub>K[X]\<^esub> ?pmod_add"
      using assms(4) in_carrier by algebra
    moreover have "(?pdiv_add, ?pmod_add) \<in> carrier (poly_ring R) \<times> carrier (poly_ring R)"
      using in_carrier carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
    moreover have "?pmod_add = [] \<or> degree ?pmod_add < degree q"
    proof (cases)
      assume "?pmod_add \<noteq> []"
      hence "a pmod q \<noteq> [] \<or> b pmod q \<noteq> []"
        using in_carrier(2,4) unfolding sym[OF univ_poly_zero[of R K]] by auto
      moreover from \<open>q \<noteq> []\<close>
      have "a pmod q = [] \<or> degree (a pmod q) < degree q" and "b pmod q = [] \<or> degree (b pmod q) < degree q"
        using assms(2-3)[THEN pmod_degree[OF assms(1) _ assms(4)]] by auto
      ultimately have "max (degree (a pmod q)) (degree (b pmod q)) < degree q"
        by auto
      thus ?thesis
        using poly_add_degree le_less_trans unfolding univ_poly_add by blast
    qed simp
    ultimately have "long_divides (a \<oplus>\<^bsub>K[X]\<^esub> b) q (?pdiv_add, ?pmod_add)"
      unfolding long_divides_def univ_poly_mult univ_poly_add by simp
    with \<open>q \<noteq> []\<close> show ?thesis
      using long_divisionI[OF assms(1) UP.a_closed[OF assms(2-3)] assms(4)] by simp
  qed
  thus ?pdiv and ?pmod
    by auto
qed

lemma (in domain) long_division_add_iff:
  assumes "subfield K R"
    and "a \<in> carrier (K[X])" "b \<in> carrier (K[X])" "c \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "a pmod q = b pmod q \<longleftrightarrow> (a \<oplus>\<^bsub>K[X]\<^esub> c) pmod q = (b \<oplus>\<^bsub>K[X]\<^esub> c) pmod q"
proof -
  interpret UP: ring "K[X]"
    using univ_poly_is_ring[OF subfieldE(1)[OF assms(1)]] .
  show ?thesis
    using assms(2-4)[THEN long_division_closed(2)[OF assms(1) _ assms(5)]]
    unfolding assms(2-3)[THEN long_division_add(2)[OF assms(1) _ assms(4-5)]] by auto
qed

lemma (in domain) pdivides_iff:
  assumes "subfield K R" and "polynomial K p" "polynomial K q"
  shows "p pdivides q \<longleftrightarrow> p divides\<^bsub>K[X]\<^esub> q"
proof
  show "p divides\<^bsub>K [X]\<^esub> q \<Longrightarrow> p pdivides q"
    using carrier_polynomial[OF subfieldE(1)[OF assms(1)]]
    unfolding pdivides_def factor_def univ_poly_mult univ_poly_carrier by auto
next
  interpret UP: ring "poly_ring R"
    using univ_poly_is_ring[OF carrier_is_subring] .
  
  have in_carrier: "p \<in> carrier (poly_ring R)" "q \<in> carrier (poly_ring R)"
    using carrier_polynomial[OF subfieldE(1)[OF assms(1)]] assms
    unfolding univ_poly_carrier by auto

  assume "p pdivides q"
  then obtain b where "b \<in> carrier (poly_ring R)" and "q = p \<otimes>\<^bsub>poly_ring R\<^esub> b"
      unfolding pdivides_def factor_def by blast
  show "p divides\<^bsub>K[X]\<^esub> q"
  proof (cases)
    assume "p = []"
    with \<open>b \<in> carrier (poly_ring R)\<close> and \<open>q = p \<otimes>\<^bsub>poly_ring R\<^esub> b\<close> have "q = []"
      unfolding univ_poly_mult sym[OF univ_poly_carrier]
      using poly_mult_zero(1)[OF polynomial_incl] by simp
    with \<open>p = []\<close> show ?thesis
      using poly_mult_zero(2)[of "[]"]
      unfolding factor_def univ_poly_mult by auto 
  next
    interpret UP: ring "poly_ring R"
      using univ_poly_is_ring[OF carrier_is_subring] .

    assume "p \<noteq> []"
    from \<open>p pdivides q\<close> obtain b where "b \<in> carrier (poly_ring R)" and "q = p \<otimes>\<^bsub>poly_ring R\<^esub> b"
      unfolding pdivides_def factor_def by blast
    moreover have "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)"
      using assms carrier_polynomial[OF subfieldE(1)[OF assms(1)]] unfolding univ_poly_carrier by auto
    ultimately have "q = (p \<otimes>\<^bsub>poly_ring R\<^esub> b) \<oplus>\<^bsub>poly_ring R\<^esub> \<zero>\<^bsub>poly_ring R\<^esub>"
      by algebra
    with \<open>b \<in> carrier (poly_ring R)\<close> have "long_divides q p (b, [])"
      unfolding long_divides_def univ_poly_zero by auto
    with \<open>p \<noteq> []\<close> have "b \<in> carrier (K[X])"
      using long_divisionI[of K q p b] long_division_closed[of K q p] assms
      unfolding univ_poly_carrier by auto
    with \<open>q = p \<otimes>\<^bsub>poly_ring R\<^esub> b\<close> show ?thesis
      unfolding factor_def univ_poly_mult by blast
  qed
qed

lemma (in domain) pdivides_iff_shell:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pdivides q \<longleftrightarrow> p divides\<^bsub>K[X]\<^esub> q"
  using pdivides_iff assms by (simp add: univ_poly_carrier)

lemma (in domain) pmod_zero_iff_pdivides:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p pmod q = [] \<longleftrightarrow> q pdivides p"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] .

  show ?thesis
  proof
    assume pmod: "p pmod q = []"
    have "p pdiv q \<in> carrier (K[X])" and "p pmod q \<in> carrier (K[X])"
      using long_division_closed[OF assms] by auto
    hence "p = q \<otimes>\<^bsub>K[X]\<^esub> (p pdiv q)"
      using pdiv_pmod[OF assms] assms(3) unfolding pmod sym[OF univ_poly_zero[of R K]] by algebra
    with \<open>p pdiv q \<in> carrier (K[X])\<close> show "q pdivides p"
      unfolding pdivides_iff_shell[OF assms(1,3,2)] factor_def by blast
  next
    assume "q pdivides p" show "p pmod q = []"
    proof (cases)
      assume "q = []" with \<open>q pdivides p\<close> show ?thesis
        using zero_pdivides unfolding pmod_def by simp
    next
      assume "q \<noteq> []"
      from \<open>q pdivides p\<close> obtain r where "r \<in> carrier (K[X])" and "p = q \<otimes>\<^bsub>K[X]\<^esub> r"
        unfolding pdivides_iff_shell[OF assms(1,3,2)] factor_def by blast
      hence "p = (q \<otimes>\<^bsub>K[X]\<^esub> r) \<oplus>\<^bsub>K[X]\<^esub> []"
        using assms(2) unfolding sym[OF univ_poly_zero[of R K]] by simp
      moreover from \<open>r \<in> carrier (K[X])\<close> have "r \<in> carrier (poly_ring R)"
        using carrier_polynomial_shell[OF subfieldE(1)[OF assms(1)]] by auto
      ultimately have "long_divides p q (r, [])"
        unfolding long_divides_def univ_poly_mult univ_poly_add by auto
      with \<open>q \<noteq> []\<close> show ?thesis
        using long_divisionI[OF assms] by simp
    qed
  qed
qed

lemma (in domain) same_pmod_iff_pdivides:
  assumes "subfield K R" and "a \<in> carrier (K[X])" "b \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "a pmod q = b pmod q \<longleftrightarrow> q pdivides (a \<ominus>\<^bsub>K[X]\<^esub> b)"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] .

  have "a pmod q = b pmod q \<longleftrightarrow> (a \<oplus>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> b)) pmod q = (b \<oplus>\<^bsub>K[X]\<^esub> (\<ominus>\<^bsub>K[X]\<^esub> b)) pmod q"
    using long_division_add_iff[OF assms(1-3) UP.a_inv_closed[OF assms(3)] assms(4)] .
  also have " ... \<longleftrightarrow> (a \<ominus>\<^bsub>K[X]\<^esub> b) pmod q = \<zero>\<^bsub>K[X]\<^esub> pmod q"
    using assms(2-3) by algebra
  also have " ... \<longleftrightarrow> q pdivides (a \<ominus>\<^bsub>K[X]\<^esub> b)"
    using pmod_zero_iff_pdivides[OF assms(1) UP.minus_closed[OF assms(2-3)] assms(4)]
    unfolding univ_poly_zero long_division_zero(2)[OF assms(1,4)] .
  finally show ?thesis .
qed

lemma (in domain) pdivides_imp_degree_le:
  assumes "subring K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])" "q \<noteq> []"
  shows "p pdivides q \<Longrightarrow> degree p \<le> degree q"
proof -
  assume "p pdivides q"
  then obtain r where r: "polynomial (carrier R) r" "q = poly_mult p r"
    unfolding pdivides_def factor_def univ_poly_mult univ_poly_carrier by blast
  moreover have p: "polynomial (carrier R) p"
    using assms(2) carrier_polynomial[OF assms(1)] unfolding univ_poly_carrier by auto
  moreover have "p \<noteq> []" and "r \<noteq> []"
    using poly_mult_zero(2)[OF polynomial_incl[OF p]] r(2) assms(4) by auto 
  ultimately show "degree p \<le> degree q"
    using poly_mult_degree_eq[OF carrier_is_subring, of p r] by auto
qed

lemma (in domain) pprimeE:
  assumes "subfield K R" "p \<in> carrier (K[X])" "pprime K p"
  shows "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p pdivides (q \<otimes>\<^bsub>K[X]\<^esub> r) \<Longrightarrow> p pdivides q \<or> p pdivides r"
  using assms(2-3) poly_mult_closed[OF subfieldE(1)[OF assms(1)]] pdivides_iff[OF assms(1)]
  unfolding ring_prime_def prime_def 
  by (auto simp add: univ_poly_mult univ_poly_carrier univ_poly_zero)

lemma (in domain) pprimeI:
  assumes "subfield K R" "p \<in> carrier (K[X])" "p \<noteq> []" "p \<notin> Units (K[X])"
    and "\<And>q r. \<lbrakk> q \<in> carrier (K[X]); r \<in> carrier (K[X])\<rbrakk> \<Longrightarrow>
                 p pdivides (q \<otimes>\<^bsub>K[X]\<^esub> r) \<Longrightarrow> p pdivides q \<or> p pdivides r"
  shows "pprime K p"
  using assms(2-5) poly_mult_closed[OF subfieldE(1)[OF assms(1)]] pdivides_iff[OF assms(1)]
  unfolding ring_prime_def prime_def
  by (auto simp add: univ_poly_mult univ_poly_carrier univ_poly_zero)

lemma (in domain) associated_polynomials_iff:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "q \<in> carrier (K[X])"
  shows "p \<sim>\<^bsub>K[X]\<^esub> q \<longleftrightarrow> (\<exists>k \<in> K - { \<zero> }. p = [ k ] \<otimes>\<^bsub>K[X]\<^esub> q)"
  using domain.ring_associated_iff[OF univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] assms(2-3)]
  unfolding univ_poly_units[OF assms(1)] by auto

corollary (in domain) associated_polynomials_imp_same_length: (* stronger than "imp_same_degree" *)
  assumes "subring K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])"
  shows "p \<sim>\<^bsub>K[X]\<^esub> q \<Longrightarrow> length p = length q"
proof -
  { fix p q
    assume p: "p \<in> carrier (K[X])" and q: "q \<in> carrier (K[X])" and "p \<sim>\<^bsub>K[X]\<^esub> q"
    have "length p \<le> length q"
    proof (cases "q = []")
      case True with \<open>p \<sim>\<^bsub>K[X]\<^esub> q\<close> have "p = []"
        unfolding associated_def True factor_def univ_poly_def by auto
      thus ?thesis
        using True by simp
    next
      case False
      from \<open>p \<sim>\<^bsub>K[X]\<^esub> q\<close> have "p divides\<^bsub>K [X]\<^esub> q"
        unfolding associated_def by simp
      hence "p divides\<^bsub>poly_ring R\<^esub> q"
        using carrier_polynomial[OF assms(1)]
        unfolding factor_def univ_poly_carrier univ_poly_mult by auto
      with \<open>q \<noteq> []\<close> have "degree p \<le> degree q"
        using pdivides_imp_degree_le[OF assms(1) p q] unfolding pdivides_def by simp
      with \<open>q \<noteq> []\<close> show ?thesis
        by (cases "p = []", auto simp add: Suc_leI le_diff_iff)
    qed
  } note aux_lemma = this

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  assume "p \<sim>\<^bsub>K[X]\<^esub> q" thus ?thesis
    using aux_lemma[OF assms(2-3)] aux_lemma[OF assms(3,2) UP.associated_sym] by simp
qed

lemma (in ring) divides_pirreducible_condition:
  assumes "pirreducible K q" and "p \<in> carrier (K[X])"
  shows "p divides\<^bsub>K[X]\<^esub> q \<Longrightarrow> p \<in> Units (K[X]) \<or> p \<sim>\<^bsub>K[X]\<^esub> q"
  using divides_irreducible_condition[of "K[X]" q p] assms
  unfolding ring_irreducible_def by auto

subsection \<open>Polynomial Power\<close>

lemma (in domain) polynomial_pow_not_zero:
  assumes "p \<in> carrier (poly_ring R)" and "p \<noteq> []"
  shows "p [^]\<^bsub>poly_ring R\<^esub> (n::nat) \<noteq> []"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from assms UP.integral show ?thesis
    unfolding sym[OF univ_poly_zero[of R "carrier R"]]
    by (induction n, auto)
qed

lemma (in domain) subring_polynomial_pow_not_zero:
  assumes "subring K R" and "p \<in> carrier (K[X])" and "p \<noteq> []"
  shows "p [^]\<^bsub>K[X]\<^esub> (n::nat) \<noteq> []"
  using domain.polynomial_pow_not_zero[OF subring_is_domain, of K p n] assms
  unfolding univ_poly_consistent[OF assms(1)] by simp

lemma (in domain) polynomial_pow_degree:
  assumes "p \<in> carrier (poly_ring R)"
  shows "degree (p [^]\<^bsub>poly_ring R\<^esub> n) = n * degree p"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  show ?thesis
  proof (induction n)
    case 0 thus ?case
      using UP.nat_pow_0 unfolding univ_poly_one by auto
  next
    let ?ppow = "\<lambda>n. p [^]\<^bsub>poly_ring R\<^esub> n"
    case (Suc n) thus ?case
    proof (cases "p = []")
      case True thus ?thesis
        using univ_poly_zero[of R "carrier R"] UP.r_null assms by auto
    next
      case False
      hence "?ppow n \<in> carrier (poly_ring R)" and "?ppow n \<noteq> []" and "p \<noteq> []"
        using polynomial_pow_not_zero[of p n] assms by (auto simp add: univ_poly_one)
      thus ?thesis
        using poly_mult_degree_eq[OF carrier_is_subring, of "?ppow n" p] Suc assms
        unfolding univ_poly_carrier univ_poly_zero
        by (auto simp add: add.commute univ_poly_mult)
    qed
  qed
qed

lemma (in domain) subring_polynomial_pow_degree:
  assumes "subring K R" and "p \<in> carrier (K[X])"
  shows "degree (p [^]\<^bsub>K[X]\<^esub> n) = n * degree p"
  using domain.polynomial_pow_degree[OF subring_is_domain, of K p n] assms
  unfolding univ_poly_consistent[OF assms(1)] by simp

lemma (in domain) polynomial_pow_division:
  assumes "p \<in> carrier (poly_ring R)" and "(n::nat) \<le> m"
  shows "(p [^]\<^bsub>poly_ring R\<^esub> n) pdivides (p [^]\<^bsub>poly_ring R\<^esub> m)"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  let ?ppow = "\<lambda>n. p [^]\<^bsub>poly_ring R\<^esub> n"

  have "?ppow n \<otimes>\<^bsub>poly_ring R\<^esub> ?ppow k = ?ppow (n + k)" for k
    using assms(1) by (simp add: UP.nat_pow_mult)
  thus ?thesis
    using dividesI[of "?ppow (m - n)" "poly_ring R" "?ppow m" "?ppow n"] assms
    unfolding pdivides_def by auto
qed

lemma (in domain) subring_polynomial_pow_division:
  assumes "subring K R" and "p \<in> carrier (K[X])" and "(n::nat) \<le> m"
  shows "(p [^]\<^bsub>K[X]\<^esub> n) divides\<^bsub>K[X]\<^esub> (p [^]\<^bsub>K[X]\<^esub> m)"
  using domain.polynomial_pow_division[OF subring_is_domain, of K p n m] assms
  unfolding univ_poly_consistent[OF assms(1)] pdivides_def by simp

lemma (in domain) pirreducible_pow_pdivides_iff:
  assumes "subfield K R" "p \<in> carrier (K[X])" "q \<in> carrier (K[X])" "r \<in> carrier (K[X])"
    and "pirreducible K p" and "\<not> (p pdivides q)"
  shows "(p [^]\<^bsub>K[X]\<^esub> (n :: nat)) pdivides (q \<otimes>\<^bsub>K[X]\<^esub> r) \<longleftrightarrow> (p [^]\<^bsub>K[X]\<^esub> n) pdivides r"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .
  show ?thesis
  proof (cases "r = []")
    case True with \<open>q \<in> carrier (K[X])\<close> have "q \<otimes>\<^bsub>K[X]\<^esub> r = []" and "r = []"
      unfolding  sym[OF univ_poly_zero[of R K]] by auto
    thus ?thesis
      using pdivides_zero[OF subfieldE(1),of K] assms by auto
  next
    case False then have not_zero: "p \<noteq> []" "q \<noteq> []" "r \<noteq> []" "q \<otimes>\<^bsub>K[X]\<^esub> r \<noteq> []"
      using subfieldE(1) pdivides_zero[OF _ assms(2)] assms(1-2,5-6) pirreducibleE(1)
            UP.integral_iff[OF assms(3-4)] univ_poly_zero[of R K] by auto
    from \<open>p \<noteq> []\<close>
    have ppow: "p [^]\<^bsub>K[X]\<^esub> (n :: nat) \<noteq> []" "p [^]\<^bsub>K[X]\<^esub> (n :: nat) \<in> carrier (K[X])"
      using subring_polynomial_pow_not_zero[OF subfieldE(1)] assms(1-2) by auto
    have not_pdiv: "\<not> (p divides\<^bsub>mult_of (K[X])\<^esub> q)"
      using assms(6) pdivides_iff_shell[OF assms(1-3)] unfolding pdivides_def by auto
    have prime: "prime (mult_of (K[X])) p"
      using assms(5) pprime_iff_pirreducible[OF assms(1-2)]
      unfolding sym[OF UP.prime_eq_prime_mult[OF assms(2)]] ring_prime_def by simp
    have "a pdivides b \<longleftrightarrow> a divides\<^bsub>mult_of (K[X])\<^esub> b"
      if "a \<in> carrier (K[X])" "a \<noteq> \<zero>\<^bsub>K[X]\<^esub>" "b \<in> carrier (K[X])" "b \<noteq> \<zero>\<^bsub>K[X]\<^esub>" for a b
      using that UP.divides_imp_divides_mult[of a b] divides_mult_imp_divides[of "K[X]" a b]
      unfolding pdivides_iff_shell[OF assms(1) that(1,3)] by blast
    thus ?thesis
      using UP.mult_of.prime_pow_divides_iff[OF _ _ _ prime not_pdiv, of r] ppow not_zero assms(2-4)
      unfolding nat_pow_mult_of carrier_mult_of mult_mult_of sym[OF univ_poly_zero[of R K]]
      by (metis DiffI UP.m_closed singletonD)
  qed
qed

lemma (in domain) subring_degree_one_imp_pirreducible:
  assumes "subring K R" and "a \<in> Units (R \<lparr> carrier := K \<rparr>)" and "b \<in> K"
  shows "pirreducible K [ a, b ]"
proof (rule pirreducibleI[OF assms(1)])
  have "a \<in> K" and "a \<noteq> \<zero>"
    using assms(2) subringE(1)[OF assms(1)] unfolding Units_def by auto
  thus "[ a, b ] \<in> carrier (K[X])" and "[ a, b ] \<noteq> []" and "[ a, b ] \<notin> Units (K [X])"
    using univ_poly_units_incl[OF assms(1)] assms(2-3)
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
next
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF assms(1)] .

  { fix q r
    assume q: "q \<in> carrier (K[X])" and r: "r \<in> carrier (K[X])" and "[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r"
    hence not_zero: "q \<noteq> []" "r \<noteq> []"
      by (metis UP.integral_iff list.distinct(1) univ_poly_zero)+
    have "degree (q \<otimes>\<^bsub>K[X]\<^esub> r) = degree q + degree r"
      using not_zero poly_mult_degree_eq[OF assms(1)] q r
      by (simp add: univ_poly_carrier univ_poly_mult)
    with sym[OF \<open>[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r\<close>] have "degree q + degree r = 1" and "q \<noteq> []" "r \<noteq> []"
      using not_zero by auto
  } note aux_lemma1 = this

  { fix q r
    assume q: "q \<in> carrier (K[X])" "q \<noteq> []" and r: "r \<in> carrier (K[X])" "r \<noteq> []"
      and "[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r" and "degree q = 1" and "degree r = 0"
    hence "length q = Suc (Suc 0)" and "length r = Suc 0"
      by (linarith, metis add.right_neutral add_eq_if length_0_conv)
    from \<open>length q = Suc (Suc 0)\<close> obtain c d where q_def: "q = [ c, d ]"
      by (metis length_0_conv length_Cons list.exhaust nat.inject)
    from \<open>length r = Suc 0\<close> obtain e where r_def: "r = [ e ]"
      by (metis length_0_conv length_Suc_conv)
    from \<open>r = [ e ]\<close> and \<open>q = [ c, d ]\<close>
    have c: "c \<in> K" "c \<noteq> \<zero>" and d: "d \<in> K" and e: "e \<in> K" "e \<noteq> \<zero>"
      using r q subringE(1)[OF assms(1)] unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    with sym[OF \<open>[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r\<close>] have "a = c \<otimes> e"
      using poly_mult_lead_coeff[OF assms(1), of q r]
      unfolding polynomial_def sym[OF univ_poly_mult[of R K]] r_def q_def by auto
    obtain inv_a where a: "a \<in> K" and inv_a: "inv_a \<in> K" "a \<otimes> inv_a = \<one>" "inv_a \<otimes> a = \<one>"
      using assms(2) unfolding Units_def by auto
    hence "a \<noteq> \<zero>" and "inv_a \<noteq> \<zero>"
      using subringE(1)[OF assms(1)] integral_iff by auto
    with \<open>c \<in> K\<close> and \<open>c \<noteq> \<zero>\<close> have in_carrier: "[ c \<otimes> inv_a ] \<in> carrier (K[X])"
      using subringE(1,6)[OF assms(1)] inv_a integral
      unfolding sym[OF univ_poly_carrier] polynomial_def
      by (auto, meson subsetD)
    moreover have "[ c \<otimes> inv_a ] \<otimes>\<^bsub>K[X]\<^esub> r = [ \<one> ]"
      using \<open>a = c \<otimes> e\<close> a inv_a c e subsetD[OF subringE(1)[OF assms(1)]]
      unfolding r_def univ_poly_mult by (auto) (simp add: m_assoc m_lcomm integral_iff)+
    ultimately have "r \<in> Units (K[X])"
      using r(1) UP.m_comm[OF in_carrier r(1)] unfolding sym[OF univ_poly_one[of R K]] Units_def by auto
  } note aux_lemma2 = this

  fix q r
  assume q: "q \<in> carrier (K[X])" and r: "r \<in> carrier (K[X])" and qr: "[ a, b ] = q \<otimes>\<^bsub>K[X]\<^esub> r"
  thus "q \<in> Units (K[X]) \<or> r \<in> Units (K[X])"
    using aux_lemma1[OF q r qr] aux_lemma2[of q r] aux_lemma2[of r q] UP.m_comm add_is_1 by auto
qed

lemma (in domain) degree_one_imp_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "pirreducible K p"
proof -
  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where p: "p = [ a, b ]"
    by (metis length_0_conv length_Cons nat.inject neq_Nil_conv)
  with \<open>p \<in> carrier (K[X])\<close> show ?thesis
    using subring_degree_one_imp_pirreducible[OF subfieldE(1)[OF assms(1)], of a b]
          subfield.subfield_Units[OF assms(1)]
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
qed

lemma (in ring) degree_oneE[elim]:
  assumes "p \<in> carrier (K[X])" and "degree p = 1"
    and "\<And>a b. \<lbrakk> a \<in> K; a \<noteq> \<zero>; b \<in> K; p = [ a, b ] \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where "p = [ a, b ]"
    by (metis length_0_conv length_Cons nat.inject neq_Nil_conv)
  with \<open>p \<in> carrier (K[X])\<close> have "a \<in> K" and "a \<noteq> \<zero>" and "b \<in> K"
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  with \<open>p = [ a, b ]\<close> show ?thesis
    using assms(3) by simp
qed

lemma (in domain) subring_degree_one_associatedI:
  assumes "subring K R" and "a \<in> K" "a' \<in> K" and "b \<in> K" and "a \<otimes> a' = \<one>"
  shows "[ a , b ] \<sim>\<^bsub>K[X]\<^esub> [ \<one>, a' \<otimes> b ]"
proof -
  from \<open>a \<otimes> a' = \<one>\<close> have not_zero: "a \<noteq> \<zero>" "a' \<noteq> \<zero>"
    using subringE(1)[OF assms(1)] assms(2-3) by auto
  hence "[ a, b ] = [ a ] \<otimes>\<^bsub>K[X]\<^esub> [ \<one>, a' \<otimes> b ]"
    using assms(2-4)[THEN subsetD[OF subringE(1)[OF assms(1)]]] assms(5) m_assoc
    unfolding univ_poly_mult by fastforce
  moreover have "[ a, b ] \<in> carrier (K[X])" and "[ \<one>, a' \<otimes> b ] \<in> carrier (K[X])"
    using subringE(1,3,6)[OF assms(1)] not_zero one_not_zero assms
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  moreover have "[ a ] \<in> Units (K[X])"
  proof -
    from \<open>a \<noteq> \<zero>\<close> and \<open>a' \<noteq> \<zero>\<close> have "[ a ] \<in> carrier (K[X])" and "[ a' ] \<in> carrier (K[X])"
      using assms(2-3) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    moreover have "a' \<otimes> a = \<one>"
      using subsetD[OF subringE(1)[OF assms(1)]] assms m_comm by simp 
    hence "[ a ] \<otimes>\<^bsub>K[X]\<^esub> [ a' ] = [ \<one> ]" and "[ a' ] \<otimes>\<^bsub>K[X]\<^esub> [ a ] = [ \<one> ]"
      using assms unfolding univ_poly_mult by auto
    ultimately show ?thesis
      unfolding sym[OF univ_poly_one[of R K]] Units_def by blast
  qed
  ultimately show ?thesis
    using domain.ring_associated_iff[OF univ_poly_is_domain[OF assms(1)]] by blast
qed

lemma (in domain) degree_one_associatedI:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "p \<sim>\<^bsub>K[X]\<^esub> [ \<one>, inv (lead_coeff p) \<otimes> (const_term p) ]"
proof -
  from \<open>p \<in> carrier (K[X])\<close> and \<open>degree p = 1\<close>
  obtain a b where "p = [ a, b ]" and "a \<in> K" "a \<noteq> \<zero>" and "b \<in> K"
    by auto
  thus ?thesis
    using subring_degree_one_associatedI[OF subfieldE(1)[OF assms(1)]]
          subfield_m_inv[OF assms(1)] subsetD[OF subfieldE(3)[OF assms(1)]]
    unfolding const_term_def
    by auto
qed

subsection \<open>Ideals\<close>

lemma (in domain) exists_unique_gen:
  assumes "subfield K R" "ideal I (K[X])" "I \<noteq> { [] }"
  shows "\<exists>!p \<in> carrier (K[X]). lead_coeff p = \<one> \<and> I = PIdl\<^bsub>K[X]\<^esub> p"
    (is "\<exists>!p. ?generator p")
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .
  obtain q where q: "q \<in> carrier (K[X])" "I = PIdl\<^bsub>K[X]\<^esub> q"
    using UP.exists_gen[OF assms(2)] by blast
  hence not_nil: "q \<noteq> []"
    using UP.genideal_zero UP.cgenideal_eq_genideal[OF UP.zero_closed] assms(3)
    by (auto simp add: univ_poly_zero)
  hence "lead_coeff q \<in> K - { \<zero> }"
    using q(1) unfolding univ_poly_def polynomial_def by auto
  hence inv_lc_q: "inv (lead_coeff q) \<in> K - { \<zero> }" "inv (lead_coeff q) \<otimes> lead_coeff q = \<one>"
    using subfield_m_inv[OF assms(1)] by auto 

  define p where "p = [ inv (lead_coeff q) ] \<otimes>\<^bsub>K[X]\<^esub> q"
  have is_poly: "polynomial K [ inv (lead_coeff q) ]" "polynomial K q"
    using inv_lc_q(1) q(1) unfolding univ_poly_def polynomial_def by auto
  hence in_carrier: "p \<in> carrier (K[X])"
    using UP.m_closed unfolding univ_poly_carrier p_def by simp
  have lc_p: "lead_coeff p = \<one>"
    using poly_mult_lead_coeff[OF subfieldE(1)[OF assms(1)] is_poly _ not_nil] inv_lc_q(2)
    unfolding p_def univ_poly_mult[of R K] by simp
  moreover have PIdl_p: "I = PIdl\<^bsub>K[X]\<^esub> p"
    using UP.associated_iff_same_ideal[OF in_carrier q(1)] q(2) inv_lc_q(1) p_def
          associated_polynomials_iff[OF assms(1) in_carrier q(1)]
    by auto
  ultimately have "?generator p"
    using in_carrier by simp

  moreover
  have "\<And>r. \<lbrakk> r \<in> carrier (K[X]); lead_coeff r = \<one>; I = PIdl\<^bsub>K[X]\<^esub> r \<rbrakk> \<Longrightarrow> r = p"
  proof -
    fix r assume r: "r \<in> carrier (K[X])" "lead_coeff r = \<one>" "I = PIdl\<^bsub>K[X]\<^esub> r"
    have "subring K R"
      by (simp add: \<open>subfield K R\<close> subfieldE(1))
    obtain k where k: "k \<in> K - { \<zero> }" "r = [ k ] \<otimes>\<^bsub>K[X]\<^esub> p"
      using UP.associated_iff_same_ideal[OF r(1) in_carrier] PIdl_p r(3)
            associated_polynomials_iff[OF assms(1) r(1) in_carrier]
      by auto
    hence "polynomial K [ k ]"
      unfolding polynomial_def by simp
    moreover have "p \<noteq> []"
      using not_nil UP.associated_iff_same_ideal[OF in_carrier q(1)] q(2) PIdl_p
            associated_polynomials_imp_same_length[OF \<open>subring K R\<close> in_carrier q(1)] by auto
    ultimately have "lead_coeff r = k \<otimes> (lead_coeff p)"
      using poly_mult_lead_coeff[OF subfieldE(1)[OF assms(1)]] in_carrier k(2)
      unfolding univ_poly_def by (auto simp del: poly_mult.simps)
    hence "k = \<one>"
      using lc_p r(2) k(1) subfieldE(3)[OF assms(1)] by auto
    hence "r = map ((\<otimes>) \<one>) p"
      using poly_mult_const(1)[OF subfieldE(1)[OF assms(1)] _ k(1), of p] in_carrier
      unfolding k(2) univ_poly_carrier[of R K] univ_poly_mult[of R K] by auto
    moreover have "set p \<subseteq> carrier R"
      using polynomial_in_carrier[OF subfieldE(1)[OF assms(1)]]
            in_carrier univ_poly_carrier[of R K] by auto
    hence "map ((\<otimes>) \<one>) p = p"
      by (induct p) (auto)
    ultimately show "r = p" by simp
  qed

  ultimately show ?thesis by blast
qed

proposition (in domain) exists_unique_pirreducible_gen:
  assumes "subfield K R" "ring_hom_ring (K[X]) R h"
    and "a_kernel (K[X]) R h \<noteq> { [] }" "a_kernel (K[X]) R h \<noteq> carrier (K[X])"
  shows "\<exists>!p \<in> carrier (K[X]). pirreducible K p \<and> lead_coeff p = \<one> \<and> a_kernel (K[X]) R h = PIdl\<^bsub>K[X]\<^esub> p"
    (is "\<exists>!p. ?generator p")
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  have "ideal (a_kernel (K[X]) R h) (K[X])"
    using ring_hom_ring.kernel_is_ideal[OF assms(2)] .
  then obtain p
    where p: "p \<in> carrier (K[X])" "lead_coeff p = \<one>" "a_kernel (K[X]) R h = PIdl\<^bsub>K[X]\<^esub> p"
      and unique:
      "\<And>q. \<lbrakk> q \<in> carrier (K[X]); lead_coeff q = \<one>; a_kernel (K[X]) R h = PIdl\<^bsub>K[X]\<^esub> q \<rbrakk> \<Longrightarrow> q = p"
    using exists_unique_gen[OF assms(1) _ assms(3)] by metis

  have "p \<in> carrier (K[X]) - { [] }"
      using UP.genideal_zero UP.cgenideal_eq_genideal[OF UP.zero_closed] assms(3) p(1,3)
      by (auto simp add: univ_poly_zero)
  hence "pprime K p"
    using ring_hom_ring.primeideal_vimage[OF assms(2) UP.is_cring zeroprimeideal]
          UP.primeideal_iff_prime[of p]
    unfolding univ_poly_zero sym[OF p(3)] a_kernel_def' by simp
  hence "pirreducible K p"
    using pprime_iff_pirreducible[OF assms(1) p(1)] by simp
  thus ?thesis
    using p unique by metis 
qed

lemma (in domain) cgenideal_pirreducible:
  assumes "subfield K R" and "p \<in> carrier (K[X])" "pirreducible K p" 
  shows "\<lbrakk> pirreducible K q; q \<in> PIdl\<^bsub>K[X]\<^esub> p \<rbrakk> \<Longrightarrow> p \<sim>\<^bsub>K[X]\<^esub> q"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  assume q: "pirreducible K q" "q \<in> PIdl\<^bsub>K[X]\<^esub> p"
  hence in_carrier: "q \<in> carrier (K[X])"
    using additive_subgroup.a_subset[OF ideal.axioms(1)[OF UP.cgenideal_ideal[OF assms(2)]]] by auto
  hence "p divides\<^bsub>K[X]\<^esub> q"
    by (meson q assms(2) UP.cgenideal_ideal UP.cgenideal_minimal UP.to_contain_is_to_divide)
  then obtain r where r: "r \<in> carrier (K[X])" "q = p \<otimes>\<^bsub>K[X]\<^esub> r"
    by auto
  hence "r \<in> Units (K[X])"
    using pirreducibleE(3)[OF _ in_carrier q(1) assms(2) r(1)] subfieldE(1)[OF assms(1)]
          pirreducibleE(2)[OF _ assms(2-3)] by auto
  thus "p \<sim>\<^bsub>K[X]\<^esub> q"
    using UP.ring_associated_iff[OF in_carrier assms(2)] r(2) UP.associated_sym
    unfolding UP.m_comm[OF assms(2) r(1)] by auto
qed


subsection \<open>Roots and Multiplicity\<close>

definition (in ring) is_root :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where "is_root p x \<longleftrightarrow> (x \<in> carrier R \<and> eval p x = \<zero> \<and> p \<noteq> [])"

definition (in ring) alg_mult :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
  where "alg_mult p x =
           (if p = [] then 0 else
             (if x \<in> carrier R then Greatest (\<lambda> n. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p) else 0))"

definition (in ring) roots :: "'a list \<Rightarrow> 'a multiset"
  where "roots p = Abs_multiset (alg_mult p)"

definition (in ring) roots_on :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a multiset"
  where "roots_on K p = roots p \<inter># mset_set K"

definition (in ring) splitted :: "'a list \<Rightarrow> bool"
  where "splitted p \<longleftrightarrow> size (roots p) = degree p"

definition (in ring) splitted_on :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "splitted_on K p \<longleftrightarrow> size (roots_on K p) = degree p"

lemma (in domain) pdivides_imp_root_sharing:
  assumes "p \<in> carrier (poly_ring R)" "p pdivides q" and "a \<in> carrier R"
  shows "eval p a = \<zero> \<Longrightarrow> eval q a = \<zero>"
proof - 
  from \<open>p pdivides q\<close> obtain r where r: "q = p \<otimes>\<^bsub>poly_ring R\<^esub> r" "r \<in> carrier (poly_ring R)"
    unfolding pdivides_def factor_def by auto
  hence "eval q a = (eval p a) \<otimes> (eval r a)"
    using ring_hom_memE(2)[OF eval_is_hom[OF carrier_is_subring assms(3)] assms(1) r(2)] by simp
  thus "eval p a = \<zero> \<Longrightarrow> eval q a = \<zero>"
    using ring_hom_memE(1)[OF eval_is_hom[OF carrier_is_subring assms(3)] r(2)] by auto
qed

lemma (in domain) degree_one_root:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p = 1"
  shows "eval p (\<ominus> (inv (lead_coeff p) \<otimes> (const_term p))) = \<zero>"
    and "inv (lead_coeff p) \<otimes> (const_term p) \<in> K" 
proof -
  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where p: "p = [ a, b ]"
    by (metis (no_types, opaque_lifting) Suc_length_conv length_0_conv)
  hence "a \<in> K - { \<zero> }" "b \<in> K"  and in_carrier: "a \<in> carrier R" "b \<in> carrier R"
    using assms(2) subfieldE(3)[OF assms(1)] unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence inv_a: "inv a \<in> carrier R" "a \<otimes> inv a = \<one>" and "inv a \<in> K"
    using subfield_m_inv(1-2)[OF assms(1), of a] subfieldE(3)[OF assms(1)] by auto 
  hence "eval p (\<ominus> (inv a \<otimes> b)) = a \<otimes> (\<ominus> (inv a \<otimes> b)) \<oplus> b"
    using in_carrier unfolding p by simp
  also have " ... = \<ominus> (a \<otimes> (inv a \<otimes> b)) \<oplus> b"
    using inv_a in_carrier by (simp add: r_minus)
  also have " ... = \<zero>"
    using in_carrier(2) unfolding sym[OF m_assoc[OF in_carrier(1) inv_a(1) in_carrier(2)]] inv_a(2) by algebra
  finally have "eval p (\<ominus> (inv a \<otimes> b)) = \<zero>" .
  moreover have ct: "const_term p = b"
    using in_carrier unfolding p const_term_def by auto
  ultimately show "eval p (\<ominus> (inv (lead_coeff p) \<otimes> (const_term p))) = \<zero>"
    unfolding p by simp
  from \<open>inv a \<in> K\<close> and \<open>b \<in> K\<close>
  show "inv (lead_coeff p) \<otimes> (const_term p) \<in> K"
    using p subringE(6)[OF subfieldE(1)[OF assms(1)]] unfolding ct by auto
qed
lemma (in domain) is_root_imp_pdivides:
  assumes "p \<in> carrier (poly_ring R)"
  shows "is_root p x \<Longrightarrow> [ \<one>, \<ominus> x ] pdivides p"
proof -
  let ?b = "[ \<one> , \<ominus> x ]"

  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume "is_root p x" hence x: "x \<in> carrier R" and is_root: "eval p x = \<zero>"
    unfolding is_root_def by auto
  hence b: "?b \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  then obtain q r where q: "q \<in> carrier (poly_ring R)" and r: "r \<in> carrier (poly_ring R)"
    and long_divides: "p = (?b \<otimes>\<^bsub>poly_ring R\<^esub> q) \<oplus>\<^bsub>poly_ring R\<^esub> r" "r = [] \<or> degree r < degree ?b"
    using long_division_theorem[OF carrier_is_subring, of p ?b] assms by (auto simp add: univ_poly_carrier)

  show ?thesis
  proof (cases "r = []")
    case True then have "r = \<zero>\<^bsub>poly_ring R\<^esub>"
      unfolding univ_poly_zero[of R "carrier R"] .
    thus ?thesis
      using long_divides(1) q r b dividesI[OF q, of p ?b] by (simp add: pdivides_def)
  next
    case False then have "length r = Suc 0"
      using long_divides(2) le_SucE by fastforce
    then obtain a where "r = [ a ]" and a: "a \<in> carrier R" and "a \<noteq> \<zero>"
      using r unfolding sym[OF univ_poly_carrier] polynomial_def
      by (metis False length_0_conv length_Suc_conv list.sel(1) list.set_sel(1) subset_code(1))

    have "eval p x = ((eval ?b x) \<otimes> (eval q x)) \<oplus> (eval r x)"
      using long_divides(1) ring_hom_memE[OF eval_is_hom[OF carrier_is_subring x]] by (simp add: b q r)
    also have " ... = eval r x"
      using ring_hom_memE[OF eval_is_hom[OF carrier_is_subring x]] x b q r by (auto, algebra)
    finally have "a = \<zero>"
      using a unfolding \<open>r = [ a ]\<close> is_root by simp
    with \<open>a \<noteq> \<zero>\<close> have False .. thus ?thesis ..
  qed
qed

lemma (in domain) pdivides_imp_is_root:
  assumes "p \<noteq> []" and "x \<in> carrier R"
  shows "[ \<one>, \<ominus> x ] pdivides p \<Longrightarrow> is_root p x"
proof -
  assume "[ \<one>, \<ominus> x ] pdivides p"
  then obtain q where q: "q \<in> carrier (poly_ring R)" and pdiv: "p = [ \<one>, \<ominus> x ] \<otimes>\<^bsub>poly_ring R\<^esub> q"
    unfolding pdivides_def by auto
  moreover have "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
    using assms(2) unfolding sym[OF univ_poly_carrier] polynomial_def by simp
  ultimately have "eval p x = \<zero>"
    using ring_hom_memE[OF eval_is_hom[OF carrier_is_subring, of x]] assms(2) by (auto, algebra)
  with \<open>p \<noteq> []\<close> and \<open>x \<in> carrier R\<close> show "is_root p x"
    unfolding is_root_def by simp 
qed

lemma (in domain) associated_polynomials_imp_same_is_root:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" and "p \<sim>\<^bsub>poly_ring R\<^esub> q"
  shows "is_root p x \<longleftrightarrow> is_root q x"
proof (cases "p = []")
  case True with \<open>p \<sim>\<^bsub>poly_ring R\<^esub> q\<close> have "q = []"
    unfolding associated_def True factor_def univ_poly_def by auto
  thus ?thesis
    using True unfolding is_root_def by simp 
next
  case False
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  { fix p q
    assume p: "p \<in> carrier (poly_ring R)" and q: "q \<in> carrier (poly_ring R)" and pq: "p \<sim>\<^bsub>poly_ring R\<^esub> q"
    have "is_root p x \<Longrightarrow> is_root q x"
    proof -
      assume is_root: "is_root p x"
      then have "[ \<one>, \<ominus> x ] pdivides p" and "p \<noteq> []" and "x \<in> carrier R"
        using is_root_imp_pdivides[OF p] unfolding is_root_def by auto
      moreover have "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
        using is_root unfolding is_root_def sym[OF univ_poly_carrier] polynomial_def by simp
      ultimately have "[ \<one>, \<ominus> x ] pdivides q"
        using UP.divides_cong_r[OF _ pq ] unfolding pdivides_def by simp
      with \<open>p \<noteq> []\<close> and \<open>x \<in> carrier R\<close> show ?thesis
        using associated_polynomials_imp_same_length[OF carrier_is_subring p q pq]
              pdivides_imp_is_root[of q x]
        by fastforce  
    qed
  }

  then show ?thesis
    using assms UP.associated_sym[OF assms(3)] by blast 
qed

lemma (in ring) monic_degree_one_root_condition:
  assumes "a \<in> carrier R" shows "is_root [ \<one>, \<ominus> a ] b \<longleftrightarrow> a = b"
  using assms minus_equality r_neg[OF assms] unfolding is_root_def by (auto, fastforce)

lemma (in field) degree_one_root_condition:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 1"
  shows "is_root p x \<longleftrightarrow> x = \<ominus> (inv (lead_coeff p) \<otimes> (const_term p))"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from \<open>degree p = 1\<close> have "length p = Suc (Suc 0)"
    by simp
  then obtain a b where p: "p = [ a, b ]"
    by (metis length_0_conv length_Cons list.exhaust nat.inject)
  hence a: "a \<in> carrier R" "a \<noteq> \<zero>" and b: "b \<in> carrier R"
    using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence inv_a: "inv a \<in> carrier R" "(inv a) \<otimes> a = \<one>"
    using subfield_m_inv[OF carrier_is_subfield, of a] by auto
  hence in_carrier: "[ \<one>, (inv a) \<otimes> b ] \<in> carrier (poly_ring R)"
    using b unfolding sym[OF univ_poly_carrier] polynomial_def by auto

  have "p \<sim>\<^bsub>poly_ring R\<^esub> [ \<one>, (inv a) \<otimes> b ]"
  proof (rule UP.associatedI2'[OF _ _ in_carrier, of _ "[ a ]"])
    have "p = [ a ] \<otimes>\<^bsub>poly_ring R\<^esub> [ \<one>, inv a \<otimes> b ]"
      using a inv_a b m_assoc[of a "inv a" b] unfolding p univ_poly_mult by (auto, algebra)
    also have " ... = [ \<one>, inv a \<otimes> b ] \<otimes>\<^bsub>poly_ring R\<^esub> [ a ]"
      using UP.m_comm[OF in_carrier, of "[ a ]"] a
      by (auto simp add: sym[OF univ_poly_carrier] polynomial_def)
    finally show "p = [ \<one>, inv a \<otimes> b ] \<otimes>\<^bsub>poly_ring R\<^esub> [ a ]" .
  next
    from \<open>a \<in> carrier R\<close> and \<open>a \<noteq> \<zero>\<close> show "[ a ] \<in> Units (poly_ring R)"
      unfolding univ_poly_units[OF carrier_is_subfield] by simp
  qed

  moreover have "(inv a) \<otimes> b = \<ominus> (\<ominus> (inv (lead_coeff p) \<otimes> (const_term p)))"
    and "inv (lead_coeff p) \<otimes> (const_term p) \<in> carrier R"
    using inv_a a b unfolding p const_term_def by auto

  ultimately show ?thesis
    using associated_polynomials_imp_same_is_root[OF assms(1) in_carrier]
          monic_degree_one_root_condition
    by (metis add.inv_closed)
qed

lemma (in domain) is_root_poly_mult_imp_is_root:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)"
  shows "is_root (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x \<Longrightarrow> (is_root p x) \<or> (is_root q x)"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume is_root: "is_root (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x"
  hence "p \<noteq> []" and "q \<noteq> []"
    unfolding is_root_def sym[OF univ_poly_zero[of R "carrier R"]]
    using UP.l_null[OF assms(2)] UP.r_null[OF assms(1)] by blast+
  moreover have x: "x \<in> carrier R" and "eval (p \<otimes>\<^bsub>poly_ring R\<^esub> q) x = \<zero>"
    using is_root unfolding is_root_def by simp+
  hence "eval p x = \<zero> \<or> eval q x = \<zero>"
    using ring_hom_memE[OF eval_is_hom[OF carrier_is_subring], of x] assms integral by auto 
  ultimately show "(is_root p x) \<or> (is_root q x)"
    using x unfolding is_root_def by auto
qed

lemma (in domain) degree_zero_imp_not_is_root:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 0" shows "\<not> is_root p x"
proof (cases "p = []", simp add: is_root_def)
  case False with \<open>degree p = 0\<close> have "length p = Suc 0"
    using le_SucE by fastforce 
  then obtain a where "p = [ a ]" and "a \<in> carrier R" and "a \<noteq> \<zero>"
    using assms unfolding sym[OF univ_poly_carrier] polynomial_def
    by (metis False length_0_conv length_Suc_conv list.sel(1) list.set_sel(1) subset_code(1))
  thus ?thesis
    unfolding is_root_def by auto 
qed

lemma (in domain) finite_number_of_roots:
  assumes "p \<in> carrier (poly_ring R)" shows "finite { x. is_root p x }"
  using assms
proof (induction "degree p" arbitrary: p)
  case 0 thus ?case
    by (simp add: degree_zero_imp_not_is_root)
next
  case (Suc n) show ?case
  proof (cases "{ x. is_root p x } = {}")
    case True thus ?thesis
      by (simp add: True) 
  next
    interpret UP: domain "poly_ring R"
      using univ_poly_is_domain[OF carrier_is_subring] .

    case False
    then obtain a where is_root: "is_root p a"
      by blast
    hence a: "a \<in> carrier R" and eval: "eval p a = \<zero>" and p_not_zero: "p \<noteq> []"
      unfolding is_root_def by auto
    hence in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
      unfolding sym[OF univ_poly_carrier] polynomial_def by auto

    obtain q where q: "q \<in> carrier (poly_ring R)" and p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q"
      using is_root_imp_pdivides[OF Suc(3) is_root] unfolding pdivides_def by auto
    with \<open>p \<noteq> []\<close> have q_not_zero: "q \<noteq> []"
      using UP.r_null UP.integral in_carrier unfolding sym[OF univ_poly_zero[of R "carrier R"]]
      by metis
    hence "degree q = n"
      using poly_mult_degree_eq[OF carrier_is_subring, of "[ \<one>, \<ominus> a ]" q]
            in_carrier q p_not_zero p Suc(2)
      unfolding univ_poly_carrier
      by (metis One_nat_def Suc_eq_plus1 diff_Suc_1 list.distinct(1)
                list.size(3-4) plus_1_eq_Suc univ_poly_mult)
    hence "finite { x. is_root q x }"
      using Suc(1)[OF _ q] by simp

    moreover have "{ x. is_root p x } \<subseteq> insert a { x. is_root q x }"
      using is_root_poly_mult_imp_is_root[OF in_carrier q]
            monic_degree_one_root_condition[OF a]
      unfolding p by auto

    ultimately show ?thesis
      using finite_subset by auto
  qed
qed

lemma (in domain) alg_multE:
  assumes "x \<in> carrier R" and "p \<in> carrier (poly_ring R)" and "p \<noteq> []"
  shows "([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p x)) pdivides p"
    and "\<And>n. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p \<Longrightarrow> n \<le> alg_mult p x"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  let ?ppow = "\<lambda>n :: nat. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n)"

  define S :: "nat set" where "S = { n. ?ppow n pdivides p }"
  have "?ppow 0 = \<one>\<^bsub>poly_ring R\<^esub>"
    using UP.nat_pow_0 by simp
  hence "0 \<in> S"
    using UP.one_divides[OF assms(2)] unfolding S_def pdivides_def by simp
  hence "S \<noteq> {}"
    by auto

  moreover have "n \<le> degree p" if "n \<in> S" for n :: nat
  proof -
    have "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
      using assms unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    hence "?ppow n \<in> carrier (poly_ring R)"
      using assms unfolding univ_poly_zero by auto
    with \<open>n \<in> S\<close> have "degree (?ppow n) \<le> degree p"
      using pdivides_imp_degree_le[OF carrier_is_subring _ assms(2-3), of "?ppow n"] by (simp add: S_def)
    with \<open>[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)\<close> show ?thesis
      using polynomial_pow_degree by simp
  qed
  hence "finite S"
    using finite_nat_set_iff_bounded_le by blast

  ultimately have MaxS: "\<And>n. n \<in> S \<Longrightarrow> n \<le> Max S" "Max S \<in> S"
    using Max_ge[of S] Max_in[of S] by auto
  with \<open>x \<in> carrier R\<close> have "alg_mult p x = Max S"
    using Greatest_equality[of "\<lambda>n. ?ppow n pdivides p" "Max S"] assms(3)
    unfolding S_def alg_mult_def by auto
  thus "([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p x)) pdivides p"
   and "\<And>n. ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p \<Longrightarrow> n \<le> alg_mult p x"
    using MaxS unfolding S_def by auto
qed

lemma (in domain) le_alg_mult_imp_pdivides:
  assumes "x \<in> carrier R" and "p \<in> carrier (poly_ring R)"
  shows "n \<le> alg_mult p x \<Longrightarrow> ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides p"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume le_alg_mult: "n \<le> alg_mult p x"
  have in_carrier: "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
    using assms(1) unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  hence ppow_pdivides:
    "([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> n) pdivides
     ([ \<one>, \<ominus> x ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p x))"
    using polynomial_pow_division[OF _ le_alg_mult] by simp

  show ?thesis
  proof (cases "p = []")
    case True thus ?thesis
      using in_carrier pdivides_zero[OF carrier_is_subring] by auto
  next
    case False thus ?thesis
      using ppow_pdivides UP.divides_trans UP.nat_pow_closed alg_multE(1)[OF assms] in_carrier
      unfolding pdivides_def by meson
  qed
qed

lemma (in domain) alg_mult_gt_zero_iff_is_root:
  assumes "p \<in> carrier (poly_ring R)" shows "alg_mult p x > 0 \<longleftrightarrow> is_root p x"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .
  show ?thesis
  proof
    assume is_root: "is_root p x" hence x: "x \<in> carrier R" and not_zero: "p \<noteq> []"
      unfolding is_root_def by auto
    have "[\<one>, \<ominus> x] [^]\<^bsub>poly_ring R\<^esub> (Suc 0) = [\<one>, \<ominus> x]"
      using x unfolding univ_poly_def by auto
    thus "alg_mult p x > 0"
      using is_root_imp_pdivides[OF _ is_root] alg_multE(2)[OF x, of p "Suc 0"] not_zero assms by auto
  next
    assume gt_zero: "alg_mult p x > 0"
    hence x: "x \<in> carrier R" and not_zero: "p \<noteq> []"
      unfolding alg_mult_def by (cases "p = []", auto, cases "x \<in> carrier R", auto)
    hence in_carrier: "[ \<one>, \<ominus> x ] \<in> carrier (poly_ring R)"
      unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    with \<open>x \<in> carrier R\<close> have "[ \<one>, \<ominus> x ] pdivides p" and "eval [ \<one>, \<ominus> x ] x = \<zero>"
      using le_alg_mult_imp_pdivides[of x p "1::nat"] gt_zero assms by (auto, algebra)
    thus "is_root p x"
      using pdivides_imp_root_sharing[OF in_carrier] not_zero x by (simp add: is_root_def)
  qed
qed

lemma (in domain) alg_mult_eq_count_roots:
  assumes "p \<in> carrier (poly_ring R)" shows "alg_mult p = count (roots p)"
  using finite_number_of_roots[OF assms]
  unfolding sym[OF alg_mult_gt_zero_iff_is_root[OF assms]]
  by (simp add: roots_def) 

lemma (in domain) roots_mem_iff_is_root:
  assumes "p \<in> carrier (poly_ring R)" shows "x \<in># roots p \<longleftrightarrow> is_root p x"
  using alg_mult_eq_count_roots[OF assms] count_greater_zero_iff
  unfolding roots_def sym[OF alg_mult_gt_zero_iff_is_root[OF assms]] by metis

lemma (in domain) degree_zero_imp_empty_roots:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 0" shows "roots p = {#}"
  using degree_zero_imp_not_is_root[of p] roots_mem_iff_is_root[of p] assms by auto

lemma (in domain) degree_zero_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 0" shows "splitted p"
  unfolding splitted_def degree_zero_imp_empty_roots[OF assms] assms(2) by simp

lemma (in domain) roots_inclI':
  assumes "p \<in> carrier (poly_ring R)" and "\<And>a. \<lbrakk> a \<in> carrier R; p \<noteq> [] \<rbrakk> \<Longrightarrow> alg_mult p a \<le> count m a" 
  shows "roots p \<subseteq># m"
proof (intro mset_subset_eqI)
  fix a show "count (roots p) a \<le> count m a"
    using assms unfolding sym[OF alg_mult_eq_count_roots[OF assms(1)]] alg_mult_def
    by (cases "p = []", simp, cases "a \<in> carrier R", auto)
qed

lemma (in domain) roots_inclI:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" "q \<noteq> []"
    and "\<And>a. \<lbrakk> a \<in> carrier R; p \<noteq> [] \<rbrakk> \<Longrightarrow> ([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p a)) pdivides q"
  shows "roots p \<subseteq># roots q"
  using roots_inclI'[OF assms(1), of "roots q"] assms alg_multE(2)[OF _ assms(2-3)]
  unfolding sym[OF alg_mult_eq_count_roots[OF assms(2)]] by auto

lemma (in domain) pdivides_imp_roots_incl:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" "q \<noteq> []"
  shows "p pdivides q \<Longrightarrow> roots p \<subseteq># roots q"
proof (rule roots_inclI[OF assms])
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  fix a assume "p pdivides q" and a: "a \<in> carrier R"
  hence "[ \<one> , \<ominus> a ] \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by simp
  with \<open>p pdivides q\<close> show "([\<one>, \<ominus> a] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p a)) pdivides q"
    using UP.divides_trans[of _p q] le_alg_mult_imp_pdivides[OF a assms(1)]
    by (auto simp add: pdivides_def)
qed

lemma (in domain) associated_polynomials_imp_same_roots:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" and "p \<sim>\<^bsub>poly_ring R\<^esub> q"
  shows "roots p = roots q"
  using assms pdivides_imp_roots_incl zero_pdivides
  unfolding pdivides_def associated_def 
  by (metis subset_mset.eq_iff)

lemma (in domain) monic_degree_one_roots:
  assumes "a \<in> carrier R" shows "roots [ \<one> , \<ominus> a ] = {# a #}"
proof -
  let ?p = "[ \<one> , \<ominus> a ]"

  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  from \<open>a \<in> carrier R\<close> have in_carrier: "?p \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by simp
  show ?thesis
  proof (rule subset_mset.antisym)
    show "{# a #} \<subseteq># roots ?p"
      using roots_mem_iff_is_root[OF in_carrier]
            monic_degree_one_root_condition[OF assms]
      by simp
  next
    show "roots ?p \<subseteq># {# a #}"
    proof (rule mset_subset_eqI, auto)
      fix b assume "a \<noteq> b" thus "count (roots ?p) b = 0"
        using alg_mult_gt_zero_iff_is_root[OF in_carrier]
              monic_degree_one_root_condition[OF assms]
        unfolding sym[OF alg_mult_eq_count_roots[OF in_carrier]]
        by fastforce
    next
      have "(?p [^]\<^bsub>poly_ring R\<^esub> (alg_mult ?p a)) pdivides ?p"
        using le_alg_mult_imp_pdivides[OF assms in_carrier] by simp
      hence "degree (?p [^]\<^bsub>poly_ring R\<^esub> (alg_mult ?p a)) \<le> degree ?p"
        using pdivides_imp_degree_le[OF carrier_is_subring, of _ ?p] in_carrier by auto
      thus "count (roots ?p) a \<le> Suc 0"
        using polynomial_pow_degree[OF in_carrier]
        unfolding sym[OF alg_mult_eq_count_roots[OF in_carrier]]
        by auto
    qed
  qed
qed

lemma (in domain) degree_one_roots:
  assumes "a \<in> carrier R" "a' \<in> carrier R" and "b \<in> carrier R" and "a \<otimes> a' = \<one>"
  shows "roots [ a , b ] = {# \<ominus> (a' \<otimes> b) #}"
proof -
  have "[ a, b ] \<in> carrier (poly_ring R)" and "[ \<one>, a' \<otimes> b ] \<in> carrier (poly_ring R)"
    using assms unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  thus ?thesis
    using subring_degree_one_associatedI[OF carrier_is_subring assms] assms
          monic_degree_one_roots associated_polynomials_imp_same_roots
    by (metis add.inv_closed local.minus_minus m_closed)
qed

lemma (in field) degree_one_imp_singleton_roots:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 1"
  shows "roots p = {# \<ominus> (inv (lead_coeff p) \<otimes> (const_term p)) #}"
proof -
  from \<open>p \<in> carrier (poly_ring R)\<close> and \<open>degree p = 1\<close>
  obtain a b where "p = [ a, b ]" and "a \<in> carrier R" "a \<noteq> \<zero>" and "b \<in> carrier R"
    by auto
  thus ?thesis
    using degree_one_roots[of a "inv a" b]
    by (auto simp add: const_term_def field_Units)
qed

lemma (in field) degree_one_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "degree p = 1" shows "splitted p"
  using degree_one_imp_singleton_roots[OF assms] assms(2) unfolding splitted_def by simp

lemma (in field) no_roots_imp_same_roots:
  assumes "p \<in> carrier (poly_ring R)" "p \<noteq> []" and "q \<in> carrier (poly_ring R)"
  shows "roots p = {#} \<Longrightarrow> roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots q"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .

  assume no_roots: "roots p = {#}" show "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots q"
  proof (intro subset_mset.antisym)
    have pdiv: "q pdivides (p \<otimes>\<^bsub>poly_ring R\<^esub> q)"
      using UP.divides_prod_l assms unfolding pdivides_def by blast
    show "roots q \<subseteq># roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q)"
      using pdivides_imp_roots_incl[OF _ _ _ pdiv] assms
            degree_zero_imp_empty_roots[OF assms(3)]
      by (cases "q = []", auto, metis UP.l_null UP.m_rcancel UP.zero_closed univ_poly_zero)
  next
    show "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) \<subseteq># roots q"
    proof (cases "p \<otimes>\<^bsub>poly_ring R\<^esub> q = []")
      case True thus ?thesis
        using degree_zero_imp_empty_roots[OF UP.m_closed[OF assms(1,3)]] by simp
    next
      case False with \<open>p \<noteq> []\<close> have q_not_zero: "q \<noteq> []"
        by (metis UP.r_null assms(1) univ_poly_zero)
      show ?thesis
      proof (rule roots_inclI[OF UP.m_closed[OF assms(1,3)] assms(3) q_not_zero])
        fix a assume a: "a \<in> carrier R"
        hence "\<not> ([ \<one>, \<ominus> a ] pdivides p)"
          using assms(1-2) no_roots pdivides_imp_is_root roots_mem_iff_is_root[of p] by auto
        moreover have in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
          using a unfolding sym[OF univ_poly_carrier] polynomial_def by auto
        hence "pirreducible (carrier R) [ \<one>, \<ominus> a ]"
          using degree_one_imp_pirreducible[OF carrier_is_subfield] by simp
        moreover
        have "([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult (p \<otimes>\<^bsub>poly_ring R\<^esub> q) a)) pdivides (p \<otimes>\<^bsub>poly_ring R\<^esub> q)"
          using le_alg_mult_imp_pdivides[OF a UP.m_closed, of p q] assms by simp
        ultimately show "([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult (p \<otimes>\<^bsub>poly_ring R\<^esub> q) a)) pdivides q"
          using pirreducible_pow_pdivides_iff[OF carrier_is_subfield in_carrier] assms by auto
      qed
    qed
  qed
qed

lemma (in field) poly_mult_degree_one_monic_imp_same_roots:
  assumes "a \<in> carrier R" and "p \<in> carrier (poly_ring R)" "p \<noteq> []"
  shows "roots ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) = add_mset a (roots p)"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .
  
  from \<open>a \<in> carrier R\<close> have in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
    unfolding sym[OF univ_poly_carrier] polynomial_def by simp

  show ?thesis
  proof (intro subset_mset.antisym[OF roots_inclI' mset_subset_eqI])
    show "([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) \<in> carrier (poly_ring R)"
      using in_carrier assms(2) by simp
  next
    fix b assume b: "b \<in> carrier R" and "[ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p \<noteq> []"
    hence not_zero: "p \<noteq> []"
      unfolding univ_poly_def by auto
    from \<open>b \<in> carrier R\<close> have in_carrier':  "[ \<one>, \<ominus> b ] \<in> carrier (poly_ring R)"
      unfolding sym[OF univ_poly_carrier] polynomial_def by simp
    show "alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) b \<le> count (add_mset a (roots p)) b"
    proof (cases "a = b")
      case False
      hence "\<not> [ \<one>, \<ominus> b ] pdivides [ \<one>, \<ominus> a ]"
        using assms(1) b monic_degree_one_root_condition pdivides_imp_is_root by blast
      moreover have "pirreducible (carrier R) [ \<one>, \<ominus> b ]"
        using degree_one_imp_pirreducible[OF carrier_is_subfield in_carrier'] by simp
      ultimately
      have "[ \<one>, \<ominus> b ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) b) pdivides p"
        using le_alg_mult_imp_pdivides[OF b UP.m_closed, of _ p] assms(2) in_carrier
              pirreducible_pow_pdivides_iff[OF carrier_is_subfield in_carrier' in_carrier, of p]
        by auto
      with \<open>a \<noteq> b\<close> show ?thesis
        using alg_mult_eq_count_roots[OF assms(2)] alg_multE(2)[OF b assms(2) not_zero] by auto
    next
      case True
      have "[ \<one>, \<ominus> a ] pdivides ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using dividesI[OF assms(2)] unfolding pdivides_def by auto
      with \<open>[ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p \<noteq> []\<close>
      have "alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) a \<ge> Suc 0"
        using alg_multE(2)[of a _ "Suc 0"] in_carrier assms by auto
      then obtain m where m: "alg_mult ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p) a = Suc m"
        using Suc_le_D by blast
      hence "([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> ([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> m)) pdivides
             ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using le_alg_mult_imp_pdivides[OF _ UP.m_closed, of a _ p]
              in_carrier assms UP.nat_pow_Suc2 by force
      hence "([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> m) pdivides p"
        using UP.mult_divides in_carrier assms(2)
        unfolding univ_poly_zero pdivides_def factor_def
        by (simp add: UP.m_assoc UP.m_lcancel univ_poly_zero)
      with \<open>a = b\<close> show ?thesis
        using alg_mult_eq_count_roots assms in_carrier UP.nat_pow_Suc2 
              alg_multE(2)[OF assms(1) _ not_zero] m
        by auto
    qed
  next
    fix b
    have not_zero: "[ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p \<noteq> []"
      using assms in_carrier univ_poly_zero[of R] UP.integral by auto

    show "count (add_mset a (roots p)) b \<le> count (roots ([\<one>, \<ominus> a] \<otimes>\<^bsub>poly_ring R\<^esub> p)) b"
    proof (cases "a = b")
      case True
      have "([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> ([ \<one>, \<ominus> a ] [^]\<^bsub>poly_ring R\<^esub> (alg_mult p a))) pdivides
            ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using UP.divides_mult[OF _ in_carrier] le_alg_mult_imp_pdivides[OF assms(1,2)] in_carrier assms
        by (auto simp add: pdivides_def)
      with \<open>a = b\<close> show ?thesis
        using alg_mult_eq_count_roots assms in_carrier UP.nat_pow_Suc2 
              alg_multE(2)[OF assms(1) _ not_zero]
        by auto
    next
      case False
      have "p pdivides ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> p)"
        using dividesI[OF in_carrier] UP.m_comm in_carrier assms unfolding pdivides_def by auto
      thus ?thesis
        using False pdivides_imp_roots_incl assms in_carrier not_zero
        by (simp add: subseteq_mset_def)
    qed
  qed
qed

lemma (in domain) not_empty_rootsE[elim]:
  assumes "p \<in> carrier (poly_ring R)" and "roots p \<noteq> {#}"
    and "\<And>a. \<lbrakk> a \<in> carrier R; a \<in># roots p;
               [ \<one>, \<ominus> a ] \<in> carrier (poly_ring R); [ \<one>, \<ominus> a ] pdivides p \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  from \<open>roots p \<noteq> {#}\<close> obtain a where "a \<in># roots p"
    by blast
  with \<open>p \<in> carrier (poly_ring R)\<close> have "[ \<one>, \<ominus> a ] pdivides p"
    and "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)" and "a \<in> carrier R"
    using is_root_imp_pdivides[of p] roots_mem_iff_is_root[of p] is_root_def[of p a]
    unfolding sym[OF univ_poly_carrier] polynomial_def by auto
  with \<open>a \<in># roots p\<close> show ?thesis
    using assms(3)[of a] by auto
qed

lemma (in field) associated_polynomials_imp_same_roots:
  assumes "p \<in> carrier (poly_ring R)" "p \<noteq> []" and "q \<in> carrier (poly_ring R)" "q \<noteq> []"
  shows "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots p + roots q"
proof -
  interpret UP: domain "poly_ring R"
    using univ_poly_is_domain[OF carrier_is_subring] .
  from assms show ?thesis
  proof (induction "degree p" arbitrary: p rule: less_induct)
    case less show ?case
    proof (cases "roots p = {#}")
      case True thus ?thesis
        using no_roots_imp_same_roots[of p q] less by simp
    next
      case False with \<open>p \<in> carrier (poly_ring R)\<close>
      obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and pdiv: "[ \<one>, \<ominus> a ] pdivides p"
          and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
        by blast
      show ?thesis
      proof (cases "degree p = 1")
        case True with \<open>p \<in> carrier (poly_ring R)\<close>
        obtain b c where p: "p = [ b, c ]" and b: "b \<in> carrier R" "b \<noteq> \<zero>" and c: "c \<in> carrier R"
          by auto
        with \<open>a \<in># roots p\<close> have roots: "roots p = {# a #}" and a: "\<ominus> a = inv b \<otimes> c" "a \<in> carrier R"
          and lead: "lead_coeff p = b" and const: "const_term p = c"
          using degree_one_imp_singleton_roots[of p] less(2) field_Units
          unfolding const_term_def by auto
        hence "(p \<otimes>\<^bsub>poly_ring R\<^esub> q) \<sim>\<^bsub>poly_ring R\<^esub> ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q)"
          using UP.mult_cong_l[OF degree_one_associatedI[OF carrier_is_subfield _ True]] less(2,4)
          by (auto simp add: a lead const)
        hence "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots ([ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q)"
          using associated_polynomials_imp_same_roots in_carrier less(2,4) unfolding a by simp
        thus ?thesis
          unfolding poly_mult_degree_one_monic_imp_same_roots[OF a(2) less(4,5)] roots by simp
      next
        case False
        from \<open>[ \<one>, \<ominus> a ] pdivides p\<close>
        obtain r where p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> r" and r: "r \<in> carrier (poly_ring R)"
          unfolding pdivides_def by auto
        with \<open>p \<noteq> []\<close> have not_zero: "r \<noteq> []"
          using in_carrier univ_poly_zero[of R "carrier R"] UP.integral_iff by auto
        with \<open>p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> r\<close> have deg: "degree p = Suc (degree r)"
          using poly_mult_degree_eq[OF carrier_is_subring, of _ r] in_carrier r
          unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
        with \<open>r \<noteq> []\<close> and \<open>q \<noteq> []\<close> have "r \<otimes>\<^bsub>poly_ring R\<^esub> q \<noteq> []"
          using in_carrier univ_poly_zero[of R "carrier R"] UP.integral less(4) r by auto
        hence "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = add_mset a (roots (r \<otimes>\<^bsub>poly_ring R\<^esub> q))"
          using poly_mult_degree_one_monic_imp_same_roots[OF a UP.m_closed[OF r less(4)]]
                UP.m_assoc[OF in_carrier r less(4)] p by auto
        also have " ... = add_mset a (roots r + roots q)"
          using less(1)[OF _ r not_zero less(4-5)] deg by simp
        also have " ... = (add_mset a (roots r)) + roots q"
          by simp
        also have " ... = roots p + roots q"
          using poly_mult_degree_one_monic_imp_same_roots[OF a r not_zero] p by simp 
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma (in field) size_roots_le_degree:
  assumes "p \<in> carrier (poly_ring R)" shows "size (roots p) \<le> degree p"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  case less show ?case
  proof (cases "roots p = {#}", simp)
    interpret UP: domain "poly_ring R"
      using univ_poly_is_domain[OF carrier_is_subring] .

    case False with \<open>p \<in> carrier (poly_ring R)\<close>
    obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and "[ \<one>, \<ominus> a ] pdivides p"
      and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
      by blast
    then obtain q where p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q" and q: "q \<in> carrier (poly_ring R)"
      unfolding pdivides_def by auto
    with \<open>a \<in># roots p\<close> have "p \<noteq> []"
      using degree_zero_imp_empty_roots[OF less(2)] by auto
    hence not_zero: "q \<noteq> []"
      using in_carrier univ_poly_zero[of R "carrier R"] UP.integral_iff p by auto
    hence "degree p = Suc (degree q)"
      using poly_mult_degree_eq[OF carrier_is_subring, of _ q] in_carrier p q
      unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
    with \<open>q \<noteq> []\<close> show ?thesis
      using poly_mult_degree_one_monic_imp_same_roots[OF a q] p less(1)[OF _ q]
      by (metis Suc_le_mono lessI size_add_mset) 
  qed
qed

lemma (in domain) pirreducible_roots:
  assumes "p \<in> carrier (poly_ring R)" and "pirreducible (carrier R) p" and "degree p \<noteq> 1"
  shows "roots p = {#}"
proof (rule ccontr)
  assume "roots p \<noteq> {#}" with \<open>p \<in> carrier (poly_ring R)\<close>
  obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and "[ \<one>, \<ominus> a ] pdivides p"
    and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
    by blast
  hence "[ \<one>, \<ominus> a ] \<sim>\<^bsub>poly_ring R\<^esub> p"
    using divides_pirreducible_condition[OF assms(2) in_carrier]
          univ_poly_units_incl[OF carrier_is_subring]
    unfolding pdivides_def by auto
  hence "degree p = 1"
    using associated_polynomials_imp_same_length[OF carrier_is_subring in_carrier assms(1)] by auto
  with \<open>degree p \<noteq> 1\<close> show False ..
qed

lemma (in field) pirreducible_imp_not_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "pirreducible (carrier R) p" and "degree p \<noteq> 1"
  shows "\<not> splitted p"
  using pirreducible_roots[of p] pirreducible_degree[OF carrier_is_subfield, of p] assms
  by (simp add: splitted_def)

lemma (in field)
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)"
    and "pirreducible (carrier R) p" and "degree p \<noteq> 1"
  shows "roots (p \<otimes>\<^bsub>poly_ring R\<^esub> q) = roots q"
  using no_roots_imp_same_roots[of p q] pirreducible_roots[of p] assms
  unfolding ring_irreducible_def univ_poly_zero by auto

lemma (in field) trivial_factors_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)"
    and "\<And>q. \<lbrakk> q \<in> carrier (poly_ring R); pirreducible (carrier R) q; q pdivides p \<rbrakk> \<Longrightarrow> degree q \<le> 1"
  shows "splitted p"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  interpret UP: principal_domain "poly_ring R"
    using univ_poly_is_principal[OF carrier_is_subfield] .
  case less show ?case
  proof (cases "degree p = 0", simp add: degree_zero_imp_splitted[OF less(2)])
    case False show ?thesis
    proof (cases "roots p = {#}")
      case True
      from \<open>degree p \<noteq> 0\<close> have "p \<notin> Units (poly_ring R)" and "p \<in> carrier (poly_ring R) - { [] }"
        using univ_poly_units'[OF carrier_is_subfield, of p] less(2) by auto
      then obtain q where "q \<in> carrier (poly_ring R)" "pirreducible (carrier R) q" and "q pdivides p"
        using UP.exists_irreducible_divisor[of p] unfolding univ_poly_zero pdivides_def by auto
      with \<open>degree p \<noteq> 0\<close> have "roots p \<noteq> {#}"
        using degree_one_imp_singleton_roots[OF _ , of q] less(3)[of q]
              pdivides_imp_roots_incl[OF _ less(2), of q]
              pirreducible_degree[OF carrier_is_subfield, of q]
        by force
      from \<open>roots p = {#}\<close> and \<open>roots p \<noteq> {#}\<close> have False
        by simp
      thus ?thesis ..
    next
      case False with \<open>p \<in> carrier (poly_ring R)\<close>
      obtain a where a: "a \<in> carrier R" and "a \<in># roots p" and "[ \<one>, \<ominus> a ] pdivides p"
        and in_carrier: "[ \<one>, \<ominus> a ] \<in> carrier (poly_ring R)"
        by blast
      then obtain q where p: "p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q" and q: "q \<in> carrier (poly_ring R)"
        unfolding pdivides_def by blast
      with \<open>degree p \<noteq> 0\<close> have "p \<noteq> []"
        by auto
      with \<open>p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q\<close> have "q \<noteq> []"
        using in_carrier q unfolding sym[OF univ_poly_zero[of R "carrier R"]] by auto
      with \<open>p = [ \<one>, \<ominus> a ] \<otimes>\<^bsub>poly_ring R\<^esub> q\<close> and \<open>p \<noteq> []\<close> have "degree p = Suc (degree q)"
        using poly_mult_degree_eq[OF carrier_is_subring] in_carrier q
        unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]] by auto
      moreover have "q pdivides p"
        using p dividesI[OF in_carrier] UP.m_comm[OF in_carrier q] by (auto simp add: pdivides_def)
      hence "degree r = 1" if "r \<in> carrier (poly_ring R)" and "pirreducible (carrier R) r"
        and "r pdivides q" for r
        using less(3)[OF that(1-2)] UP.divides_trans[OF _ _ that(1), of q p] that(3)
              pirreducible_degree[OF carrier_is_subfield that(1-2)] 
        by (auto simp add: pdivides_def)
      ultimately have "splitted q"
        using less(1)[OF _ q] by auto
      with \<open>degree p = Suc (degree q)\<close> and \<open>q \<noteq> []\<close> show ?thesis
        using poly_mult_degree_one_monic_imp_same_roots[OF a q]
        unfolding sym[OF p] splitted_def
        by simp
    qed
  qed
qed

lemma (in field) pdivides_imp_splitted:
  assumes "p \<in> carrier (poly_ring R)" and "q \<in> carrier (poly_ring R)" "q \<noteq> []" and "splitted q" 
  shows "p pdivides q \<Longrightarrow> splitted p"
proof (cases "p = []")
  case True thus ?thesis
    using degree_zero_imp_splitted[OF assms(1)] by simp
next
  interpret UP: principal_domain "poly_ring R"
    using univ_poly_is_principal[OF carrier_is_subfield] .

  case False
  assume "p pdivides q"
  then obtain b where b: "b \<in> carrier (poly_ring R)" and q: "q = p \<otimes>\<^bsub>poly_ring R\<^esub> b"
    unfolding pdivides_def by auto
  with \<open>q \<noteq> []\<close> have "p \<noteq> []" and "b \<noteq> []"
    using assms UP.integral_iff[of p b] unfolding sym[OF univ_poly_zero[of R "carrier R"]] by auto
  hence "degree p + degree b = size (roots p) + size (roots b)"
    using associated_polynomials_imp_same_roots[of p b] assms b q splitted_def
          poly_mult_degree_eq[OF carrier_is_subring,of p b]
    unfolding univ_poly_carrier sym[OF univ_poly_mult[of R "carrier R"]]
    by auto
  moreover have "size (roots p) \<le> degree p" and "size (roots b) \<le> degree b"
    using size_roots_le_degree assms(1) b by auto
  ultimately show ?thesis
    unfolding splitted_def by linarith
qed

lemma (in field) splitted_imp_trivial_factors:
  assumes "p \<in> carrier (poly_ring R)" "p \<noteq> []" and "splitted p"
  shows "\<And>q. \<lbrakk> q \<in> carrier (poly_ring R); pirreducible (carrier R) q; q pdivides p \<rbrakk> \<Longrightarrow> degree q = 1"
  using pdivides_imp_splitted[OF _ assms] pirreducible_imp_not_splitted
  by auto 


subsection \<open>Link between @{term \<open>(pmod)\<close>} and @{term rupture_surj}\<close>

lemma (in domain) rupture_surj_composed_with_pmod:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "q \<in> carrier (K[X])"
  shows "rupture_surj K p q = rupture_surj K p (q pmod p)"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .
  interpret Rupt: ring "Rupt K p"
    using assms by (simp add: UP.cgenideal_ideal ideal.quotient_is_ring rupture_def)

  let ?h = "rupture_surj K p"

  have "?h q = (?h p \<otimes>\<^bsub>Rupt K p\<^esub> ?h (q pdiv p)) \<oplus>\<^bsub>Rupt K p\<^esub> ?h (q pmod p)"
   and "?h (q pdiv p) \<in> carrier (Rupt K p)" "?h (q pmod p) \<in> carrier (Rupt K p)"
    using pdiv_pmod[OF assms(1,3,2)] long_division_closed[OF assms(1,3,2)] assms UP.m_closed
          ring_hom_memE[OF rupture_surj_hom(1)[OF subfieldE(1)[OF assms(1)] assms(2)]]
    by metis+
  moreover have "?h p = PIdl\<^bsub>K[X]\<^esub> p"
    using assms by (simp add: UP.a_rcos_zero UP.cgenideal_ideal UP.cgenideal_self)
  hence "?h p = \<zero>\<^bsub>Rupt K p\<^esub>"
    unfolding rupture_def FactRing_def by simp
  ultimately show ?thesis
    by simp
qed

corollary (in domain) rupture_carrier_as_pmod_image:
  assumes "subfield K R" and "p \<in> carrier (K[X])"
  shows "(rupture_surj K p) ` ((\<lambda>q. q pmod p) ` (carrier (K[X]))) = carrier (Rupt K p)"
    (is "?lhs = ?rhs")
proof
  have "(\<lambda>q. q pmod p) ` carrier (K[X]) \<subseteq> carrier (K[X])"
    using long_division_closed(2)[OF assms(1) _ assms(2)] by auto
  thus "?lhs \<subseteq> ?rhs"
    using ring_hom_memE(1)[OF rupture_surj_hom(1)[OF subfieldE(1)[OF assms(1)] assms(2)]] by auto
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix a assume "a \<in> carrier (Rupt K p)"
    then obtain q where "q \<in> carrier (K[X])" and "a = rupture_surj K p q"
      unfolding rupture_def FactRing_def A_RCOSETS_def' by auto
    thus "a \<in> ?lhs"
      using rupture_surj_composed_with_pmod[OF assms] by auto
  qed
qed

lemma (in domain) rupture_surj_inj_on:
  assumes "subfield K R" and "p \<in> carrier (K[X])"
  shows "inj_on (rupture_surj K p) ((\<lambda>q. q pmod p) ` (carrier (K[X])))"
proof (intro inj_onI)
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  fix a b
  assume "a \<in> (\<lambda>q. q pmod p) ` carrier (K[X])"
     and "b \<in> (\<lambda>q. q pmod p) ` carrier (K[X])"
  then obtain q s
    where q: "q \<in> carrier (K[X])" "a = q pmod p"
      and s: "s \<in> carrier (K[X])" "b = s pmod p"
    by auto
  moreover assume "rupture_surj K p a = rupture_surj K p b"
  ultimately have "q \<ominus>\<^bsub>K[X]\<^esub> s \<in> (PIdl\<^bsub>K[X]\<^esub> p)"
    using UP.quotient_eq_iff_same_a_r_cos[OF UP.cgenideal_ideal[OF assms(2)], of q s]
          rupture_surj_composed_with_pmod[OF assms] by auto
  hence "p pdivides (q \<ominus>\<^bsub>K[X]\<^esub> s)"
    using assms q(1) s(1) UP.to_contain_is_to_divide pdivides_iff_shell
    by (meson UP.cgenideal_ideal UP.cgenideal_minimal UP.minus_closed)
  thus "a = b"
    unfolding q s same_pmod_iff_pdivides[OF assms(1) q(1) s(1) assms(2)] .
qed


subsection \<open>Dimension\<close>

definition (in ring) exp_base :: "'a \<Rightarrow> nat \<Rightarrow> 'a list"
  where "exp_base x n = map (\<lambda>i. x [^] i) (rev [0..< n])"

lemma (in ring) exp_base_closed:
  assumes "x \<in> carrier R" shows "set (exp_base x n) \<subseteq> carrier R"
  using assms by (induct n) (auto simp add: exp_base_def)

lemma (in ring) exp_base_append:
  shows "exp_base x (n + m) = (map (\<lambda>i. x [^] i) (rev [n..< n + m])) @ exp_base x n"
  unfolding exp_base_def by (metis map_append rev_append upt_add_eq_append zero_le)

lemma (in ring) drop_exp_base:
  shows "drop n (exp_base x m) = exp_base x (m - n)"
proof -
  have ?thesis if "n > m"
    using that by (simp add: exp_base_def)
  moreover have ?thesis if "n \<le> m"
    using exp_base_append[of x "m - n" n] that by auto
  ultimately show ?thesis
    by linarith 
qed

lemma (in ring) combine_eq_eval:
  shows "combine Ks (exp_base x (length Ks)) = eval Ks x"
  unfolding exp_base_def by (induct Ks) (auto)

lemma (in domain) pmod_image_characterization:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "p \<noteq> []"
  shows "(\<lambda>q. q pmod p) ` carrier (K[X]) = { q \<in> carrier (K[X]). length q \<le> degree p }"
proof -
  interpret UP: principal_domain "K[X]"
    using univ_poly_is_principal[OF assms(1)] .

  show ?thesis
  proof (intro no_atp(10)[OF subsetI subsetI])
    fix q assume "q \<in> { q \<in> carrier (K[X]). length q \<le> degree p }"
    then have "q \<in> carrier (K[X])" and "length q \<le> degree p"
      by simp+

    show "q \<in> (\<lambda>q. q pmod p) ` carrier (K[X])"
    proof (cases "q = []")
      case True
      have "p pmod p = q"
        unfolding True pmod_zero_iff_pdivides[OF assms(1,2,2)]
        using assms(1-2) pdivides_iff_shell by auto
      thus ?thesis
        using assms(2) by blast 
    next
      case False
      with \<open>length q \<le> degree p\<close> have "degree q < degree p"
        using le_eq_less_or_eq by fastforce 
      with \<open>q \<in> carrier (K[X])\<close> show ?thesis
        using pmod_const(2)[OF assms(1) _ assms(2), of q] by (metis imageI) 
    qed
  next
    fix q assume "q \<in> (\<lambda>q. q pmod p) ` carrier (K[X])"
    then obtain q' where "q' \<in> carrier (K[X])" and "q = q' pmod p"
      by auto
    thus "q \<in> { q \<in> carrier (K[X]). length q \<le> degree p }"
      using long_division_closed(2)[OF assms(1) _ assms(2), of q']
            pmod_degree[OF assms(1) _ assms(2-3), of q']
      by auto
  qed
qed

lemma (in domain) Span_var_pow_base:
  assumes "subfield K R"
  shows "ring.Span (K[X]) (poly_of_const ` K) (ring.exp_base (K[X]) X n) =
         { q \<in> carrier (K[X]). length q \<le> n }" (is "?lhs = ?rhs")
proof -
  note subring = subfieldE(1)[OF assms]
  note subfield = univ_poly_subfield_of_consts[OF assms]

  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subring] .

  show ?thesis
  proof (intro no_atp(10)[OF subsetI subsetI])
    fix q assume "q \<in> { q \<in> carrier (K[X]). length q \<le> n }"
    then have q: "q \<in> carrier (K[X])" "length q \<le> n"
      by simp+

    let ?repl = "replicate (n - length q) \<zero>\<^bsub>K[X]\<^esub>"
    let ?map = "map poly_of_const q"
    let ?comb = "UP.combine"
    define Ks where "Ks = ?repl @ ?map"

    have "q = ?comb ?map (UP.exp_base X (length q))"
      using q eval_rewrite[OF subring q(1)] unfolding sym[OF UP.combine_eq_eval] by auto
    moreover from \<open>length q \<le> n\<close>
    have "?comb (?repl @ Ks) (UP.exp_base X n) =  ?comb Ks (UP.exp_base X (length q))"
      if "set Ks \<subseteq> carrier (K[X])" for Ks
      using UP.combine_prepend_replicate[OF that UP.exp_base_closed[OF var_closed(1)[OF subring]]]
      unfolding UP.drop_exp_base by auto

    moreover have "set ?map \<subseteq> carrier (K[X])"
      using map_norm_in_poly_ring_carrier[OF subring q(1)]
      unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    
    moreover have "?repl = map poly_of_const (replicate (n - length q) \<zero>)"
      unfolding poly_of_const_def univ_poly_zero by (induct "n - length q") (auto)
    hence "set ?repl \<subseteq> poly_of_const ` K"
      using subringE(2)[OF subring] by auto
    moreover from \<open>q \<in> carrier (K[X])\<close> have "set q \<subseteq> K"
      unfolding sym[OF univ_poly_carrier] polynomial_def by auto
    hence "set ?map \<subseteq> poly_of_const ` K"
      by auto

    ultimately have "q = ?comb Ks (UP.exp_base X n)" and "set Ks \<subseteq> poly_of_const ` K"
      by (simp add: Ks_def)+
    thus "q \<in> UP.Span (poly_of_const ` K) (UP.exp_base X n)"
      using UP.Span_eq_combine_set[OF subfield UP.exp_base_closed[OF var_closed(1)[OF subring]]] by auto
  next
    fix q assume "q \<in> UP.Span (poly_of_const ` K) (UP.exp_base X n)"
    thus "q \<in> { q \<in> carrier (K[X]). length q \<le> n }"
    proof (induction n arbitrary: q)
      case 0 thus ?case
        unfolding UP.exp_base_def by (auto simp add: univ_poly_zero)
    next
      case (Suc n)
      then obtain k p where k: "k \<in> K" and p: "p \<in> UP.Span (poly_of_const ` K) (UP.exp_base X n)"
        and q: "q = ((poly_of_const k) \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> n)) \<oplus>\<^bsub>K[X]\<^esub> p"
        unfolding UP.exp_base_def using UP.line_extension_mem_iff by auto
      have p_in_carrier: "p \<in> carrier (K[X])" and "length p \<le> n"
        using Suc(1)[OF p] by simp+
      moreover from \<open>k \<in> K\<close> have "poly_of_const k \<in> carrier (K[X])"
        unfolding poly_of_const_def sym[OF univ_poly_carrier] polynomial_def by auto
      ultimately have "q \<in> carrier (K[X])"
        unfolding q using var_pow_closed[OF subring, of n] by algebra

      moreover have "poly_of_const k = \<zero>\<^bsub>K[X]\<^esub>" if "k = \<zero>"
        unfolding poly_of_const_def that univ_poly_zero by simp
      with \<open>p \<in> carrier (K[X])\<close> have "q = p" if "k = \<zero>"
        unfolding q using var_pow_closed[OF subring, of n] that by algebra
      with \<open>length p \<le> n\<close> have "length q \<le> Suc n" if "k = \<zero>"
        using that by simp

      moreover have "poly_of_const k = [ k ]" if "k \<noteq> \<zero>"
        unfolding poly_of_const_def using that by simp
      hence monom: "monom k n = (poly_of_const k) \<otimes>\<^bsub>K[X]\<^esub> (X [^]\<^bsub>K[X]\<^esub> n)" if "k \<noteq> \<zero>"
        using that monom_eq_var_pow[OF subring] subfieldE(3)[OF assms] k by auto
      with \<open>p \<in> carrier (K[X])\<close> and \<open>k \<in> K\<close> and \<open>length p \<le> n\<close>
      have "length q = Suc n" if "k \<noteq> \<zero>"
        using that poly_add_length_eq[OF subring monom_is_polynomial[OF subring, of k n], of p]
        unfolding univ_poly_carrier monom_def univ_poly_add sym[OF monom[OF that]] q by auto  
      ultimately show ?case
        by (cases "k = \<zero>", auto)
    qed
  qed
qed

lemma (in domain) var_pow_base_independent:
  assumes "subfield K R"
  shows "ring.independent (K[X]) (poly_of_const ` K) (ring.exp_base (K[X]) X n)"
proof -
  note subring = subfieldE(1)[OF assms]
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subring] .

  show ?thesis
  proof (induction n, simp add: UP.exp_base_def)
    case (Suc n)
    have "X [^]\<^bsub>K[X]\<^esub> n \<notin> UP.Span (poly_of_const ` K) (ring.exp_base (K[X]) X n)"
      unfolding sym[OF unitary_monom_eq_var_pow[OF subring]] monom_def
                Span_var_pow_base[OF assms] by auto
    moreover have "X [^]\<^bsub>K[X]\<^esub> n # UP.exp_base X n = UP.exp_base X (Suc n)"
      unfolding UP.exp_base_def by simp
    ultimately show ?case
      using UP.li_Cons[OF var_pow_closed[OF subring, of n] _Suc] by simp
  qed
qed

lemma (in domain) bounded_degree_dimension:
  assumes "subfield K R"
  shows "ring.dimension (K[X]) n (poly_of_const ` K) { q \<in> carrier (K[X]). length q \<le> n }"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms]] .
  have "length (UP.exp_base X n) = n"
    unfolding UP.exp_base_def by simp
  thus ?thesis
    using UP.dimension_independent[OF var_pow_base_independent[OF assms], of n]
    unfolding Span_var_pow_base[OF assms] by simp
qed

corollary (in domain) univ_poly_infinite_dimension:
  assumes "subfield K R" shows "ring.infinite_dimension (K[X]) (poly_of_const ` K) (carrier (K[X]))"
proof (rule ccontr)
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms]] .

  assume "\<not> UP.infinite_dimension (poly_of_const ` K) (carrier (K[X]))"
  then obtain n where n: "UP.dimension n (poly_of_const ` K) (carrier (K[X]))"
    by blast
  show False
    using UP.independent_length_le_dimension[OF univ_poly_subfield_of_consts[OF assms] n
          var_pow_base_independent[OF assms, of "Suc n"]
          UP.exp_base_closed[OF var_closed(1)[OF subfieldE(1)[OF assms]]]]
    unfolding UP.exp_base_def by simp
qed

corollary (in domain) rupture_dimension:
  assumes "subfield K R" and "p \<in> carrier (K[X])" and "degree p > 0"
  shows "ring.dimension (Rupt K p) (degree p) ((rupture_surj K p) ` poly_of_const ` K) (carrier (Rupt K p))"
proof -
  interpret UP: domain "K[X]"
    using univ_poly_is_domain[OF subfieldE(1)[OF assms(1)]] .
  interpret Hom: ring_hom_ring "K[X]" "Rupt K p" "rupture_surj K p"
    using rupture_surj_hom(2)[OF subfieldE(1)[OF assms(1)] assms(2)] .

  have not_nil: "p \<noteq> []"
    using assms(3) by auto

  show ?thesis
    using Hom.inj_hom_dimension[OF univ_poly_subfield_of_consts rupture_one_not_zero
          rupture_surj_inj_on] bounded_degree_dimension assms
    unfolding sym[OF rupture_carrier_as_pmod_image[OF assms(1-2)]]
              pmod_image_characterization[OF assms(1-2) not_nil]
    by simp
qed

end