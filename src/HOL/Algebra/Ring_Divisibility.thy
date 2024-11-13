(*  Title:      HOL/Algebra/Ring_Divisibility.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Ring_Divisibility
imports Ideal Divisibility QuotRing Multiplicative_Group

begin

(* TEMPORARY ====================================================================== *)
definition mult_of :: "('a, 'b) ring_scheme \<Rightarrow> 'a monoid" where
  "mult_of R \<equiv> \<lparr> carrier = carrier R - {\<zero>\<^bsub>R\<^esub>}, mult = mult R, one = \<one>\<^bsub>R\<^esub>\<rparr>"

lemma carrier_mult_of [simp]: "carrier (mult_of R) = carrier R - {\<zero>\<^bsub>R\<^esub>}"
  by (simp add: mult_of_def)

lemma mult_mult_of [simp]: "mult (mult_of R) = mult R"
 by (simp add: mult_of_def)

lemma nat_pow_mult_of: "([^]\<^bsub>mult_of R\<^esub>) = (([^]\<^bsub>R\<^esub>) :: _ \<Rightarrow> nat \<Rightarrow> _)"
  by (simp add: mult_of_def fun_eq_iff nat_pow_def)

lemma one_mult_of [simp]: "\<one>\<^bsub>mult_of R\<^esub> = \<one>\<^bsub>R\<^esub>"
  by (simp add: mult_of_def)
(* ================================================================================ *)

section \<open>The Arithmetic of Rings\<close>

text \<open>In this section we study the links between the divisibility theory and that of rings\<close>


subsection \<open>Definitions\<close>

locale factorial_domain = domain + factorial_monoid "mult_of R"

locale noetherian_ring = ring +
  assumes finetely_gen: "ideal I R \<Longrightarrow> \<exists>A \<subseteq> carrier R. finite A \<and> I = Idl A"

locale noetherian_domain = noetherian_ring + domain

locale principal_domain = domain +
  assumes exists_gen: "ideal I R \<Longrightarrow> \<exists>a \<in> carrier R. I = PIdl a"

locale euclidean_domain =
  domain R for R (structure) + fixes \<phi> :: "'a \<Rightarrow> nat"
  assumes euclidean_function:
  " \<lbrakk> a \<in> carrier R - { \<zero> }; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow>
   \<exists>q r. q \<in> carrier R \<and> r \<in> carrier R \<and> a = (b \<otimes> q) \<oplus> r \<and> ((r = \<zero>) \<or> (\<phi> r < \<phi> b))"

definition ring_irreducible :: "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> bool" (\<open>ring'_irreducible\<index>\<close>)
  where "ring_irreducible\<^bsub>R\<^esub> a \<longleftrightarrow> (a \<noteq> \<zero>\<^bsub>R\<^esub>) \<and> (irreducible R a)"

definition ring_prime :: "('a, 'b) ring_scheme \<Rightarrow> 'a \<Rightarrow> bool" (\<open>ring'_prime\<index>\<close>)
  where "ring_prime\<^bsub>R\<^esub> a \<longleftrightarrow> (a \<noteq> \<zero>\<^bsub>R\<^esub>) \<and> (prime R a)"


subsection \<open>The cancellative monoid of a domain. \<close>

sublocale domain < mult_of: comm_monoid_cancel "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) =  one R"
  using m_comm m_assoc
  by (auto intro!: comm_monoid_cancelI comm_monoidI
         simp add: m_rcancel integral_iff)

sublocale factorial_domain < mult_of: factorial_monoid "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) =  one R"
  using factorial_monoid_axioms by auto

lemma (in ring) noetherian_ringI:
  assumes "\<And>I. ideal I R \<Longrightarrow> \<exists>A \<subseteq> carrier R. finite A \<and> I = Idl A"
  shows "noetherian_ring R"
  using assms by unfold_locales auto

lemma (in domain) euclidean_domainI:
  assumes "\<And>a b. \<lbrakk> a \<in> carrier R - { \<zero> }; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow>
           \<exists>q r. q \<in> carrier R \<and> r \<in> carrier R \<and> a = (b \<otimes> q) \<oplus> r \<and> ((r = \<zero>) \<or> (\<phi> r < \<phi> b))"
  shows "euclidean_domain R \<phi>"
  using assms by unfold_locales auto


subsection \<open>Passing from \<^term>\<open>R\<close> to \<^term>\<open>mult_of R\<close> and vice-versa. \<close>

lemma divides_mult_imp_divides [simp]: "a divides\<^bsub>(mult_of R)\<^esub> b \<Longrightarrow> a divides\<^bsub>R\<^esub> b"
  unfolding factor_def by auto

lemma (in domain) divides_imp_divides_mult [simp]:
  "\<lbrakk> a \<in> carrier R; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow> a divides\<^bsub>R\<^esub> b \<Longrightarrow> a divides\<^bsub>(mult_of R)\<^esub> b"
  unfolding factor_def using integral_iff by auto

lemma (in cring) divides_one:
  assumes "a \<in> carrier R"
  shows "a divides \<one> \<longleftrightarrow> a \<in> Units R"
  using assms m_comm unfolding factor_def Units_def by force

lemma (in ring) one_divides:
  assumes "a \<in> carrier R" shows "\<one> divides a"
  using assms unfolding factor_def by simp

lemma (in ring) divides_zero:
  assumes "a \<in> carrier R" shows "a divides \<zero>"
  using r_null[OF assms] unfolding factor_def by force

lemma (in ring) zero_divides:
  shows "\<zero> divides a \<longleftrightarrow> a = \<zero>"
  unfolding factor_def by auto

lemma (in domain) divides_mult_zero:
  assumes "a \<in> carrier R" shows "a divides\<^bsub>(mult_of R)\<^esub> \<zero> \<Longrightarrow> a = \<zero>"
  using integral[OF _ assms] unfolding factor_def by auto

lemma (in ring) divides_mult:
  assumes "a \<in> carrier R" "c \<in> carrier R"
  shows "a divides b \<Longrightarrow> (c \<otimes> a) divides (c \<otimes> b)"
  using m_assoc[OF assms(2,1)] unfolding factor_def by auto

lemma (in domain) mult_divides:
  assumes "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R - { \<zero> }"
  shows "(c \<otimes> a) divides (c \<otimes> b) \<Longrightarrow> a divides b"
  using assms m_assoc[of c] unfolding factor_def by (simp add: m_lcancel)

lemma (in domain) assoc_iff_assoc_mult:
  assumes "a \<in> carrier R" and "b \<in> carrier R"
  shows "a \<sim> b \<longleftrightarrow> a \<sim>\<^bsub>(mult_of R)\<^esub> b"
proof
  assume "a \<sim>\<^bsub>(mult_of R)\<^esub> b" thus "a \<sim> b"
    unfolding associated_def factor_def by auto
next
  assume A: "a \<sim> b"
  then obtain c1 c2
    where c1: "c1 \<in> carrier R" "a = b \<otimes> c1" and c2: "c2 \<in> carrier R" "b = a \<otimes> c2"
    unfolding associated_def factor_def by auto
  show "a \<sim>\<^bsub>(mult_of R)\<^esub> b"
  proof (cases "a = \<zero>")
    assume a: "a = \<zero>" then have b: "b = \<zero>"
      using c2 by auto
    show ?thesis
      unfolding associated_def factor_def a b by auto
  next
    assume a: "a \<noteq> \<zero>"
    hence b: "b \<noteq> \<zero>" and c1_not_zero: "c1 \<noteq> \<zero>"
      using c1 assms by auto
    hence c2_not_zero: "c2 \<noteq> \<zero>"
      using c2 assms by auto
    show ?thesis
      unfolding associated_def factor_def using c1 c2 c1_not_zero c2_not_zero a b by auto
  qed
qed

lemma (in domain) Units_mult_eq_Units [simp]: "Units (mult_of R) = Units R"
  unfolding Units_def using insert_Diff integral_iff by auto

lemma (in domain) ring_associated_iff:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<sim> b \<longleftrightarrow> (\<exists>u \<in> Units R. a = u \<otimes> b)"
proof (cases "a = \<zero>")
  assume [simp]: "a = \<zero>" show ?thesis
  proof
    assume "a \<sim> b" thus "\<exists>u \<in> Units R. a = u \<otimes> b"
      using zero_divides unfolding associated_def by force
  next
    assume "\<exists>u \<in> Units R. a = u \<otimes> b" then have "b = \<zero>"
      by (metis Units_closed Units_l_cancel \<open>a = \<zero>\<close> assms r_null)
    thus "a \<sim> b"
      using zero_divides[of \<zero>] by auto
  qed
next
  assume a: "a \<noteq> \<zero>" show ?thesis
  proof (cases "b = \<zero>")
    assume "b = \<zero>" thus ?thesis
      using assms a zero_divides[of a] r_null unfolding associated_def by blast
  next
    assume b: "b \<noteq> \<zero>"
    have "(\<exists>u \<in> Units R. a = u \<otimes> b) \<longleftrightarrow> (\<exists>u \<in> Units R. a = b \<otimes> u)"
      using m_comm[OF assms(2)] Units_closed by auto
    thus ?thesis
      using mult_of.associated_iff[of a b] a b assms
      unfolding assoc_iff_assoc_mult[OF assms] Units_mult_eq_Units
      by auto
  qed
qed

lemma (in domain) properfactor_mult_imp_properfactor:
  "\<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> properfactor (mult_of R) b a \<Longrightarrow> properfactor R b a"
proof -
  assume A: "a \<in> carrier R" "b \<in> carrier R" "properfactor (mult_of R) b a"
  then obtain c where c: "c \<in> carrier (mult_of R)" "a = b \<otimes> c"
    unfolding properfactor_def factor_def by auto
  have "a \<noteq> \<zero>"
  proof (rule ccontr)
    assume a: "\<not> a \<noteq> \<zero>"
    hence "b = \<zero>" using c A integral[of b c] by auto
    hence "b = a \<otimes> \<one>" using a A by simp
    hence "a divides\<^bsub>(mult_of R)\<^esub> b"
      unfolding factor_def by auto
    thus False using A unfolding properfactor_def by simp
  qed
  hence "b \<noteq> \<zero>"
    using c A integral_iff by auto
  thus "properfactor R b a"
    using A divides_imp_divides_mult[of a b] unfolding properfactor_def
    by (meson DiffI divides_mult_imp_divides empty_iff insert_iff)
qed

lemma (in domain) properfactor_imp_properfactor_mult:
  "\<lbrakk> a \<in> carrier R - { \<zero> }; b \<in> carrier R \<rbrakk> \<Longrightarrow> properfactor R b a \<Longrightarrow> properfactor (mult_of R) b a"
  unfolding properfactor_def factor_def by auto

lemma (in domain) properfactor_of_zero:
  assumes "b \<in> carrier R"
  shows "\<not> properfactor (mult_of R) b \<zero>" and "properfactor R b \<zero> \<longleftrightarrow> b \<noteq> \<zero>"
  using divides_mult_zero[OF assms] divides_zero[OF assms] unfolding properfactor_def by auto


subsection \<open>Irreducible\<close>

text \<open>The following lemmas justify the need for a definition of irreducible specific to rings:
      for \<^term>\<open>irreducible R\<close>, we need to suppose we are not in a field (which is plausible,
      but \<^term>\<open>\<not> field R\<close> is an assumption we want to avoid; for \<^term>\<open>irreducible (mult_of R)\<close>, zero
      is allowed. \<close>

lemma (in domain) zero_is_irreducible_mult:
  shows "irreducible (mult_of R) \<zero>"
  unfolding irreducible_def Units_def properfactor_def factor_def
  using integral_iff by fastforce

lemma (in domain) zero_is_irreducible_iff_field:
  shows "irreducible R \<zero> \<longleftrightarrow> field R"
proof
  assume irr: "irreducible R \<zero>"
  have "\<And>a. \<lbrakk> a \<in> carrier R; a \<noteq> \<zero> \<rbrakk> \<Longrightarrow> properfactor R a \<zero>"
    unfolding properfactor_def factor_def by (auto, metis r_null zero_closed)
  hence "carrier R - { \<zero> } = Units R"
    using irr unfolding irreducible_def by auto
  thus "field R"
    using field.intro[OF domain_axioms] unfolding field_axioms_def by simp
next
  assume field: "field R" show "irreducible R \<zero>"
    using field.field_Units[OF field]
    unfolding irreducible_def properfactor_def factor_def by blast
qed

lemma (in domain) irreducible_imp_irreducible_mult:
  "\<lbrakk> a \<in> carrier R; irreducible R a \<rbrakk> \<Longrightarrow> irreducible (mult_of R) a"
  using zero_is_irreducible_mult Units_mult_eq_Units properfactor_mult_imp_properfactor
  by (cases "a = \<zero>") (auto simp add: irreducible_def)

lemma (in domain) irreducible_mult_imp_irreducible:
  "\<lbrakk> a \<in> carrier R - { \<zero> }; irreducible (mult_of R) a \<rbrakk> \<Longrightarrow> irreducible R a"
    unfolding irreducible_def using properfactor_imp_properfactor_mult properfactor_divides by fastforce

lemma (in domain) ring_irreducibleE:
  assumes "r \<in> carrier R" and "ring_irreducible r"
  shows "r \<noteq> \<zero>" "irreducible R r" "irreducible (mult_of R) r" "r \<notin> Units R"
    and "\<And>a b. \<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> r = a \<otimes> b \<Longrightarrow> a \<in> Units R \<or> b \<in> Units R"
proof -
  show "irreducible (mult_of R) r" "irreducible R r"
    using assms irreducible_imp_irreducible_mult unfolding ring_irreducible_def by auto
  show "r \<noteq> \<zero>" "r \<notin> Units R"
    using assms unfolding ring_irreducible_def irreducible_def by auto
next
  fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R" and r: "r = a \<otimes> b"
  show "a \<in> Units R \<or> b \<in> Units R"
  proof (cases "properfactor R a r")
    assume "properfactor R a r" thus ?thesis
      using a assms(2) unfolding ring_irreducible_def irreducible_def by auto
  next
    assume not_proper: "\<not> properfactor R a r"
    hence "r divides a"
      using r b unfolding properfactor_def by auto
    then obtain c where c: "c \<in> carrier R" "a = r \<otimes> c"
      unfolding factor_def by auto
    have "\<one> = c \<otimes> b"
      using r c(1) b assms m_assoc m_lcancel[OF _ assms(1) one_closed m_closed[OF c(1) b]]
      unfolding c(2) ring_irreducible_def by auto
    thus ?thesis
      using c(1) b m_comm unfolding Units_def by auto
  qed
qed

lemma (in domain) ring_irreducibleI:
  assumes "r \<in> carrier R - { \<zero> }" "r \<notin> Units R"
    and "\<And>a b. \<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> r = a \<otimes> b \<Longrightarrow> a \<in> Units R \<or> b \<in> Units R"
  shows "ring_irreducible r"
  unfolding ring_irreducible_def
proof
  show "r \<noteq> \<zero>" using assms(1) by blast
next
  show "irreducible R r"
  proof (rule irreducibleI[OF assms(2)])
    fix a assume a: "a \<in> carrier R" "properfactor R a r"
    then obtain b where b: "b \<in> carrier R" "r = a \<otimes> b"
      unfolding properfactor_def factor_def by blast
    hence "a \<in> Units R \<or> b \<in> Units R"
      using assms(3)[OF a(1) b(1)] by simp
    thus "a \<in> Units R"
    proof (auto)
      assume "b \<in> Units R"
      hence "r \<otimes> inv b = a" and "inv b \<in> carrier R"
        using b a by (simp add: m_assoc)+
      thus ?thesis
        using a(2) unfolding properfactor_def factor_def by blast
    qed
  qed
qed

lemma (in domain) ring_irreducibleI':
  assumes "r \<in> carrier R - { \<zero> }" "irreducible (mult_of R) r"
  shows "ring_irreducible r"
  unfolding ring_irreducible_def
  using irreducible_mult_imp_irreducible[OF assms] assms(1) by auto


subsection \<open>Primes\<close>

lemma (in domain) zero_is_prime: "prime R \<zero>" "prime (mult_of R) \<zero>"
  using integral unfolding prime_def factor_def Units_def by auto

lemma (in domain) prime_eq_prime_mult:
  assumes "p \<in> carrier R"
  shows "prime R p \<longleftrightarrow> prime (mult_of R) p"
proof (cases "p = \<zero>", auto simp add: zero_is_prime)
  assume "p \<noteq> \<zero>" "prime R p" thus "prime (mult_of R) p"
    unfolding prime_def
    using divides_mult_imp_divides Units_mult_eq_Units mult_mult_of
    by (metis DiffD1 assms carrier_mult_of divides_imp_divides_mult)
next
  assume p: "p \<noteq> \<zero>" "prime (mult_of R) p" show "prime R p"
  proof (rule primeI)
    show "p \<notin> Units R"
      using p(2) Units_mult_eq_Units unfolding prime_def by simp
  next
    fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R" and dvd: "p divides a \<otimes> b"
    then obtain c where c: "c \<in> carrier R" "a \<otimes> b = p \<otimes> c"
      unfolding factor_def by auto
    show "p divides a \<or> p divides b"
    proof (cases "a \<otimes> b = \<zero>")
      case True thus ?thesis
        using integral[OF _ a b] c unfolding factor_def by force
    next
      case False
      hence "p divides\<^bsub>(mult_of R)\<^esub> (a \<otimes> b)"
        using divides_imp_divides_mult[OF assms _ dvd] m_closed[OF a b] by simp
      moreover have "a \<noteq> \<zero>" "b \<noteq> \<zero>" "c \<noteq> \<zero>"
        using False a b c p l_null integral_iff by (auto, simp add: assms)
      ultimately show ?thesis
        using a b p unfolding prime_def
        by (auto, metis Diff_iff divides_mult_imp_divides singletonD)
    qed
  qed
qed

lemma (in domain) ring_primeE:
  assumes "p \<in> carrier R" "ring_prime p"
  shows "p \<noteq> \<zero>" "prime (mult_of R) p" "prime R p"
  using assms prime_eq_prime_mult unfolding ring_prime_def by auto

lemma (in ring) ring_primeI: (* in ring only to avoid instantiating R *)
  assumes "p \<noteq> \<zero>" "prime R p" shows "ring_prime p"
  using assms unfolding ring_prime_def by auto

lemma (in domain) ring_primeI':
  assumes "p \<in> carrier R - { \<zero> }" "prime (mult_of R) p"
  shows "ring_prime p"
  using assms prime_eq_prime_mult unfolding ring_prime_def by auto


subsection \<open>Basic Properties\<close>

lemma (in cring) to_contain_is_to_divide:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "PIdl b \<subseteq> PIdl a \<longleftrightarrow> a divides b"
proof
  show "PIdl b \<subseteq> PIdl a \<Longrightarrow> a divides b"
  proof -
    assume "PIdl b \<subseteq> PIdl a"
    hence "b \<in> PIdl a"
      by (meson assms(2) local.ring_axioms ring.cgenideal_self subsetCE)
    thus ?thesis
      unfolding factor_def cgenideal_def using m_comm assms(1) by blast
  qed
  show "a divides b \<Longrightarrow> PIdl b \<subseteq> PIdl a"
  proof -
    assume "a divides b" then obtain c where c: "c \<in> carrier R" "b = c \<otimes> a"
      unfolding factor_def using m_comm[OF assms(1)] by blast
    show "PIdl b \<subseteq> PIdl a"
    proof
      fix x assume "x \<in> PIdl b"
      then obtain d where d: "d \<in> carrier R" "x = d \<otimes> b"
        unfolding cgenideal_def by blast
      hence "x = (d \<otimes> c) \<otimes> a"
        using c d m_assoc assms by simp
      thus "x \<in> PIdl a"
        unfolding cgenideal_def using m_assoc assms c d by blast
    qed
  qed
qed

lemma (in cring) associated_iff_same_ideal:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<sim> b \<longleftrightarrow> PIdl a = PIdl b"
  unfolding associated_def
  using to_contain_is_to_divide[OF assms]
        to_contain_is_to_divide[OF assms(2,1)] by auto

lemma (in cring) ideal_eq_carrier_iff:
  assumes "a \<in> carrier R"
  shows "carrier R = PIdl a \<longleftrightarrow> a \<in> Units R"
proof
  assume "carrier R = PIdl a"
  hence "\<one> \<in> PIdl a"
    by auto
  then obtain b where "b \<in> carrier R" "\<one> = a \<otimes> b" "\<one> = b \<otimes> a"
    unfolding cgenideal_def using m_comm[OF assms] by auto
  thus "a \<in> Units R"
    using assms unfolding Units_def by auto
next
  assume "a \<in> Units R"
  then have inv_a: "inv a \<in> carrier R" "inv a \<otimes> a = \<one>"
    by auto
  have "carrier R \<subseteq> PIdl a"
  proof
    fix b assume "b \<in> carrier R"
    hence "(b \<otimes> inv a) \<otimes> a = b" and "b \<otimes> inv a \<in> carrier R"
      using m_assoc[OF _ inv_a(1) assms] inv_a by auto
    thus "b \<in> PIdl a"
      unfolding cgenideal_def by force
  qed
  thus "carrier R = PIdl a"
    using assms by (simp add: cgenideal_eq_rcos r_coset_subset_G subset_antisym)
qed

lemma (in domain) primeideal_iff_prime:
  assumes "p \<in> carrier R - { \<zero> }"
  shows "primeideal (PIdl p) R \<longleftrightarrow> ring_prime p"
proof
  assume PIdl: "primeideal (PIdl p) R" show "ring_prime p"
  proof (rule ring_primeI)
    show "p \<noteq> \<zero>" using assms by simp
  next
    show "prime R p"
    proof (rule primeI)
      show "p \<notin> Units R"
        using ideal_eq_carrier_iff[of p] assms primeideal.I_notcarr[OF PIdl] by auto
    next
      fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R" and dvd: "p divides a \<otimes> b"
      hence "a \<otimes> b \<in> PIdl p"
        by (meson assms DiffD1 cgenideal_self contra_subsetD m_closed to_contain_is_to_divide)
      hence "a \<in> PIdl p \<or> b \<in> PIdl p"
        using primeideal.I_prime[OF PIdl a b] by simp
      thus "p divides a \<or> p divides b"
        using assms a b Idl_subset_ideal' cgenideal_eq_genideal to_contain_is_to_divide by auto
    qed
  qed
next
  assume prime: "ring_prime p" show "primeideal (PIdl p) R"
  proof (rule primeidealI[OF cgenideal_ideal cring_axioms])
    show "p \<in> carrier R" and "carrier R \<noteq> PIdl p"
      using ideal_eq_carrier_iff[of p] assms prime
      unfolding ring_prime_def prime_def by auto
  next
    fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R" "a \<otimes> b \<in> PIdl p"
    hence "p divides a \<otimes> b"
      using assms Idl_subset_ideal' cgenideal_eq_genideal to_contain_is_to_divide by auto
    hence "p divides a \<or> p divides b"
      using a b assms primeE[OF ring_primeE(3)[OF _ prime]] by auto
    thus "a \<in> PIdl p \<or> b \<in> PIdl p"
      using a b assms Idl_subset_ideal' cgenideal_eq_genideal to_contain_is_to_divide by auto
  qed
qed


subsection \<open>Noetherian Rings\<close>

lemma (in ring) chain_Union_is_ideal:
  assumes "subset.chain { I. ideal I R } C"
  shows "ideal (if C = {} then { \<zero> } else (\<Union>C)) R"
proof (cases "C = {}")
  case True thus ?thesis by (simp add: zeroideal)
next
  case False have "ideal (\<Union>C) R"
  proof (rule idealI[OF ring_axioms])
    show "subgroup (\<Union>C) (add_monoid R)"
    proof
      show "\<Union>C \<subseteq> carrier (add_monoid R)"
        using assms subgroup.subset[OF additive_subgroup.a_subgroup]
        unfolding pred_on.chain_def ideal_def by auto

      obtain I where I: "I \<in> C" "ideal I R"
        using False assms unfolding pred_on.chain_def by auto
      thus "\<one>\<^bsub>add_monoid R\<^esub> \<in> \<Union>C"
        using additive_subgroup.zero_closed[OF ideal.axioms(1)[OF I(2)]] by auto
    next
      fix x y assume "x \<in> \<Union>C" "y \<in> \<Union>C"
      then obtain I where I: "I \<in> C" "x \<in> I" "y \<in> I"
        using assms unfolding pred_on.chain_def by blast
      hence ideal: "ideal I R"
        using assms unfolding pred_on.chain_def by auto
      thus "x \<otimes>\<^bsub>add_monoid R\<^esub> y \<in> \<Union>C"
        using UnionI I additive_subgroup.a_closed unfolding ideal_def by fastforce

      show "inv\<^bsub>add_monoid R\<^esub> x \<in> \<Union>C"
        using UnionI I additive_subgroup.a_inv_closed ideal unfolding ideal_def a_inv_def by metis
    qed
  next
    fix a x assume a: "a \<in> \<Union>C" and x: "x \<in> carrier R"
    then obtain I where I: "ideal I R" "a \<in> I" and "I \<in> C"
      using assms unfolding pred_on.chain_def by auto
    thus "x \<otimes> a \<in> \<Union>C" and "a \<otimes> x \<in> \<Union>C"
      using ideal.I_l_closed[OF I x] ideal.I_r_closed[OF I x] by auto
  qed
  thus ?thesis
    using False by simp
qed

lemma (in noetherian_ring) ideal_chain_is_trivial:
  assumes "C \<noteq> {}" "subset.chain { I. ideal I R } C"
  shows "\<Union>C \<in> C"
proof -
  have aux_lemma: "\<exists>I. I \<in> C \<and> S \<subseteq> I" if "finite S" "S \<subseteq> \<Union>C" for S
    using that
  proof (induct S)
    case empty
    thus ?case using assms(1) by blast
  next
    case (insert s S)
    then obtain I where I: "I \<in> C" "S \<subseteq> I"
      by blast
    moreover obtain I' where I': "I' \<in> C" "s \<in> I'"
      using insert(4) by blast
    ultimately have "I \<subseteq> I' \<or> I' \<subseteq> I"
      using assms unfolding pred_on.chain_def by blast
    thus ?case
      using I I' by blast
  qed

  obtain S where S: "finite S" "S \<subseteq> carrier R" "\<Union>C = Idl S"
    using finetely_gen[OF chain_Union_is_ideal[OF assms(2)]] assms(1) by auto
  then obtain I where I: "I \<in> C" and "S \<subseteq> I"
    using aux_lemma[OF S(1)] genideal_self[OF S(2)] by blast
  hence "Idl S \<subseteq> I"
    using assms unfolding pred_on.chain_def
    by (metis genideal_minimal mem_Collect_eq rev_subsetD)
  hence "\<Union>C = I"
    using S(3) I by auto
  thus ?thesis
    using I by simp
qed

lemma (in ring) trivial_ideal_chain_imp_noetherian:
  assumes "\<And>C. \<lbrakk> C \<noteq> {}; subset.chain { I. ideal I R } C \<rbrakk> \<Longrightarrow> \<Union>C \<in> C"
  shows "noetherian_ring R"
proof (rule noetherian_ringI)
  fix I assume I: "ideal I R"
  have in_carrier: "I \<subseteq> carrier R" and add_subgroup: "additive_subgroup I R"
    using ideal.axioms(1)[OF I] additive_subgroup.a_subset by auto

  define S where "S = { Idl S' | S'. S' \<subseteq> I \<and> finite S' }"
  have "\<exists>M \<in> S. \<forall>S' \<in> S. M \<subseteq> S' \<longrightarrow> S' = M"
  proof (rule subset_Zorn)
    fix C assume C: "subset.chain S C"
    show "\<exists>U \<in> S. \<forall>S' \<in> C. S' \<subseteq> U"
    proof (cases "C = {}")
      case True
      have "{ \<zero> } \<in> S"
        using additive_subgroup.zero_closed[OF add_subgroup] genideal_zero
        by (auto simp add: S_def)
      thus ?thesis
        using True by auto
    next
      case False
      have "S \<subseteq> { I. ideal I R }"
        using additive_subgroup.a_subset[OF add_subgroup] genideal_ideal
        by (auto simp add: S_def)
      hence "subset.chain { I. ideal I R } C"
        using C unfolding pred_on.chain_def by auto
      then have "\<Union>C \<in> C"
        using assms False by simp
      thus ?thesis
        by (meson C Union_upper pred_on.chain_def subsetCE)
    qed
  qed
  then obtain M where M: "M \<in> S" "\<And>S'. \<lbrakk>S' \<in> S; M \<subseteq> S' \<rbrakk> \<Longrightarrow> S' = M"
    by auto
  then obtain S' where S': "S' \<subseteq> I" "finite S'" "M = Idl S'"
    by (auto simp add: S_def)
  hence "M \<subseteq> I"
    using I genideal_minimal by (auto simp add: S_def)
  moreover have "I \<subseteq> M"
  proof (rule ccontr)
    assume "\<not> I \<subseteq> M"
    then obtain a where a: "a \<in> I" "a \<notin> M"
      by auto
    have "M \<subseteq> Idl (insert a S')"
      using S' a(1) genideal_minimal[of "Idl (insert a S')" S']
            in_carrier genideal_ideal genideal_self
      by (meson insert_subset subset_trans)
    moreover have "Idl (insert a S') \<in> S"
      using a(1) S' by (auto simp add: S_def)
    ultimately have "M = Idl (insert a S')"
      using M(2) by auto
    hence "a \<in> M"
      using genideal_self S'(1) a (1) in_carrier by (meson insert_subset subset_trans)
    from \<open>a \<in> M\<close> and \<open>a \<notin> M\<close> show False by simp
  qed
  ultimately have "M = I" by simp
  thus "\<exists>A \<subseteq> carrier R. finite A \<and> I = Idl A"
    using S' in_carrier by blast
qed

lemma (in noetherian_domain) factorization_property:
  assumes "a \<in> carrier R - { \<zero> }" "a \<notin> Units R"
  shows "\<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs a" (is "?factorizable a")
proof (rule ccontr)
  assume a: "\<not> ?factorizable a"
  define S where "S = { PIdl r | r. r \<in> carrier R - { \<zero> } \<and> r \<notin> Units R \<and> \<not> ?factorizable r }"
  then obtain C where C: "subset.maxchain S C"
    using subset.Hausdorff by blast
  hence chain: "subset.chain S C"
    using pred_on.maxchain_def by blast
  moreover have "S \<subseteq> { I. ideal I R }"
    using cgenideal_ideal by (auto simp add: S_def)
  ultimately have "subset.chain { I. ideal I R } C"
    by (meson dual_order.trans pred_on.chain_def)
  moreover have "PIdl a \<in> S"
    using assms a by (auto simp add: S_def)
  hence "subset.chain S { PIdl a }"
    unfolding pred_on.chain_def by auto
  hence "C \<noteq> {}"
    using C unfolding pred_on.maxchain_def by auto
  ultimately have "\<Union>C \<in> C"
    using ideal_chain_is_trivial by simp
  hence "\<Union>C \<in> S"
    using chain unfolding pred_on.chain_def by auto
  then obtain r where r: "\<Union>C = PIdl r" "r \<in> carrier R - { \<zero> }" "r \<notin> Units R" "\<not> ?factorizable r"
    by (auto simp add: S_def)
  have "\<exists>p. p \<in> carrier R - { \<zero> } \<and> p \<notin> Units R \<and> \<not> ?factorizable p \<and> p divides r \<and> \<not> r divides p"
  proof -
    have "wfactors (mult_of R) [ r ] r" if "irreducible (mult_of R) r"
      using r(2) that unfolding wfactors_def by auto
    hence "\<not> irreducible (mult_of R) r"
      using r(2,4) by auto
    hence "\<not> ring_irreducible r"
      using ring_irreducibleE(3) r(2) by auto
    then obtain p1 p2
      where p1_p2: "p1 \<in> carrier R" "p2 \<in> carrier R" "r = p1 \<otimes> p2" "p1 \<notin> Units R" "p2 \<notin> Units R"
      using ring_irreducibleI[OF r(2-3)] by auto
    hence in_carrier: "p1 \<in> carrier (mult_of R)" "p2 \<in> carrier (mult_of R)"
      using r(2) by auto

    have "\<lbrakk> ?factorizable p1; ?factorizable p2 \<rbrakk> \<Longrightarrow> ?factorizable r"
      using mult_of.wfactors_mult[OF _ _ in_carrier] p1_p2(3) by (metis le_sup_iff set_append)
    hence "\<not> ?factorizable p1 \<or> \<not> ?factorizable p2"
      using r(4) by auto

    moreover
    have "\<And>p1 p2. \<lbrakk> p1 \<in> carrier R; p2 \<in> carrier R; r = p1 \<otimes> p2; r divides p1 \<rbrakk> \<Longrightarrow> p2 \<in> Units R"
    proof -
      fix p1 p2 assume A: "p1 \<in> carrier R" "p2 \<in> carrier R" "r = p1 \<otimes> p2" "r divides p1"
      then obtain c where c: "c \<in> carrier R" "p1 = r \<otimes> c"
        unfolding factor_def by blast
      hence "\<one> = c \<otimes> p2"
        using A m_lcancel[OF _ _ one_closed, of r "c \<otimes> p2"] r(2) by (auto, metis m_assoc m_closed)
      thus "p2 \<in> Units R"
        unfolding Units_def using c A(2) m_comm[OF c(1) A(2)] by auto
    qed
    hence "\<not> r divides p1" and "\<not> r divides p2"
      using p1_p2 m_comm[OF p1_p2(1-2)] by blast+

    ultimately show ?thesis
      using p1_p2 in_carrier by (metis carrier_mult_of dividesI' m_comm)
  qed
  then obtain p
    where p: "p \<in> carrier R - { \<zero> }" "p \<notin> Units R" "\<not> ?factorizable p" "p divides r" "\<not> r divides p"
    by blast
  hence "PIdl p \<in> S"
    unfolding S_def by auto
  moreover have "\<Union>C \<subset> PIdl p"
    using p r to_contain_is_to_divide unfolding r(1) by (metis Diff_iff psubsetI)
  ultimately have "subset.chain S (insert (PIdl p) C)" and "C \<subset> (insert (PIdl p) C)"
    unfolding pred_on.chain_def by (metis C psubsetE subset_maxchain_max, blast)
  thus False
    using C unfolding pred_on.maxchain_def by blast
qed

lemma (in noetherian_domain) exists_irreducible_divisor:
  assumes "a \<in> carrier R - { \<zero> }" and "a \<notin> Units R"
  obtains b where "b \<in> carrier R" and "ring_irreducible b" and "b divides a"
proof -
  obtain fs where set_fs: "set fs \<subseteq> carrier (mult_of R)" and "wfactors (mult_of R) fs a"
    using factorization_property[OF assms] by blast
  hence "a \<in> Units R" if "fs = []"
    using that assms(1) Units_cong assoc_iff_assoc_mult unfolding wfactors_def by (simp, blast)
  hence "fs \<noteq> []"
    using assms(2) by auto
  then obtain f' fs' where fs: "fs = f' # fs'"
    using list.exhaust by blast
  from \<open>wfactors (mult_of R) fs a\<close> have "f' divides a"
    using mult_of.wfactors_dividesI[OF _ set_fs] assms(1) unfolding fs by auto
  moreover from \<open>wfactors (mult_of R) fs a\<close> have "ring_irreducible f'" and "f' \<in> carrier R"
    using set_fs ring_irreducibleI'[of f'] unfolding wfactors_def fs by auto
  ultimately show thesis
    using that by blast
qed


subsection \<open>Principal Domains\<close>

sublocale principal_domain \<subseteq> noetherian_domain
proof
  fix I assume "ideal I R"
  then obtain i where "i \<in> carrier R" "I = Idl { i }"
    using exists_gen cgenideal_eq_genideal by auto
  thus "\<exists>A \<subseteq> carrier R. finite A \<and> I = Idl A"
    by blast
qed

lemma (in principal_domain) irreducible_imp_maximalideal:
  assumes "p \<in> carrier R"
    and "ring_irreducible p"
  shows "maximalideal (PIdl p) R"
proof (rule maximalidealI)
  show "ideal (PIdl p) R"
    using assms(1) by (simp add: cgenideal_ideal)
next
  show "carrier R \<noteq> PIdl p"
    using ideal_eq_carrier_iff[OF assms(1)] ring_irreducibleE(4)[OF assms] by auto
next
  fix J assume J: "ideal J R" "PIdl p \<subseteq> J" "J \<subseteq> carrier R"
  then obtain q where q: "q \<in> carrier R" "J = PIdl q"
    using exists_gen[OF J(1)] cgenideal_eq_rcos by metis
  hence "q divides p"
    using to_contain_is_to_divide[of q p] using assms(1) J(1-2) by simp
  then obtain r where r: "r \<in> carrier R" "p = q \<otimes> r"
    unfolding factor_def by auto
  hence "q \<in> Units R \<or> r \<in> Units R"
    using ring_irreducibleE(5)[OF assms q(1)] by auto
  thus "J = PIdl p \<or> J = carrier R"
  proof
    assume "q \<in> Units R" thus ?thesis
      using ideal_eq_carrier_iff[OF q(1)] q(2) by auto
  next
    assume "r \<in> Units R" hence "p \<sim> q"
      using assms(1) r q(1) associatedI2' by blast
    thus ?thesis
      unfolding associated_iff_same_ideal[OF assms(1) q(1)] q(2) by auto
  qed
qed

corollary (in principal_domain) primeness_condition:
  assumes "p \<in> carrier R"
  shows "ring_irreducible p \<longleftrightarrow> ring_prime p"
proof
  show "ring_irreducible p \<Longrightarrow> ring_prime p"
    using maximalideal_prime[OF irreducible_imp_maximalideal] ring_irreducibleE(1)
          primeideal_iff_prime assms by auto
next
  show "ring_prime p \<Longrightarrow> ring_irreducible p"
    using mult_of.prime_irreducible ring_primeI[of p] ring_irreducibleI' assms
    unfolding ring_prime_def prime_eq_prime_mult[OF assms] by auto
qed

lemma (in principal_domain) domain_iff_prime:
  assumes "a \<in> carrier R - { \<zero> }"
  shows "domain (R Quot (PIdl a)) \<longleftrightarrow> ring_prime a"
  using quot_domain_iff_primeideal[of "PIdl a"] primeideal_iff_prime[of a]
        cgenideal_ideal[of a] assms by auto

lemma (in principal_domain) field_iff_prime:
  assumes "a \<in> carrier R - { \<zero> }"
  shows "field (R Quot (PIdl a)) \<longleftrightarrow> ring_prime a"
proof
  show "ring_prime a \<Longrightarrow> field  (R Quot (PIdl a))"
    using  primeness_condition[of a] irreducible_imp_maximalideal[of a]
           maximalideal.quotient_is_field[of "PIdl a" R] is_cring assms by auto
next
  show "field  (R Quot (PIdl a)) \<Longrightarrow> ring_prime a"
    unfolding field_def using domain_iff_prime[of a] assms by auto
qed


sublocale principal_domain < mult_of: primeness_condition_monoid "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
    unfolding primeness_condition_monoid_def
              primeness_condition_monoid_axioms_def
proof (auto simp add: mult_of.is_comm_monoid_cancel)
  fix a assume a: "a \<in> carrier R" "a \<noteq> \<zero>" "irreducible (mult_of R) a"
  show "prime (mult_of R) a"
    using primeness_condition[OF a(1)] irreducible_mult_imp_irreducible[OF _ a(3)] a(1-2)
    unfolding ring_prime_def ring_irreducible_def prime_eq_prime_mult[OF a(1)] by auto
qed

sublocale principal_domain < mult_of: factorial_monoid "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  using mult_of.wfactors_unique factorization_property mult_of.is_comm_monoid_cancel
  by (auto intro!: mult_of.factorial_monoidI)

sublocale principal_domain \<subseteq> factorial_domain
  unfolding factorial_domain_def using domain_axioms mult_of.factorial_monoid_axioms by simp

lemma (in principal_domain) ideal_sum_iff_gcd:
  assumes "a \<in> carrier R" "b \<in> carrier R" "d \<in> carrier R"
  shows "PIdl d = PIdl a <+>\<^bsub>R\<^esub> PIdl b \<longleftrightarrow> d gcdof a b"
proof -
  have aux_lemma: "d gcdof a b"
    if in_carrier: "a \<in> carrier R" "b \<in> carrier R" "d \<in> carrier R"
    and ideal_eq: "PIdl d = PIdl a <+>\<^bsub>R\<^esub> PIdl b"
    for a b d
  proof (auto simp add: isgcd_def)
    have "a \<in> PIdl d" and "b \<in> PIdl d"
      using in_carrier(1-2)[THEN cgenideal_ideal] additive_subgroup.zero_closed[OF ideal.axioms(1)]
            in_carrier(1-2)[THEN cgenideal_self] in_carrier(1-2)
      unfolding ideal_eq set_add_def' by force+
    thus "d divides a" and "d divides b"
      using in_carrier(1,2)[THEN to_contain_is_to_divide[OF in_carrier(3)]]
            cgenideal_minimal[OF cgenideal_ideal[OF in_carrier(3)]] by simp+
  next
    fix c assume c: "c \<in> carrier R" "c divides a" "c divides b"
    hence "PIdl a \<subseteq> PIdl c" and "PIdl b \<subseteq> PIdl c"
      using to_contain_is_to_divide in_carrier by auto
    hence "PIdl a <+>\<^bsub>R\<^esub> PIdl b \<subseteq> PIdl c"
      by (metis Un_subset_iff c(1) in_carrier(1-2) cgenideal_ideal genideal_minimal union_genideal)
    thus "c divides d"
      using ideal_eq to_contain_is_to_divide[OF c(1) in_carrier(3)] by simp
  qed

  have "PIdl d = PIdl a <+>\<^bsub>R\<^esub> PIdl b \<Longrightarrow> d gcdof a b"
    using aux_lemma assms by simp

  moreover
  have "d gcdof a b \<Longrightarrow> PIdl d = PIdl a <+>\<^bsub>R\<^esub> PIdl b"
  proof -
    assume d: "d gcdof a b"
    obtain c where c: "c \<in> carrier R" "PIdl c = PIdl a <+>\<^bsub>R\<^esub> PIdl b"
      using exists_gen[OF add_ideals[OF assms(1-2)[THEN cgenideal_ideal]]] by blast
    hence "c gcdof a b"
      using aux_lemma assms by simp
    from \<open>d gcdof a b\<close> and \<open>c gcdof a b\<close> have "d \<sim> c"
      using assms c(1) by (simp add: associated_def isgcd_def)
    thus ?thesis
      using c(2) associated_iff_same_ideal[OF assms(3) c(1)] by simp
  qed

  ultimately show ?thesis by auto
qed

lemma (in principal_domain) bezout_identity:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "PIdl a <+>\<^bsub>R\<^esub> PIdl b = PIdl (somegcd R a b)"
proof -
  have "\<exists>d \<in> carrier R. d gcdof a b"
    using exists_gen[OF add_ideals[OF assms(1-2)[THEN cgenideal_ideal]]]
          ideal_sum_iff_gcd[OF assms(1-2)] by auto
  thus ?thesis
    using ideal_sum_iff_gcd[OF assms(1-2)] somegcd_def
    by (metis (no_types, lifting) tfl_some)
qed

subsection \<open>Euclidean Domains\<close>

sublocale euclidean_domain \<subseteq> principal_domain
  unfolding principal_domain_def principal_domain_axioms_def
proof (auto)
  show "domain R" by (simp add: domain_axioms)
next
  fix I assume I: "ideal I R" have "principalideal I R"
  proof (cases "I = { \<zero> }")
    case True thus ?thesis by (simp add: zeropideal)
  next
    case False hence A: "I - { \<zero> } \<noteq> {}"
      using I additive_subgroup.zero_closed ideal.axioms(1) by auto
    define phi_img :: "nat set" where "phi_img = (\<phi> ` (I - { \<zero> }))"
    hence "phi_img \<noteq> {}" using A by simp
    then obtain m where "m \<in> phi_img" "\<And>k. k \<in> phi_img \<Longrightarrow> m \<le> k"
      using exists_least_iff[of "\<lambda>n. n \<in> phi_img"] not_less by force
    then obtain a where a: "a \<in> I - { \<zero> }" "\<And>b. b \<in> I - { \<zero> } \<Longrightarrow> \<phi> a \<le> \<phi> b"
      using phi_img_def by blast
    have "I = PIdl a"
    proof (rule ccontr)
      assume "I \<noteq> PIdl a"
      then obtain b where b: "b \<in> I" "b \<notin> PIdl a"
        using I \<open>a \<in> I - {\<zero>}\<close> cgenideal_minimal by auto
      hence "b \<noteq> \<zero>"
        by (metis DiffD1 I a(1) additive_subgroup.zero_closed cgenideal_ideal ideal.Icarr ideal.axioms(1))
      then obtain q r
        where eucl_div: "q \<in> carrier R" "r \<in> carrier R" "b = (a \<otimes> q) \<oplus> r" "r = \<zero> \<or> \<phi> r < \<phi> a"
        using euclidean_function[of b a] a(1) b(1) ideal.Icarr[OF I] by auto
      hence "r = \<zero> \<Longrightarrow> b \<in> PIdl a"
        unfolding cgenideal_def using m_comm[of a] ideal.Icarr[OF I] a(1) by auto
      hence 1: "\<phi> r < \<phi> a \<and> r \<noteq> \<zero>"
        using eucl_div(4) b(2) by auto

      have "r = (\<ominus> (a \<otimes> q)) \<oplus> b"
        using eucl_div(1-3) a(1) b(1) ideal.Icarr[OF I] r_neg1 by auto
      moreover have "\<ominus> (a \<otimes> q) \<in> I"
        using eucl_div(1) a(1) I
        by (meson DiffD1 additive_subgroup.a_inv_closed ideal.I_r_closed ideal.axioms(1))
      ultimately have 2: "r \<in> I"
        using b(1) additive_subgroup.a_closed[OF ideal.axioms(1)[OF I]] by auto

      from 1 and 2 show False
        using a(2) by fastforce
    qed
    thus ?thesis
      by (meson DiffD1 I cgenideal_is_principalideal ideal.Icarr local.a(1))
  qed
  thus "\<exists>a \<in> carrier R. I = PIdl a"
    by (simp add: cgenideal_eq_genideal principalideal.generate)
qed


sublocale field \<subseteq> euclidean_domain R "\<lambda>_. 0"
proof (rule euclidean_domainI)
  fix a b
  let ?eucl_div = "\<lambda>q r. q \<in> carrier R \<and> r \<in> carrier R \<and> a = b \<otimes> q \<oplus> r \<and> (r = \<zero> \<or> 0 < 0)"

  assume a: "a \<in> carrier R - { \<zero> }" and b: "b \<in> carrier R - { \<zero> }"
  hence "a = b \<otimes> ((inv b) \<otimes> a) \<oplus> \<zero>"
    by (metis DiffD1 Units_inv_closed Units_r_inv field_Units l_one m_assoc r_zero)
  hence "?eucl_div _ ((inv b) \<otimes> a) \<zero>"
    using a b field_Units by auto
  thus "\<exists>q r. ?eucl_div _ q r"
    by blast
qed

end
