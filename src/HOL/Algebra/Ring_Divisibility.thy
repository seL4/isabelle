(* ************************************************************************** *)
(* Title:      Ring_Divisibility.thy                                          *)
(* Author:     Paulo Emílio de Vilhena                                        *)
(* ************************************************************************** *)

theory Ring_Divisibility
imports Ideal Divisibility QuotRing

begin

section \<open>Definitions ported from Multiplicative_Group.thy\<close>

definition mult_of :: "('a, 'b) ring_scheme \<Rightarrow> 'a monoid" where
  "mult_of R \<equiv> \<lparr> carrier = carrier R - { \<zero>\<^bsub>R\<^esub> }, mult = mult R, one = \<one>\<^bsub>R\<^esub> \<rparr>"

lemma carrier_mult_of [simp]: "carrier (mult_of R) = carrier R - { \<zero>\<^bsub>R\<^esub> }"
  by (simp add: mult_of_def)

lemma mult_mult_of [simp]: "mult (mult_of R) = mult R"
 by (simp add: mult_of_def)

lemma nat_pow_mult_of: "([^]\<^bsub>mult_of R\<^esub>) = (([^]\<^bsub>R\<^esub>) :: _ \<Rightarrow> nat \<Rightarrow> _)"
  by (simp add: mult_of_def fun_eq_iff nat_pow_def)

lemma one_mult_of [simp]: "\<one>\<^bsub>mult_of R\<^esub> = \<one>\<^bsub>R\<^esub>"
  by (simp add: mult_of_def)

lemmas mult_of_simps = carrier_mult_of mult_mult_of nat_pow_mult_of one_mult_of


section \<open>The Arithmetic of Rings\<close>

text \<open>In this section we study the links between the divisibility theory and that of rings\<close>


subsection \<open>Definitions\<close>

locale factorial_domain = domain + factorial_monoid "mult_of R"

locale noetherian_ring = ring +
  assumes finetely_gen: "ideal I R \<Longrightarrow> \<exists>A. A \<subseteq> carrier R \<and> finite A \<and> I = Idl A"

locale noetherian_domain = noetherian_ring + domain

locale principal_domain = domain +
  assumes principal_I: "ideal I R \<Longrightarrow> principalideal I R"

locale euclidean_domain = R?: domain R for R (structure) + fixes \<phi> :: "'a \<Rightarrow> nat"
  assumes euclidean_function:
  " \<lbrakk> a \<in> carrier R - { \<zero> }; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow>
   \<exists>q r. q \<in> carrier R \<and> r \<in> carrier R \<and> a = (b \<otimes> q) \<oplus> r \<and> ((r = \<zero>) \<or> (\<phi> r < \<phi> b))"

lemma (in domain) mult_of_is_comm_monoid: "comm_monoid (mult_of R)"
  apply (rule comm_monoidI)
  apply (auto simp add: integral_iff m_assoc)
  apply (simp add: m_comm)
  done

lemma (in domain) cancel_property: "comm_monoid_cancel (mult_of R)"
  by (rule comm_monoid_cancelI) (auto simp add: mult_of_is_comm_monoid m_rcancel)

sublocale domain < mult_of: comm_monoid_cancel "(mult_of R)"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  using cancel_property by auto

sublocale noetherian_domain \<subseteq> domain ..

sublocale principal_domain \<subseteq> domain ..

sublocale euclidean_domain \<subseteq> domain ..

lemma (in factorial_monoid) is_factorial_monoid: "factorial_monoid G" ..

sublocale factorial_domain < mult_of: factorial_monoid "mult_of R"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  using factorial_monoid_axioms by auto

lemma (in domain) factorial_domainI:
  assumes "\<And>a. a \<in> carrier (mult_of R) \<Longrightarrow>
               \<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs a"
      and "\<And>a fs fs'. \<lbrakk> a \<in> carrier (mult_of R);
                        set fs \<subseteq> carrier (mult_of R);
                        set fs' \<subseteq> carrier (mult_of R);
                        wfactors (mult_of R) fs a;
                        wfactors (mult_of R) fs' a \<rbrakk> \<Longrightarrow>
                        essentially_equal (mult_of R) fs fs'"
    shows "factorial_domain R"
  unfolding factorial_domain_def using mult_of.factorial_monoidI assms domain_axioms by auto

lemma (in domain) is_domain: "domain R" ..

lemma (in ring) noetherian_ringI:
  assumes "\<And>I. ideal I R \<Longrightarrow> \<exists>A. A \<subseteq> carrier R \<and> finite A \<and> I = Idl A"
  shows "noetherian_ring R"
  unfolding noetherian_ring_def noetherian_ring_axioms_def using assms is_ring by simp

lemma (in domain) noetherian_domainI:
  assumes "\<And>I. ideal I R \<Longrightarrow> \<exists>A. A \<subseteq> carrier R \<and> finite A \<and> I = Idl A"
  shows "noetherian_domain R"
  unfolding noetherian_domain_def noetherian_ring_def noetherian_ring_axioms_def
  using assms is_ring is_domain by simp

lemma (in domain) principal_domainI:
  assumes "\<And>I. ideal I R \<Longrightarrow> principalideal I R"
  shows "principal_domain R"
  unfolding principal_domain_def principal_domain_axioms_def using is_domain assms by auto

lemma (in domain) principal_domainI2:
  assumes "\<And>I. ideal I R \<Longrightarrow> \<exists>a \<in> carrier R. I = PIdl a"
  shows "principal_domain R"
  unfolding principal_domain_def principal_domain_axioms_def
  using is_domain assms principalidealI cgenideal_eq_genideal by auto

lemma (in domain) euclidean_domainI:
  assumes "\<And>a b. \<lbrakk> a \<in> carrier R - { \<zero> }; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow>
           \<exists>q r. q \<in> carrier R \<and> r \<in> carrier R \<and> a = (b \<otimes> q) \<oplus> r \<and> ((r = \<zero>) \<or> (\<phi> r < \<phi> b))"
  shows "euclidean_domain R \<phi>"
  using assms by unfold_locales auto


subsection \<open>Basic Properties\<close>

text \<open>Links between domains and commutative cancellative monoids\<close>

lemma (in cring) to_contain_is_to_divide:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "(PIdl b \<subseteq> PIdl a) = (a divides b)"
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
  shows "(a \<sim> b) = (PIdl a = PIdl b)"
  unfolding associated_def
  using to_contain_is_to_divide[OF assms]
        to_contain_is_to_divide[OF assms(2) assms(1)] by auto

lemma divides_mult_imp_divides [simp]: "a divides\<^bsub>(mult_of R)\<^esub> b \<Longrightarrow> a divides\<^bsub>R\<^esub> b"
  unfolding factor_def by auto

lemma (in domain) divides_imp_divides_mult [simp]:
  "\<lbrakk> a \<in> carrier R; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow>
     a divides\<^bsub>R\<^esub> b \<Longrightarrow> a divides\<^bsub>(mult_of R)\<^esub> b"
  unfolding factor_def using integral_iff by auto 

lemma assoc_mult_imp_assoc [simp]: "a \<sim>\<^bsub>(mult_of R)\<^esub> b \<Longrightarrow> a \<sim>\<^bsub>R\<^esub> b"
  unfolding associated_def by simp

lemma (in domain) assoc_imp_assoc_mult [simp]:
  "\<lbrakk> a \<in> carrier R - { \<zero> } ; b \<in> carrier R - { \<zero> } \<rbrakk> \<Longrightarrow>
     a \<sim>\<^bsub>R\<^esub> b \<Longrightarrow> a \<sim>\<^bsub>(mult_of R)\<^esub> b"
  unfolding associated_def by simp

lemma (in domain) Units_mult_eq_Units [simp]: "Units (mult_of R) = Units R"
  unfolding Units_def using insert_Diff integral_iff by auto

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

lemma (in domain) primeideal_iff_prime:
  assumes "p \<in> carrier (mult_of R)"
  shows "(primeideal (PIdl p) R) = (prime (mult_of R) p)"
proof
  show "prime (mult_of R) p \<Longrightarrow> primeideal (PIdl p) R"
  proof (rule primeidealI)
    assume A: "prime (mult_of R) p"
    show "ideal (PIdl p) R" and "cring R"
      using assms is_cring by (auto simp add: cgenideal_ideal)
    show "carrier R \<noteq> PIdl p"
    proof (rule ccontr)
      assume "\<not> carrier R \<noteq> PIdl p" hence "carrier R = PIdl p" by simp
      then obtain c where "c \<in> carrier R" "c \<otimes> p = \<one>"
        unfolding cgenideal_def using one_closed by (smt mem_Collect_eq)
      hence "p \<in> Units R" unfolding Units_def using m_comm assms by auto
      thus False using A unfolding prime_def by simp
    qed
    fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R" and ab: "a \<otimes> b \<in> PIdl p"
    thus "a \<in> PIdl p \<or> b \<in> PIdl p"
    proof (cases "a = \<zero> \<or> b = \<zero>")
      case True thus "a \<in> PIdl p \<or> b \<in> PIdl p" using ab a b by auto
    next
      { fix a assume "a \<in> carrier R" "p divides\<^bsub>mult_of R\<^esub> a"
        then obtain c where "c \<in> carrier R" "a = p \<otimes> c"
          unfolding factor_def by auto
        hence "a \<in> PIdl p" unfolding cgenideal_def using assms m_comm by auto }
      note aux_lemma = this

      case False hence "a \<noteq> \<zero> \<and> b \<noteq> \<zero>" by simp
      hence diff_zero: "a \<otimes> b \<noteq> \<zero>" using a b integral by blast
      then obtain c where c: "c \<in> carrier R" "a \<otimes> b = p \<otimes> c"
        using assms ab m_comm unfolding cgenideal_def by auto
      hence "c \<noteq> \<zero>" using c assms diff_zero by auto
      hence "p divides\<^bsub>(mult_of R)\<^esub> (a \<otimes> b)"
        unfolding factor_def using ab c by auto
      hence "p divides\<^bsub>(mult_of R)\<^esub> a \<or> p divides\<^bsub>(mult_of R)\<^esub> b"
        using A a b False unfolding prime_def by auto
      thus "a \<in> PIdl p \<or> b \<in> PIdl p" using a b aux_lemma by blast
    qed
  qed
next
  show "primeideal (PIdl p) R \<Longrightarrow> prime (mult_of R) p"
  proof -
    assume A: "primeideal (PIdl p) R" show "prime (mult_of R) p"
    proof (rule primeI)
      show "p \<notin> Units (mult_of R)"
      proof (rule ccontr)
        assume "\<not> p \<notin> Units (mult_of R)"
        hence p: "p \<in> Units (mult_of R)" by simp
        then obtain q where q: "q \<in> carrier R - { \<zero> }" "p \<otimes> q = \<one>" "q \<otimes> p = \<one>"
          unfolding Units_def apply simp by blast
        have "PIdl p = carrier R"
        proof
          show "PIdl p \<subseteq> carrier R"
            by (simp add: assms A additive_subgroup.a_subset ideal.axioms(1) primeideal.axioms(1))
        next
          show "carrier R \<subseteq> PIdl p"
          proof
            fix r assume r: "r \<in> carrier R" hence "r = (r \<otimes> q) \<otimes> p"
              using p q m_assoc unfolding Units_def by simp
            thus "r \<in> PIdl p" unfolding cgenideal_def using q r m_closed by blast
          qed
        qed
        moreover have "PIdl p \<noteq> carrier R" using A primeideal.I_notcarr by auto
        ultimately show False by simp 
      qed
    next
      { fix a assume "a \<in> PIdl p" and a: "a \<noteq> \<zero>"
        then obtain c where c: "c \<in> carrier R" "a = p \<otimes> c"
          unfolding cgenideal_def using m_comm assms by auto
        hence "c \<noteq> \<zero>" using assms a by auto
        hence "p divides\<^bsub>mult_of R\<^esub> a" unfolding factor_def using c by auto }
      note aux_lemma = this

      fix a b
      assume a: "a \<in> carrier (mult_of R)" and b: "b \<in> carrier (mult_of R)"
         and p: "p divides\<^bsub>mult_of R\<^esub> a \<otimes>\<^bsub>mult_of R\<^esub> b"
      then obtain c where "c \<in> carrier R" "a \<otimes> b = c \<otimes> p"
        unfolding factor_def using m_comm assms by auto
      hence "a \<otimes> b \<in> PIdl p" unfolding cgenideal_def by blast
      hence "a \<in> PIdl p \<or> b \<in> PIdl p" using A primeideal.I_prime[OF A] a b by auto
      thus "p divides\<^bsub>mult_of R\<^esub> a \<or> p divides\<^bsub>mult_of R\<^esub> b"
        using a b aux_lemma by auto
    qed
  qed
qed


subsection \<open>Noetherian Rings\<close>

lemma (in noetherian_ring) trivial_ideal_seq:
  assumes "\<And>i :: nat. ideal (I i) R"
    and "\<And>i j. i \<le> j \<Longrightarrow> I i \<subseteq> I j"
  shows "\<exists>n. \<forall>k. k \<ge> n \<longrightarrow> I k = I n"
proof -
  have "ideal (\<Union>i. I i) R"
  proof
    show "(\<Union>i. I i) \<subseteq> carrier (add_monoid R)"
      using additive_subgroup.a_subset assms(1) ideal.axioms(1) by fastforce
    have "\<one>\<^bsub>add_monoid R\<^esub> \<in> I 0"
      by (simp add: additive_subgroup.zero_closed assms(1) ideal.axioms(1))
    thus "\<one>\<^bsub>add_monoid R\<^esub> \<in> (\<Union>i. I i)" by blast
  next
    fix x y assume x: "x \<in> (\<Union>i. I i)" and y: "y \<in> (\<Union>i. I i)"
    then obtain i j where i: "x \<in> I i" and j: "y \<in> I j" by blast
    hence "inv\<^bsub>add_monoid R\<^esub> x \<in> I i"
      by (simp add: additive_subgroup.a_subgroup assms(1) ideal.axioms(1) subgroup.m_inv_closed)
    thus "inv\<^bsub>add_monoid R\<^esub> x \<in> (\<Union>i. I i)" by blast
    have "x \<otimes>\<^bsub>add_monoid R\<^esub> y \<in> I (max i j)"
      by (metis add.subgroupE(4) additive_subgroup.a_subgroup assms(1-2) i j ideal.axioms(1)
          max.cobounded1 max.cobounded2 monoid.select_convs(1) rev_subsetD)
    thus "x \<otimes>\<^bsub>add_monoid R\<^esub> y \<in> (\<Union>i. I i)" by blast
  next
    fix x a assume x: "x \<in> carrier R" and a: "a \<in> (\<Union>i. I i)"
    then obtain i where i: "a \<in> I i" by blast
    hence "x \<otimes> a \<in> I i" and "a \<otimes> x \<in> I i"
      by (simp_all add: assms(1) ideal.I_l_closed ideal.I_r_closed x)
    thus "x \<otimes> a \<in> (\<Union>i. I i)"
     and "a \<otimes> x \<in> (\<Union>i. I i)" by blast+
  qed

  then obtain S where S: "S \<subseteq> carrier R" "finite S" "(\<Union>i. I i) = Idl S"
    by (meson finetely_gen)
  hence "S \<subseteq> (\<Union>i. I i)"
    by (simp add: genideal_self)

  from \<open>finite S\<close> and \<open>S \<subseteq> (\<Union>i. I i)\<close> have "\<exists>n. S \<subseteq> I n"
  proof (induct S set: "finite")
    case empty thus ?case by simp 
  next
    case (insert x S')
    then obtain n m where m: "S' \<subseteq> I m" and n: "x \<in> I n" by blast
    hence "insert x S' \<subseteq> I (max m n)"
      by (meson assms(2) insert_subsetI max.cobounded1 max.cobounded2 rev_subsetD subset_trans) 
    thus ?case by blast
  qed
  then obtain n where "S \<subseteq> I n" by blast
  hence "I n = (\<Union>i. I i)"
    by (metis S(3) Sup_upper assms(1) genideal_minimal range_eqI subset_antisym)
  thus ?thesis
    by (metis (full_types) Sup_upper assms(2) range_eqI subset_antisym)
qed

lemma increasing_set_seq_iff:
  "(\<And>i. I i \<subseteq> I (Suc i)) == (\<And>i j. i \<le> j \<Longrightarrow> I i \<subseteq> I j)"
proof
  fix i j :: "nat"
  assume A: "\<And>i. I i \<subseteq> I (Suc i)" and "i \<le> j"
  then obtain k where k: "j = i + k"
    using le_Suc_ex by blast
  have "I i \<subseteq> I (i + k)"
    by (induction k) (simp_all add: A lift_Suc_mono_le)
  thus "I i \<subseteq> I j" using k by simp
next
  fix i assume "\<And>i j. i \<le> j \<Longrightarrow> I i \<subseteq> I j"
  thus "I i \<subseteq> I (Suc i)" by simp
qed


text \<open>Helper definition for the proofs below\<close>
fun S_builder :: "_ \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "S_builder R J 0 = {}" |
  "S_builder R J (Suc n) =
     (let diff = (J - Idl\<^bsub>R\<^esub> (S_builder R J n)) in
        (if diff \<noteq> {} then insert (SOME x. x \<in> diff) (S_builder R J n) else (S_builder R J n)))"

lemma S_builder_incl: "S_builder R J n \<subseteq> J"
  by (induction n) (simp_all, (metis (no_types, lifting) some_eq_ex subsetI))

lemma (in ring) S_builder_const1:
  assumes "ideal J R" "S_builder R J (Suc n) = S_builder R J n"
  shows "J = Idl (S_builder R J n)"
proof -
  have "J - Idl (S_builder R J n) = {}"
  proof (rule ccontr)
    assume "J - Idl (S_builder R J n) \<noteq> {}"
    hence "S_builder R J (Suc n) = insert (SOME x. x \<in> (J - Idl (S_builder R J n))) (S_builder R J n)"
      by simp
    moreover have "(S_builder R J n) \<subseteq> Idl (S_builder R J n)"
      using S_builder_incl assms(1)
      by (metis additive_subgroup.a_subset dual_order.trans genideal_self ideal.axioms(1))
    ultimately have "S_builder R J (Suc n) \<noteq> S_builder R J n"
      by (metis Diff_iff \<open>J - Idl S_builder R J n \<noteq> {}\<close> insert_subset some_in_eq)
    thus False using assms(2) by simp
  qed
  thus "J = Idl (S_builder R J n)"
    by (meson S_builder_incl[of R J n] Diff_eq_empty_iff assms(1) genideal_minimal subset_antisym)
qed

lemma (in ring) S_builder_const2:
  assumes "ideal J R" "Idl (S_builder R J (Suc n)) = Idl (S_builder R J n)"
  shows "S_builder R J (Suc n) = S_builder R J n"
proof (rule ccontr)
  assume "S_builder R J (Suc n) \<noteq> S_builder R J n"
  hence A: "J - Idl (S_builder R J n) \<noteq> {}" by auto
  hence "S_builder R J (Suc n) = insert (SOME x. x \<in> (J - Idl (S_builder R J n))) (S_builder R J n)" by simp
  then obtain x where x: "x \<in> (J - Idl (S_builder R J n))"
                  and S: "S_builder R J (Suc n) = insert x (S_builder R J n)"
    using A some_in_eq by blast
  have "x \<notin> Idl (S_builder R J n)" using x by blast
  moreover have "x \<in> Idl (S_builder R J (Suc n))"
    by (metis (full_types) S S_builder_incl additive_subgroup.a_subset
        assms(1) dual_order.trans genideal_self ideal.axioms(1) insert_subset)
  ultimately show False using assms(2) by blast
qed

lemma (in ring) trivial_ideal_seq_imp_noetherian:
  assumes "\<And>I. \<lbrakk> \<And>i :: nat. ideal (I i) R; \<And>i j. i \<le> j \<Longrightarrow> (I i) \<subseteq> (I j) \<rbrakk> \<Longrightarrow>
                 (\<exists>n. \<forall>k. k \<ge> n \<longrightarrow> I k = I n)"
  shows "noetherian_ring R"
proof -
  have "\<And>J. ideal J R \<Longrightarrow> \<exists>A. A \<subseteq> carrier R \<and> finite A \<and> J = Idl A"
  proof -
    fix J assume J: "ideal J R"
    define S and I where "S = (\<lambda>i. S_builder R J i)" and "I = (\<lambda>i. Idl (S i))"
    hence "\<And>i. ideal (I i) R"
      by (meson J S_builder_incl additive_subgroup.a_subset genideal_ideal ideal.axioms(1) subset_trans)
    moreover have "\<And>n. S n \<subseteq> S (Suc n)" using S_def by auto
    hence "\<And>n. I n \<subseteq> I (Suc n)"
      using S_builder_incl[of R J] J S_def I_def
      by (meson additive_subgroup.a_subset dual_order.trans ideal.axioms(1) subset_Idl_subset)
    ultimately obtain n where "\<And>k. k \<ge> n \<Longrightarrow> I k = I n"
      using assms increasing_set_seq_iff[of I] by (metis lift_Suc_mono_le) 
    hence "J = Idl (S_builder R J n)"
      using S_builder_const1[OF J, of n] S_builder_const2[OF J, of n] I_def S_def
      by (meson Suc_n_not_le_n le_cases)
    moreover have "finite (S_builder R J n)" by (induction n) (simp_all)
    ultimately show "\<exists>A. A \<subseteq> carrier R \<and> finite A \<and> J = Idl A"
      by (meson J S_builder_incl ideal.Icarr set_rev_mp subsetI)
  qed
  thus ?thesis
    by (simp add: local.ring_axioms noetherian_ring_axioms_def noetherian_ring_def) 
qed

lemma (in noetherian_domain) wfactors_exists:
  assumes "x \<in> carrier (mult_of R)"
  shows "\<exists>fs. set fs \<subseteq> carrier (mult_of R) \<and> wfactors (mult_of R) fs x" (is "?P x")
proof (rule ccontr)
  { fix x
    assume A: "x \<in> carrier (mult_of R)" "\<not> ?P x"
    have "\<exists>a. a \<in> carrier (mult_of R) \<and> properfactor (mult_of R) a x \<and> \<not> ?P a"
    proof -
      have "\<not> irreducible (mult_of R) x"
      proof (rule ccontr)
        assume "\<not> (\<not> irreducible (mult_of R) x)" hence "irreducible (mult_of R) x" by simp
        hence "wfactors (mult_of R) [ x ] x" unfolding wfactors_def using A by auto 
        thus False using A by auto
      qed
      moreover have  "\<not> x \<in> Units (mult_of R)"
        using A monoid.unit_wfactors[OF mult_of.monoid_axioms, of x] by auto
      ultimately
      obtain a where a: "a \<in> carrier (mult_of R)" "properfactor (mult_of R) a x" "a \<notin> Units (mult_of R)"
        unfolding irreducible_def by blast
      then obtain b where b: "b \<in> carrier (mult_of R)" "x = a \<otimes> b"
        unfolding properfactor_def by auto
      hence b_properfactor: "properfactor (mult_of R) b x"
        using A a mult_of.m_comm mult_of.properfactorI3 by blast
      have "\<not> ?P a \<or> \<not> ?P b"
      proof (rule ccontr)
        assume "\<not> (\<not> ?P a \<or> \<not> ?P b)"
        then obtain fs_a fs_b
          where fs_a: "wfactors (mult_of R) fs_a a" "set fs_a \<subseteq> carrier (mult_of R)"
            and fs_b: "wfactors (mult_of R) fs_b b" "set fs_b \<subseteq> carrier (mult_of R)" by blast
        hence "wfactors (mult_of R) (fs_a @ fs_b) x"
          using fs_a fs_b a b mult_of.wfactors_mult by simp
        moreover have "set (fs_a @ fs_b) \<subseteq> carrier (mult_of R)"
          using fs_a fs_b by auto
        ultimately show False using A by blast 
      qed
      thus ?thesis using a b b_properfactor mult_of.m_comm by blast
    qed } note aux_lemma = this
  
  assume A: "\<not> ?P x"

  define f :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    where "f = (\<lambda>a x. (a \<in> carrier (mult_of R) \<and> properfactor (mult_of R) a x \<and> \<not> ?P a))"
  define factor_seq :: "nat \<Rightarrow> 'a"
    where "factor_seq = rec_nat x (\<lambda>n y. (SOME a. f a y))"
  define I where "I = (\<lambda>i. PIdl (factor_seq i))"
  have factor_seq_props:
    "\<And>n. properfactor (mult_of R) (factor_seq (Suc n)) (factor_seq n) \<and> 
         (factor_seq n) \<in> carrier (mult_of R) \<and> \<not> ?P (factor_seq n)" (is "\<And>n. ?Q n")
  proof -
    fix n show "?Q n"
    proof (induct n)
      case 0
      have x: "factor_seq 0 = x"
        using factor_seq_def by simp
      hence "factor_seq (Suc 0) = (SOME a. f a x)"
        by (simp add: factor_seq_def)
      moreover have "\<exists>a. f a x"
        using aux_lemma[OF assms] A f_def by blast
      ultimately have "f (factor_seq (Suc 0)) x"
        using tfl_some by metis
      thus ?case using f_def A assms x by simp
    next
      case (Suc n)
      have "factor_seq (Suc n) = (SOME a. f a (factor_seq n))"
        by (simp add: factor_seq_def)
      moreover have "\<exists>a. f a (factor_seq n)"
        using aux_lemma f_def Suc.hyps by blast
      ultimately have Step0: "f (factor_seq (Suc n)) (factor_seq n)"
        using tfl_some by metis
      hence "\<exists>a. f a (factor_seq (Suc n))"
        using aux_lemma f_def by blast
      moreover have "factor_seq (Suc (Suc n)) = (SOME a. f a (factor_seq (Suc n)))"
        by (simp add: factor_seq_def)
      ultimately have Step1: "f (factor_seq (Suc (Suc n))) (factor_seq (Suc n))"
        using tfl_some by metis
      show ?case using Step0 Step1 f_def by simp
    qed
  qed

  have in_carrier: "\<And>i. factor_seq i \<in> carrier R"
    using factor_seq_props by simp 
  hence "\<And>i. ideal (I i) R"
    using I_def by (simp add: cgenideal_ideal)

  moreover
  have "\<And>i. factor_seq (Suc i) divides factor_seq i"
    using factor_seq_props unfolding properfactor_def by auto
  hence "\<And>i. PIdl (factor_seq i) \<subseteq> PIdl (factor_seq (Suc i))"
    using in_carrier to_contain_is_to_divide by simp
  hence "\<And>i j. i \<le> j \<Longrightarrow> I i \<subseteq> I j"
    using increasing_set_seq_iff[of I] unfolding I_def by auto

  ultimately obtain n where "\<And>k. n \<le> k \<Longrightarrow> I n = I k"
    by (metis trivial_ideal_seq)
  hence "I (Suc n) \<subseteq> I n" by (simp add: equalityD2)
  hence "factor_seq n divides factor_seq (Suc n)"
    using in_carrier I_def to_contain_is_to_divide by simp
  moreover have "\<not> factor_seq n divides\<^bsub>(mult_of R)\<^esub> factor_seq (Suc n)"
    using factor_seq_props[of n] unfolding properfactor_def by simp
  hence "\<not> factor_seq n divides factor_seq (Suc n)"
    using divides_imp_divides_mult[of "factor_seq n" "factor_seq (Suc n)"]
          in_carrier[of n] factor_seq_props[of "Suc n"] by auto
  ultimately show False by simp
qed


subsection \<open>Principal Domains\<close>

sublocale principal_domain \<subseteq> noetherian_domain
proof
  fix I assume "ideal I R"
  then obtain i where "i \<in> carrier R" "I = Idl { i }"
    using principal_I principalideal.generate by blast
  thus "\<exists>A \<subseteq> carrier R. finite A \<and> I = Idl A" by blast
qed

lemma (in principal_domain) irreducible_imp_maximalideal:
  assumes "p \<in> carrier (mult_of R)"
    and "irreducible (mult_of R) p"
  shows "maximalideal (PIdl p) R"
proof (rule maximalidealI)
  show "ideal (PIdl p) R"
    using assms(1) by (simp add: cgenideal_ideal)
next
  show "carrier R \<noteq> PIdl p"
  proof (rule ccontr)
    assume "\<not> carrier R \<noteq> PIdl p"
    hence "carrier R = PIdl p" by simp
    then obtain c where "c \<in> carrier R" "\<one> = c \<otimes> p"
      unfolding cgenideal_def using one_closed by auto
    hence "p \<in> Units R"
      unfolding Units_def using assms(1) m_comm by auto
    thus False
      using assms unfolding irreducible_def by auto
  qed
next
  fix J assume J: "ideal J R" "PIdl p \<subseteq> J" "J \<subseteq> carrier R"
  then obtain q where q: "q \<in> carrier R" "J = PIdl q"
    using principal_I[OF J(1)] cgenideal_eq_rcos is_cring
          principalideal.rcos_generate by (metis contra_subsetD)
  hence "q divides p"
    using to_contain_is_to_divide[of q p] using assms(1) J(1-2) by simp
  hence q_div_p: "q divides\<^bsub>(mult_of R)\<^esub> p"
    using assms(1) divides_imp_divides_mult[OF q(1), of p] by (simp add: \<open>q divides p\<close>) 
  show "J = PIdl p \<or> J = carrier R"
  proof (cases "q \<in> Units R")
    case True thus ?thesis
      by (metis J(1) Units_r_inv_ex cgenideal_self ideal.I_r_closed ideal.one_imp_carrier q(1) q(2))
  next
    case False
    have q_in_carr: "q \<in> carrier (mult_of R)"
      using q_div_p unfolding factor_def using assms(1) q(1) by auto
    hence "p divides\<^bsub>(mult_of R)\<^esub> q"
      using q_div_p False assms(2) unfolding irreducible_def properfactor_def by auto
    hence "p \<sim> q" using q_div_p
      unfolding associated_def by simp
    thus ?thesis using associated_iff_same_ideal[of p q] assms(1) q_in_carr q by simp
  qed
qed

corollary (in principal_domain) primeness_condition:
  assumes "p \<in> carrier (mult_of R)"
  shows "(irreducible (mult_of R) p) \<longleftrightarrow> (prime (mult_of R) p)"
proof
  show "irreducible (mult_of R) p \<Longrightarrow> prime (mult_of R) p"
    using irreducible_imp_maximalideal maximalideal_prime primeideal_iff_prime assms by auto
next
  show "prime (mult_of R) p \<Longrightarrow> irreducible (mult_of R) p"
    using mult_of.prime_irreducible by simp
qed

lemma (in principal_domain) domain_iff_prime:
  assumes "a \<in> carrier R - { \<zero> }"
  shows "domain (R Quot (PIdl a)) \<longleftrightarrow> prime (mult_of R) a"
  using quot_domain_iff_primeideal[of "PIdl a"] primeideal_iff_prime[of a]
        cgenideal_ideal[of a] assms by auto

lemma (in principal_domain) field_iff_prime:
  assumes "a \<in> carrier R - { \<zero> }"
  shows "field (R Quot (PIdl a)) \<longleftrightarrow> prime (mult_of R) a"
proof
  show "prime (mult_of R) a \<Longrightarrow> field  (R Quot (PIdl a))"
    using  primeness_condition[of a] irreducible_imp_maximalideal[of a]
           maximalideal.quotient_is_field[of "PIdl a" R] is_cring assms by auto
next
  show "field  (R Quot (PIdl a)) \<Longrightarrow> prime (mult_of R) a"
    unfolding field_def using domain_iff_prime[of a] assms by auto
qed

sublocale principal_domain < mult_of: primeness_condition_monoid "(mult_of R)"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  unfolding primeness_condition_monoid_def
            primeness_condition_monoid_axioms_def
  using mult_of.is_comm_monoid_cancel primeness_condition by auto

sublocale principal_domain < mult_of: factorial_monoid "(mult_of R)"
  rewrites "mult (mult_of R) = mult R"
       and "one  (mult_of R) = one R"
  apply (rule mult_of.factorial_monoidI)
  using mult_of.wfactors_unique wfactors_exists mult_of.is_comm_monoid_cancel by auto

sublocale principal_domain \<subseteq> factorial_domain
  unfolding factorial_domain_def using is_domain mult_of.is_factorial_monoid by simp

lemma (in principal_domain) ideal_sum_iff_gcd:
  assumes "a \<in> carrier (mult_of R)" "b \<in> carrier (mult_of R)" "d \<in> carrier (mult_of R)"
  shows "((PIdl a) <+>\<^bsub>R\<^esub> (PIdl b) = (PIdl d)) \<longleftrightarrow> (d gcdof\<^bsub>(mult_of R)\<^esub> a b)"
proof
  assume A: "(PIdl a) <+>\<^bsub>R\<^esub> (PIdl b) = (PIdl d)" show "d gcdof\<^bsub>(mult_of R)\<^esub> a b"
  proof -
    have "(PIdl a) \<subseteq> (PIdl d) \<and> (PIdl b) \<subseteq> (PIdl d)"
    using assms
      by (simp, metis Un_subset_iff cgenideal_ideal cgenideal_minimal local.ring_axioms
          ring.genideal_self ring.oneideal ring.union_genideal A)
    hence "d divides a \<and> d divides b"
      using assms apply simp
      using to_contain_is_to_divide[of d a] to_contain_is_to_divide[of d b] by auto
    hence "d divides\<^bsub>(mult_of R)\<^esub> a \<and> d divides\<^bsub>(mult_of R)\<^esub> b"
      using assms by simp

    moreover
    have "\<And>c. \<lbrakk> c \<in> carrier (mult_of R); c divides\<^bsub>(mult_of R)\<^esub> a; c divides\<^bsub>(mult_of R)\<^esub> b \<rbrakk> \<Longrightarrow>
                c divides\<^bsub>(mult_of R)\<^esub> d"
    proof -
      fix c assume c: "c \<in> carrier (mult_of R)"
               and "c divides\<^bsub>(mult_of R)\<^esub> a" "c divides\<^bsub>(mult_of R)\<^esub> b"
      hence "c divides a" "c divides b" by auto
      hence "(PIdl a) \<subseteq> (PIdl c) \<and> (PIdl b) \<subseteq> (PIdl c)"
        using to_contain_is_to_divide[of c a] to_contain_is_to_divide[of c b] c assms by simp
      hence "((PIdl a) <+>\<^bsub>R\<^esub> (PIdl b)) \<subseteq> (PIdl c)"
        using assms c
        by (simp, metis Un_subset_iff cgenideal_ideal cgenideal_minimal
                        Idl_subset_ideal oneideal union_genideal)
      hence incl: "(PIdl d) \<subseteq> (PIdl c)" using A by simp
      hence "c divides d"
        using c assms(3) apply simp
        using to_contain_is_to_divide[of c d] by blast
      thus "c divides\<^bsub>(mult_of R)\<^esub> d" using c assms(3) by simp
    qed

    ultimately show ?thesis unfolding isgcd_def by simp
  qed
next
  assume A:"d gcdof\<^bsub>mult_of R\<^esub> a b" show "PIdl a <+>\<^bsub>R\<^esub> PIdl b = PIdl d"
  proof
    have "d divides a" "d divides b"
      using A unfolding isgcd_def by auto
    hence "(PIdl a) \<subseteq> (PIdl d) \<and> (PIdl b) \<subseteq> (PIdl d)"
      using to_contain_is_to_divide[of d a] to_contain_is_to_divide[of d b] assms by simp
    thus "PIdl a <+>\<^bsub>R\<^esub> PIdl b \<subseteq> PIdl d" using assms
      by (simp, metis Un_subset_iff cgenideal_ideal cgenideal_minimal
                      Idl_subset_ideal oneideal union_genideal)
  next
    have "ideal ((PIdl a) <+>\<^bsub>R\<^esub> (PIdl b)) R"
      using assms by (simp add: cgenideal_ideal local.ring_axioms ring.add_ideals)
    then obtain c where c: "c \<in> carrier R" "(PIdl c) = (PIdl a) <+>\<^bsub>R\<^esub> (PIdl b)"
      using cgenideal_eq_genideal principal_I principalideal.generate by force
    hence "(PIdl a) \<subseteq> (PIdl c) \<and> (PIdl b) \<subseteq> (PIdl c)" using assms
      by (simp, metis Un_subset_iff cgenideal_ideal cgenideal_minimal
                      genideal_self oneideal union_genideal)
    hence "c divides a \<and> c divides b" using c(1) assms apply simp
      using to_contain_is_to_divide[of c a] to_contain_is_to_divide[of c b] by blast
    hence "c divides\<^bsub>(mult_of R)\<^esub> a \<and> c divides\<^bsub>(mult_of R)\<^esub> b"
      using assms(1-2) c(1) by simp

    moreover have neq_zero: "c \<noteq> \<zero>"
    proof (rule ccontr)
      assume "\<not> c \<noteq> \<zero>" hence "PIdl c = { \<zero> }"
        using cgenideal_eq_genideal genideal_zero by auto
      moreover have "\<one> \<otimes> a \<in> PIdl a \<and> \<zero> \<otimes> b \<in> PIdl b"
        unfolding cgenideal_def using assms one_closed zero_closed by blast
      hence "(\<one> \<otimes> a) \<oplus> (\<zero> \<otimes> b) \<in> (PIdl a) <+>\<^bsub>R\<^esub> (PIdl b)"
        unfolding set_add_def' by auto
      hence "a \<in> PIdl c"
        using c assms by simp
      ultimately show False
        using assms(1) by simp
    qed

    ultimately have "c divides\<^bsub>(mult_of R)\<^esub> d"
      using A c(1) unfolding isgcd_def by simp
    hence "(PIdl d) \<subseteq> (PIdl c)"
      using to_contain_is_to_divide[of c d] c(1) assms(3) by simp
    thus "PIdl d \<subseteq> PIdl a <+>\<^bsub>R\<^esub> PIdl b" using c by simp
  qed
qed

lemma (in principal_domain) bezout_identity:
  assumes "a \<in> carrier (mult_of R)" "b \<in> carrier (mult_of R)"
  shows "(PIdl a) <+>\<^bsub>R\<^esub> (PIdl b) = (PIdl (somegcd (mult_of R) a b))"
proof -
  have "(somegcd (mult_of R) a b) \<in> carrier (mult_of R)"
    using mult_of.gcd_exists[OF assms] by simp
  hence "\<And>x. x = somegcd (mult_of R) a b \<Longrightarrow> (PIdl a) <+>\<^bsub>R\<^esub> (PIdl b) = (PIdl x)"
    using mult_of.gcd_isgcd[OF assms] ideal_sum_iff_gcd[OF assms] by simp
  thus ?thesis
    using mult_of.gcd_exists[OF assms] by blast
qed


subsection \<open>Euclidean Domains\<close>

sublocale euclidean_domain \<subseteq> principal_domain
  unfolding principal_domain_def principal_domain_axioms_def
proof (auto)
  show "domain R" by (simp add: domain_axioms)
next
  fix I assume I: "ideal I R" show "principalideal I R"
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