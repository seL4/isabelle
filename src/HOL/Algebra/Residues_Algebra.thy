section \<open>The Residue Ring as a HOL-Algebra Structure\<close>

theory Residues_Algebra
  imports "HOL-Number_Theory.Cong" "HOL-Number_Theory.Totient"
    "HOL-Algebra.Multiplicative_Group"
begin

text \<open>
  The @{term residue_ring} construction and the @{text residues} and @{text residues_prime} locales,
  split out of \<open>Residues\<close> so that the residue-number-theory proper no longer depends on
  HOL-Algebra.  Nothing here is new: it is the record-based development as it stood, kept because a
  substantial body of work outside this theory --- \<open>Padic_Ints\<close>, \<open>Padic_Field\<close>,
  \<open>Crypto_Standards\<close>, \<open>Schoenhage_Strassen\<close>, \<open>Elliptic_Curves_Group_Law\<close> and others ---
  reasons inside these locales and about @{term "carrier R"}, and so cannot be served by a
  carrier-set replacement.

  The theorems of elementary residue number theory --- Euler, Fermat, Wilson, the existence of a
  primitive root, the bound on the number of roots --- are proved natively in \<open>Residues\<close> and are
  not repeated here.  What remains below are the locale-internal forms, which those developments
  extend.
\<close>

text \<open>The statement below is about a type-class ring, but its proof goes through the record-based
  ring, so it belongs with the HOL-Algebra material rather than with \<open>Residues\<close>.  \<open>Perfect_Fields\<close>
  uses it.\<close>

lemma (in ring_1) CHAR_dvd_CARD: "CHAR('a) dvd card (UNIV :: 'a set)"
proof (cases "card (UNIV :: 'a set) = 0")
  case False
  hence [intro]: "CHAR('a) > 0"
    by (simp add: card_eq_0_iff finite_imp_CHAR_pos)    
  define G where "G = \<lparr> carrier = (UNIV :: 'a set), monoid.mult = (+), one = (0 :: 'a) \<rparr>"
  define H where "H = (of_nat ` {..<CHAR('a)} :: 'a set)"
  interpret group G
  proof (rule groupI)
    fix x assume x: "x \<in> carrier G"
    show "\<exists>y\<in>carrier G. y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>"
      by (intro bexI[of _ "-x"]) (auto simp: G_def)
  qed (auto simp: G_def add_ac)

  interpret subgroup H G
  proof
    show "\<one>\<^bsub>G\<^esub> \<in> H"
      using False unfolding G_def H_def by force
  next
    fix x y :: 'a
    assume "x \<in> H" "y \<in> H"
    then obtain x' y' where [simp]: "x = of_nat x'" "y = of_nat y'"
      by (auto simp: H_def)
    have "x + y = of_nat ((x' + y') mod CHAR('a))"
      by (auto simp flip: of_nat_add simp: of_nat_eq_iff_cong_CHAR)
    moreover have "(x' + y') mod CHAR('a) < CHAR('a)"
      using H_def \<open>y \<in> H\<close> by fastforce
    ultimately show "x \<otimes>\<^bsub>G\<^esub> y \<in> H"
      by (auto simp: H_def G_def intro!: imageI)
  next
    fix x :: 'a
    assume x: "x \<in> H"
    then obtain x' where [simp]: "x = of_nat x'" and x': "x' < CHAR('a)"
      by (auto simp: H_def)
    have "CHAR('a) dvd x' + (CHAR('a) - x') mod CHAR('a)"
      using mod_eq_0_iff_dvd mod_if x' by fastforce
    hence "x + of_nat ((CHAR('a) - x') mod CHAR('a)) = 0"
      by (auto simp flip: of_nat_add simp: of_nat_eq_0_iff_char_dvd)
    moreover from this have "inv\<^bsub>G\<^esub> x = of_nat ((CHAR('a) - x') mod CHAR('a))"
      by (intro inv_equality) (auto simp: G_def add_ac)
    moreover have "of_nat ((CHAR('a) - x') mod CHAR('a)) \<in> H"
      unfolding H_def using \<open>CHAR('a) > 0\<close> by (intro imageI) auto
    ultimately show "inv\<^bsub>G\<^esub> x \<in> H" by force
  qed (auto simp: G_def H_def)

  have "card H dvd card (rcosets\<^bsub>G\<^esub> H) * card H"
    by simp
  also have "card (rcosets\<^bsub>G\<^esub> H) * card H = Coset.order G"
  proof (rule lagrange_finite)
    show "finite (carrier G)"
      using False card_ge_0_finite by (auto simp: G_def)
  qed (fact is_subgroup)
  finally have "card H dvd card (UNIV :: 'a set)"
    by (simp add: Coset.order_def G_def)
  also have "card H = card {..<CHAR('a)}"
    unfolding H_def by (intro card_image inj_onI) (auto simp: of_nat_eq_iff_cong_CHAR cong_def)
  finally show "CHAR('a) dvd card (UNIV :: 'a set)"
    by simp
qed auto

subsection \<open>A locale for residue rings\<close>

definition residue_ring :: "int \<Rightarrow> int ring"
  where
    "residue_ring m =
      \<lparr>carrier = {0..m - 1},
       monoid.mult = \<lambda>x y. (x * y) mod m,
       one = 1,
       zero = 0,
       add = \<lambda>x y. (x + y) mod m\<rparr>"

locale residues =
  fixes m :: int and R (structure)
  assumes m_gt_one: "m > 1"
  defines R_m_def: "R \<equiv> residue_ring m"
begin

lemma abelian_group: "abelian_group R"
proof -
  have "\<exists>y\<in>{0..m - 1}. (x + y) mod m = 0" if "0 \<le> x" "x < m" for x
  proof (cases "x = 0")
    case True
    with m_gt_one show ?thesis by simp
  next
    case False
    then have "(x + (m - x)) mod m = 0"
      by simp
    with m_gt_one that show ?thesis
      by (metis False atLeastAtMost_iff diff_ge_0_iff_ge diff_left_mono int_one_le_iff_zero_less less_le)
  qed
  with m_gt_one show ?thesis
    by (fastforce simp add: R_m_def residue_ring_def mod_add_right_eq ac_simps  intro!: abelian_groupI)
qed

lemma comm_monoid: "comm_monoid R"
proof -
  have "\<And>x y z. \<lbrakk>x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)"
    "\<And>x y. \<lbrakk>x \<in> carrier R; y \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
    unfolding R_m_def residue_ring_def
    by (simp_all add: algebra_simps mod_mult_right_eq)
  then show ?thesis
    unfolding R_m_def residue_ring_def
    by unfold_locales (use m_gt_one in simp_all)
qed

interpretation comm_monoid R
  using comm_monoid by blast

lemma cring: "cring R"
  apply (intro cringI abelian_group comm_monoid)
  unfolding R_m_def residue_ring_def
  apply (auto simp add: comm_semiring_class.distrib mod_add_eq mod_mult_left_eq)
  done

end

sublocale residues < cring
  by (rule cring)


context residues
begin

text \<open>
  These lemmas translate back and forth between internal and
  external concepts.
\<close>

lemma res_carrier_eq: "carrier R = {0..m - 1}"
  by (auto simp: R_m_def residue_ring_def)

lemma res_add_eq: "x \<oplus> y = (x + y) mod m"
  by (auto simp: R_m_def residue_ring_def)

lemma res_mult_eq: "x \<otimes> y = (x * y) mod m"
  by (auto simp: R_m_def residue_ring_def)

lemma res_zero_eq: "\<zero> = 0"
  by (auto simp: R_m_def residue_ring_def)

lemma res_one_eq: "\<one> = 1"
  by (auto simp: R_m_def residue_ring_def units_of_def)

lemma res_units_eq: "Units R = {x. 0 < x \<and> x < m \<and> coprime x m}" (is "_ = ?rhs")
proof
  show "Units R \<subseteq> ?rhs"
    using zero_less_mult_iff invertible_coprime 
    by (fastforce simp: Units_def R_m_def residue_ring_def)
next
  show "?rhs \<subseteq> Units R"
    unfolding Units_def R_m_def residue_ring_def 
    by (force simp add: cong_def coprime_iff_invertible'_int mult.commute)
qed

lemma res_neg_eq: "\<ominus> x = (- x) mod m"
proof -
  have "\<ominus> x = (THE y. 0 \<le> y \<and> y < m \<and> (x + y) mod m = 0 \<and> (y + x) mod m = 0)"
    by (simp add: R_m_def a_inv_def m_inv_def residue_ring_def)
  also have "\<dots> = (- x) mod m"
  proof -
    have "\<And>y. 0 \<le> y \<and> y < m \<and> (x + y) mod m = 0 \<and> (y + x) mod m = 0 \<Longrightarrow>
         y = - x mod m"
      by (metis minus_add_cancel mod_add_eq plus_int_code(1) zmod_trivial_iff)
    then show ?thesis
      by (intro the_equality) (use m_gt_one  in \<open>simp add: add.commute mod_add_right_eq\<close>)
  qed
  finally show ?thesis .
qed

lemma finite [iff]: "finite (carrier R)"
  by (simp add: res_carrier_eq)

lemma finite_Units [iff]: "finite (Units R)"
  by (simp add: finite_ring_finite_units)

text \<open>
  The function \<open>a \<mapsto> a mod m\<close> maps the integers to the
  residue classes. The following lemmas show that this mapping
  respects addition and multiplication on the integers.
\<close>

lemma mod_in_carrier [iff]: "a mod m \<in> carrier R"
  unfolding res_carrier_eq
  using insert m_gt_one by auto

lemma add_cong: "(x mod m) \<oplus> (y mod m) = (x + y) mod m"
  by (auto simp: R_m_def residue_ring_def mod_simps)

lemma mult_cong: "(x mod m) \<otimes> (y mod m) = (x * y) mod m"
  by (auto simp: R_m_def residue_ring_def mod_simps)

lemma zero_cong: "\<zero> = 0"
  by (auto simp: R_m_def residue_ring_def)

lemma one_cong: "\<one> = 1 mod m"
  using m_gt_one by (auto simp: R_m_def residue_ring_def)

(* FIXME revise algebra library to use 1? *)
lemma pow_cong: "(x mod m) [^] n = x^n mod m"
  using m_gt_one
proof (induct n)
  case 0
  then show ?case
    by (simp add: one_cong) 
next
  case (Suc n)
  then show ?case
    by (simp add: mult_cong power_commutes) 
qed

lemma neg_cong: "\<ominus> (x mod m) = (- x) mod m"
  by (metis mod_minus_eq res_neg_eq)

lemma (in residues) prod_cong: "finite A \<Longrightarrow> (\<Otimes>i\<in>A. (f i) mod m) = (\<Prod>i\<in>A. f i) mod m"
  by (induct set: finite) (auto simp: one_cong mult_cong)

lemma (in residues) sum_cong: "finite A \<Longrightarrow> (\<Oplus>i\<in>A. (f i) mod m) = (\<Sum>i\<in>A. f i) mod m"
  by (induct set: finite) (auto simp: zero_cong add_cong)

lemma mod_in_res_units [simp]:
  assumes "1 < m" and "coprime a m"
  shows "a mod m \<in> Units R"
proof (cases "a mod m = 0")
  case True
  with assms show ?thesis
    by (auto simp add: res_units_eq gcd_red_int [symmetric])
next
  case False
  from assms have "0 < m" by simp
  then have "0 \<le> a mod m" by (rule pos_mod_sign [of m a])
  with False have "0 < a mod m" by simp
  with assms show ?thesis
    by (auto simp add: res_units_eq gcd_red_int [symmetric] ac_simps)
qed

lemma res_eq_to_cong: "(a mod m) = (b mod m) \<longleftrightarrow> [a = b] (mod m)"
  by (auto simp: cong_def)


text \<open>Simplifying with these will translate a ring equation in R to a congruence.\<close>
lemmas res_to_cong_simps =
  add_cong mult_cong pow_cong one_cong
  prod_cong sum_cong neg_cong res_eq_to_cong

text \<open>Other useful facts about the residue ring.\<close>
lemma one_eq_neg_one: "\<one> = \<ominus> \<one> \<Longrightarrow> m = 2"
  using one_cong res_neg_eq res_one_eq zmod_zminus1_eq_if by fastforce

end


subsection \<open>Prime residues\<close>

locale residues_prime =
  fixes p :: nat and R (structure)
  assumes p_prime [intro]: "prime p"
  defines "R \<equiv> residue_ring (int p)"

sublocale residues_prime < residues p
proof
  show "1 < int p"
    using prime_gt_1_nat by auto
qed

context residues_prime
begin

lemma p_coprime_left:
  "coprime p a \<longleftrightarrow> \<not> p dvd a"
  using p_prime by (auto intro: prime_imp_coprime dest: coprime_common_divisor)

lemma p_coprime_right:
  "coprime a p  \<longleftrightarrow> \<not> p dvd a"
  using p_coprime_left [of a] by (simp add: ac_simps)

lemma p_coprime_left_int:
  "coprime (int p) a \<longleftrightarrow> \<not> int p dvd a"
  using p_prime by (auto intro: prime_imp_coprime dest: coprime_common_divisor)

lemma p_coprime_right_int:
  "coprime a (int p) \<longleftrightarrow> \<not> int p dvd a"
  using coprime_commute p_coprime_left_int by blast

lemma is_field: "field R"
proof -
  have "0 < x \<Longrightarrow> x < int p \<Longrightarrow> coprime (int p) x" for x
    by (rule prime_imp_coprime) (auto simp add: zdvd_not_zless)
  then show ?thesis
    by (intro cring.field_intro2 cring)
      (auto simp add: res_carrier_eq res_one_eq res_zero_eq res_units_eq ac_simps)
qed

lemma res_prime_units_eq: "Units R = {1..p - 1}"
  by (auto simp add: res_units_eq p_coprime_right_int zdvd_not_zless)

end

sublocale residues_prime < field
  by (rule is_field)

subsection \<open>Euler's theorem\<close>

lemma (in residues) totatives_eq:
  "totatives (nat m) = nat ` Units R"
proof -
  from m_gt_one have "\<bar>m\<bar> > 1"
    by simp
  then have "totatives (nat \<bar>m\<bar>) = nat ` abs ` Units R"
    by (auto simp add: totatives_def res_units_eq image_iff le_less)
      (use m_gt_one zless_nat_eq_int_zless in force)
  moreover have "\<bar>m\<bar> = m" "abs ` Units R = Units R"
    using m_gt_one by (auto simp add: res_units_eq image_iff)
  ultimately show ?thesis
    by simp
qed

lemma (in residues) totient_eq:
  "totient (nat m) = card (Units R)"
proof  -
  have *: "inj_on nat (Units R)"
    by (rule inj_onI) (auto simp add: res_units_eq)
  then show ?thesis
    by (simp add: totient_def totatives_eq card_image)
qed

lemma (in residues_prime) prime_totient_eq: "totient p = p - 1"
  using p_prime totient_prime by blast

lemma (in residues) euler_theorem:
  assumes "coprime a m"
  shows "[a ^ totient (nat m) = 1] (mod m)"
proof -
  have "a ^ totient (nat m) mod m = 1 mod m"
    by (metis assms finite_Units m_gt_one mod_in_res_units one_cong totient_eq pow_cong units_power_order_eq_one)
  then show ?thesis
    using res_eq_to_cong by blast
qed

subsection \<open>Wilson's theorem\<close>

lemma (in field) inv_pair_lemma: "x \<in> Units R \<Longrightarrow> y \<in> Units R \<Longrightarrow>
    {x, inv x} \<noteq> {y, inv y} \<Longrightarrow> {x, inv x} \<inter> {y, inv y} = {}"
  by auto


lemma (in residues_prime) wilson_theorem1:
  assumes a: "p > 2"
  shows "[fact (p - 1) = (-1::int)] (mod p)"
proof -
  let ?Inverse_Pairs = "{{x, inv x}| x. x \<in> Units R - {\<one>, \<ominus> \<one>}}"
  have UR: "Units R = {\<one>, \<ominus> \<one>} \<union> \<Union>?Inverse_Pairs"
    by auto
  have 11: "\<one> \<noteq> \<ominus> \<one>"
    using a one_eq_neg_one by force
  have "(\<Otimes>i\<in>Units R. i) = (\<Otimes>i\<in>{\<one>, \<ominus> \<one>}. i) \<otimes> (\<Otimes>i\<in>\<Union>?Inverse_Pairs. i)"
    apply (subst UR)
    apply (subst finprod_Un_disjoint)
    using inv_one inv_eq_neg_one_eq apply (auto intro!: funcsetI)+
    done
  also have "(\<Otimes>i\<in>{\<one>, \<ominus> \<one>}. i) = \<ominus> \<one>"
    by (simp add: 11)
  also have "(\<Otimes>i\<in>(\<Union>?Inverse_Pairs). i) = (\<Otimes>A\<in>?Inverse_Pairs. (\<Otimes>y\<in>A. y))"
    by (rule finprod_Union_disjoint) (auto simp: pairwise_def disjnt_def dest!: inv_eq_imp_eq)
  also have "\<dots> = \<one>"
    apply (rule finprod_one_eqI)
    apply clarsimp
    apply (subst finprod_insert)
        apply auto
    apply (metis inv_eq_self)
    done
  finally have "(\<Otimes>i\<in>Units R. i) = \<ominus> \<one>"
    by simp
  also have "(\<Otimes>i\<in>Units R. i) = (\<Otimes>i\<in>Units R. i mod p)"
    by (rule finprod_cong') (auto simp: res_units_eq)
  also have "\<dots> = (\<Prod>i\<in>Units R. i) mod p"
    by (rule prod_cong) auto
  also have "\<dots> = fact (p - 1) mod p"
    using assms
    by (simp add: res_prime_units_eq int_prod zmod_int prod_int_eq fact_prod)
  finally have "fact (p - 1) mod p = \<ominus> \<one>" .
  then show ?thesis
    by (simp add: cong_def res_neg_eq res_one_eq zmod_int)
qed

lemma mod_nat_int_pow_eq:
  fixes n :: nat and p a :: int
  shows "a \<ge> 0 \<Longrightarrow> p \<ge> 0 \<Longrightarrow> (nat a ^ n) mod (nat p) = nat ((a ^ n) mod p)"
  by (simp add: nat_mod_as_int)

end
