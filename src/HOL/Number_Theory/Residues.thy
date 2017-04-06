(*  Title:      HOL/Number_Theory/Residues.thy
    Author:     Jeremy Avigad

An algebraic treatment of residue rings, and resulting proofs of
Euler's theorem and Wilson's theorem.
*)

section \<open>Residue rings\<close>

theory Residues
imports
  Cong
  "~~/src/HOL/Algebra/More_Group"
  "~~/src/HOL/Algebra/More_Ring"
  "~~/src/HOL/Algebra/More_Finite_Product"
  "~~/src/HOL/Algebra/Multiplicative_Group"
begin

definition QuadRes :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "QuadRes p a = (\<exists>y. ([y^2 = a] (mod p)))"

definition Legendre :: "int \<Rightarrow> int \<Rightarrow> int" where
  "Legendre a p = (if ([a = 0] (mod p)) then 0
    else if QuadRes p a then 1
    else -1)"

subsection \<open>A locale for residue rings\<close>

definition residue_ring :: "int \<Rightarrow> int ring"
where
  "residue_ring m =
    \<lparr>carrier = {0..m - 1},
     mult = \<lambda>x y. (x * y) mod m,
     one = 1,
     zero = 0,
     add = \<lambda>x y. (x + y) mod m\<rparr>"

locale residues =
  fixes m :: int and R (structure)
  assumes m_gt_one: "m > 1"
  defines "R \<equiv> residue_ring m"
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
    by (fastforce simp add: R_def residue_ring_def mod_add_right_eq ac_simps  intro!: abelian_groupI)
qed    

lemma comm_monoid: "comm_monoid R"
  unfolding R_def residue_ring_def
  apply (rule comm_monoidI)
    using m_gt_one  apply auto
  apply (metis mod_mult_right_eq mult.assoc mult.commute)
  apply (metis mult.commute)
  done

lemma cring: "cring R"
  apply (intro cringI abelian_group comm_monoid)
  unfolding R_def residue_ring_def
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
  unfolding R_def residue_ring_def by auto

lemma res_add_eq: "x \<oplus> y = (x + y) mod m"
  unfolding R_def residue_ring_def by auto

lemma res_mult_eq: "x \<otimes> y = (x * y) mod m"
  unfolding R_def residue_ring_def by auto

lemma res_zero_eq: "\<zero> = 0"
  unfolding R_def residue_ring_def by auto

lemma res_one_eq: "\<one> = 1"
  unfolding R_def residue_ring_def units_of_def by auto

lemma res_units_eq: "Units R = {x. 0 < x \<and> x < m \<and> coprime x m}"
  using m_gt_one
  unfolding Units_def R_def residue_ring_def
  apply auto
  apply (subgoal_tac "x \<noteq> 0")
  apply auto
  apply (metis invertible_coprime_int)
  apply (subst (asm) coprime_iff_invertible'_int)
  apply (auto simp add: cong_int_def mult.commute)
  done

lemma res_neg_eq: "\<ominus> x = (- x) mod m"
  using m_gt_one unfolding R_def a_inv_def m_inv_def residue_ring_def
  apply simp
  apply (rule the_equality)
  apply (simp add: mod_add_right_eq)
  apply (simp add: add.commute mod_add_right_eq)
  apply (metis add.right_neutral minus_add_cancel mod_add_right_eq mod_pos_pos_trivial)
  done

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
  unfolding R_def residue_ring_def
  by (auto simp add: mod_simps)

lemma mult_cong: "(x mod m) \<otimes> (y mod m) = (x * y) mod m"
  unfolding R_def residue_ring_def
  by (auto simp add: mod_simps)

lemma zero_cong: "\<zero> = 0"
  unfolding R_def residue_ring_def by auto

lemma one_cong: "\<one> = 1 mod m"
  using m_gt_one unfolding R_def residue_ring_def by auto

(* FIXME revise algebra library to use 1? *)
lemma pow_cong: "(x mod m) (^) n = x^n mod m"
  using m_gt_one
  apply (induct n)
  apply (auto simp add: nat_pow_def one_cong)
  apply (metis mult.commute mult_cong)
  done

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
  case True with assms show ?thesis
    by (auto simp add: res_units_eq gcd_red_int [symmetric])
next
  case False
  from assms have "0 < m" by simp
  with pos_mod_sign [of m a] have "0 \<le> a mod m" .
  with False have "0 < a mod m" by simp
  with assms show ?thesis
    by (auto simp add: res_units_eq gcd_red_int [symmetric] ac_simps)
qed

lemma res_eq_to_cong: "(a mod m) = (b mod m) \<longleftrightarrow> [a = b] (mod m)"
  unfolding cong_int_def by auto


text \<open>Simplifying with these will translate a ring equation in R to a congruence.\<close>
lemmas res_to_cong_simps = add_cong mult_cong pow_cong one_cong
    prod_cong sum_cong neg_cong res_eq_to_cong

text \<open>Other useful facts about the residue ring.\<close>
lemma one_eq_neg_one: "\<one> = \<ominus> \<one> \<Longrightarrow> m = 2"
  apply (simp add: res_one_eq res_neg_eq)
  apply (metis add.commute add_diff_cancel mod_mod_trivial one_add_one uminus_add_conv_diff
    zero_neq_one zmod_zminus1_eq_if)
  done

end


subsection \<open>Prime residues\<close>

locale residues_prime =
  fixes p :: nat and R (structure)
  assumes p_prime [intro]: "prime p"
  defines "R \<equiv> residue_ring (int p)"

sublocale residues_prime < residues p
  unfolding R_def residues_def
  using p_prime apply auto
  apply (metis (full_types) of_nat_1 of_nat_less_iff prime_gt_1_nat)
  done

context residues_prime
begin

lemma is_field: "field R"
proof -
  have "\<And>x. \<lbrakk>gcd x (int p) \<noteq> 1; 0 \<le> x; x < int p\<rbrakk> \<Longrightarrow> x = 0"
    by (metis dual_order.order_iff_strict gcd.commute less_le_not_le p_prime prime_imp_coprime prime_nat_int_transfer zdvd_imp_le)
  then show ?thesis
  apply (intro cring.field_intro2 cring)
  apply (auto simp add: res_carrier_eq res_one_eq res_zero_eq res_units_eq)
    done
qed

lemma res_prime_units_eq: "Units R = {1..p - 1}"
  apply (subst res_units_eq)
  apply auto
  apply (subst gcd.commute)
  apply (auto simp add: p_prime prime_imp_coprime_int zdvd_not_zless)
  done

end

sublocale residues_prime < field
  by (rule is_field)


section \<open>Test cases: Euler's theorem and Wilson's theorem\<close>

subsection \<open>Euler's theorem\<close>

text \<open>The definition of the totient function.\<close>

definition phi :: "int \<Rightarrow> nat"
  where "phi m = card {x. 0 < x \<and> x < m \<and> coprime x m}"

lemma phi_def_nat: "phi m = card {x. 0 < x \<and> x < nat m \<and> coprime x (nat m)}"
  unfolding phi_def
proof (rule bij_betw_same_card [of nat])
  show "bij_betw nat {x. 0 < x \<and> x < m \<and> coprime x m} {x. 0 < x \<and> x < nat m \<and> coprime x (nat m)}"
    apply (auto simp add: inj_on_def bij_betw_def image_def)
     apply (metis dual_order.irrefl dual_order.strict_trans leI nat_1 transfer_nat_int_gcd(1))
    apply (metis One_nat_def of_nat_0 of_nat_1 of_nat_less_0_iff int_nat_eq nat_int
        transfer_int_nat_gcd(1) of_nat_less_iff)
    done
qed
  
lemma prime_phi:
  assumes "2 \<le> p" "phi p = p - 1"
  shows "prime p"
proof -
  have *: "{x. 0 < x \<and> x < p \<and> coprime x p} = {1..p - 1}"
    using assms unfolding phi_def_nat
    by (intro card_seteq) fastforce+
  have False if **: "1 < x" "x < p" and "x dvd p" for x :: nat
  proof -
    from * have cop: "x \<in> {1..p - 1} \<Longrightarrow> coprime x p"
      by blast
    have "coprime x p"
      apply (rule cop)
      using ** apply auto
      done
    with \<open>x dvd p\<close> \<open>1 < x\<close> show ?thesis
      by auto
  qed
  then show ?thesis
    using \<open>2 \<le> p\<close>
    by (simp add: prime_nat_iff)
       (metis One_nat_def dvd_pos_nat nat_dvd_not_less nat_neq_iff not_gr0
              not_numeral_le_zero one_dvd)
qed

lemma phi_zero [simp]: "phi 0 = 0"
  unfolding phi_def by (auto simp add: card_eq_0_iff)

lemma phi_one [simp]: "phi 1 = 0"
  by (auto simp add: phi_def card_eq_0_iff)

lemma phi_leq: "phi x \<le> nat x - 1"
proof -
  have "phi x \<le> card {1..x - 1}"
    unfolding phi_def by (rule card_mono) auto
  then show ?thesis by simp
qed

lemma phi_nonzero:
  "phi x > 0" if "2 \<le> x"
proof -
  have "finite {y. 0 < y \<and> y < x}"
    by simp
  then have "finite {y. 0 < y \<and> y < x \<and> coprime y x}"
    by (auto intro: rev_finite_subset)
  moreover have "1 \<in> {y. 0 < y \<and> y < x \<and> coprime y x}"
    using that by simp
  ultimately have "card {y. 0 < y \<and> y < x \<and> coprime y x} \<noteq> 0"
    by auto
  then show ?thesis
    by (simp add: phi_def)
qed

lemma (in residues) phi_eq: "phi m = card (Units R)"
  by (simp add: phi_def res_units_eq)

lemma (in residues) euler_theorem1:
  assumes a: "gcd a m = 1"
  shows "[a^phi m = 1] (mod m)"
proof -
  have "a ^ phi m mod m = 1 mod m"
    by (metis assms finite_Units m_gt_one mod_in_res_units one_cong phi_eq pow_cong units_power_order_eq_one)
  then show ?thesis
    using res_eq_to_cong by blast
qed

text \<open>Outside the locale, we can relax the restriction \<open>m > 1\<close>.\<close>
lemma euler_theorem:
  assumes "m \<ge> 0"
    and "gcd a m = 1"
  shows "[a^phi m = 1] (mod m)"
proof (cases "m = 0 | m = 1")
  case True
  then show ?thesis by auto
next
  case False
  with assms show ?thesis
    by (intro residues.euler_theorem1, unfold residues_def, auto)
qed

lemma (in residues_prime) phi_prime: "phi p = nat p - 1"
  by (simp add: residues.phi_eq residues_axioms residues_prime.res_prime_units_eq residues_prime_axioms)

lemma phi_prime: "prime (int p) \<Longrightarrow> phi p = nat p - 1"
  by (simp add: residues_prime.intro residues_prime.phi_prime)

lemma fermat_theorem:
  fixes a :: int
  assumes "prime (int p)"
    and "\<not> p dvd a"
  shows "[a^(p - 1) = 1] (mod p)"
proof -
  from assms have "[a ^ phi p = 1] (mod p)"
    by (auto intro!: euler_theorem intro!: prime_imp_coprime_int[of p]
             simp: gcd.commute[of _ "int p"])
  also have "phi p = nat p - 1"
    by (rule phi_prime) (rule assms)
  finally show ?thesis
    by (metis nat_int)
qed

lemma fermat_theorem_nat:
  assumes "prime (int p)" and "\<not> p dvd a"
  shows "[a ^ (p - 1) = 1] (mod p)"
  using fermat_theorem [of p a] assms
  by (metis of_nat_1 of_nat_power transfer_int_nat_cong zdvd_int)


subsection \<open>Wilson's theorem\<close>

lemma (in field) inv_pair_lemma: "x \<in> Units R \<Longrightarrow> y \<in> Units R \<Longrightarrow>
    {x, inv x} \<noteq> {y, inv y} \<Longrightarrow> {x, inv x} \<inter> {y, inv y} = {}"
  apply auto
  apply (metis Units_inv_inv)+
  done

lemma (in residues_prime) wilson_theorem1:
  assumes a: "p > 2"
  shows "[fact (p - 1) = (-1::int)] (mod p)"
proof -
  let ?Inverse_Pairs = "{{x, inv x}| x. x \<in> Units R - {\<one>, \<ominus> \<one>}}"
  have UR: "Units R = {\<one>, \<ominus> \<one>} \<union> \<Union>?Inverse_Pairs"
    by auto
  have "(\<Otimes>i\<in>Units R. i) = (\<Otimes>i\<in>{\<one>, \<ominus> \<one>}. i) \<otimes> (\<Otimes>i\<in>\<Union>?Inverse_Pairs. i)"
    apply (subst UR)
    apply (subst finprod_Un_disjoint)
    apply (auto intro: funcsetI)
    using inv_one apply auto[1]
    using inv_eq_neg_one_eq apply auto
    done
  also have "(\<Otimes>i\<in>{\<one>, \<ominus> \<one>}. i) = \<ominus> \<one>"
    apply (subst finprod_insert)
    apply auto
    apply (frule one_eq_neg_one)
    using a apply force
    done
  also have "(\<Otimes>i\<in>(\<Union>?Inverse_Pairs). i) = (\<Otimes>A\<in>?Inverse_Pairs. (\<Otimes>y\<in>A. y))"
    apply (subst finprod_Union_disjoint)
    apply auto
    apply (metis Units_inv_inv)+
    done
  also have "\<dots> = \<one>"
    apply (rule finprod_one)
    apply auto
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
    apply (simp add: fact_prod)
    using assms
    apply (subst res_prime_units_eq)
    apply (simp add: int_prod zmod_int prod_int_eq)
    done
  finally have "fact (p - 1) mod p = \<ominus> \<one>" .
  then show ?thesis
    by (metis of_nat_fact Divides.transfer_int_nat_functions(2)
      cong_int_def res_neg_eq res_one_eq)
qed

lemma wilson_theorem:
  assumes "prime p"
  shows "[fact (p - 1) = - 1] (mod p)"
proof (cases "p = 2")
  case True
  then show ?thesis
    by (simp add: cong_int_def fact_prod)
next
  case False
  then show ?thesis
    using assms prime_ge_2_nat
    by (metis residues_prime.wilson_theorem1 residues_prime.intro le_eq_less_or_eq)
qed

text {*
  This result can be transferred to the multiplicative group of
  $\mathbb{Z}/p\mathbb{Z}$ for $p$ prime. *}

lemma mod_nat_int_pow_eq:
  fixes n :: nat and p a :: int
  assumes "a \<ge> 0" "p \<ge> 0"
  shows "(nat a ^ n) mod (nat p) = nat ((a ^ n) mod p)"
  using assms
  by (simp add: int_one_le_iff_zero_less nat_mod_distrib order_less_imp_le nat_power_eq[symmetric])

theorem residue_prime_mult_group_has_gen :
 fixes p :: nat
 assumes prime_p : "prime p"
 shows "\<exists>a \<in> {1 .. p - 1}. {1 .. p - 1} = {a^i mod p|i . i \<in> UNIV}"
proof -
  have "p\<ge>2" using prime_gt_1_nat[OF prime_p] by simp
  interpret R:residues_prime "p" "residue_ring p" unfolding residues_prime_def
    by (simp add: prime_p)
  have car: "carrier (residue_ring (int p)) - {\<zero>\<^bsub>residue_ring (int p)\<^esub>} =  {1 .. int p - 1}"
    by (auto simp add: R.zero_cong R.res_carrier_eq)
  obtain a where a:"a \<in> {1 .. int p - 1}"
         and a_gen:"{1 .. int p - 1} = {a(^)\<^bsub>residue_ring (int p)\<^esub>i|i::nat . i \<in> UNIV}"
    apply atomize_elim using field.finite_field_mult_group_has_gen[OF R.is_field]
    by (auto simp add: car[symmetric] carrier_mult_of)
  { fix x fix i :: nat assume x: "x \<in> {1 .. int p - 1}"
    hence "x (^)\<^bsub>residue_ring (int p)\<^esub> i = x ^ i mod (int p)" using R.pow_cong[of x i] by auto}
  note * = this
  have **:"nat ` {1 .. int p - 1} = {1 .. p - 1}" (is "?L = ?R")
  proof
    { fix n assume n: "n \<in> ?L"
      then have "n \<in> ?R" using `p\<ge>2` by force
    } thus "?L \<subseteq> ?R" by blast
    { fix n assume n: "n \<in> ?R"
      then have "n \<in> ?L" using `p\<ge>2` Set_Interval.transfer_nat_int_set_functions(2) by fastforce
    } thus "?R \<subseteq> ?L" by blast
  qed
  have "nat ` {a^i mod (int p) | i::nat. i \<in> UNIV} = {nat a^i mod p | i . i \<in> UNIV}" (is "?L = ?R")
  proof
    { fix x assume x: "x \<in> ?L"
      then obtain i where i:"x = nat (a^i mod (int p))" by blast
      hence "x = nat a ^ i mod p" using mod_nat_int_pow_eq[of a "int p" i] a `p\<ge>2` by auto
      hence "x \<in> ?R" using i by blast
    } thus "?L \<subseteq> ?R" by blast
    { fix x assume x: "x \<in> ?R"
      then obtain i where i:"x = nat a^i mod p" by blast
      hence "x \<in> ?L" using mod_nat_int_pow_eq[of a "int p" i] a `p\<ge>2` by auto
    } thus "?R \<subseteq> ?L" by blast
  qed
  hence "{1 .. p - 1} = {nat a^i mod p | i. i \<in> UNIV}"
    using * a a_gen ** by presburger
  moreover
  have "nat a \<in> {1 .. p - 1}" using a by force
  ultimately show ?thesis ..
qed

end
