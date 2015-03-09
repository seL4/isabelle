(*  Title       : Fact.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    The integer version of factorial and other additions by Jeremy Avigad.
*)

section{*Factorial Function*}

theory Fact
imports Main
begin

class fact =
  fixes fact :: "'a \<Rightarrow> 'a"

instantiation nat :: fact
begin 

fun
  fact_nat :: "nat \<Rightarrow> nat"
where
  fact_0_nat: "fact_nat 0 = Suc 0"
| fact_Suc: "fact_nat (Suc x) = Suc x * fact x"

instance ..

end

(* definitions for the integers *)

instantiation int :: fact

begin 

definition
  fact_int :: "int \<Rightarrow> int"
where  
  "fact_int x = (if x >= 0 then int (fact (nat x)) else 0)"

instance proof qed

end


subsection {* Set up Transfer *}

lemma transfer_nat_int_factorial:
  "(x::int) >= 0 \<Longrightarrow> fact (nat x) = nat (fact x)"
  unfolding fact_int_def
  by auto


lemma transfer_nat_int_factorial_closure:
  "x >= (0::int) \<Longrightarrow> fact x >= 0"
  by (auto simp add: fact_int_def)

declare transfer_morphism_nat_int[transfer add return: 
    transfer_nat_int_factorial transfer_nat_int_factorial_closure]

lemma transfer_int_nat_factorial:
  "fact (int x) = int (fact x)"
  unfolding fact_int_def by auto

lemma transfer_int_nat_factorial_closure:
  "is_nat x \<Longrightarrow> fact x >= 0"
  by (auto simp add: fact_int_def)

declare transfer_morphism_int_nat[transfer add return: 
    transfer_int_nat_factorial transfer_int_nat_factorial_closure]


subsection {* Factorial *}

lemma fact_0_int [simp]: "fact (0::int) = 1"
  by (simp add: fact_int_def)

lemma fact_1_nat [simp]: "fact (1::nat) = 1"
  by simp

lemma fact_Suc_0_nat [simp]: "fact (Suc 0) = Suc 0"
  by simp

lemma fact_1_int [simp]: "fact (1::int) = 1"
  by (simp add: fact_int_def)

lemma fact_plus_one_nat: "fact ((n::nat) + 1) = (n + 1) * fact n"
  by simp

lemma fact_plus_one_int: 
  assumes "n >= 0"
  shows "fact ((n::int) + 1) = (n + 1) * fact n"
  using assms unfolding fact_int_def 
  by (simp add: nat_add_distrib algebra_simps int_mult)

lemma fact_reduce_nat: "(n::nat) > 0 \<Longrightarrow> fact n = n * fact (n - 1)"
  apply (subgoal_tac "n = Suc (n - 1)")
  apply (erule ssubst)
  apply (subst fact_Suc)
  apply simp_all
  done

lemma fact_reduce_int: "(n::int) > 0 \<Longrightarrow> fact n = n * fact (n - 1)"
  apply (subgoal_tac "n = (n - 1) + 1")
  apply (erule ssubst)
  apply (subst fact_plus_one_int)
  apply simp_all
  done

lemma fact_nonzero_nat [simp]: "fact (n::nat) \<noteq> 0"
  apply (induct n)
  apply (auto simp add: fact_plus_one_nat)
  done

lemma fact_nonzero_int [simp]: "n >= 0 \<Longrightarrow> fact (n::int) ~= 0"
  by (simp add: fact_int_def)

lemma fact_gt_zero_nat [simp]: "fact (n :: nat) > 0"
  by (insert fact_nonzero_nat [of n], arith)

lemma fact_gt_zero_int [simp]: "n >= 0 \<Longrightarrow> fact (n :: int) > 0"
  by (auto simp add: fact_int_def)

lemma fact_ge_one_nat [simp]: "fact (n :: nat) >= 1"
  by (insert fact_nonzero_nat [of n], arith)

lemma fact_ge_Suc_0_nat [simp]: "fact (n :: nat) >= Suc 0"
  by (insert fact_nonzero_nat [of n], arith)

lemma fact_ge_one_int [simp]: "n >= 0 \<Longrightarrow> fact (n :: int) >= 1"
  apply (auto simp add: fact_int_def)
  apply (subgoal_tac "1 = int 1")
  apply (erule ssubst)
  apply (subst zle_int)
  apply auto
  done

lemma dvd_fact_nat [rule_format]: "1 <= m \<longrightarrow> m <= n \<longrightarrow> m dvd fact (n::nat)"
  apply (induct n)
  apply force
  apply (auto simp only: fact_Suc)
  apply (subgoal_tac "m = Suc n")
  apply (erule ssubst)
  apply (rule dvd_triv_left)
  apply auto
  done

lemma dvd_fact_int [rule_format]: "1 <= m \<longrightarrow> m <= n \<longrightarrow> m dvd fact (n::int)"
  apply (case_tac "1 <= n")
  apply (induct n rule: int_ge_induct)
  apply (auto simp add: fact_plus_one_int)
  apply (subgoal_tac "m = i + 1")
  apply auto
  done

lemma interval_plus_one_nat: "(i::nat) <= j + 1 \<Longrightarrow> 
  {i..j+1} = {i..j} Un {j+1}"
  by auto

lemma interval_Suc: "i <= Suc j \<Longrightarrow> {i..Suc j} = {i..j} Un {Suc j}"
  by auto

lemma interval_plus_one_int: "(i::int) <= j + 1 \<Longrightarrow> {i..j+1} = {i..j} Un {j+1}"
  by auto

lemma fact_altdef_nat: "fact (n::nat) = (PROD i:{1..n}. i)"
  apply (induct n)
  apply force
  apply (subst fact_Suc)
  apply (subst interval_Suc)
  apply auto
done

lemma fact_altdef_int: "n >= 0 \<Longrightarrow> fact (n::int) = (PROD i:{1..n}. i)"
  apply (induct n rule: int_ge_induct)
  apply force
  apply (subst fact_plus_one_int, assumption)
  apply (subst interval_plus_one_int)
  apply auto
done

lemma fact_dvd: "n \<le> m \<Longrightarrow> fact n dvd fact (m::nat)"
  by (auto simp add: fact_altdef_nat intro!: setprod_dvd_setprod_subset)

lemma fact_mod: "m \<le> (n::nat) \<Longrightarrow> fact n mod fact m = 0"
  by (auto simp add: dvd_imp_mod_0 fact_dvd)

lemma fact_div_fact:
  assumes "m \<ge> (n :: nat)"
  shows "(fact m) div (fact n) = \<Prod>{n + 1..m}"
proof -
  obtain d where "d = m - n" by auto
  from assms this have "m = n + d" by auto
  have "fact (n + d) div (fact n) = \<Prod>{n + 1..n + d}"
  proof (induct d)
    case 0
    show ?case by simp
  next
    case (Suc d')
    have "fact (n + Suc d') div fact n = Suc (n + d') * fact (n + d') div fact n"
      by simp
    also from Suc.hyps have "... = Suc (n + d') * \<Prod>{n + 1..n + d'}" 
      unfolding div_mult1_eq[of _ "fact (n + d')"] by (simp add: fact_mod)
    also have "... = \<Prod>{n + 1..n + Suc d'}"
      by (simp add: atLeastAtMostSuc_conv setprod.insert)
    finally show ?case .
  qed
  from this `m = n + d` show ?thesis by simp
qed

lemma fact_mono_nat: "(m::nat) \<le> n \<Longrightarrow> fact m \<le> fact n"
apply (drule le_imp_less_or_eq)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k, auto)
done

lemma fact_neg_int [simp]: "m < (0::int) \<Longrightarrow> fact m = 0"
  unfolding fact_int_def by auto

lemma fact_ge_zero_int [simp]: "fact m >= (0::int)"
  apply (case_tac "m >= 0")
  apply auto
  apply (frule fact_gt_zero_int)
  apply arith
done

lemma fact_mono_int_aux [rule_format]: "k >= (0::int) \<Longrightarrow> 
    fact (m + k) >= fact m"
  apply (case_tac "m < 0")
  apply auto
  apply (induct k rule: int_ge_induct)
  apply auto
  apply (subst add.assoc [symmetric])
  apply (subst fact_plus_one_int)
  apply auto
  apply (erule order_trans)
  apply (subst mult_le_cancel_right1)
  apply (subgoal_tac "fact (m + i) >= 0")
  apply arith
  apply auto
done

lemma fact_mono_int: "(m::int) <= n \<Longrightarrow> fact m <= fact n"
  apply (insert fact_mono_int_aux [of "n - m" "m"])
  apply auto
done

text{*Note that @{term "fact 0 = fact 1"}*}
lemma fact_less_mono_nat: "[| (0::nat) < m; m < n |] ==> fact m < fact n"
apply (drule_tac m = m in less_imp_Suc_add, auto)
apply (induct_tac k, auto)
done

lemma fact_less_mono_int_aux: "k >= 0 \<Longrightarrow> (0::int) < m \<Longrightarrow>
    fact m < fact ((m + 1) + k)"
  apply (induct k rule: int_ge_induct)
  apply (simp add: fact_plus_one_int)
  apply (subst (2) fact_reduce_int)
  apply (auto simp add: ac_simps)
  apply (erule order_less_le_trans)
  apply auto
  done

lemma fact_less_mono_int: "(0::int) < m \<Longrightarrow> m < n \<Longrightarrow> fact m < fact n"
  apply (insert fact_less_mono_int_aux [of "n - (m + 1)" "m"])
  apply auto
done

lemma fact_num_eq_if_nat: "fact (m::nat) = 
  (if m=0 then 1 else m * fact (m - 1))"
by (cases m) auto

lemma fact_add_num_eq_if_nat:
  "fact ((m::nat) + n) = (if m + n = 0 then 1 else (m + n) * fact (m + n - 1))"
by (cases "m + n") auto

lemma fact_add_num_eq_if2_nat:
  "fact ((m::nat) + n) = 
    (if m = 0 then fact n else (m + n) * fact ((m - 1) + n))"
by (cases m) auto

lemma fact_le_power: "fact n \<le> n^n"
proof (induct n)
  case (Suc n)
  then have "fact n \<le> Suc n ^ n" by (rule le_trans) (simp add: power_mono)
  then show ?case by (simp add: add_le_mono)
qed simp

subsection {* @{term fact} and @{term of_nat} *}

lemma of_nat_fact_not_zero [simp]: "of_nat (fact n) \<noteq> (0::'a::semiring_char_0)"
by auto

lemma of_nat_fact_gt_zero [simp]: "(0::'a::{linordered_semidom}) < of_nat(fact n)" by auto

lemma of_nat_fact_ge_zero [simp]: "(0::'a::linordered_semidom) \<le> of_nat(fact n)"
by simp

lemma inv_of_nat_fact_gt_zero [simp]: "(0::'a::linordered_field) < inverse (of_nat (fact n))"
by (auto simp add: positive_imp_inverse_positive)

lemma inv_of_nat_fact_ge_zero [simp]: "(0::'a::linordered_field) \<le> inverse (of_nat (fact n))"
by (auto intro: order_less_imp_le)

lemma fact_eq_rev_setprod_nat: "fact (k::nat) = (\<Prod>i<k. k - i)"
  unfolding fact_altdef_nat
  by (rule setprod.reindex_bij_witness[where i="\<lambda>i. k - i" and j="\<lambda>i. k - i"]) auto

lemma fact_div_fact_le_pow:
  assumes "r \<le> n" shows "fact n div fact (n - r) \<le> n ^ r"
proof -
  have "\<And>r. r \<le> n \<Longrightarrow> \<Prod>{n - r..n} = (n - r) * \<Prod>{Suc (n - r)..n}"
    by (subst setprod.insert[symmetric]) (auto simp: atLeastAtMost_insertL)
  with assms show ?thesis
    by (induct r rule: nat.induct) (auto simp add: fact_div_fact Suc_diff_Suc mult_le_mono)
qed

lemma fact_numeral:  --{*Evaluation for specific numerals*}
  "fact (numeral k) = (numeral k) * (fact (pred_numeral k))"
  by (simp add: numeral_eq_Suc)


text {* This development is based on the work of Andy Gordon and
  Florian Kammueller. *}

subsection {* Basic definitions and lemmas *}

primrec binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "choose" 65)
where
  "0 choose k = (if k = 0 then 1 else 0)"
| "Suc n choose k = (if k = 0 then 1 else (n choose (k - 1)) + (n choose k))"

lemma binomial_n_0 [simp]: "(n choose 0) = 1"
  by (cases n) simp_all

lemma binomial_0_Suc [simp]: "(0 choose Suc k) = 0"
  by simp

lemma binomial_Suc_Suc [simp]: "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)"
  by simp

lemma choose_reduce_nat: 
  "0 < (n::nat) \<Longrightarrow> 0 < k \<Longrightarrow>
    (n choose k) = ((n - 1) choose (k - 1)) + ((n - 1) choose k)"
  by (metis Suc_diff_1 binomial.simps(2) neq0_conv)

lemma binomial_eq_0: "n < k \<Longrightarrow> n choose k = 0"
  by (induct n arbitrary: k) auto

declare binomial.simps [simp del]

lemma binomial_n_n [simp]: "n choose n = 1"
  by (induct n) (simp_all add: binomial_eq_0)

lemma binomial_Suc_n [simp]: "Suc n choose n = Suc n"
  by (induct n) simp_all

lemma binomial_1 [simp]: "n choose Suc 0 = n"
  by (induct n) simp_all

lemma zero_less_binomial: "k \<le> n \<Longrightarrow> n choose k > 0"
  by (induct n k rule: diff_induct) simp_all

lemma binomial_eq_0_iff [simp]: "n choose k = 0 \<longleftrightarrow> n < k"
  by (metis binomial_eq_0 less_numeral_extra(3) not_less zero_less_binomial)

lemma zero_less_binomial_iff [simp]: "n choose k > 0 \<longleftrightarrow> k \<le> n"
  by (metis binomial_eq_0_iff not_less0 not_less zero_less_binomial)

lemma Suc_times_binomial_eq:
  "Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
  apply (induct n arbitrary: k, simp add: binomial.simps)
  apply (case_tac k)
   apply (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq binomial_eq_0)
  done

text{*The absorption property*}
lemma Suc_times_binomial:
  "Suc k * (Suc n choose Suc k) = Suc n * (n choose k)"
  using Suc_times_binomial_eq by auto

text{*This is the well-known version of absorption, but it's harder to use because of the
  need to reason about division.*}
lemma binomial_Suc_Suc_eq_times:
    "(Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
  by (simp add: Suc_times_binomial_eq del: mult_Suc mult_Suc_right)

text{*Another version of absorption, with -1 instead of Suc.*}
lemma times_binomial_minus1_eq:
  "0 < k \<Longrightarrow> k * (n choose k) = n * ((n - 1) choose (k - 1))"
  using Suc_times_binomial_eq [where n = "n - 1" and k = "k - 1"]
  by (auto split add: nat_diff_split)


subsection {* Combinatorial theorems involving @{text "choose"} *}

text {*By Florian Kamm\"uller, tidied by LCP.*}

lemma card_s_0_eq_empty: "finite A \<Longrightarrow> card {B. B \<subseteq> A & card B = 0} = 1"
  by (simp cong add: conj_cong add: finite_subset [THEN card_0_eq])

lemma choose_deconstruct: "finite M \<Longrightarrow> x \<notin> M \<Longrightarrow>
    {s. s \<subseteq> insert x M \<and> card s = Suc k} =
    {s. s \<subseteq> M \<and> card s = Suc k} \<union> {s. \<exists>t. t \<subseteq> M \<and> card t = k \<and> s = insert x t}"
  apply safe
     apply (auto intro: finite_subset [THEN card_insert_disjoint])
  by (metis (full_types) Diff_insert_absorb Set.set_insert Zero_neq_Suc card_Diff_singleton_if 
     card_eq_0_iff diff_Suc_1 in_mono subset_insert_iff)

lemma finite_bex_subset [simp]:
  assumes "finite B"
    and "\<And>A. A \<subseteq> B \<Longrightarrow> finite {x. P x A}"
  shows "finite {x. \<exists>A \<subseteq> B. P x A}"
  by (metis (no_types) assms finite_Collect_bounded_ex finite_Collect_subsets)

text{*There are as many subsets of @{term A} having cardinality @{term k}
 as there are sets obtained from the former by inserting a fixed element
 @{term x} into each.*}
lemma constr_bij:
   "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow>
    card {B. \<exists>C. C \<subseteq> A \<and> card C = k \<and> B = insert x C} =
    card {B. B \<subseteq> A & card(B) = k}"
  apply (rule card_bij_eq [where f = "\<lambda>s. s - {x}" and g = "insert x"])
  apply (auto elim!: equalityE simp add: inj_on_def)
  apply (metis card_Diff_singleton_if finite_subset in_mono)
  done

text {*
  Main theorem: combinatorial statement about number of subsets of a set.
*}

theorem n_subsets: "finite A \<Longrightarrow> card {B. B \<subseteq> A \<and> card B = k} = (card A choose k)"
proof (induct k arbitrary: A)
  case 0 then show ?case by (simp add: card_s_0_eq_empty)
next
  case (Suc k)
  show ?case using `finite A`
  proof (induct A)
    case empty show ?case by (simp add: card_s_0_eq_empty)
  next
    case (insert x A)
    then show ?case using Suc.hyps
      apply (simp add: card_s_0_eq_empty choose_deconstruct)
      apply (subst card_Un_disjoint)
         prefer 4 apply (force simp add: constr_bij)
        prefer 3 apply force
       prefer 2 apply (blast intro: finite_Pow_iff [THEN iffD2]
         finite_subset [of _ "Pow (insert x F)" for F])
      apply (blast intro: finite_Pow_iff [THEN iffD2, THEN [2] finite_subset])
      done
  qed
qed


subsection {* The binomial theorem (courtesy of Tobias Nipkow): *}

text{* Avigad's version, generalized to any commutative ring *}
theorem binomial_ring: "(a+b::'a::{comm_ring_1,power})^n = 
  (\<Sum>k=0..n. (of_nat (n choose k)) * a^k * b^(n-k))" (is "?P n")
proof (induct n)
  case 0 then show "?P 0" by simp
next
  case (Suc n)
  have decomp: "{0..n+1} = {0} Un {n+1} Un {1..n}"
    by auto
  have decomp2: "{0..n} = {0} Un {1..n}"
    by auto
  have "(a+b)^(n+1) = 
      (a+b) * (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    using Suc.hyps by simp
  also have "\<dots> = a*(\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k)) +
                   b*(\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    by (rule distrib_right)
  also have "\<dots> = (\<Sum>k=0..n. of_nat (n choose k) * a^(k+1) * b^(n-k)) +
                  (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n-k+1))"
    by (auto simp add: setsum_right_distrib ac_simps)
  also have "\<dots> = (\<Sum>k=0..n. of_nat (n choose k) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n+1. of_nat (n choose (k - 1)) * a^k * b^(n+1-k))"
    by (simp add:setsum_shift_bounds_cl_Suc_ivl Suc_diff_le field_simps  
        del:setsum_cl_ivl_Suc)
  also have "\<dots> = a^(n+1) + b^(n+1) +
                  (\<Sum>k=1..n. of_nat (n choose (k - 1)) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n. of_nat (n choose k) * a^k * b^(n+1-k))"
    by (simp add: decomp2)
  also have
      "\<dots> = a^(n+1) + b^(n+1) + 
            (\<Sum>k=1..n. of_nat(n+1 choose k) * a^k * b^(n+1-k))"
    by (auto simp add: field_simps setsum.distrib [symmetric] choose_reduce_nat)
  also have "\<dots> = (\<Sum>k=0..n+1. of_nat (n+1 choose k) * a^k * b^(n+1-k))"
    using decomp by (simp add: field_simps)
  finally show "?P (Suc n)" by simp
qed

text{* Original version for the naturals *}
corollary binomial: "(a+b::nat)^n = (\<Sum>k=0..n. (of_nat (n choose k)) * a^k * b^(n-k))"
    using binomial_ring [of "int a" "int b" n]
  by (simp only: of_nat_add [symmetric] of_nat_mult [symmetric] of_nat_power [symmetric]
           of_nat_setsum [symmetric]
           of_nat_eq_iff of_nat_id)

lemma binomial_fact_lemma: "k \<le> n \<Longrightarrow> fact k * fact (n - k) * (n choose k) = fact n"
proof (induct n arbitrary: k rule: nat_less_induct)
  fix n k assume H: "\<forall>m<n. \<forall>x\<le>m. fact x * fact (m - x) * (m choose x) =
                      fact m" and kn: "k \<le> n"
  let ?ths = "fact k * fact (n - k) * (n choose k) = fact n"
  { assume "n=0" then have ?ths using kn by simp }
  moreover
  { assume "k=0" then have ?ths using kn by simp }
  moreover
  { assume nk: "n=k" then have ?ths by simp }
  moreover
  { fix m h assume n: "n = Suc m" and h: "k = Suc h" and hm: "h < m"
    from n have mn: "m < n" by arith
    from hm have hm': "h \<le> m" by arith
    from hm h n kn have km: "k \<le> m" by arith
    have "m - h = Suc (m - Suc h)" using  h km hm by arith
    with km h have th0: "fact (m - h) = (m - h) * fact (m - k)"
      by simp
    from n h th0
    have "fact k * fact (n - k) * (n choose k) =
        k * (fact h * fact (m - h) * (m choose h)) + 
        (m - h) * (fact k * fact (m - k) * (m choose k))"
      by (simp add: field_simps)
    also have "\<dots> = (k + (m - h)) * fact m"
      using H[rule_format, OF mn hm'] H[rule_format, OF mn km]
      by (simp add: field_simps)
    finally have ?ths using h n km by simp }
  moreover have "n=0 \<or> k = 0 \<or> k = n \<or> (\<exists>m h. n = Suc m \<and> k = Suc h \<and> h < m)"
    using kn by presburger
  ultimately show ?ths by blast
qed

lemma binomial_fact:
  assumes kn: "k \<le> n"
  shows "(of_nat (n choose k) :: 'a::{field,ring_char_0}) =
    of_nat (fact n) / (of_nat (fact k) * of_nat (fact (n - k)))"
  using binomial_fact_lemma[OF kn]
  by (simp add: field_simps of_nat_mult [symmetric])

end
