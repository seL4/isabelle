(*  Title:      HOL/Number_Theory/UniqueFactorization.thy
    Author:     Jeremy Avigad

Note: there were previous Isabelle formalizations of unique
factorization due to Thomas Marthedal Rasmussen, and, building on
that, by Jeremy Avigad and David Gray.
*)

section \<open>Unique factorization for the natural numbers and the integers\<close>

theory UniqueFactorization
imports Cong "~~/src/HOL/Library/Multiset"
begin

(* As a simp or intro rule,

     prime p \<Longrightarrow> p > 0

   wreaks havoc here. When the premise includes \<forall>x \<in># M. prime x, it
   leads to the backchaining

     x > 0
     prime x
     x \<in># M   which is, unfortunately,
     count M x > 0
*)

(* Here is a version of set product for multisets. Is it worth moving
   to multiset.thy? If so, one should similarly define msetsum for abelian
   semirings, using of_nat. Also, is it worth developing bounded quantifiers
   "\<forall>i \<in># M. P i"?
*)


subsection \<open>Unique factorization: multiset version\<close>

lemma multiset_prime_factorization_exists:
  "n > 0 \<Longrightarrow> (\<exists>M. (\<forall>p::nat \<in> set_mset M. prime p) \<and> n = (\<Prod>i \<in># M. i))"
proof (induct n rule: nat_less_induct)
  fix n :: nat
  assume ih: "\<forall>m < n. 0 < m \<longrightarrow> (\<exists>M. (\<forall>p\<in>set_mset M. prime p) \<and> m = (\<Prod>i \<in># M. i))"
  assume "n > 0"
  then consider "n = 1" | "n > 1" "prime n" | "n > 1" "\<not> prime n"
    by arith
  then show "\<exists>M. (\<forall>p \<in> set_mset M. prime p) \<and> n = (\<Prod>i\<in>#M. i)"
  proof cases
    case 1
    then have "(\<forall>p\<in>set_mset {#}. prime p) \<and> n = (\<Prod>i \<in># {#}. i)"
      by auto
    then show ?thesis ..
  next
    case 2
    then have "(\<forall>p\<in>set_mset {#n#}. prime p) \<and> n = (\<Prod>i \<in># {#n#}. i)"
      by auto
    then show ?thesis ..
  next
    case 3
    with not_prime_eq_prod_nat
    obtain m k where n: "n = m * k" "1 < m" "m < n" "1 < k" "k < n"
      by blast
    with ih obtain Q R where "(\<forall>p \<in> set_mset Q. prime p) \<and> m = (\<Prod>i\<in>#Q. i)"
        and "(\<forall>p\<in>set_mset R. prime p) \<and> k = (\<Prod>i\<in>#R. i)"
      by blast
    then have "(\<forall>p\<in>set_mset (Q + R). prime p) \<and> n = (\<Prod>i \<in># Q + R. i)"
      by (auto simp add: n msetprod_Un)
    then show ?thesis ..
  qed
qed

lemma multiset_prime_factorization_unique_aux:
  fixes a :: nat
  assumes "\<forall>p\<in>set_mset M. prime p"
    and "\<forall>p\<in>set_mset N. prime p"
    and "(\<Prod>i \<in># M. i) dvd (\<Prod>i \<in># N. i)"
  shows "count M a \<le> count N a"
proof (cases "a \<in> set_mset M")
  case True
  with assms have a: "prime a"
    by auto
  with True have "a ^ count M a dvd (\<Prod>i \<in># M. i)"
    by (auto simp add: msetprod_multiplicity)
  also have "\<dots> dvd (\<Prod>i \<in># N. i)"
    by (rule assms)
  also have "\<dots> = (\<Prod>i \<in> set_mset N. i ^ count N i)"
    by (simp add: msetprod_multiplicity)
  also have "\<dots> = a ^ count N a * (\<Prod>i \<in> (set_mset N - {a}). i ^ count N i)"
  proof (cases "a \<in> set_mset N")
    case True
    then have b: "set_mset N = {a} \<union> (set_mset N - {a})"
      by auto
    then show ?thesis
      by (subst (1) b, subst setprod.union_disjoint, auto)
  next
    case False
    then show ?thesis
      by auto
  qed
  finally have "a ^ count M a dvd a ^ count N a * (\<Prod>i \<in> (set_mset N - {a}). i ^ count N i)" .
  moreover
  have "coprime (a ^ count M a) (\<Prod>i \<in> (set_mset N - {a}). i ^ count N i)"
    apply (subst gcd.commute)
    apply (rule setprod_coprime_nat)
    apply (rule primes_imp_powers_coprime_nat)
    using assms True
    apply auto
    done
  ultimately have "a ^ count M a dvd a ^ count N a"
    by (elim coprime_dvd_mult)
  with a show ?thesis
    using power_dvd_imp_le prime_def by blast
next
  case False
  then show ?thesis
    by auto
qed

lemma multiset_prime_factorization_unique:
  assumes "\<forall>p::nat \<in> set_mset M. prime p"
    and "\<forall>p \<in> set_mset N. prime p"
    and "(\<Prod>i \<in># M. i) = (\<Prod>i \<in># N. i)"
  shows "M = N"
proof -
  have "count M a = count N a" for a
  proof -
    from assms have "count M a \<le> count N a"
      by (intro multiset_prime_factorization_unique_aux, auto)
    moreover from assms have "count N a \<le> count M a"
      by (intro multiset_prime_factorization_unique_aux, auto)
    ultimately show ?thesis
      by auto
  qed
  then show ?thesis
    by (simp add: multiset_eq_iff)
qed

definition multiset_prime_factorization :: "nat \<Rightarrow> nat multiset"
where
  "multiset_prime_factorization n =
    (if n > 0
     then THE M. (\<forall>p \<in> set_mset M. prime p) \<and> n = (\<Prod>i \<in># M. i)
     else {#})"

lemma multiset_prime_factorization: "n > 0 \<Longrightarrow>
    (\<forall>p \<in> set_mset (multiset_prime_factorization n). prime p) \<and>
       n = (\<Prod>i \<in># (multiset_prime_factorization n). i)"
  apply (unfold multiset_prime_factorization_def)
  apply clarsimp
  apply (frule multiset_prime_factorization_exists)
  apply clarify
  apply (rule theI)
  apply (insert multiset_prime_factorization_unique)
  apply auto
  done


subsection \<open>Prime factors and multiplicity for nat and int\<close>

class unique_factorization =
  fixes multiplicity :: "'a \<Rightarrow> 'a \<Rightarrow> nat"
    and prime_factors :: "'a \<Rightarrow> 'a set"

text \<open>Definitions for the natural numbers.\<close>
instantiation nat :: unique_factorization
begin

definition multiplicity_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "multiplicity_nat p n = count (multiset_prime_factorization n) p"

definition prime_factors_nat :: "nat \<Rightarrow> nat set"
  where "prime_factors_nat n = set_mset (multiset_prime_factorization n)"

instance ..

end

text \<open>Definitions for the integers.\<close>
instantiation int :: unique_factorization
begin

definition multiplicity_int :: "int \<Rightarrow> int \<Rightarrow> nat"
  where "multiplicity_int p n = multiplicity (nat p) (nat n)"

definition prime_factors_int :: "int \<Rightarrow> int set"
  where "prime_factors_int n = int ` (prime_factors (nat n))"

instance ..

end


subsection \<open>Set up transfer\<close>

lemma transfer_nat_int_prime_factors: "prime_factors (nat n) = nat ` prime_factors n"
  unfolding prime_factors_int_def
  apply auto
  apply (subst transfer_int_nat_set_return_embed)
  apply assumption
  done

lemma transfer_nat_int_prime_factors_closure: "n \<ge> 0 \<Longrightarrow> nat_set (prime_factors n)"
  by (auto simp add: nat_set_def prime_factors_int_def)

lemma transfer_nat_int_multiplicity:
  "p \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> multiplicity (nat p) (nat n) = multiplicity p n"
  by (auto simp add: multiplicity_int_def)

declare transfer_morphism_nat_int[transfer add return:
  transfer_nat_int_prime_factors transfer_nat_int_prime_factors_closure
  transfer_nat_int_multiplicity]

lemma transfer_int_nat_prime_factors: "prime_factors (int n) = int ` prime_factors n"
  unfolding prime_factors_int_def by auto

lemma transfer_int_nat_prime_factors_closure: "is_nat n \<Longrightarrow> nat_set (prime_factors n)"
  by (simp only: transfer_nat_int_prime_factors_closure is_nat_def)

lemma transfer_int_nat_multiplicity: "multiplicity (int p) (int n) = multiplicity p n"
  by (auto simp add: multiplicity_int_def)

declare transfer_morphism_int_nat[transfer add return:
  transfer_int_nat_prime_factors transfer_int_nat_prime_factors_closure
  transfer_int_nat_multiplicity]


subsection \<open>Properties of prime factors and multiplicity for nat and int\<close>

lemma prime_factors_ge_0_int [elim]:
  fixes n :: int
  shows "p \<in> prime_factors n \<Longrightarrow> p \<ge> 0"
  unfolding prime_factors_int_def by auto

lemma prime_factors_prime_nat [intro]:
  fixes n :: nat
  shows "p \<in> prime_factors n \<Longrightarrow> prime p"
  apply (cases "n = 0")
  apply (simp add: prime_factors_nat_def multiset_prime_factorization_def)
  apply (auto simp add: prime_factors_nat_def multiset_prime_factorization)
  done

lemma prime_factors_prime_int [intro]:
  fixes n :: int
  assumes "n \<ge> 0" and "p \<in> prime_factors n"
  shows "prime p"
  apply (rule prime_factors_prime_nat [transferred, of n p, simplified])
  using assms apply auto
  done

lemma prime_factors_gt_0_nat:
  fixes p :: nat
  shows "p \<in> prime_factors x \<Longrightarrow> p > 0"
    using prime_factors_prime_nat by force

lemma prime_factors_gt_0_int:
  shows "x \<ge> 0 \<Longrightarrow> p \<in> prime_factors x \<Longrightarrow> int p > (0::int)"
    by (simp add: prime_factors_gt_0_nat)

lemma prime_factors_finite_nat [iff]:
  fixes n :: nat
  shows "finite (prime_factors n)"
  unfolding prime_factors_nat_def by auto

lemma prime_factors_finite_int [iff]:
  fixes n :: int
  shows "finite (prime_factors n)"
  unfolding prime_factors_int_def by auto

lemma prime_factors_altdef_nat:
  fixes n :: nat
  shows "prime_factors n = {p. multiplicity p n > 0}"
  by (force simp add: prime_factors_nat_def multiplicity_nat_def)

lemma prime_factors_altdef_int:
  fixes n :: int
  shows "prime_factors n = {p. p \<ge> 0 \<and> multiplicity p n > 0}"
  apply (unfold prime_factors_int_def multiplicity_int_def)
  apply (subst prime_factors_altdef_nat)
  apply (auto simp add: image_def)
  done

lemma prime_factorization_nat:
  fixes n :: nat
  shows "n > 0 \<Longrightarrow> n = (\<Prod>p \<in> prime_factors n. p ^ multiplicity p n)"
  apply (frule multiset_prime_factorization)
  apply (simp add: prime_factors_nat_def multiplicity_nat_def msetprod_multiplicity)
  done

lemma prime_factorization_int:
  fixes n :: int
  assumes "n > 0"
  shows "n = (\<Prod>p \<in> prime_factors n. p ^ multiplicity p n)"
  apply (rule prime_factorization_nat [transferred, of n])
  using assms apply auto
  done

lemma prime_factorization_unique_nat:
  fixes f :: "nat \<Rightarrow> _"
  assumes S_eq: "S = {p. 0 < f p}"
    and "finite S"
    and S: "\<forall>p\<in>S. prime p" "n = (\<Prod>p\<in>S. p ^ f p)"
  shows "S = prime_factors n \<and> (\<forall>p. f p = multiplicity p n)"
proof -
  from assms have "f \<in> multiset"
    by (auto simp add: multiset_def)
  moreover from assms have "n > 0" 
    by (auto intro: prime_gt_0_nat)
  ultimately have "multiset_prime_factorization n = Abs_multiset f"
    apply (unfold multiset_prime_factorization_def)
    apply (subst if_P, assumption)
    apply (rule the1_equality)
    apply (rule ex_ex1I)
    apply (rule multiset_prime_factorization_exists, assumption)
    apply (rule multiset_prime_factorization_unique)
    apply force
    apply force
    apply force
    using S S_eq  apply (simp add: set_mset_def msetprod_multiplicity)
    done
  with \<open>f \<in> multiset\<close> have "count (multiset_prime_factorization n) = f"
    by simp
  with S_eq show ?thesis
    by (simp add: set_mset_def multiset_def prime_factors_nat_def multiplicity_nat_def)
qed

lemma prime_factors_characterization_nat:
  "S = {p. 0 < f (p::nat)} \<Longrightarrow>
    finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> prime_factors n = S"
  by (rule prime_factorization_unique_nat [THEN conjunct1, symmetric])

lemma prime_factors_characterization'_nat:
  "finite {p. 0 < f (p::nat)} \<Longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow>
      prime_factors (\<Prod>p | 0 < f p. p ^ f p) = {p. 0 < f p}"
  by (rule prime_factors_characterization_nat) auto

(* A minor glitch:*)
thm prime_factors_characterization'_nat
    [where f = "\<lambda>x. f (int (x::nat))",
      transferred direction: nat "op \<le> (0::int)", rule_format]

(*
  Transfer isn't smart enough to know that the "0 < f p" should
  remain a comparison between nats. But the transfer still works.
*)

lemma primes_characterization'_int [rule_format]:
  "finite {p. p \<ge> 0 \<and> 0 < f (p::int)} \<Longrightarrow> \<forall>p. 0 < f p \<longrightarrow> prime p \<Longrightarrow>
      prime_factors (\<Prod>p | p \<ge> 0 \<and> 0 < f p. p ^ f p) = {p. p \<ge> 0 \<and> 0 < f p}"
  using prime_factors_characterization'_nat
    [where f = "\<lambda>x. f (int (x::nat))",
    transferred direction: nat "op \<le> (0::int)"]
  by auto

lemma prime_factors_characterization_int:
  "S = {p. 0 < f (p::int)} \<Longrightarrow> finite S \<Longrightarrow>
    \<forall>p\<in>S. prime (nat p) \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> prime_factors n = S"
  apply simp
  apply (subgoal_tac "{p. 0 < f p} = {p. 0 \<le> p \<and> 0 < f p}")
  apply (simp only:)
  apply (subst primes_characterization'_int)
  apply simp_all
  apply (metis nat_int)
  apply (metis le_cases nat_le_0 zero_not_prime_nat)
  done

lemma multiplicity_characterization_nat:
  "S = {p. 0 < f (p::nat)} \<Longrightarrow> finite S \<Longrightarrow> \<forall>p\<in>S. prime p \<Longrightarrow>
    n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow> multiplicity p n = f p"
  apply (frule prime_factorization_unique_nat [THEN conjunct2, rule_format, symmetric])
  apply auto
  done

lemma multiplicity_characterization'_nat: "finite {p. 0 < f (p::nat)} \<longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<longrightarrow>
      multiplicity p (\<Prod>p | 0 < f p. p ^ f p) = f p"
  apply (intro impI)
  apply (rule multiplicity_characterization_nat)
  apply auto
  done

lemma multiplicity_characterization'_int [rule_format]:
  "finite {p. p \<ge> 0 \<and> 0 < f (p::int)} \<Longrightarrow>
    (\<forall>p. 0 < f p \<longrightarrow> prime p) \<Longrightarrow> p \<ge> 0 \<Longrightarrow>
      multiplicity p (\<Prod>p | p \<ge> 0 \<and> 0 < f p. p ^ f p) = f p"
  apply (insert multiplicity_characterization'_nat
    [where f = "\<lambda>x. f (int (x::nat))",
      transferred direction: nat "op \<le> (0::int)", rule_format])
  apply auto
  done

lemma multiplicity_characterization_int: "S = {p. 0 < f (p::int)} \<Longrightarrow>
    finite S \<Longrightarrow> \<forall>p\<in>S. prime (nat p) \<Longrightarrow> n = (\<Prod>p\<in>S. p ^ f p) \<Longrightarrow>
      p \<ge> 0 \<Longrightarrow> multiplicity p n = f p"
  apply simp
  apply (subgoal_tac "{p. 0 < f p} = {p. 0 \<le> p \<and> 0 < f p}")
  apply (simp only:)
  apply (subst multiplicity_characterization'_int)
  apply simp_all
  apply (metis nat_int)
  apply (metis le_cases nat_le_0 zero_not_prime_nat)
  done

lemma multiplicity_zero_nat [simp]: "multiplicity (p::nat) 0 = 0"
  by (simp add: multiplicity_nat_def multiset_prime_factorization_def)

lemma multiplicity_zero_int [simp]: "multiplicity (p::int) 0 = 0"
  by (simp add: multiplicity_int_def)

lemma multiplicity_one_nat': "multiplicity p (1::nat) = 0"
  by (subst multiplicity_characterization_nat [where f = "\<lambda>x. 0"], auto)

lemma multiplicity_one_nat [simp]: "multiplicity p (Suc 0) = 0"
  by (metis One_nat_def multiplicity_one_nat')

lemma multiplicity_one_int [simp]: "multiplicity p (1::int) = 0"
  by (metis multiplicity_int_def multiplicity_one_nat' transfer_nat_int_numerals(2))

lemma multiplicity_prime_nat [simp]: "prime p \<Longrightarrow> multiplicity p p = 1"
  apply (subst multiplicity_characterization_nat [where f = "\<lambda>q. if q = p then 1 else 0"])
  apply auto
  apply (metis (full_types) less_not_refl)
  done

lemma multiplicity_prime_power_nat [simp]: "prime p \<Longrightarrow> multiplicity p (p ^ n) = n"
  apply (cases "n = 0")
  apply auto
  apply (subst multiplicity_characterization_nat [where f = "\<lambda>q. if q = p then n else 0"])
  apply auto
  apply (metis (full_types) less_not_refl)
  done

lemma multiplicity_prime_power_int [simp]: "prime p \<Longrightarrow> multiplicity p (int p ^ n) = n"
  by (metis multiplicity_prime_power_nat of_nat_power transfer_int_nat_multiplicity)

lemma multiplicity_nonprime_nat [simp]:
  fixes p n :: nat
  shows "\<not> prime p \<Longrightarrow> multiplicity p n = 0"
  apply (cases "n = 0")
  apply auto
  apply (frule multiset_prime_factorization)
  apply (auto simp add: set_mset_def multiplicity_nat_def)
  done

lemma multiplicity_not_factor_nat [simp]:
  fixes p n :: nat
  shows "p \<notin> prime_factors n \<Longrightarrow> multiplicity p n = 0"
  apply (subst (asm) prime_factors_altdef_nat)
  apply auto
  done

lemma multiplicity_not_factor_int [simp]:
  fixes n :: int
  shows "p \<ge> 0 \<Longrightarrow> p \<notin> prime_factors n \<Longrightarrow> multiplicity p n = 0"
  apply (subst (asm) prime_factors_altdef_int)
  apply auto
  done

(*FIXME: messy*)
lemma multiplicity_product_aux_nat: "(k::nat) > 0 \<Longrightarrow> l > 0 \<Longrightarrow>
    (prime_factors k) \<union> (prime_factors l) = prime_factors (k * l) \<and>
    (\<forall>p. multiplicity p k + multiplicity p l = multiplicity p (k * l))"
  apply (rule prime_factorization_unique_nat)
  apply (simp only: prime_factors_altdef_nat)
  apply auto
  apply (subst power_add)
  apply (subst setprod.distrib)
  apply (rule arg_cong2 [where f = "\<lambda>x y. x*y"])
  apply (subgoal_tac "prime_factors k \<union> prime_factors l = prime_factors k \<union>
      (prime_factors l - prime_factors k)")
  apply (erule ssubst)
  apply (subst setprod.union_disjoint)
  apply auto
  apply (metis One_nat_def nat_mult_1_right prime_factorization_nat setprod.neutral_const)
  apply (subgoal_tac "prime_factors k \<union> prime_factors l = prime_factors l \<union>
      (prime_factors k - prime_factors l)")
  apply (erule ssubst)
  apply (subst setprod.union_disjoint)
  apply auto
  apply (subgoal_tac "(\<Prod>p\<in>prime_factors k - prime_factors l. p ^ multiplicity p l) =
      (\<Prod>p\<in>prime_factors k - prime_factors l. 1)")
  apply auto
  apply (metis One_nat_def nat_mult_1_right prime_factorization_nat setprod.neutral_const)
  done

(* transfer doesn't have the same problem here with the right
   choice of rules. *)

lemma multiplicity_product_aux_int:
  assumes "(k::int) > 0" and "l > 0"
  shows "prime_factors k \<union> prime_factors l = prime_factors (k * l) \<and>
    (\<forall>p \<ge> 0. multiplicity p k + multiplicity p l = multiplicity p (k * l))"
  apply (rule multiplicity_product_aux_nat [transferred, of l k])
  using assms apply auto
  done

lemma prime_factors_product_nat: "(k::nat) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> prime_factors (k * l) =
    prime_factors k \<union> prime_factors l"
  by (rule multiplicity_product_aux_nat [THEN conjunct1, symmetric])

lemma prime_factors_product_int: "(k::int) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> prime_factors (k * l) =
    prime_factors k \<union> prime_factors l"
  by (rule multiplicity_product_aux_int [THEN conjunct1, symmetric])

lemma multiplicity_product_nat: "(k::nat) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> multiplicity p (k * l) =
    multiplicity p k + multiplicity p l"
  by (rule multiplicity_product_aux_nat [THEN conjunct2, rule_format, symmetric])

lemma multiplicity_product_int: "(k::int) > 0 \<Longrightarrow> l > 0 \<Longrightarrow> p \<ge> 0 \<Longrightarrow>
    multiplicity p (k * l) = multiplicity p k + multiplicity p l"
  by (rule multiplicity_product_aux_int [THEN conjunct2, rule_format, symmetric])

lemma multiplicity_setprod_nat: "finite S \<Longrightarrow> \<forall>x\<in>S. f x > 0 \<Longrightarrow>
    multiplicity (p::nat) (\<Prod>x \<in> S. f x) = (\<Sum>x \<in> S. multiplicity p (f x))"
  apply (induct set: finite)
  apply auto
  apply (subst multiplicity_product_nat)
  apply auto
  done

(* Transfer is delicate here for two reasons: first, because there is
   an implicit quantifier over functions (f), and, second, because the
   product over the multiplicity should not be translated to an integer
   product.

   The way to handle the first is to use quantifier rules for functions.
   The way to handle the second is to turn off the offending rule.
*)

lemma transfer_nat_int_sum_prod_closure3: "(\<Sum>x \<in> A. int (f x)) \<ge> 0" "(\<Prod>x \<in> A. int (f x)) \<ge> 0"
  apply (rule setsum_nonneg; auto)
  apply (rule setprod_nonneg; auto)
  done

declare transfer_morphism_nat_int[transfer
  add return: transfer_nat_int_sum_prod_closure3
  del: transfer_nat_int_sum_prod2 (1)]

lemma multiplicity_setprod_int: "p \<ge> 0 \<Longrightarrow> finite S \<Longrightarrow> \<forall>x\<in>S. f x > 0 \<Longrightarrow>
    multiplicity (p::int) (\<Prod>x \<in> S. f x) = (\<Sum>x \<in> S. multiplicity p (f x))"
  apply (frule multiplicity_setprod_nat
    [where f = "\<lambda>x. nat(int(nat(f x)))",
      transferred direction: nat "op \<le> (0::int)"])
  apply auto
  apply (subst (asm) setprod.cong)
  apply (rule refl)
  apply (rule if_P)
  apply auto
  apply (rule setsum.cong)
  apply auto
  done

declare transfer_morphism_nat_int[transfer
  add return: transfer_nat_int_sum_prod2 (1)]

lemma multiplicity_prod_prime_powers_nat:
    "finite S \<Longrightarrow> \<forall>p\<in>S. prime (p::nat) \<Longrightarrow>
       multiplicity p (\<Prod>p \<in> S. p ^ f p) = (if p \<in> S then f p else 0)"
  apply (subgoal_tac "(\<Prod>p \<in> S. p ^ f p) = (\<Prod>p \<in> S. p ^ (\<lambda>x. if x \<in> S then f x else 0) p)")
  apply (erule ssubst)
  apply (subst multiplicity_characterization_nat)
  prefer 5 apply (rule refl)
  apply (rule refl)
  apply auto
  apply (subst setprod.mono_neutral_right)
  apply assumption
  prefer 3
  apply (rule setprod.cong)
  apply (rule refl)
  apply auto
  done

(* Here the issue with transfer is the implicit quantifier over S *)

lemma multiplicity_prod_prime_powers_int:
    "(p::int) \<ge> 0 \<Longrightarrow> finite S \<Longrightarrow> \<forall>p\<in>S. prime (nat p) \<Longrightarrow>
       multiplicity p (\<Prod>p \<in> S. p ^ f p) = (if p \<in> S then f p else 0)"
  apply (subgoal_tac "int ` nat ` S = S")
  apply (frule multiplicity_prod_prime_powers_nat
    [where f = "\<lambda>x. f(int x)" and S = "nat ` S", transferred])
  apply auto
  apply (metis linear nat_0_iff zero_not_prime_nat)
  apply (metis (full_types) image_iff int_nat_eq less_le less_linear nat_0_iff zero_not_prime_nat)
  done

lemma multiplicity_distinct_prime_power_nat:
    "prime p \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> multiplicity p (q ^ n) = 0"
  apply (subgoal_tac "q ^ n = setprod (\<lambda>x. x ^ n) {q}")
  apply (erule ssubst)
  apply (subst multiplicity_prod_prime_powers_nat)
  apply auto
  done

lemma multiplicity_distinct_prime_power_int:
    "prime p \<Longrightarrow> prime q \<Longrightarrow> p \<noteq> q \<Longrightarrow> multiplicity p (int q ^ n) = 0"
  by (metis multiplicity_distinct_prime_power_nat of_nat_power transfer_int_nat_multiplicity)

lemma dvd_multiplicity_nat:
  fixes x y :: nat
  shows "0 < y \<Longrightarrow> x dvd y \<Longrightarrow> multiplicity p x \<le> multiplicity p y"
  apply (cases "x = 0")
  apply (auto simp add: dvd_def multiplicity_product_nat)
  done

lemma dvd_multiplicity_int:
  fixes p x y :: int
  shows "0 < y \<Longrightarrow> 0 \<le> x \<Longrightarrow> x dvd y \<Longrightarrow> p \<ge> 0 \<Longrightarrow> multiplicity p x \<le> multiplicity p y"
  apply (cases "x = 0")
  apply (auto simp add: dvd_def)
  apply (subgoal_tac "0 < k")
  apply (auto simp add: multiplicity_product_int)
  apply (erule zero_less_mult_pos)
  apply arith
  done

lemma dvd_prime_factors_nat [intro]:
  fixes x y :: nat
  shows "0 < y \<Longrightarrow> x dvd y \<Longrightarrow> prime_factors x \<le> prime_factors y"
  apply (simp only: prime_factors_altdef_nat)
  apply auto
  apply (metis dvd_multiplicity_nat le_0_eq neq0_conv)
  done

lemma dvd_prime_factors_int [intro]:
  fixes x y :: int
  shows "0 < y \<Longrightarrow> 0 \<le> x \<Longrightarrow> x dvd y \<Longrightarrow> prime_factors x \<le> prime_factors y"
  apply (auto simp add: prime_factors_altdef_int)
  apply (metis dvd_multiplicity_int le_0_eq neq0_conv)
  done

lemma multiplicity_dvd_nat:
  fixes x y :: nat
  shows "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> \<forall>p. multiplicity p x \<le> multiplicity p y \<Longrightarrow> x dvd y"
  apply (subst prime_factorization_nat [of x], assumption)
  apply (subst prime_factorization_nat [of y], assumption)
  apply (rule setprod_dvd_setprod_subset2)
  apply force
  apply (subst prime_factors_altdef_nat)+
  apply auto
  apply (metis gr0I le_0_eq less_not_refl)
  apply (metis le_imp_power_dvd)
  done

lemma multiplicity_dvd_int:
  fixes x y :: int
  shows "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> \<forall>p\<ge>0. multiplicity p x \<le> multiplicity p y \<Longrightarrow> x dvd y"
  apply (subst prime_factorization_int [of x], assumption)
  apply (subst prime_factorization_int [of y], assumption)
  apply (rule setprod_dvd_setprod_subset2)
  apply force
  apply (subst prime_factors_altdef_int)+
  apply auto
  apply (metis le_imp_power_dvd prime_factors_ge_0_int)
  done

lemma multiplicity_dvd'_nat:
  fixes x y :: nat
  shows "0 < x \<Longrightarrow> \<forall>p. prime p \<longrightarrow> multiplicity p x \<le> multiplicity p y \<Longrightarrow> x dvd y"
  by (metis gcd_lcm_complete_lattice_nat.top_greatest le_refl multiplicity_dvd_nat
      multiplicity_nonprime_nat neq0_conv)

lemma multiplicity_dvd'_int:
  fixes x y :: int
  shows "0 < x \<Longrightarrow> 0 \<le> y \<Longrightarrow>
    \<forall>p. prime p \<longrightarrow> multiplicity p x \<le> multiplicity p y \<Longrightarrow> x dvd y"
  by (metis dvd_int_iff abs_of_nat multiplicity_dvd'_nat multiplicity_int_def nat_int
    zero_le_imp_eq_int zero_less_imp_eq_int)

lemma dvd_multiplicity_eq_nat:
  fixes x y :: nat
  shows "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> x dvd y \<longleftrightarrow> (\<forall>p. multiplicity p x \<le> multiplicity p y)"
  by (auto intro: dvd_multiplicity_nat multiplicity_dvd_nat)

lemma dvd_multiplicity_eq_int: "0 < (x::int) \<Longrightarrow> 0 < y \<Longrightarrow>
    (x dvd y) = (\<forall>p\<ge>0. multiplicity p x \<le> multiplicity p y)"
  by (auto intro: dvd_multiplicity_int multiplicity_dvd_int)

lemma prime_factors_altdef2_nat:
  fixes n :: nat
  shows "n > 0 \<Longrightarrow> p \<in> prime_factors n \<longleftrightarrow> prime p \<and> p dvd n"
  apply (cases "prime p")
  apply auto
  apply (subst prime_factorization_nat [where n = n], assumption)
  apply (rule dvd_trans)
  apply (rule dvd_power [where x = p and n = "multiplicity p n"])
  apply (subst (asm) prime_factors_altdef_nat, force)
  apply rule
  apply auto
  apply (metis One_nat_def Zero_not_Suc dvd_multiplicity_nat le0
    le_antisym multiplicity_not_factor_nat multiplicity_prime_nat)
  done

lemma prime_factors_altdef2_int:
  fixes n :: int
  assumes "n > 0"
  shows "p \<in> prime_factors n \<longleftrightarrow> prime p \<and> p dvd n"
  using assms by (simp add:  prime_factors_altdef2_nat [transferred])

lemma multiplicity_eq_nat:
  fixes x and y::nat
  assumes [arith]: "x > 0" "y > 0"
    and mult_eq [simp]: "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"
  apply (rule dvd_antisym)
  apply (auto intro: multiplicity_dvd'_nat)
  done

lemma multiplicity_eq_int:
  fixes x y :: int
  assumes [arith]: "x > 0" "y > 0"
    and mult_eq [simp]: "\<And>p. prime p \<Longrightarrow> multiplicity p x = multiplicity p y"
  shows "x = y"
  apply (rule dvd_antisym [transferred])
  apply (auto intro: multiplicity_dvd'_int)
  done


subsection \<open>An application\<close>

lemma gcd_eq_nat:
  fixes x y :: nat
  assumes pos [arith]: "x > 0" "y > 0"
  shows "gcd x y =
    (\<Prod>p \<in> prime_factors x \<union> prime_factors y. p ^ min (multiplicity p x) (multiplicity p y))"
  (is "_ = ?z")
proof -
  have [arith]: "?z > 0" 
    using prime_factors_gt_0_nat by auto
  have aux: "\<And>p. prime p \<Longrightarrow> multiplicity p ?z = min (multiplicity p x) (multiplicity p y)"
    apply (subst multiplicity_prod_prime_powers_nat)
    apply auto
    done
  have "?z dvd x"
    by (intro multiplicity_dvd'_nat) (auto simp add: aux intro: prime_gt_0_nat)
  moreover have "?z dvd y"
    by (intro multiplicity_dvd'_nat) (auto simp add: aux intro: prime_gt_0_nat)
  moreover have "w dvd x \<and> w dvd y \<longrightarrow> w dvd ?z" for w
  proof (cases "w = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
      apply auto
      apply (erule multiplicity_dvd'_nat)
      apply (auto intro: dvd_multiplicity_nat simp add: aux)
      done
  qed
  ultimately have "?z = gcd x y"
    by (subst gcd_unique_nat [symmetric], blast)
  then show ?thesis
    by auto
qed

lemma lcm_eq_nat:
  assumes pos [arith]: "x > 0" "y > 0"
  shows "lcm (x::nat) y =
    (\<Prod>p \<in> prime_factors x \<union> prime_factors y. p ^ max (multiplicity p x) (multiplicity p y))"
  (is "_ = ?z")
proof -
  have [arith]: "?z > 0"
    by (auto intro: prime_gt_0_nat)
  have aux: "\<And>p. prime p \<Longrightarrow> multiplicity p ?z = max (multiplicity p x) (multiplicity p y)"
    apply (subst multiplicity_prod_prime_powers_nat)
    apply auto
    done
  have "x dvd ?z"
    by (intro multiplicity_dvd'_nat) (auto simp add: aux)
  moreover have "y dvd ?z"
    by (intro multiplicity_dvd'_nat) (auto simp add: aux)
  moreover have "x dvd w \<and> y dvd w \<longrightarrow> ?z dvd w" for w
  proof (cases "w = 0")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis
      apply auto
      apply (rule multiplicity_dvd'_nat)
      apply (auto intro: prime_gt_0_nat dvd_multiplicity_nat simp add: aux)
      done
  qed
  ultimately have "?z = lcm x y"
    by (subst lcm_unique_nat [symmetric], blast)
  then show ?thesis
    by auto
qed

lemma multiplicity_gcd_nat:
  fixes p x y :: nat
  assumes [arith]: "x > 0" "y > 0"
  shows "multiplicity p (gcd x y) = min (multiplicity p x) (multiplicity p y)"
  apply (subst gcd_eq_nat)
  apply auto
  apply (subst multiplicity_prod_prime_powers_nat)
  apply auto
  done

lemma multiplicity_lcm_nat:
  fixes p x y :: nat
  assumes [arith]: "x > 0" "y > 0"
  shows "multiplicity p (lcm x y) = max (multiplicity p x) (multiplicity p y)"
  apply (subst lcm_eq_nat)
  apply auto
  apply (subst multiplicity_prod_prime_powers_nat)
  apply auto
  done

lemma gcd_lcm_distrib_nat:
  fixes x y z :: nat
  shows "gcd x (lcm y z) = lcm (gcd x y) (gcd x z)"
  apply (cases "x = 0 | y = 0 | z = 0")
  apply auto
  apply (rule multiplicity_eq_nat)
  apply (auto simp add: multiplicity_gcd_nat multiplicity_lcm_nat lcm_pos_nat)
  done

lemma gcd_lcm_distrib_int:
  fixes x y z :: int
  shows "gcd x (lcm y z) = lcm (gcd x y) (gcd x z)"
  apply (subst (1 2 3) gcd_abs_int)
  apply (subst lcm_abs_int)
  apply (subst (2) abs_of_nonneg)
  apply force
  apply (rule gcd_lcm_distrib_nat [transferred])
  apply auto
  done

end
