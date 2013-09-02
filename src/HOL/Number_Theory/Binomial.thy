(*  Title:      HOL/Number_Theory/Binomial.thy
    Authors:    Lawrence C. Paulson, Jeremy Avigad, Tobias Nipkow

Defines the "choose" function, and establishes basic properties.

The original theory "Binomial" was by Lawrence C. Paulson, based on
the work of Andy Gordon and Florian Kammueller. The approach here,
which derives the definition of binomial coefficients in terms of the
factorial function, is due to Jeremy Avigad. The binomial theorem was
formalized by Tobias Nipkow.
*)

header {* Binomial *}

theory Binomial
imports Cong Fact
begin


subsection {* Main definitions *}

class binomial =
  fixes binomial :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "choose" 65)

(* definitions for the natural numbers *)

instantiation nat :: binomial
begin 

fun binomial_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "binomial_nat n k =
   (if k = 0 then 1 else
    if n = 0 then 0 else
      (binomial (n - 1) k) + (binomial (n - 1) (k - 1)))"

instance ..

end

(* definitions for the integers *)

instantiation int :: binomial
begin 

definition binomial_int :: "int => int \<Rightarrow> int" where
  "binomial_int n k =
   (if n \<ge> 0 \<and> k \<ge> 0 then int (binomial (nat n) (nat k))
    else 0)"

instance ..

end


subsection {* Set up Transfer *}

lemma transfer_nat_int_binomial:
  "(n::int) >= 0 \<Longrightarrow> k >= 0 \<Longrightarrow> binomial (nat n) (nat k) = 
      nat (binomial n k)"
  unfolding binomial_int_def 
  by auto

lemma transfer_nat_int_binomial_closure:
  "n >= (0::int) \<Longrightarrow> k >= 0 \<Longrightarrow> binomial n k >= 0"
  by (auto simp add: binomial_int_def)

declare transfer_morphism_nat_int[transfer add return: 
    transfer_nat_int_binomial transfer_nat_int_binomial_closure]

lemma transfer_int_nat_binomial:
  "binomial (int n) (int k) = int (binomial n k)"
  unfolding fact_int_def binomial_int_def by auto

lemma transfer_int_nat_binomial_closure:
  "is_nat n \<Longrightarrow> is_nat k \<Longrightarrow> binomial n k >= 0"
  by (auto simp add: binomial_int_def)

declare transfer_morphism_int_nat[transfer add return: 
    transfer_int_nat_binomial transfer_int_nat_binomial_closure]


subsection {* Binomial coefficients *}

lemma choose_zero_nat [simp]: "(n::nat) choose 0 = 1"
  by simp

lemma choose_zero_int [simp]: "n \<ge> 0 \<Longrightarrow> (n::int) choose 0 = 1"
  by (simp add: binomial_int_def)

lemma zero_choose_nat [rule_format,simp]: "ALL (k::nat) > n. n choose k = 0"
  by (induct n rule: induct'_nat, auto)

lemma zero_choose_int [rule_format,simp]: "(k::int) > n \<Longrightarrow> n choose k = 0"
  unfolding binomial_int_def
  apply (cases "n < 0")
  apply force
  apply (simp del: binomial_nat.simps)
  done

lemma choose_reduce_nat: "(n::nat) > 0 \<Longrightarrow> 0 < k \<Longrightarrow>
    (n choose k) = ((n - 1) choose k) + ((n - 1) choose (k - 1))"
  by simp

lemma choose_reduce_int: "(n::int) > 0 \<Longrightarrow> 0 < k \<Longrightarrow>
    (n choose k) = ((n - 1) choose k) + ((n - 1) choose (k - 1))"
  unfolding binomial_int_def
  apply (subst choose_reduce_nat)
    apply (auto simp del: binomial_nat.simps simp add: nat_diff_distrib)
  done

lemma choose_plus_one_nat: "((n::nat) + 1) choose (k + 1) = 
    (n choose (k + 1)) + (n choose k)"
  by (simp add: choose_reduce_nat)

lemma choose_Suc_nat: "(Suc n) choose (Suc k) = 
    (n choose (Suc k)) + (n choose k)"
  by (simp add: choose_reduce_nat One_nat_def)

lemma choose_plus_one_int: "n \<ge> 0 \<Longrightarrow> k \<ge> 0 \<Longrightarrow> ((n::int) + 1) choose (k + 1) = 
    (n choose (k + 1)) + (n choose k)"
  by (simp add: binomial_int_def choose_plus_one_nat nat_add_distrib del: binomial_nat.simps)

declare binomial_nat.simps [simp del]

lemma choose_self_nat [simp]: "((n::nat) choose n) = 1"
  by (induct n rule: induct'_nat) (auto simp add: choose_plus_one_nat)

lemma choose_self_int [simp]: "n \<ge> 0 \<Longrightarrow> ((n::int) choose n) = 1"
  by (auto simp add: binomial_int_def)

lemma choose_one_nat [simp]: "(n::nat) choose 1 = n"
  by (induct n rule: induct'_nat) (auto simp add: choose_reduce_nat)

lemma choose_one_int [simp]: "n \<ge> 0 \<Longrightarrow> (n::int) choose 1 = n"
  by (auto simp add: binomial_int_def)

lemma plus_one_choose_self_nat [simp]: "(n::nat) + 1 choose n = n + 1"
  apply (induct n rule: induct'_nat, force)
  apply (case_tac "n = 0")
  apply auto
  apply (subst choose_reduce_nat)
  apply (auto simp add: One_nat_def)  
  (* natdiff_cancel_numerals introduces Suc *)
done

lemma Suc_choose_self_nat [simp]: "(Suc n) choose n = Suc n"
  using plus_one_choose_self_nat by (simp add: One_nat_def)

lemma plus_one_choose_self_int [rule_format, simp]: 
    "(n::int) \<ge> 0 \<longrightarrow> n + 1 choose n = n + 1"
   by (auto simp add: binomial_int_def nat_add_distrib)

(* bounded quantification doesn't work with the unicode characters? *)
lemma choose_pos_nat [rule_format]: "ALL k <= (n::nat). 
    ((n::nat) choose k) > 0"
  apply (induct n rule: induct'_nat) 
  apply force
  apply clarify
  apply (case_tac "k = 0")
  apply force
  apply (subst choose_reduce_nat)
  apply auto
  done

lemma choose_pos_int: "n \<ge> 0 \<Longrightarrow> k >= 0 \<Longrightarrow> k \<le> n \<Longrightarrow>
    ((n::int) choose k) > 0"
  by (auto simp add: binomial_int_def choose_pos_nat)

lemma binomial_induct [rule_format]: "(ALL (n::nat). P n n) \<longrightarrow> 
    (ALL n. P (n + 1) 0) \<longrightarrow> (ALL n. (ALL k < n. P n k \<longrightarrow> P n (k + 1) \<longrightarrow>
    P (n + 1) (k + 1))) \<longrightarrow> (ALL k <= n. P n k)"
  apply (induct n rule: induct'_nat)
  apply auto
  apply (case_tac "k = 0")
  apply auto
  apply (case_tac "k = n + 1")
  apply auto
  apply (drule_tac x = n in spec) back back 
  apply (drule_tac x = "k - 1" in spec) back back back
  apply auto
  done

lemma choose_altdef_aux_nat: "(k::nat) \<le> n \<Longrightarrow> 
    fact k * fact (n - k) * (n choose k) = fact n"
  apply (rule binomial_induct [of _ k n])
  apply auto
proof -
  fix k :: nat and n
  assume less: "k < n"
  assume ih1: "fact k * fact (n - k) * (n choose k) = fact n"
  then have one: "fact (k + 1) * fact (n - k) * (n choose k) = (k + 1) * fact n"
    by (subst fact_plus_one_nat, auto)
  assume ih2: "fact (k + 1) * fact (n - (k + 1)) * (n choose (k + 1)) =  fact n"
  with less have "fact (k + 1) * fact ((n - (k + 1)) + 1) * 
      (n choose (k + 1)) = (n - k) * fact n"
    by (subst (2) fact_plus_one_nat, auto)
  with less have two: "fact (k + 1) * fact (n - k) * (n choose (k + 1)) = 
      (n - k) * fact n" by simp
  have "fact (k + 1) * fact (n - k) * (n + 1 choose (k + 1)) =
      fact (k + 1) * fact (n - k) * (n choose (k + 1)) + 
      fact (k + 1) * fact (n - k) * (n choose k)" 
    by (subst choose_reduce_nat, auto simp add: field_simps)
  also note one
  also note two
  also from less have "(n - k) * fact n + (k + 1) * fact n= fact (n + 1)" 
    apply (subst fact_plus_one_nat)
    apply (subst distrib_right [symmetric])
    apply simp
    done
  finally show "fact (k + 1) * fact (n - k) * (n + 1 choose (k + 1)) = 
    fact (n + 1)" .
qed

lemma choose_altdef_nat: "(k::nat) \<le> n \<Longrightarrow> 
    n choose k = fact n div (fact k * fact (n - k))"
  apply (frule choose_altdef_aux_nat)
  apply (erule subst)
  apply (simp add: mult_ac)
  done


lemma choose_altdef_int: 
  assumes "(0::int) <= k" and "k <= n"
  shows "n choose k = fact n div (fact k * fact (n - k))"
  apply (subst tsub_eq [symmetric], rule assms)
  apply (rule choose_altdef_nat [transferred])
  using assms apply auto
  done

lemma choose_dvd_nat: "(k::nat) \<le> n \<Longrightarrow> fact k * fact (n - k) dvd fact n"
  unfolding dvd_def apply (frule choose_altdef_aux_nat)
  (* why don't blast and auto get this??? *)
  apply (rule exI)
  apply (erule sym)
  done

lemma choose_dvd_int: 
  assumes "(0::int) <= k" and "k <= n"
  shows "fact k * fact (n - k) dvd fact n"
  apply (subst tsub_eq [symmetric], rule assms)
  apply (rule choose_dvd_nat [transferred])
  using assms apply auto
  done

(* generalizes Tobias Nipkow's proof to any commutative semiring *)
theorem binomial: "(a+b::'a::{comm_ring_1,power})^n = 
  (SUM k=0..n. (of_nat (n choose k)) * a^k * b^(n-k))" (is "?P n")
proof (induct n rule: induct'_nat)
  show "?P 0" by simp
next
  fix n
  assume ih: "?P n"
  have decomp: "{0..n+1} = {0} Un {n+1} Un {1..n}"
    by auto
  have decomp2: "{0..n} = {0} Un {1..n}"
    by auto
  have decomp3: "{1..n+1} = {n+1} Un {1..n}"
    by auto
  have "(a+b)^(n+1) = 
      (a+b) * (SUM k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    using ih by simp
  also have "... =  a*(SUM k=0..n. of_nat (n choose k) * a^k * b^(n-k)) +
                   b*(SUM k=0..n. of_nat (n choose k) * a^k * b^(n-k))"
    by (rule distrib)
  also have "... = (SUM k=0..n. of_nat (n choose k) * a^(k+1) * b^(n-k)) +
                  (SUM k=0..n. of_nat (n choose k) * a^k * b^(n-k+1))"
    by (subst (1 2) power_plus_one, simp add: setsum_right_distrib mult_ac)
  also have "... = (SUM k=0..n. of_nat (n choose k) * a^k * b^(n+1-k)) +
                  (SUM k=1..n+1. of_nat (n choose (k - 1)) * a^k * b^(n+1-k))"
    by (simp add:setsum_shift_bounds_cl_Suc_ivl Suc_diff_le
      field_simps One_nat_def del:setsum_cl_ivl_Suc)
  also have "... = a^(n+1) + b^(n+1) +
                  (SUM k=1..n. of_nat (n choose (k - 1)) * a^k * b^(n+1-k)) +
                  (SUM k=1..n. of_nat (n choose k) * a^k * b^(n+1-k))"
    by (simp add: decomp2 decomp3)
  also have
      "... = a^(n+1) + b^(n+1) + 
         (SUM k=1..n. of_nat(n+1 choose k) * a^k * b^(n+1-k))"
    by (auto simp add: field_simps setsum_addf [symmetric]
      choose_reduce_nat)
  also have "... = (SUM k=0..n+1. of_nat (n+1 choose k) * a^k * b^(n+1-k))"
    using decomp by (simp add: field_simps)
  finally show "?P (n + 1)" by simp
qed

lemma card_subsets_nat:
  fixes S :: "'a set"
  shows "finite S \<Longrightarrow> card {T. T \<le> S \<and> card T = k} = card S choose k"
proof (induct arbitrary: k set: finite)
  case empty
  show ?case by (auto simp add: Collect_conv_if)
next
  case (insert x F)
  note iassms = insert(1,2)
  note ih = insert(3)
  show ?case
  proof (induct k rule: induct'_nat)
    case zero
    from iassms have "{T. T \<le> (insert x F) \<and> card T = 0} = {{}}"
      by (auto simp: finite_subset)
    then show ?case by auto
  next
    case (plus1 k)
    from iassms have fin: "finite (insert x F)" by auto
    then have "{ T. T \<subseteq> insert x F \<and> card T = k + 1} =
      {T. T \<le> F & card T = k + 1} Un 
      {T. T \<le> insert x F & x : T & card T = k + 1}"
      by auto
    with iassms fin have "card ({T. T \<le> insert x F \<and> card T = k + 1}) = 
      card ({T. T \<subseteq> F \<and> card T = k + 1}) + 
      card ({T. T \<subseteq> insert x F \<and> x : T \<and> card T = k + 1})"
      apply (subst card_Un_disjoint [symmetric])
      apply auto
        (* note: nice! Didn't have to say anything here *)
      done
    also from ih have "card ({T. T \<subseteq> F \<and> card T = k + 1}) = 
      card F choose (k+1)" by auto
    also have "card ({T. T \<subseteq> insert x F \<and> x : T \<and> card T = k + 1}) =
      card ({T. T <= F & card T = k})"
    proof -
      let ?f = "%T. T Un {x}"
      from iassms have "inj_on ?f {T. T <= F & card T = k}"
        unfolding inj_on_def by auto
      then have "card ({T. T <= F & card T = k}) = 
        card(?f ` {T. T <= F & card T = k})"
        by (rule card_image [symmetric])
      also have "?f ` {T. T <= F & card T = k} = 
        {T. T \<subseteq> insert x F \<and> x : T \<and> card T = k + 1}" (is "?L=?R")
      proof-
        { fix S assume "S \<subseteq> F"
          then have "card(insert x S) = card S +1"
            using iassms by (auto simp: finite_subset) }
        moreover
        { fix T assume 1: "T \<subseteq> insert x F" "x : T" "card T = k+1"
          let ?S = "T - {x}"
          have "?S <= F & card ?S = k \<and> T = insert x ?S"
            using 1 fin by (auto simp: finite_subset) }
        ultimately show ?thesis by(auto simp: image_def)
      qed
      finally show ?thesis by (rule sym)
    qed
    also from ih have "card ({T. T <= F & card T = k}) = card F choose k"
      by auto
    finally have "card ({T. T \<le> insert x F \<and> card T = k + 1}) = 
      card F choose (k + 1) + (card F choose k)".
    with iassms choose_plus_one_nat show ?case
      by (auto simp del: card.insert)
  qed
qed

lemma choose_le_pow:
  assumes "r \<le> n" shows "n choose r \<le> n ^ r"
proof -
  have X: "\<And>r. r \<le> n \<Longrightarrow> \<Prod>{n - r..n} = (n - r) * \<Prod>{Suc (n - r)..n}"
    by (subst setprod_insert[symmetric]) (auto simp: atLeastAtMost_insertL)
  have "n choose r \<le> fact n div fact (n - r)"
    using `r \<le> n` by (simp add: choose_altdef_nat div_le_mono2)
  also have "\<dots> \<le> n ^ r" using `r \<le> n`
    by (induct r rule: nat.induct)
     (auto simp add: fact_div_fact Suc_diff_Suc X One_nat_def mult_le_mono)
 finally show ?thesis .
qed

lemma card_UNION:
  assumes "finite A" and "\<forall>k \<in> A. finite k"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. -1 ^ (card I + 1) * int (card (\<Inter>I)))"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. -1 ^ (card I + 1) * (\<Sum>_\<in>\<Inter>I. 1))" by simp
  also have "\<dots> = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (\<Sum>_\<in>\<Inter>I. -1 ^ (card I + 1)))" (is "_ = nat ?rhs")
    by(subst setsum_right_distrib) simp
  also have "?rhs = (\<Sum>(I, _)\<in>Sigma {I. I \<subseteq> A \<and> I \<noteq> {}} Inter. -1 ^ (card I + 1))"
    using assms by(subst setsum_Sigma)(auto)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:UNIV. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). -1 ^ (card I + 1))"
    by(rule setsum_reindex_cong[where f="\<lambda>(x, y). (y, x)"])(auto intro: inj_onI simp add: split_beta)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:\<Union>A. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). -1 ^ (card I + 1))"
    using assms by(auto intro!: setsum_mono_zero_cong_right finite_SigmaI2 intro: finite_subset[where B="\<Union>A"])
  also have "\<dots> = (\<Sum>x\<in>\<Union>A. (\<Sum>I|I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I. -1 ^ (card I + 1)))" 
    using assms by(subst setsum_Sigma) auto
  also have "\<dots> = (\<Sum>_\<in>\<Union>A. 1)" (is "setsum ?lhs _ = _")
  proof(rule setsum_cong[OF refl])
    fix x
    assume x: "x \<in> \<Union>A"
    def K \<equiv> "{X \<in> A. x \<in> X}"
    with `finite A` have K: "finite K" by auto

    let ?I = "\<lambda>i. {I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I}"
    have "inj_on snd (SIGMA i:{1..card A}. ?I i)"
      using assms by(auto intro!: inj_onI)
    moreover have [symmetric]: "snd ` (SIGMA i:{1..card A}. ?I i) = {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}"
      using assms by(auto intro!: rev_image_eqI[where x="(card a, a)", standard] simp add: card_gt_0_iff[folded Suc_le_eq] One_nat_def dest: finite_subset intro: card_mono)
    ultimately have "?lhs x = (\<Sum>(i, I)\<in>(SIGMA i:{1..card A}. ?I i). -1 ^ (i + 1))"
      by(rule setsum_reindex_cong[where f=snd]) fastforce
    also have "\<dots> = (\<Sum>i=1..card A. (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. -1 ^ (i + 1)))"
      using assms by(subst setsum_Sigma) auto
    also have "\<dots> = (\<Sum>i=1..card A. -1 ^ (i + 1) * (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1))"
      by(subst setsum_right_distrib) simp
    also have "\<dots> = (\<Sum>i=1..card K. -1 ^ (i + 1) * (\<Sum>I|I \<subseteq> K \<and> card I = i. 1))" (is "_ = ?rhs")
    proof(rule setsum_mono_zero_cong_right[rule_format])
      show "{1..card K} \<subseteq> {1..card A}" using `finite A`
        by(auto simp add: K_def intro: card_mono)
    next
      fix i
      assume "i \<in> {1..card A} - {1..card K}"
      hence i: "i \<le> card A" "card K < i" by auto
      have "{I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I} = {I. I \<subseteq> K \<and> card I = i}" 
        by(auto simp add: K_def)
      also have "\<dots> = {}" using `finite A` i
        by(auto simp add: K_def dest: card_mono[rotated 1])
      finally show "-1 ^ (i + 1) * (\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1 :: int) = 0"
        by(simp only:) simp
    next
      fix i
      have "(\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1) = (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)"
        (is "?lhs = ?rhs")
        by(rule setsum_cong)(auto simp add: K_def)
      thus "-1 ^ (i + 1) * ?lhs = -1 ^ (i + 1) * ?rhs" by simp
    qed simp
    also have "{I. I \<subseteq> K \<and> card I = 0} = {{}}" using assms
      by(auto simp add: card_eq_0_iff K_def dest: finite_subset)
    hence "?rhs = (\<Sum>i = 0..card K. -1 ^ (i + 1) * (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)) + 1"
      by(subst (2) setsum_head_Suc)(simp_all add: One_nat_def)
    also have "\<dots> = (\<Sum>i = 0..card K. -1 * (-1 ^ i * int (card K choose i))) + 1"
      using K by(subst card_subsets_nat[symmetric]) simp_all
    also have "\<dots> = - (\<Sum>i = 0..card K. -1 ^ i * int (card K choose i)) + 1"
      by(subst setsum_right_distrib[symmetric]) simp
    also have "\<dots> =  - ((-1 + 1) ^ card K) + 1"
      by(subst binomial)(simp add: mult_ac)
    also have "\<dots> = 1" using x K by(auto simp add: K_def card_gt_0_iff)
    finally show "?lhs x = 1" .
  qed
  also have "nat \<dots> = card (\<Union>A)" by simp
  finally show ?thesis ..
qed

end
