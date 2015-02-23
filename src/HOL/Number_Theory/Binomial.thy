(*  Title:      HOL/Number_Theory/Binomial.thy
    Authors:    Lawrence C. Paulson, Jeremy Avigad, Tobias Nipkow

Defines the "choose" function, and establishes basic properties.
*)

section {* Binomial *}

theory Binomial
imports Cong Fact Complex_Main
begin


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

lemma choose_row_sum: "(\<Sum>k=0..n. n choose k) = 2^n"
  using binomial [of 1 "1" n]
  by (simp add: numeral_2_eq_2)

lemma sum_choose_lower: "(\<Sum>k=0..n. (r+k) choose k) = Suc (r+n) choose n"
  by (induct n) auto

lemma sum_choose_upper: "(\<Sum>k=0..n. k choose m) = Suc n choose Suc m"
  by (induct n) auto

lemma natsum_reverse_index:
  fixes m::nat
  shows "(\<And>k. m \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> g k = f (m + n - k)) \<Longrightarrow> (\<Sum>k=m..n. f k) = (\<Sum>k=m..n. g k)"
  by (rule setsum.reindex_bij_witness[where i="\<lambda>k. m+n-k" and j="\<lambda>k. m+n-k"]) auto

text{*NW diagonal sum property*}
lemma sum_choose_diagonal:
  assumes "m\<le>n" shows "(\<Sum>k=0..m. (n-k) choose (m-k)) = Suc n choose m"
proof -
  have "(\<Sum>k=0..m. (n-k) choose (m-k)) = (\<Sum>k=0..m. (n-m+k) choose k)"
    by (rule natsum_reverse_index) (simp add: assms)
  also have "... = Suc (n-m+m) choose m"
    by (rule sum_choose_lower)
  also have "... = Suc n choose m" using assms
    by simp
  finally show ?thesis .
qed

subsection{* Pochhammer's symbol : generalized rising factorial *}

text {* See @{url "http://en.wikipedia.org/wiki/Pochhammer_symbol"} *}

definition "pochhammer (a::'a::comm_semiring_1) n =
  (if n = 0 then 1 else setprod (\<lambda>n. a + of_nat n) {0 .. n - 1})"

lemma pochhammer_0 [simp]: "pochhammer a 0 = 1"
  by (simp add: pochhammer_def)

lemma pochhammer_1 [simp]: "pochhammer a 1 = a"
  by (simp add: pochhammer_def)

lemma pochhammer_Suc0 [simp]: "pochhammer a (Suc 0) = a"
  by (simp add: pochhammer_def)

lemma pochhammer_Suc_setprod: "pochhammer a (Suc n) = setprod (\<lambda>n. a + of_nat n) {0 .. n}"
  by (simp add: pochhammer_def)

lemma setprod_nat_ivl_Suc: "setprod f {0 .. Suc n} = setprod f {0..n} * f (Suc n)"
proof -
  have "{0..Suc n} = {0..n} \<union> {Suc n}" by auto
  then show ?thesis by (simp add: field_simps)
qed

lemma setprod_nat_ivl_1_Suc: "setprod f {0 .. Suc n} = f 0 * setprod f {1.. Suc n}"
proof -
  have "{0..Suc n} = {0} \<union> {1 .. Suc n}" by auto
  then show ?thesis by simp
qed


lemma pochhammer_Suc: "pochhammer a (Suc n) = pochhammer a n * (a + of_nat n)"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
  show ?thesis unfolding Suc pochhammer_Suc_setprod setprod_nat_ivl_Suc ..
qed

lemma pochhammer_rec: "pochhammer a (Suc n) = a * pochhammer (a + 1) n"
proof (cases "n = 0")
  case True
  then show ?thesis by (simp add: pochhammer_Suc_setprod)
next
  case False
  have *: "finite {1 .. n}" "0 \<notin> {1 .. n}" by auto
  have eq: "insert 0 {1 .. n} = {0..n}" by auto
  have **: "(\<Prod>n\<in>{1\<Colon>nat..n}. a + of_nat n) = (\<Prod>n\<in>{0\<Colon>nat..n - 1}. a + 1 + of_nat n)"
    apply (rule setprod.reindex_cong [where l = Suc])
    using False
    apply (auto simp add: fun_eq_iff field_simps)
    done
  show ?thesis
    apply (simp add: pochhammer_def)
    unfolding setprod.insert [OF *, unfolded eq]
    using ** apply (simp add: field_simps)
    done
qed

lemma pochhammer_fact: "of_nat (fact n) = pochhammer 1 n"
  unfolding fact_altdef_nat
  apply (cases n)
   apply (simp_all add: of_nat_setprod pochhammer_Suc_setprod)
  apply (rule setprod.reindex_cong [where l = Suc])
    apply (auto simp add: fun_eq_iff)
  done

lemma pochhammer_of_nat_eq_0_lemma:
  assumes "k > n"
  shows "pochhammer (- (of_nat n :: 'a:: idom)) k = 0"
proof (cases "n = 0")
  case True
  then show ?thesis
    using assms by (cases k) (simp_all add: pochhammer_rec)
next
  case False
  from assms obtain h where "k = Suc h" by (cases k) auto
  then show ?thesis
    by (simp add: pochhammer_Suc_setprod)
       (metis Suc_leI Suc_le_mono assms atLeastAtMost_iff less_eq_nat.simps(1))
qed

lemma pochhammer_of_nat_eq_0_lemma':
  assumes kn: "k \<le> n"
  shows "pochhammer (- (of_nat n :: 'a:: {idom,ring_char_0})) k \<noteq> 0"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  then show ?thesis
    apply (simp add: pochhammer_Suc_setprod)
    using Suc kn apply (auto simp add: algebra_simps)
    done
qed

lemma pochhammer_of_nat_eq_0_iff:
  shows "pochhammer (- (of_nat n :: 'a:: {idom,ring_char_0})) k = 0 \<longleftrightarrow> k > n"
  (is "?l = ?r")
  using pochhammer_of_nat_eq_0_lemma[of n k, where ?'a='a]
    pochhammer_of_nat_eq_0_lemma'[of k n, where ?'a = 'a]
  by (auto simp add: not_le[symmetric])


lemma pochhammer_eq_0_iff: "pochhammer a n = (0::'a::field_char_0) \<longleftrightarrow> (\<exists>k < n. a = - of_nat k)"
  apply (auto simp add: pochhammer_of_nat_eq_0_iff)
  apply (cases n)
   apply (auto simp add: pochhammer_def algebra_simps group_add_class.eq_neg_iff_add_eq_0)
  apply (metis leD not_less_eq)
  done


lemma pochhammer_eq_0_mono:
  "pochhammer a n = (0::'a::field_char_0) \<Longrightarrow> m \<ge> n \<Longrightarrow> pochhammer a m = 0"
  unfolding pochhammer_eq_0_iff by auto

lemma pochhammer_neq_0_mono:
  "pochhammer a m \<noteq> (0::'a::field_char_0) \<Longrightarrow> m \<ge> n \<Longrightarrow> pochhammer a n \<noteq> 0"
  unfolding pochhammer_eq_0_iff by auto

lemma pochhammer_minus:
  assumes kn: "k \<le> n"
  shows "pochhammer (- b) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (b - of_nat k + 1) k"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq: "((- 1) ^ Suc h :: 'a) = (\<Prod>i=0..h. - 1)"
    using setprod_constant[where A="{0 .. h}" and y="- 1 :: 'a"]
    by auto
  show ?thesis
    unfolding Suc pochhammer_Suc_setprod eq setprod.distrib[symmetric]
    by (rule setprod.reindex_bij_witness[where i="op - h" and j="op - h"])
       (auto simp: of_nat_diff)
qed

lemma pochhammer_minus':
  assumes kn: "k \<le> n"
  shows "pochhammer (b - of_nat k + 1) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (- b) k"
  unfolding pochhammer_minus[OF kn, where b=b]
  unfolding mult.assoc[symmetric]
  unfolding power_add[symmetric]
  by simp

lemma pochhammer_same: "pochhammer (- of_nat n) n =
    ((- 1) ^ n :: 'a::comm_ring_1) * of_nat (fact n)"
  unfolding pochhammer_minus[OF le_refl[of n]]
  by (simp add: of_nat_diff pochhammer_fact)


subsection{* Generalized binomial coefficients *}

definition gbinomial :: "'a::field_char_0 \<Rightarrow> nat \<Rightarrow> 'a" (infixl "gchoose" 65)
  where "a gchoose n =
    (if n = 0 then 1 else (setprod (\<lambda>i. a - of_nat i) {0 .. n - 1}) / of_nat (fact n))"

lemma gbinomial_0 [simp]: "a gchoose 0 = 1" "0 gchoose (Suc n) = 0"
  apply (simp_all add: gbinomial_def)
  apply (subgoal_tac "(\<Prod>i\<Colon>nat\<in>{0\<Colon>nat..n}. - of_nat i) = (0::'b)")
   apply (simp del:setprod_zero_iff)
  apply simp
  done

lemma gbinomial_pochhammer: "a gchoose n = (- 1) ^ n * pochhammer (- a) n / of_nat (fact n)"
proof (cases "n = 0")
  case True
  then show ?thesis by simp
next
  case False
  from this setprod_constant[of "{0 .. n - 1}" "- (1:: 'a)"]
  have eq: "(- (1\<Colon>'a)) ^ n = setprod (\<lambda>i. - 1) {0 .. n - 1}"
    by auto
  from False show ?thesis
    by (simp add: pochhammer_def gbinomial_def field_simps
      eq setprod.distrib[symmetric])
qed

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
  shows "(of_nat (n choose k) :: 'a::field_char_0) =
    of_nat (fact n) / (of_nat (fact k) * of_nat (fact (n - k)))"
  using binomial_fact_lemma[OF kn]
  by (simp add: field_simps of_nat_mult [symmetric])

lemma binomial_gbinomial: "of_nat (n choose k) = of_nat n gchoose k"
proof -
  { assume kn: "k > n"
    then have ?thesis
      by (subst binomial_eq_0[OF kn]) 
         (simp add: gbinomial_pochhammer field_simps  pochhammer_of_nat_eq_0_iff) }
  moreover
  { assume "k=0" then have ?thesis by simp }
  moreover
  { assume kn: "k \<le> n" and k0: "k\<noteq> 0"
    from k0 obtain h where h: "k = Suc h" by (cases k) auto
    from h
    have eq:"(- 1 :: 'a) ^ k = setprod (\<lambda>i. - 1) {0..h}"
      by (subst setprod_constant) auto
    have eq': "(\<Prod>i\<in>{0..h}. of_nat n + - (of_nat i :: 'a)) = (\<Prod>i\<in>{n - h..n}. of_nat i)"
        using h kn
      by (intro setprod.reindex_bij_witness[where i="op - n" and j="op - n"])
         (auto simp: of_nat_diff)
    have th0: "finite {1..n - Suc h}" "finite {n - h .. n}"
        "{1..n - Suc h} \<inter> {n - h .. n} = {}" and
        eq3: "{1..n - Suc h} \<union> {n - h .. n} = {1..n}"
      using h kn by auto
    from eq[symmetric]
    have ?thesis using kn
      apply (simp add: binomial_fact[OF kn, where ?'a = 'a]
        gbinomial_pochhammer field_simps pochhammer_Suc_setprod)
      apply (simp add: pochhammer_Suc_setprod fact_altdef_nat h
        of_nat_setprod setprod.distrib[symmetric] eq' del: One_nat_def power_Suc)
      unfolding setprod.union_disjoint[OF th0, unfolded eq3, of "of_nat:: nat \<Rightarrow> 'a"] eq[unfolded h]
      unfolding mult.assoc[symmetric]
      unfolding setprod.distrib[symmetric]
      apply simp
      apply (intro setprod.reindex_bij_witness[where i="op - n" and j="op - n"])
      apply (auto simp: of_nat_diff)
      done
  }
  moreover
  have "k > n \<or> k = 0 \<or> (k \<le> n \<and> k \<noteq> 0)" by arith
  ultimately show ?thesis by blast
qed

lemma gbinomial_1[simp]: "a gchoose 1 = a"
  by (simp add: gbinomial_def)

lemma gbinomial_Suc0[simp]: "a gchoose (Suc 0) = a"
  by (simp add: gbinomial_def)

lemma gbinomial_mult_1:
  "a * (a gchoose n) =
    of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"  (is "?l = ?r")
proof -
  have "?r = ((- 1) ^n * pochhammer (- a) n / of_nat (fact n)) * (of_nat n - (- a + of_nat n))"
    unfolding gbinomial_pochhammer
      pochhammer_Suc fact_Suc of_nat_mult right_diff_distrib power_Suc
    by (simp add:  field_simps del: of_nat_Suc)
  also have "\<dots> = ?l" unfolding gbinomial_pochhammer
    by (simp add: field_simps)
  finally show ?thesis ..
qed

lemma gbinomial_mult_1':
    "(a gchoose n) * a = of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"
  by (simp add: mult.commute gbinomial_mult_1)

lemma gbinomial_Suc:
    "a gchoose (Suc k) = (setprod (\<lambda>i. a - of_nat i) {0 .. k}) / of_nat (fact (Suc k))"
  by (simp add: gbinomial_def)

lemma gbinomial_mult_fact:
  "(of_nat (fact (Suc k)) :: 'a) * ((a::'a::field_char_0) gchoose (Suc k)) =
    (setprod (\<lambda>i. a - of_nat i) {0 .. k})"
  by (simp_all add: gbinomial_Suc field_simps del: fact_Suc)

lemma gbinomial_mult_fact':
  "((a::'a::field_char_0) gchoose (Suc k)) * (of_nat (fact (Suc k)) :: 'a) =
    (setprod (\<lambda>i. a - of_nat i) {0 .. k})"
  using gbinomial_mult_fact[of k a]
  by (subst mult.commute)


lemma gbinomial_Suc_Suc:
  "((a::'a::field_char_0) + 1) gchoose (Suc k) = a gchoose k + (a gchoose (Suc k))"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc h)
  have eq0: "(\<Prod>i\<in>{1..k}. (a + 1) - of_nat i) = (\<Prod>i\<in>{0..h}. a - of_nat i)"
    apply (rule setprod.reindex_cong [where l = Suc])
      using Suc
      apply auto
    done
  have "of_nat (fact (Suc k)) * (a gchoose k + (a gchoose (Suc k))) =
    ((a gchoose Suc h) * of_nat (fact (Suc h)) * of_nat (Suc k)) + (\<Prod>i\<in>{0\<Colon>nat..Suc h}. a - of_nat i)"
    apply (simp add: Suc field_simps del: fact_Suc)
    unfolding gbinomial_mult_fact'
    apply (subst fact_Suc)
    unfolding of_nat_mult
    apply (subst mult.commute)
    unfolding mult.assoc
    unfolding gbinomial_mult_fact
    apply (simp add: field_simps)
    done
  also have "\<dots> = (\<Prod>i\<in>{0..h}. a - of_nat i) * (a + 1)"
    unfolding gbinomial_mult_fact' setprod_nat_ivl_Suc
    by (simp add: field_simps Suc)
  also have "\<dots> = (\<Prod>i\<in>{0..k}. (a + 1) - of_nat i)"
    using eq0
    by (simp add: Suc setprod_nat_ivl_1_Suc)
  also have "\<dots> = of_nat (fact (Suc k)) * ((a + 1) gchoose (Suc k))"
    unfolding gbinomial_mult_fact ..
  finally show ?thesis by (simp del: fact_Suc)
qed

lemma gbinomial_reduce_nat:
  "0 < k \<Longrightarrow> (a::'a::field_char_0) gchoose k = (a - 1) gchoose (k - 1) + ((a - 1) gchoose k)"
by (metis Suc_pred' diff_add_cancel gbinomial_Suc_Suc)


lemma binomial_symmetric:
  assumes kn: "k \<le> n"
  shows "n choose k = n choose (n - k)"
proof-
  from kn have kn': "n - k \<le> n" by arith
  from binomial_fact_lemma[OF kn] binomial_fact_lemma[OF kn']
  have "fact k * fact (n - k) * (n choose k) =
    fact (n - k) * fact (n - (n - k)) * (n choose (n - k))" by simp
  then show ?thesis using kn by simp
qed

text{*Contributed by Manuel Eberl, generalised by LCP.
  Alternative definition of the binomial coefficient as @{term "\<Prod>i<k. (n - i) / (k - i)"} *}
lemma gbinomial_altdef_of_nat:
  fixes k :: nat
    and x :: "'a :: {field_char_0,field_inverse_zero}"
  shows "x gchoose k = (\<Prod>i<k. (x - of_nat i) / of_nat (k - i) :: 'a)"
proof -
  have "(x gchoose k) = (\<Prod>i<k. x - of_nat i) / of_nat (fact k)"
    unfolding gbinomial_def
    by (auto simp: gr0_conv_Suc lessThan_Suc_atMost atLeast0AtMost)
  also have "\<dots> = (\<Prod>i<k. (x - of_nat i) / of_nat (k - i) :: 'a)"
    unfolding fact_eq_rev_setprod_nat of_nat_setprod
    by (auto simp add: setprod_dividef intro!: setprod.cong of_nat_diff[symmetric])
  finally show ?thesis .
qed

lemma gbinomial_ge_n_over_k_pow_k:
  fixes k :: nat
    and x :: "'a :: linordered_field_inverse_zero"
  assumes "of_nat k \<le> x"
  shows "(x / of_nat k :: 'a) ^ k \<le> x gchoose k"
proof -
  have x: "0 \<le> x"
    using assms of_nat_0_le_iff order_trans by blast
  have "(x / of_nat k :: 'a) ^ k = (\<Prod>i<k. x / of_nat k :: 'a)"
    by (simp add: setprod_constant)
  also have "\<dots> \<le> x gchoose k"
    unfolding gbinomial_altdef_of_nat
  proof (safe intro!: setprod_mono)
    fix i :: nat
    assume ik: "i < k"
    from assms have "x * of_nat i \<ge> of_nat (i * k)"
      by (metis mult.commute mult_le_cancel_right of_nat_less_0_iff of_nat_mult)
    then have "x * of_nat k - x * of_nat i \<le> x * of_nat k - of_nat (i * k)" by arith
    then have "x * of_nat (k - i) \<le> (x - of_nat i) * of_nat k"
      using ik 
      by (simp add: algebra_simps zero_less_mult_iff of_nat_diff of_nat_mult)
    then have "x * of_nat (k - i) \<le> (x - of_nat i) * (of_nat k :: 'a)"
      unfolding of_nat_mult[symmetric] of_nat_le_iff .
    with assms show "x / of_nat k \<le> (x - of_nat i) / (of_nat (k - i) :: 'a)"
      using `i < k` by (simp add: field_simps)
  qed (simp add: x zero_le_divide_iff)
  finally show ?thesis .
qed

text{*Versions of the theorems above for the natural-number version of "choose"*}
lemma binomial_altdef_of_nat:
  fixes n k :: nat
    and x :: "'a :: {field_char_0,field_inverse_zero}"  --{*the point is to constrain @{typ 'a}*}
  assumes "k \<le> n"
  shows "of_nat (n choose k) = (\<Prod>i<k. of_nat (n - i) / of_nat (k - i) :: 'a)"
using assms
by (simp add: gbinomial_altdef_of_nat binomial_gbinomial of_nat_diff)

lemma binomial_ge_n_over_k_pow_k:
  fixes k n :: nat
    and x :: "'a :: linordered_field_inverse_zero"
  assumes "k \<le> n"
  shows "(of_nat n / of_nat k :: 'a) ^ k \<le> of_nat (n choose k)"
by (simp add: assms gbinomial_ge_n_over_k_pow_k binomial_gbinomial of_nat_diff)  
  
lemma binomial_le_pow:
  assumes "r \<le> n"
  shows "n choose r \<le> n ^ r"
proof -
  have "n choose r \<le> fact n div fact (n - r)"
    using `r \<le> n` by (subst binomial_fact_lemma[symmetric]) auto
  with fact_div_fact_le_pow [OF assms] show ?thesis by auto
qed

lemma binomial_altdef_nat: "(k::nat) \<le> n \<Longrightarrow>
    n choose k = fact n div (fact k * fact (n - k))"
 by (subst binomial_fact_lemma [symmetric]) auto

lemma choose_dvd_nat: "(k::nat) \<le> n \<Longrightarrow> fact k * fact (n - k) dvd fact n"
by (metis binomial_fact_lemma dvd_def)

lemma choose_dvd_int: 
  assumes "(0::int) <= k" and "k <= n"
  shows "fact k * fact (n - k) dvd fact n"
  apply (subst tsub_eq [symmetric], rule assms)
  apply (rule choose_dvd_nat [transferred])
  using assms apply auto
  done

lemma fact_fact_dvd_fact: fixes k::nat shows "fact k * fact n dvd fact (n + k)"
by (metis add.commute add_diff_cancel_left' choose_dvd_nat le_add2)

lemma choose_mult_lemma:
     "((m+r+k) choose (m+k)) * ((m+k) choose k) = ((m+r+k) choose k) * ((m+r) choose m)"
proof -
  have "((m+r+k) choose (m+k)) * ((m+k) choose k) =
        fact (m+r + k) div (fact (m + k) * fact (m+r - m)) * (fact (m + k) div (fact k * fact m))"
    by (simp add: assms binomial_altdef_nat)
  also have "... = fact (m+r+k) div (fact r * (fact k * fact m))"
    apply (subst div_mult_div_if_dvd)
    apply (auto simp: fact_fact_dvd_fact)
    apply (metis add.assoc add.commute fact_fact_dvd_fact)
    done
  also have "... = (fact (m+r+k) * fact (m+r)) div (fact r * (fact k * fact m) * fact (m+r))"
    apply (subst div_mult_div_if_dvd [symmetric])
    apply (auto simp: fact_fact_dvd_fact)
    apply (metis dvd_trans dvd.dual_order.refl fact_fact_dvd_fact mult_dvd_mono mult.left_commute)
    done
  also have "... = (fact (m+r+k) div (fact k * fact (m+r)) * (fact (m+r) div (fact r * fact m)))"
    apply (subst div_mult_div_if_dvd)
    apply (auto simp: fact_fact_dvd_fact)
    apply(metis mult.left_commute)
    done
  finally show ?thesis
    by (simp add: binomial_altdef_nat mult.commute)
qed

text{*The "Subset of a Subset" identity*}
lemma choose_mult:
  assumes "k\<le>m" "m\<le>n"
    shows "(n choose m) * (m choose k) = (n choose k) * ((n-k) choose (m-k))"
using assms choose_mult_lemma [of "m-k" "n-m" k]
by simp


subsection {* Binomial coefficients *}

lemma choose_one: "(n::nat) choose 1 = n"
  by simp

(*FIXME: messy and apparently unused*)
lemma binomial_induct [rule_format]: "(ALL (n::nat). P n n) \<longrightarrow> 
    (ALL n. P (Suc n) 0) \<longrightarrow> (ALL n. (ALL k < n. P n k \<longrightarrow> P n (Suc k) \<longrightarrow>
    P (Suc n) (Suc k))) \<longrightarrow> (ALL k <= n. P n k)"
  apply (induct n)
  apply auto
  apply (case_tac "k = 0")
  apply auto
  apply (case_tac "k = Suc n")
  apply auto
  apply (metis Suc_le_eq fact_nat.cases le_Suc_eq le_eq_less_or_eq)
  done

lemma card_UNION:
  assumes "finite A" and "\<forall>k \<in> A. finite k"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  (is "?lhs = ?rhs")
proof -
  have "?rhs = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * (\<Sum>_\<in>\<Inter>I. 1))" by simp
  also have "\<dots> = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (\<Sum>_\<in>\<Inter>I. (- 1) ^ (card I + 1)))" (is "_ = nat ?rhs")
    by(subst setsum_right_distrib) simp
  also have "?rhs = (\<Sum>(I, _)\<in>Sigma {I. I \<subseteq> A \<and> I \<noteq> {}} Inter. (- 1) ^ (card I + 1))"
    using assms by(subst setsum.Sigma)(auto)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:UNIV. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    by (rule setsum.reindex_cong [where l = "\<lambda>(x, y). (y, x)"]) (auto intro: inj_onI simp add: split_beta)
  also have "\<dots> = (\<Sum>(x, I)\<in>(SIGMA x:\<Union>A. {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}). (- 1) ^ (card I + 1))"
    using assms by(auto intro!: setsum.mono_neutral_cong_right finite_SigmaI2 intro: finite_subset[where B="\<Union>A"])
  also have "\<dots> = (\<Sum>x\<in>\<Union>A. (\<Sum>I|I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I. (- 1) ^ (card I + 1)))" 
    using assms by(subst setsum.Sigma) auto
  also have "\<dots> = (\<Sum>_\<in>\<Union>A. 1)" (is "setsum ?lhs _ = _")
  proof(rule setsum.cong[OF refl])
    fix x
    assume x: "x \<in> \<Union>A"
    def K \<equiv> "{X \<in> A. x \<in> X}"
    with `finite A` have K: "finite K" by auto
    let ?I = "\<lambda>i. {I. I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I}"
    have "inj_on snd (SIGMA i:{1..card A}. ?I i)"
      using assms by(auto intro!: inj_onI)
    moreover have [symmetric]: "snd ` (SIGMA i:{1..card A}. ?I i) = {I. I \<subseteq> A \<and> I \<noteq> {} \<and> x \<in> \<Inter>I}"
      using assms by(auto intro!: rev_image_eqI[where x="(card a, a)" for a]
        simp add: card_gt_0_iff[folded Suc_le_eq]
        dest: finite_subset intro: card_mono)
    ultimately have "?lhs x = (\<Sum>(i, I)\<in>(SIGMA i:{1..card A}. ?I i). (- 1) ^ (i + 1))"
      by (rule setsum.reindex_cong [where l = snd]) fastforce
    also have "\<dots> = (\<Sum>i=1..card A. (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. (- 1) ^ (i + 1)))"
      using assms by(subst setsum.Sigma) auto
    also have "\<dots> = (\<Sum>i=1..card A. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1))"
      by(subst setsum_right_distrib) simp
    also have "\<dots> = (\<Sum>i=1..card K. (- 1) ^ (i + 1) * (\<Sum>I|I \<subseteq> K \<and> card I = i. 1))" (is "_ = ?rhs")
    proof(rule setsum.mono_neutral_cong_right[rule_format])
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
      finally show "(- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1 :: int) = 0"
        by(simp only:) simp
    next
      fix i
      have "(\<Sum>I | I \<subseteq> A \<and> card I = i \<and> x \<in> \<Inter>I. 1) = (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)"
        (is "?lhs = ?rhs")
        by(rule setsum.cong)(auto simp add: K_def)
      thus "(- 1) ^ (i + 1) * ?lhs = (- 1) ^ (i + 1) * ?rhs" by simp
    qed simp
    also have "{I. I \<subseteq> K \<and> card I = 0} = {{}}" using assms
      by(auto simp add: card_eq_0_iff K_def dest: finite_subset)
    hence "?rhs = (\<Sum>i = 0..card K. (- 1) ^ (i + 1) * (\<Sum>I | I \<subseteq> K \<and> card I = i. 1 :: int)) + 1"
      by(subst (2) setsum_head_Suc)(simp_all )
    also have "\<dots> = (\<Sum>i = 0..card K. (- 1) * ((- 1) ^ i * int (card K choose i))) + 1"
      using K by(subst n_subsets[symmetric]) simp_all
    also have "\<dots> = - (\<Sum>i = 0..card K. (- 1) ^ i * int (card K choose i)) + 1"
      by(subst setsum_right_distrib[symmetric]) simp
    also have "\<dots> =  - ((-1 + 1) ^ card K) + 1"
      by(subst binomial_ring)(simp add: ac_simps)
    also have "\<dots> = 1" using x K by(auto simp add: K_def card_gt_0_iff)
    finally show "?lhs x = 1" .
  qed
  also have "nat \<dots> = card (\<Union>A)" by simp
  finally show ?thesis ..
qed

text{* The number of nat lists of length @{text m} summing to @{text N} is
@{term "(N + m - 1) choose N"}: *} 

lemma card_length_listsum_rec:
  assumes "m\<ge>1"
  shows "card {l::nat list. length l = m \<and> listsum l = N} =
    (card {l. length l = (m - 1) \<and> listsum l = N} +
    card {l. length l = m \<and> listsum l + 1 =  N})"
    (is "card ?C = (card ?A + card ?B)")
proof - 
  let ?A'="{l. length l = m \<and> listsum l = N \<and> hd l = 0}"
  let ?B'="{l. length l = m \<and> listsum l = N \<and> hd l \<noteq> 0}"
  let ?f ="\<lambda> l. 0#l"
  let ?g ="\<lambda> l. (hd l + 1) # tl l"
  have 1: "\<And>xs x. xs \<noteq> [] \<Longrightarrow> x = hd xs \<Longrightarrow> x # tl xs = xs" by simp
  have 2: "\<And>xs. (xs::nat list) \<noteq> [] \<Longrightarrow> listsum(tl xs) = listsum xs - hd xs"
    by(auto simp add: neq_Nil_conv)
  have f: "bij_betw ?f ?A ?A'"
    apply(rule bij_betw_byWitness[where f' = tl])
    using assms 
    by (auto simp: 2 length_0_conv[symmetric] 1 simp del: length_0_conv)
  have 3: "\<And>xs:: nat list. xs \<noteq> [] \<Longrightarrow> hd xs + (listsum xs - hd xs) = listsum xs"
    by (metis 1 listsum_simps(2) 2)
  have g: "bij_betw ?g ?B ?B'"
    apply(rule bij_betw_byWitness[where f' = "\<lambda> l. (hd l - 1) # tl l"])
    using assms
    by (auto simp: 2 length_0_conv[symmetric] intro!: 3
      simp del: length_greater_0_conv length_0_conv)
  { fix M N :: nat have "finite {xs. size xs = M \<and> set xs \<subseteq> {0..<N}}"
    using finite_lists_length_eq[OF finite_atLeastLessThan] conj_commute by auto }
    note fin = this
  have fin_A: "finite ?A" using fin[of _ "N+1"]
    by (intro finite_subset[where ?A = "?A" and ?B = "{xs. size xs = m - 1 \<and> set xs \<subseteq> {0..<N+1}}"], 
      auto simp: member_le_listsum_nat less_Suc_eq_le)
  have fin_B: "finite ?B"
    by (intro finite_subset[where ?A = "?B" and ?B = "{xs. size xs = m \<and> set xs \<subseteq> {0..<N}}"], 
      auto simp: member_le_listsum_nat less_Suc_eq_le fin)
  have uni: "?C = ?A' \<union> ?B'" by auto
  have disj: "?A' \<inter> ?B' = {}" by auto
  have "card ?C = card(?A' \<union> ?B')" using uni by simp
  also have "\<dots> = card ?A + card ?B"
    using card_Un_disjoint[OF _ _ disj] bij_betw_finite[OF f] bij_betw_finite[OF g]
      bij_betw_same_card[OF f] bij_betw_same_card[OF g] fin_A fin_B
    by presburger
  finally show ?thesis .
qed

lemma card_length_listsum: --"By Holden Lee, tidied by Tobias Nipkow"
  "card {l::nat list. size l = m \<and> listsum l = N} = (N + m - 1) choose N"
proof (cases m)
  case 0 then show ?thesis
    by (cases N) (auto simp: cong: conj_cong)
next
  case (Suc m')
    have m: "m\<ge>1" by (simp add: Suc)
    then show ?thesis
    proof (induct "N + m - 1" arbitrary: N m)
      case 0   -- "In the base case, the only solution is [0]."
      have [simp]: "{l::nat list. length l = Suc 0 \<and> (\<forall>n\<in>set l. n = 0)} = {[0]}"
        by (auto simp: length_Suc_conv)
      have "m=1 \<and> N=0" using 0 by linarith
      then show ?case by simp
    next
      case (Suc k)
      
      have c1: "card {l::nat list. size l = (m - 1) \<and> listsum l =  N} = 
        (N + (m - 1) - 1) choose N"
      proof cases
        assume "m = 1"
        with Suc.hyps have "N\<ge>1" by auto
        with `m = 1` show ?thesis by (simp add: binomial_eq_0)
      next
        assume "m \<noteq> 1" thus ?thesis using Suc by fastforce
      qed
    
      from Suc have c2: "card {l::nat list. size l = m \<and> listsum l + 1 = N} = 
        (if N>0 then ((N - 1) + m - 1) choose (N - 1) else 0)"
      proof -
        have aux: "\<And>m n. n > 0 \<Longrightarrow> Suc m = n \<longleftrightarrow> m = n - 1" by arith
        from Suc have "N>0 \<Longrightarrow>
          card {l::nat list. size l = m \<and> listsum l + 1 = N} = 
          ((N - 1) + m - 1) choose (N - 1)" by (simp add: aux)
        thus ?thesis by auto
      qed
    
      from Suc.prems have "(card {l::nat list. size l = (m - 1) \<and> listsum l = N} + 
          card {l::nat list. size l = m \<and> listsum l + 1 = N}) = (N + m - 1) choose N"
        by (auto simp: c1 c2 choose_reduce_nat[of "N + m - 1" N] simp del: One_nat_def)
      thus ?case using card_length_listsum_rec[OF Suc.prems] by auto
    qed
qed

end
