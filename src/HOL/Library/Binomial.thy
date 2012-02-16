(*  Title:      HOL/Library/Binomial.thy
    Author:     Lawrence C Paulson, Amine Chaieb
    Copyright   1997  University of Cambridge
*)

header {* Binomial Coefficients *}

theory Binomial
imports Complex_Main
begin

text {* This development is based on the work of Andy Gordon and
  Florian Kammueller. *}

primrec binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "choose" 65) where
  binomial_0: "(0 choose k) = (if k = 0 then 1 else 0)"
  | binomial_Suc: "(Suc n choose k) =
                 (if k = 0 then 1 else (n choose (k - 1)) + (n choose k))"

lemma binomial_n_0 [simp]: "(n choose 0) = 1"
by (cases n) simp_all

lemma binomial_0_Suc [simp]: "(0 choose Suc k) = 0"
by simp

lemma binomial_Suc_Suc [simp]:
  "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)"
by simp

lemma binomial_eq_0: "!!k. n < k ==> (n choose k) = 0"
by (induct n) auto

declare binomial_0 [simp del] binomial_Suc [simp del]

lemma binomial_n_n [simp]: "(n choose n) = 1"
by (induct n) (simp_all add: binomial_eq_0)

lemma binomial_Suc_n [simp]: "(Suc n choose n) = Suc n"
by (induct n) simp_all

lemma binomial_1 [simp]: "(n choose Suc 0) = n"
by (induct n) simp_all

lemma zero_less_binomial: "k \<le> n ==> (n choose k) > 0"
by (induct n k rule: diff_induct) simp_all

lemma binomial_eq_0_iff: "(n choose k = 0) = (n<k)"
apply (safe intro!: binomial_eq_0)
apply (erule contrapos_pp)
apply (simp add: zero_less_binomial)
done

lemma zero_less_binomial_iff: "(n choose k > 0) = (k\<le>n)"
by(simp add: linorder_not_less binomial_eq_0_iff neq0_conv[symmetric]
        del:neq0_conv)

(*Might be more useful if re-oriented*)
lemma Suc_times_binomial_eq:
  "!!k. k \<le> n ==> Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
apply (induct n)
apply (simp add: binomial_0)
apply (case_tac k)
apply (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq
    binomial_eq_0)
done

text{*This is the well-known version, but it's harder to use because of the
  need to reason about division.*}
lemma binomial_Suc_Suc_eq_times:
    "k \<le> n ==> (Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
  by (simp add: Suc_times_binomial_eq del: mult_Suc mult_Suc_right)

text{*Another version, with -1 instead of Suc.*}
lemma times_binomial_minus1_eq:
    "[|k \<le> n;  0<k|] ==> (n choose k) * k = n * ((n - 1) choose (k - 1))"
  apply (cut_tac n = "n - 1" and k = "k - 1" in Suc_times_binomial_eq)
  apply (simp split add: nat_diff_split, auto)
  done


subsection {* Theorems about @{text "choose"} *}

text {*
  \medskip Basic theorem about @{text "choose"}.  By Florian
  Kamm\"uller, tidied by LCP.
*}

lemma card_s_0_eq_empty:
    "finite A ==> card {B. B \<subseteq> A & card B = 0} = 1"
by (simp cong add: conj_cong add: finite_subset [THEN card_0_eq])

lemma choose_deconstruct: "finite M ==> x \<notin> M
  ==> {s. s <= insert x M & card(s) = Suc k}
       = {s. s <= M & card(s) = Suc k} Un
         {s. EX t. t <= M & card(t) = k & s = insert x t}"
  apply safe
   apply (auto intro: finite_subset [THEN card_insert_disjoint])
  apply (drule_tac x = "xa - {x}" in spec)
  apply (subgoal_tac "x \<notin> xa", auto)
  apply (erule rev_mp, subst card_Diff_singleton)
  apply (auto intro: finite_subset)
  done
(*
lemma "finite(UN y. {x. P x y})"
apply simp
lemma Collect_ex_eq

lemma "{x. EX y. P x y} = (UN y. {x. P x y})"
apply blast
*)

lemma finite_bex_subset[simp]:
  "finite B \<Longrightarrow> (!!A. A<=B \<Longrightarrow> finite{x. P x A}) \<Longrightarrow> finite{x. EX A<=B. P x A}"
apply(subgoal_tac "{x. EX A<=B. P x A} = (UN A:Pow B. {x. P x A})")
 apply simp
apply blast
done

text{*There are as many subsets of @{term A} having cardinality @{term k}
 as there are sets obtained from the former by inserting a fixed element
 @{term x} into each.*}
lemma constr_bij:
   "[|finite A; x \<notin> A|] ==>
    card {B. EX C. C <= A & card(C) = k & B = insert x C} =
    card {B. B <= A & card(B) = k}"
apply (rule_tac f = "%s. s - {x}" and g = "insert x" in card_bij_eq)
     apply (auto elim!: equalityE simp add: inj_on_def)
apply (subst Diff_insert0, auto)
done

text {*
  Main theorem: combinatorial statement about number of subsets of a set.
*}

lemma n_sub_lemma:
    "!!A. finite A ==> card {B. B <= A & card B = k} = (card A choose k)"
  apply (induct k)
   apply (simp add: card_s_0_eq_empty, atomize)
  apply (rotate_tac -1, erule finite_induct)
   apply (simp_all (no_asm_simp) cong add: conj_cong
     add: card_s_0_eq_empty choose_deconstruct)
  apply (subst card_Un_disjoint)
     prefer 4 apply (force simp add: constr_bij)
    prefer 3 apply force
   prefer 2 apply (blast intro: finite_Pow_iff [THEN iffD2]
     finite_subset [of _ "Pow (insert x F)", standard])
  apply (blast intro: finite_Pow_iff [THEN iffD2, THEN [2] finite_subset])
  done

theorem n_subsets:
    "finite A ==> card {B. B <= A & card B = k} = (card A choose k)"
  by (simp add: n_sub_lemma)


text{* The binomial theorem (courtesy of Tobias Nipkow): *}

theorem binomial: "(a+b::nat)^n = (\<Sum>k=0..n. (n choose k) * a^k * b^(n-k))"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  have decomp: "{0..n+1} = {0} \<union> {n+1} \<union> {1..n}"
    by (auto simp add:atLeastAtMost_def atLeast_def atMost_def)
  have decomp2: "{0..n} = {0} \<union> {1..n}"
    by (auto simp add:atLeastAtMost_def atLeast_def atMost_def)
  have "(a+b::nat)^(n+1) = (a+b) * (\<Sum>k=0..n. (n choose k) * a^k * b^(n-k))"
    using Suc by simp
  also have "\<dots> =  a*(\<Sum>k=0..n. (n choose k) * a^k * b^(n-k)) +
                   b*(\<Sum>k=0..n. (n choose k) * a^k * b^(n-k))"
    by (rule nat_distrib)
  also have "\<dots> = (\<Sum>k=0..n. (n choose k) * a^(k+1) * b^(n-k)) +
                  (\<Sum>k=0..n. (n choose k) * a^k * b^(n-k+1))"
    by (simp add: setsum_right_distrib mult_ac)
  also have "\<dots> = (\<Sum>k=0..n. (n choose k) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n+1. (n choose (k - 1)) * a^k * b^(n+1-k))"
    by (simp add:setsum_shift_bounds_cl_Suc_ivl Suc_diff_le
             del:setsum_cl_ivl_Suc)
  also have "\<dots> = a^(n+1) + b^(n+1) +
                  (\<Sum>k=1..n. (n choose (k - 1)) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n. (n choose k) * a^k * b^(n+1-k))"
    by (simp add: decomp2)
  also have
      "\<dots> = a^(n+1) + b^(n+1) + (\<Sum>k=1..n. (n+1 choose k) * a^k * b^(n+1-k))"
    by (simp add: nat_distrib setsum_addf binomial.simps)
  also have "\<dots> = (\<Sum>k=0..n+1. (n+1 choose k) * a^k * b^(n+1-k))"
    using decomp by simp
  finally show ?case by simp
qed

subsection{* Pochhammer's symbol : generalized raising factorial*}

definition "pochhammer (a::'a::comm_semiring_1) n = (if n = 0 then 1 else setprod (\<lambda>n. a + of_nat n) {0 .. n - 1})"

lemma pochhammer_0[simp]: "pochhammer a 0 = 1" 
  by (simp add: pochhammer_def)

lemma pochhammer_1[simp]: "pochhammer a 1 = a" by (simp add: pochhammer_def)
lemma pochhammer_Suc0[simp]: "pochhammer a (Suc 0) = a" 
  by (simp add: pochhammer_def)

lemma pochhammer_Suc_setprod: "pochhammer a (Suc n) = setprod (\<lambda>n. a + of_nat n) {0 .. n}"
  by (simp add: pochhammer_def)

lemma setprod_nat_ivl_Suc: "setprod f {0 .. Suc n} = setprod f {0..n} * f (Suc n)"
proof-
  have th: "finite {0..n}" "finite {Suc n}" "{0..n} \<inter> {Suc n} = {}" by auto
  have eq: "{0..Suc n} = {0..n} \<union> {Suc n}" by auto
  show ?thesis unfolding eq setprod_Un_disjoint[OF th] by simp
qed

lemma setprod_nat_ivl_1_Suc: "setprod f {0 .. Suc n} = f 0 * setprod f {1.. Suc n}"
proof-
  have th: "finite {0}" "finite {1..Suc n}" "{0} \<inter> {1.. Suc n} = {}" by auto
  have eq: "{0..Suc n} = {0} \<union> {1 .. Suc n}" by auto
  show ?thesis unfolding eq setprod_Un_disjoint[OF th] by simp
qed


lemma pochhammer_Suc: "pochhammer a (Suc n) = pochhammer a n * (a + of_nat n)"
proof-
  {assume "n=0" then have ?thesis by simp}
  moreover
  {fix m assume m: "n = Suc m"
    have ?thesis  unfolding m pochhammer_Suc_setprod setprod_nat_ivl_Suc ..}
  ultimately show ?thesis by (cases n, auto)
qed 

lemma pochhammer_rec: "pochhammer a (Suc n) = a * pochhammer (a + 1) n"
proof-
  {assume "n=0" then have ?thesis by (simp add: pochhammer_Suc_setprod)}
  moreover
  {assume n0: "n \<noteq> 0"
    have th0: "finite {1 .. n}" "0 \<notin> {1 .. n}" by auto
    have eq: "insert 0 {1 .. n} = {0..n}" by auto
    have th1: "(\<Prod>n\<in>{1\<Colon>nat..n}. a + of_nat n) =
      (\<Prod>n\<in>{0\<Colon>nat..n - 1}. a + 1 + of_nat n)"
      apply (rule setprod_reindex_cong [where f = Suc])
      using n0 by (auto simp add: fun_eq_iff field_simps)
    have ?thesis apply (simp add: pochhammer_def)
    unfolding setprod_insert[OF th0, unfolded eq]
    using th1 by (simp add: field_simps)}
ultimately show ?thesis by blast
qed

lemma pochhammer_fact: "of_nat (fact n) = pochhammer 1 n"
  unfolding fact_altdef_nat
  
  apply (cases n, simp_all add: of_nat_setprod pochhammer_Suc_setprod)
  apply (rule setprod_reindex_cong[where f=Suc])
  by (auto simp add: fun_eq_iff)

lemma pochhammer_of_nat_eq_0_lemma: assumes kn: "k > n"
  shows "pochhammer (- (of_nat n :: 'a:: idom)) k = 0"
proof-
  from kn obtain h where h: "k = Suc h" by (cases k, auto)
  {assume n0: "n=0" then have ?thesis using kn 
      by (cases k) (simp_all add: pochhammer_rec)}
  moreover
  {assume n0: "n \<noteq> 0"
    then have ?thesis apply (simp add: h pochhammer_Suc_setprod)
  apply (rule_tac x="n" in bexI)
  using h kn by auto}
ultimately show ?thesis by blast
qed

lemma pochhammer_of_nat_eq_0_lemma': assumes kn: "k \<le> n"
  shows "pochhammer (- (of_nat n :: 'a:: {idom, ring_char_0})) k \<noteq> 0"
proof-
  {assume "k=0" then have ?thesis by simp}
  moreover
  {fix h assume h: "k = Suc h"
    then have ?thesis apply (simp add: pochhammer_Suc_setprod)
      using h kn by (auto simp add: algebra_simps)}
  ultimately show ?thesis by (cases k, auto)
qed

lemma pochhammer_of_nat_eq_0_iff: 
  shows "pochhammer (- (of_nat n :: 'a:: {idom, ring_char_0})) k = 0 \<longleftrightarrow> k > n"
  (is "?l = ?r")
  using pochhammer_of_nat_eq_0_lemma[of n k, where ?'a='a] 
    pochhammer_of_nat_eq_0_lemma'[of k n, where ?'a = 'a]
  by (auto simp add: not_le[symmetric])


lemma pochhammer_eq_0_iff: 
  "pochhammer a n = (0::'a::field_char_0) \<longleftrightarrow> (EX k < n . a = - of_nat k) "
  apply (auto simp add: pochhammer_of_nat_eq_0_iff)
  apply (cases n, auto simp add: pochhammer_def algebra_simps group_add_class.eq_neg_iff_add_eq_0)
  apply (rule_tac x=x in exI)
  apply auto
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
proof-
  {assume k0: "k = 0" then have ?thesis by simp}
  moreover 
  {fix h assume h: "k = Suc h"
    have eq: "((- 1) ^ Suc h :: 'a) = setprod (%i. - 1) {0 .. h}"
      using setprod_constant[where A="{0 .. h}" and y="- 1 :: 'a"]
      by auto
    have ?thesis
      unfolding h pochhammer_Suc_setprod eq setprod_timesf[symmetric]
      apply (rule strong_setprod_reindex_cong[where f = "%i. h - i"])
      apply (auto simp add: inj_on_def image_def h )
      apply (rule_tac x="h - x" in bexI)
      by (auto simp add: fun_eq_iff h of_nat_diff)}
  ultimately show ?thesis by (cases k, auto)
qed

lemma pochhammer_minus':
  assumes kn: "k \<le> n" 
  shows "pochhammer (b - of_nat k + 1) k = ((- 1) ^ k :: 'a::comm_ring_1) * pochhammer (- b) k"
  unfolding pochhammer_minus[OF kn, where b=b]
  unfolding mult_assoc[symmetric]
  unfolding power_add[symmetric]
  apply simp
  done

lemma pochhammer_same: "pochhammer (- of_nat n) n = ((- 1) ^ n :: 'a::comm_ring_1) * of_nat (fact n)"
  unfolding pochhammer_minus[OF le_refl[of n]]
  by (simp add: of_nat_diff pochhammer_fact)

subsection{* Generalized binomial coefficients *}

definition gbinomial :: "'a::field_char_0 \<Rightarrow> nat \<Rightarrow> 'a" (infixl "gchoose" 65)
  where "a gchoose n = (if n = 0 then 1 else (setprod (\<lambda>i. a - of_nat i) {0 .. n - 1}) / of_nat (fact n))"

lemma gbinomial_0[simp]: "a gchoose 0 = 1" "0 gchoose (Suc n) = 0"
apply (simp_all add: gbinomial_def)
apply (subgoal_tac "(\<Prod>i\<Colon>nat\<in>{0\<Colon>nat..n}. - of_nat i) = (0::'b)")
 apply (simp del:setprod_zero_iff)
apply simp
done

lemma gbinomial_pochhammer: "a gchoose n = (- 1) ^ n * pochhammer (- a) n / of_nat (fact n)"
proof-
  {assume "n=0" then have ?thesis by simp}
  moreover
  {assume n0: "n\<noteq>0"
    from n0 setprod_constant[of "{0 .. n - 1}" "- (1:: 'a)"]
    have eq: "(- (1\<Colon>'a)) ^ n = setprod (\<lambda>i. - 1) {0 .. n - 1}"
      by auto
    from n0 have ?thesis 
      by (simp add: pochhammer_def gbinomial_def field_simps eq setprod_timesf[symmetric])}
  ultimately show ?thesis by blast
qed

lemma binomial_fact_lemma:
  "k \<le> n \<Longrightarrow> fact k * fact (n - k) * (n choose k) = fact n"
proof(induct n arbitrary: k rule: nat_less_induct)
  fix n k assume H: "\<forall>m<n. \<forall>x\<le>m. fact x * fact (m - x) * (m choose x) =
                      fact m" and kn: "k \<le> n"
    let ?ths = "fact k * fact (n - k) * (n choose k) = fact n"
  {assume "n=0" then have ?ths using kn by simp}
  moreover
  {assume "k=0" then have ?ths using kn by simp}
  moreover
  {assume nk: "n=k" then have ?ths by simp}
  moreover
  {fix m h assume n: "n = Suc m" and h: "k = Suc h" and hm: "h < m"
    from n have mn: "m < n" by arith
    from hm have hm': "h \<le> m" by arith
    from hm h n kn have km: "k \<le> m" by arith
    have "m - h = Suc (m - Suc h)" using  h km hm by arith 
    with km h have th0: "fact (m - h) = (m - h) * fact (m - k)"
      by simp
    from n h th0 
    have "fact k * fact (n - k) * (n choose k) = k * (fact h * fact (m - h) * (m choose h)) +  (m - h) * (fact k * fact (m - k) * (m choose k))"
      by (simp add: field_simps)
    also have "\<dots> = (k + (m - h)) * fact m"
      using H[rule_format, OF mn hm'] H[rule_format, OF mn km]
      by (simp add: field_simps)
    finally have ?ths using h n km by simp}
  moreover have "n=0 \<or> k = 0 \<or> k = n \<or> (EX m h. n=Suc m \<and> k = Suc h \<and> h < m)" using kn by presburger
  ultimately show ?ths by blast
qed
  
lemma binomial_fact: 
  assumes kn: "k \<le> n" 
  shows "(of_nat (n choose k) :: 'a::field_char_0) = of_nat (fact n) / (of_nat (fact k) * of_nat (fact (n - k)))"
  using binomial_fact_lemma[OF kn]
  by (simp add: field_simps of_nat_mult [symmetric])

lemma binomial_gbinomial: "of_nat (n choose k) = of_nat n gchoose k"
proof-
  {assume kn: "k > n" 
    from kn binomial_eq_0[OF kn] have ?thesis 
      by (simp add: gbinomial_pochhammer field_simps
        pochhammer_of_nat_eq_0_iff)}
  moreover
  {assume "k=0" then have ?thesis by simp}
  moreover
  {assume kn: "k \<le> n" and k0: "k\<noteq> 0"
    from k0 obtain h where h: "k = Suc h" by (cases k, auto)
    from h
    have eq:"(- 1 :: 'a) ^ k = setprod (\<lambda>i. - 1) {0..h}"
      by (subst setprod_constant, auto)
    have eq': "(\<Prod>i\<in>{0..h}. of_nat n + - (of_nat i :: 'a)) = (\<Prod>i\<in>{n - h..n}. of_nat i)"
      apply (rule strong_setprod_reindex_cong[where f="op - n"])
      using h kn 
      apply (simp_all add: inj_on_def image_iff Bex_def set_eq_iff)
      apply clarsimp
      apply (presburger)
      apply presburger
      by (simp add: fun_eq_iff field_simps of_nat_add[symmetric] del: of_nat_add)
    have th0: "finite {1..n - Suc h}" "finite {n - h .. n}" 
"{1..n - Suc h} \<inter> {n - h .. n} = {}" and eq3: "{1..n - Suc h} \<union> {n - h .. n} = {1..n}" using h kn by auto
    from eq[symmetric]
    have ?thesis using kn
      apply (simp add: binomial_fact[OF kn, where ?'a = 'a] 
        gbinomial_pochhammer field_simps pochhammer_Suc_setprod)
      apply (simp add: pochhammer_Suc_setprod fact_altdef_nat h of_nat_setprod setprod_timesf[symmetric] eq' del: One_nat_def power_Suc)
      unfolding setprod_Un_disjoint[OF th0, unfolded eq3, of "of_nat:: nat \<Rightarrow> 'a"] eq[unfolded h]
      unfolding mult_assoc[symmetric] 
      unfolding setprod_timesf[symmetric]
      apply simp
      apply (rule strong_setprod_reindex_cong[where f= "op - n"])
      apply (auto simp add: inj_on_def image_iff Bex_def)
      apply presburger
      apply (subgoal_tac "(of_nat (n - x) :: 'a) = of_nat n - of_nat x")
      apply simp
      by (rule of_nat_diff, simp)
  }
  moreover
  have "k > n \<or> k = 0 \<or> (k \<le> n \<and> k \<noteq> 0)" by arith
  ultimately show ?thesis by blast
qed

lemma gbinomial_1[simp]: "a gchoose 1 = a"
  by (simp add: gbinomial_def)

lemma gbinomial_Suc0[simp]: "a gchoose (Suc 0) = a"
  by (simp add: gbinomial_def)

lemma gbinomial_mult_1: "a * (a gchoose n) = of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))" (is "?l = ?r")
proof-
  have "?r = ((- 1) ^n * pochhammer (- a) n / of_nat (fact n)) * (of_nat n - (- a + of_nat n))"
    unfolding gbinomial_pochhammer
    pochhammer_Suc fact_Suc of_nat_mult right_diff_distrib power_Suc
    by (simp add:  field_simps del: of_nat_Suc)
  also have "\<dots> = ?l" unfolding gbinomial_pochhammer
    by (simp add: field_simps)
  finally show ?thesis ..
qed

lemma gbinomial_mult_1': "(a gchoose n) * a = of_nat n * (a gchoose n) + of_nat (Suc n) * (a gchoose (Suc n))"
  by (simp add: mult_commute gbinomial_mult_1)

lemma gbinomial_Suc: "a gchoose (Suc k) = (setprod (\<lambda>i. a - of_nat i) {0 .. k}) / of_nat (fact (Suc k))"
  by (simp add: gbinomial_def)
 
lemma gbinomial_mult_fact:
  "(of_nat (fact (Suc k)) :: 'a) * ((a::'a::field_char_0) gchoose (Suc k)) = (setprod (\<lambda>i. a - of_nat i) {0 .. k})"
  unfolding gbinomial_Suc
  by (simp_all add: field_simps del: fact_Suc)

lemma gbinomial_mult_fact':
  "((a::'a::field_char_0) gchoose (Suc k)) * (of_nat (fact (Suc k)) :: 'a) = (setprod (\<lambda>i. a - of_nat i) {0 .. k})"
  using gbinomial_mult_fact[of k a]
  apply (subst mult_commute) .

lemma gbinomial_Suc_Suc: "((a::'a::field_char_0) + 1) gchoose (Suc k) = a gchoose k + (a gchoose (Suc k))"
proof-
  {assume "k = 0" then have ?thesis by simp}
  moreover
  {fix h assume h: "k = Suc h"
   have eq0: "(\<Prod>i\<in>{1..k}. (a + 1) - of_nat i) = (\<Prod>i\<in>{0..h}. a - of_nat i)"
     apply (rule strong_setprod_reindex_cong[where f = Suc])
     using h by auto

    have "of_nat (fact (Suc k)) * (a gchoose k + (a gchoose (Suc k))) = ((a gchoose Suc h) * of_nat (fact (Suc h)) * of_nat (Suc k)) + (\<Prod>i\<in>{0\<Colon>nat..Suc h}. a - of_nat i)" 
      unfolding h
      apply (simp add: field_simps del: fact_Suc)
      unfolding gbinomial_mult_fact'
      apply (subst fact_Suc)
      unfolding of_nat_mult 
      apply (subst mult_commute)
      unfolding mult_assoc
      unfolding gbinomial_mult_fact
      by (simp add: field_simps)
    also have "\<dots> = (\<Prod>i\<in>{0..h}. a - of_nat i) * (a + 1)"
      unfolding gbinomial_mult_fact' setprod_nat_ivl_Suc
      by (simp add: field_simps h)
    also have "\<dots> = (\<Prod>i\<in>{0..k}. (a + 1) - of_nat i)"
      using eq0
      unfolding h  setprod_nat_ivl_1_Suc
      by simp
    also have "\<dots> = of_nat (fact (Suc k)) * ((a + 1) gchoose (Suc k))"
      unfolding gbinomial_mult_fact ..
    finally have ?thesis by (simp del: fact_Suc) }
  ultimately show ?thesis by (cases k, auto)
qed


lemma binomial_symmetric: assumes kn: "k \<le> n" 
  shows "n choose k = n choose (n - k)"
proof-
  from kn have kn': "n - k \<le> n" by arith
  from binomial_fact_lemma[OF kn] binomial_fact_lemma[OF kn']
  have "fact k * fact (n - k) * (n choose k) = fact (n - k) * fact (n - (n - k)) * (n choose (n - k))" by simp
  then show ?thesis using kn by simp
qed

end
