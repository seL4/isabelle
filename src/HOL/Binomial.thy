(*  Title:      HOL/Binomial.thy
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1997  University of Cambridge

*)

header{*Binomial Coefficients*}

theory Binomial
imports SetInterval
begin

text{*This development is based on the work of Andy Gordon and
Florian Kammueller*}

consts
  binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat"      (infixl "choose" 65)

primrec
  binomial_0:   "(0     choose k) = (if k = 0 then 1 else 0)"

  binomial_Suc: "(Suc n choose k) =
                 (if k = 0 then 1 else (n choose (k - 1)) + (n choose k))"

lemma binomial_n_0 [simp]: "(n choose 0) = 1"
by (case_tac "n", simp_all)

lemma binomial_0_Suc [simp]: "(0 choose Suc k) = 0"
by simp

lemma binomial_Suc_Suc [simp]:
     "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)"
by simp

lemma binomial_eq_0 [rule_format]: "\<forall>k. n < k --> (n choose k) = 0"
apply (induct "n", auto)
apply (erule allE)
apply (erule mp, arith)
done

declare binomial_0 [simp del] binomial_Suc [simp del]

lemma binomial_n_n [simp]: "(n choose n) = 1"
apply (induct "n")
apply (simp_all add: binomial_eq_0)
done

lemma binomial_Suc_n [simp]: "(Suc n choose n) = Suc n"
by (induct "n", simp_all)

lemma binomial_1 [simp]: "(n choose Suc 0) = n"
by (induct "n", simp_all)

lemma zero_less_binomial [rule_format]: "k \<le> n --> 0 < (n choose k)"
by (rule_tac m = n and n = k in diff_induct, simp_all)

lemma binomial_eq_0_iff: "(n choose k = 0) = (n<k)"
apply (safe intro!: binomial_eq_0)
apply (erule contrapos_pp)
apply (simp add: zero_less_binomial)
done

lemma zero_less_binomial_iff: "(0 < n choose k) = (k\<le>n)"
by (simp add: linorder_not_less [symmetric] binomial_eq_0_iff [symmetric])

(*Might be more useful if re-oriented*)
lemma Suc_times_binomial_eq [rule_format]:
     "\<forall>k. k \<le> n --> Suc n * (n choose k) = (Suc n choose Suc k) * Suc k"
apply (induct "n")
apply (simp add: binomial_0, clarify)
apply (case_tac "k")
apply (auto simp add: add_mult_distrib add_mult_distrib2 le_Suc_eq
                      binomial_eq_0)
done

text{*This is the well-known version, but it's harder to use because of the
  need to reason about division.*}
lemma binomial_Suc_Suc_eq_times:
     "k \<le> n ==> (Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k"
by (simp add: Suc_times_binomial_eq div_mult_self_is_m zero_less_Suc
        del: mult_Suc mult_Suc_right)

text{*Another version, with -1 instead of Suc.*}
lemma times_binomial_minus1_eq:
     "[|k \<le> n;  0<k|] ==> (n choose k) * k = n * ((n - 1) choose (k - 1))"
apply (cut_tac n = "n - 1" and k = "k - 1" in Suc_times_binomial_eq)
apply (simp split add: nat_diff_split, auto)
done

subsubsection {* Theorems about @{text "choose"} *}

text {*
  \medskip Basic theorem about @{text "choose"}.  By Florian
  Kamm\"uller, tidied by LCP.
*}

lemma card_s_0_eq_empty:
    "finite A ==> card {B. B \<subseteq> A & card B = 0} = 1"
  apply (simp cong add: conj_cong add: finite_subset [THEN card_0_eq])
  apply (simp cong add: rev_conj_cong)
  done

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
   txt {* finiteness of the two sets *}
   apply (rule_tac [2] B = "Pow (A)" in finite_subset)
   apply (rule_tac B = "Pow (insert x A)" in finite_subset)
   apply fast+
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
    by(rule nat_distrib)
  also have "\<dots> = (\<Sum>k=0..n. (n choose k) * a^(k+1) * b^(n-k)) +
                  (\<Sum>k=0..n. (n choose k) * a^k * b^(n-k+1))"
    by(simp add: setsum_mult mult_ac)
  also have "\<dots> = (\<Sum>k=0..n. (n choose k) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n+1. (n choose (k - 1)) * a^k * b^(n+1-k))"
    by (simp add:setsum_shift_bounds_cl_Suc_ivl Suc_diff_le
             del:setsum_cl_ivl_Suc)
  also have "\<dots> = a^(n+1) + b^(n+1) +
                  (\<Sum>k=1..n. (n choose (k - 1)) * a^k * b^(n+1-k)) +
                  (\<Sum>k=1..n. (n choose k) * a^k * b^(n+1-k))"
    by(simp add: decomp2)
  also have
    "\<dots> = a^(n+1) + b^(n+1) + (\<Sum>k=1..n. (n+1 choose k) * a^k * b^(n+1-k))"
    by(simp add: nat_distrib setsum_addf binomial.simps)
  also have "\<dots> = (\<Sum>k=0..n+1. (n+1 choose k) * a^k * b^(n+1-k))"
    using decomp by simp
  finally show ?case by simp
qed

ML
{*
val binomial_n_0 = thm"binomial_n_0";
val binomial_0_Suc = thm"binomial_0_Suc";
val binomial_Suc_Suc = thm"binomial_Suc_Suc";
val binomial_eq_0 = thm"binomial_eq_0";
val binomial_n_n = thm"binomial_n_n";
val binomial_Suc_n = thm"binomial_Suc_n";
val binomial_1 = thm"binomial_1";
val zero_less_binomial = thm"zero_less_binomial";
val binomial_eq_0_iff = thm"binomial_eq_0_iff";
val zero_less_binomial_iff = thm"zero_less_binomial_iff";
val Suc_times_binomial_eq = thm"Suc_times_binomial_eq";
val binomial_Suc_Suc_eq_times = thm"binomial_Suc_Suc_eq_times";
val times_binomial_minus1_eq = thm"times_binomial_minus1_eq";
*}

end
