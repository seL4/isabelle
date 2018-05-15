(*  Title:      HOL/Computational_Algebra/Group_Closure.thy
    Author:     Johannes Hoelzl, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen
*)

theory Group_Closure
imports
  Main
begin

context ab_group_add
begin

inductive_set group_closure :: "'a set \<Rightarrow> 'a set" for S
  where base: "s \<in> insert 0 S \<Longrightarrow> s \<in> group_closure S"
| diff: "s \<in> group_closure S \<Longrightarrow> t \<in> group_closure S \<Longrightarrow> s - t \<in> group_closure S"

lemma zero_in_group_closure [simp]:
  "0 \<in> group_closure S"
  using group_closure.base [of 0 S] by simp

lemma group_closure_minus_iff [simp]:
  "- s \<in> group_closure S \<longleftrightarrow> s \<in> group_closure S"
  using group_closure.diff [of 0 S s] group_closure.diff [of 0 S "- s"] by auto

lemma group_closure_add:
  "s + t \<in> group_closure S" if "s \<in> group_closure S" and "t \<in> group_closure S"
  using that group_closure.diff [of s S "- t"] by auto

lemma group_closure_empty [simp]:
  "group_closure {} = {0}"
  by (rule ccontr) (auto elim: group_closure.induct)

lemma group_closure_insert_zero [simp]:
  "group_closure (insert 0 S) = group_closure S"
  by (auto elim: group_closure.induct intro: group_closure.intros)

end

context comm_ring_1
begin

lemma group_closure_scalar_mult_left:
  "of_nat n * s \<in> group_closure S" if "s \<in> group_closure S"
  using that by (induction n) (auto simp add: algebra_simps intro: group_closure_add)

lemma group_closure_scalar_mult_right:
  "s * of_nat n \<in> group_closure S" if "s \<in> group_closure S"
  using that group_closure_scalar_mult_left [of s S n] by (simp add: ac_simps)

end

lemma group_closure_abs_iff [simp]:
  "\<bar>s\<bar> \<in> group_closure S \<longleftrightarrow> s \<in> group_closure S" for s :: int
  by (simp add: abs_if)

lemma group_closure_mult_left:
  "s * t \<in> group_closure S" if "s \<in> group_closure S" for s t :: int
proof -
  from that group_closure_scalar_mult_right [of s S "nat \<bar>t\<bar>"]
    have "s * int (nat \<bar>t\<bar>) \<in> group_closure S"
    by (simp only:)
  then show ?thesis
    by (cases "t \<ge> 0") simp_all
qed

lemma group_closure_mult_right:
  "s * t \<in> group_closure S" if "t \<in> group_closure S" for s t :: int
  using that group_closure_mult_left [of t S s] by (simp add: ac_simps)

context idom
begin

lemma group_closure_mult_all_eq:
  "group_closure (times k ` S) = times k ` group_closure S"
proof (rule; rule)
  fix s
  have *: "k * a + k * b = k * (a + b)"
    "k * a - k * b = k * (a - b)" for a b
    by (simp_all add: algebra_simps)
  assume "s \<in> group_closure (times k ` S)"
  then show "s \<in> times k ` group_closure S"
    by induction (auto simp add: * image_iff intro: group_closure.base group_closure.diff bexI [of _ 0])
next
  fix s
  assume "s \<in> times k ` group_closure S"
  then obtain r where r: "r \<in> group_closure S" and s: "s = k * r"
    by auto
  from r have "k * r \<in> group_closure (times k ` S)"
    by (induction arbitrary: s) (auto simp add: algebra_simps intro: group_closure.intros)
  with s show "s \<in> group_closure (times k ` S)"
    by simp
qed

end

lemma Gcd_group_closure_eq_Gcd:
  "Gcd (group_closure S) = Gcd S" for S :: "int set"
proof (rule associated_eqI)
  have "Gcd S dvd s" if "s \<in> group_closure S" for s
    using that by induction auto
  then show "Gcd S dvd Gcd (group_closure S)"
    by auto
  have "Gcd (group_closure S) dvd s" if "s \<in> S" for s
  proof -
    from that have "s \<in> group_closure S"
      by (simp add: group_closure.base)
    then show ?thesis
      by (rule Gcd_dvd)
  qed
  then show "Gcd (group_closure S) dvd Gcd S"
    by auto
qed simp_all

lemma group_closure_sum:
  fixes S :: "int set"
  assumes X: "finite X" "X \<noteq> {}" "X \<subseteq> S"
  shows "(\<Sum>x\<in>X. a x * x) \<in> group_closure S"
  using X by (induction X rule: finite_ne_induct)
    (auto intro: group_closure_mult_right group_closure.base group_closure_add)

lemma Gcd_group_closure_in_group_closure:
  "Gcd (group_closure S) \<in> group_closure S" for S :: "int set"
proof (cases "S \<subseteq> {0}")
  case True
  then have "S = {} \<or> S = {0}"
    by auto
  then show ?thesis
    by auto
next
  case False
  then obtain s where s: "s \<noteq> 0" "s \<in> S"
    by auto
  then have s': "\<bar>s\<bar> \<noteq> 0" "\<bar>s\<bar> \<in> group_closure S"
    by (auto intro: group_closure.base)
  define m where "m = (LEAST n. n > 0 \<and> int n \<in> group_closure S)"
  have "m > 0 \<and> int m \<in> group_closure S"
    unfolding m_def
    apply (rule LeastI [of _ "nat \<bar>s\<bar>"])
    using s'
    by simp
  then have m: "int m \<in> group_closure S" and "0 < m"
    by auto

  have "Gcd (group_closure S) = int m"
  proof (rule associated_eqI)
    from m show "Gcd (group_closure S) dvd int m"
      by (rule Gcd_dvd)
    show "int m dvd Gcd (group_closure S)"
    proof (rule Gcd_greatest)
      fix s
      assume s: "s \<in> group_closure S"
      show "int m dvd s"
      proof (rule ccontr)
        assume "\<not> int m dvd s"
        then have *: "0 < s mod int m"
          using \<open>0 < m\<close> le_less by fastforce
        have "m \<le> nat (s mod int m)"
        proof (subst m_def, rule Least_le, rule)
          from * show "0 < nat (s mod int m)"
            by simp
          from minus_div_mult_eq_mod [symmetric, of s "int m"]
          have "s mod int m = s - s div int m * int m"
            by auto
          also have "s - s div int m * int m \<in> group_closure S"
            by (auto intro: group_closure.diff s group_closure_mult_right m)
          finally  show "int (nat (s mod int m)) \<in> group_closure S"
            by simp
        qed
        with * have "int m \<le> s mod int m"
          by simp
        moreover have "s mod int m < int m"
          using \<open>0 < m\<close> by simp
        ultimately show False
          by auto
      qed
    qed
  qed simp_all
  with m show ?thesis
    by simp
qed

lemma Gcd_in_group_closure:
  "Gcd S \<in> group_closure S" for S :: "int set"
  using Gcd_group_closure_in_group_closure [of S]
  by (simp add: Gcd_group_closure_eq_Gcd)

lemma group_closure_eq:
  "group_closure S = range (times (Gcd S))" for S :: "int set"
proof (auto intro: Gcd_in_group_closure group_closure_mult_left)
  fix s
  assume "s \<in> group_closure S"
  then show "s \<in> range (times (Gcd S))"
  proof induction
    case (base s)
    then have "Gcd S dvd s"
      by (auto intro: Gcd_dvd)
    then obtain t where "s = Gcd S * t" ..
    then show ?case
      by auto
  next
    case (diff s t)
    moreover have "Gcd S * a - Gcd S * b = Gcd S * (a - b)" for a b
      by (simp add: algebra_simps)
    ultimately show ?case
      by auto
  qed
qed

end
