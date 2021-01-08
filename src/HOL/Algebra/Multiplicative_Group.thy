(*  Title:      HOL/Algebra/Multiplicative_Group.thy
    Author:     Simon Wimmer
    Author:     Lars Noschinski
*)

theory Multiplicative_Group
imports
  Complex_Main
  Group
  Coset
  UnivPoly
  Generated_Groups
  Elementary_Groups
begin

section \<open>Simplification Rules for Polynomials\<close>
text_raw \<open>\label{sec:simp-rules}\<close>

lemma (in ring_hom_cring) hom_sub[simp]:
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "h (x \<ominus> y) = h x \<ominus>\<^bsub>S\<^esub> h y"
  using assms by (simp add: R.minus_eq S.minus_eq)

context UP_ring begin

lemma deg_nzero_nzero:
  assumes deg_p_nzero: "deg R p \<noteq> 0"
  shows "p \<noteq> \<zero>\<^bsub>P\<^esub>"
  using deg_zero deg_p_nzero by auto

lemma deg_add_eq:
  assumes c: "p \<in> carrier P" "q \<in> carrier P"
  assumes "deg R q \<noteq> deg R p"
  shows "deg R (p \<oplus>\<^bsub>P\<^esub> q) = max (deg R p) (deg R q)"
proof -
  let ?m = "max (deg R p) (deg R q)"
  from assms have "coeff P p ?m = \<zero> \<longleftrightarrow> coeff P q ?m \<noteq> \<zero>"
    by (metis deg_belowI lcoeff_nonzero[OF deg_nzero_nzero] linear max.absorb_iff2 max.absorb1)
  then have "coeff P (p \<oplus>\<^bsub>P\<^esub> q) ?m \<noteq> \<zero>"
    using assms by auto
  then have "deg R (p \<oplus>\<^bsub>P\<^esub> q) \<ge> ?m"
    using assms by (blast intro: deg_belowI)
  with deg_add[OF c] show ?thesis by arith
qed

lemma deg_minus_eq:
  assumes "p \<in> carrier P" "q \<in> carrier P" "deg R q \<noteq> deg R p"
  shows "deg R (p \<ominus>\<^bsub>P\<^esub> q) = max (deg R p) (deg R q)"
  using assms by (simp add: deg_add_eq a_minus_def)

end

context UP_cring begin

lemma evalRR_add:
  assumes "p \<in> carrier P" "q \<in> carrier P"
  assumes x: "x \<in> carrier R"
  shows "eval R R id x (p \<oplus>\<^bsub>P\<^esub> q) = eval R R id x p \<oplus> eval R R id x q"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom[OF x])
  show ?thesis using assms by simp
qed

lemma evalRR_sub:
  assumes "p \<in> carrier P" "q \<in> carrier P"
  assumes x: "x \<in> carrier R"
  shows "eval R R id x (p \<ominus>\<^bsub>P\<^esub> q) = eval R R id x p \<ominus> eval R R id x q"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom[OF x])
  show ?thesis using assms by simp
qed

lemma evalRR_mult:
  assumes "p \<in> carrier P" "q \<in> carrier P"
  assumes x: "x \<in> carrier R"
  shows "eval R R id x (p \<otimes>\<^bsub>P\<^esub> q) = eval R R id x p \<otimes> eval R R id x q"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom[OF x])
  show ?thesis using assms by simp
qed

lemma evalRR_monom:
  assumes a: "a \<in> carrier R" and x: "x \<in> carrier R"
  shows "eval R R id x (monom P a d) = a \<otimes> x [^] d"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  show ?thesis using assms by (simp add: eval_monom)
qed

lemma evalRR_one:
  assumes x: "x \<in> carrier R"
  shows "eval R R id x \<one>\<^bsub>P\<^esub> = \<one>"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom[OF x])
  show ?thesis using assms by simp
qed

lemma carrier_evalRR:
  assumes x: "x \<in> carrier R" and "p \<in> carrier P"
  shows "eval R R id x p \<in> carrier R"
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  interpret ring_hom_cring P R "eval R R id x" by unfold_locales (rule eval_ring_hom[OF x])
  show ?thesis using assms by simp
qed

lemmas evalRR_simps = evalRR_add evalRR_sub evalRR_mult evalRR_monom evalRR_one carrier_evalRR

end



section \<open>Properties of the Euler \<open>\<phi>\<close>-function\<close>
text_raw \<open>\label{sec:euler-phi}\<close>

text\<open>
  In this section we prove that for every positive natural number the equation
  $\sum_{d | n}^n \varphi(d) = n$ holds.
\<close>

lemma dvd_div_ge_1:
  fixes a b :: nat
  assumes "a \<ge> 1" "b dvd a"
  shows "a div b \<ge> 1"
proof -
  from \<open>b dvd a\<close> obtain c where "a = b * c" ..
  with \<open>a \<ge> 1\<close> show ?thesis by simp
qed

lemma dvd_nat_bounds:
 fixes n p :: nat
 assumes "p > 0" "n dvd p"
 shows "n > 0 \<and> n \<le> p"
 using assms by (simp add: dvd_pos_nat dvd_imp_le)

(* TODO FIXME: This is the "totient" function from HOL-Number_Theory, but since part of
   HOL-Number_Theory depends on HOL-Algebra.Multiplicative_Group, there would be a cyclic
   dependency. *)
definition phi' :: "nat => nat"
  where "phi' m = card {x. 1 \<le> x \<and> x \<le> m \<and> coprime x m}"

notation (latex output)
  phi' ("\<phi> _")

lemma phi'_nonzero:
  assumes "m > 0"
  shows "phi' m > 0"
proof -
  have "1 \<in> {x. 1 \<le> x \<and> x \<le> m \<and> coprime x m}" using assms by simp
  hence "card {x. 1 \<le> x \<and> x \<le> m \<and> coprime x m} > 0" by (auto simp: card_gt_0_iff)
  thus ?thesis unfolding phi'_def by simp
qed

lemma dvd_div_eq_1:
  fixes a b c :: nat
  assumes "c dvd a" "c dvd b" "a div c = b div c"
  shows "a = b" using assms dvd_mult_div_cancel[OF \<open>c dvd a\<close>] dvd_mult_div_cancel[OF \<open>c dvd b\<close>]
                by presburger

lemma dvd_div_eq_2:
  fixes a b c :: nat
  assumes "c>0" "a dvd c" "b dvd c" "c div a = c div b"
  shows "a = b"
  proof -
  have "a > 0" "a \<le> c" using dvd_nat_bounds[OF assms(1-2)] by auto
  have "a*(c div a) = c" using assms dvd_mult_div_cancel by fastforce
  also have "\<dots> = b*(c div a)" using assms dvd_mult_div_cancel by fastforce
  finally show "a = b" using \<open>c>0\<close> dvd_div_ge_1[OF _ \<open>a dvd c\<close>] by fastforce
qed

lemma div_mult_mono:
  fixes a b c :: nat
  assumes "a > 0" "a\<le>d"
  shows "a * b div d \<le> b"
proof -
  have "a*b div d \<le> b*a div a" using assms div_le_mono2 mult.commute[of a b] by presburger
  thus ?thesis using assms by force
qed

text\<open>
  We arrive at the main result of this section:
  For every positive natural number the equation $\sum_{d | n}^n \varphi(d) = n$ holds.

  The outline of the proof for this lemma is as follows:
  We count the $n$ fractions $1/n$, $\ldots$, $(n-1)/n$, $n/n$.
  We analyze the reduced form $a/d = m/n$ for any of those fractions.
  We want to know how many fractions $m/n$ have the reduced form denominator $d$.
  The condition $1 \leq m \leq n$ is equivalent to the condition $1 \leq a \leq d$.
  Therefore we want to know how many $a$ with $1 \leq a \leq d$ exist, s.t. \<^term>\<open>gcd a d = 1\<close>.
  This number is exactly \<^term>\<open>phi' d\<close>.

  Finally, by counting the fractions $m/n$ according to their reduced form denominator,
  we get: @{term [display] "(\<Sum>d | d dvd n . phi' d) = n"}.
  To formalize this proof in Isabelle, we analyze for an arbitrary divisor $d$ of $n$
  \begin{itemize}
    \item the set of reduced form numerators \<^term>\<open>{a. (1::nat) \<le> a \<and> a \<le> d \<and> coprime a d}\<close>
    \item the set of numerators $m$, for which $m/n$ has the reduced form denominator $d$,
      i.e. the set \<^term>\<open>{m \<in> {1::nat .. n}. n div gcd m n = d}\<close>
  \end{itemize}
  We show that \<^term>\<open>\<lambda>a. a*n div d\<close> with the inverse \<^term>\<open>\<lambda>a. a div gcd a n\<close> is
  a bijection between theses sets, thus yielding the equality
  @{term [display] "phi' d = card {m \<in> {1 .. n}. n div gcd m n = d}"}
  This gives us
  @{term [display] "(\<Sum>d | d dvd n . phi' d)
          = card (\<Union>d \<in> {d. d dvd n}. {m \<in> {1 .. n}. n div gcd m n = d})"}
  and by showing
  \<^term>\<open>(\<Union>d \<in> {d. d dvd n}. {m \<in> {1::nat .. n}. n div gcd m n = d}) \<supseteq> {1 .. n}\<close>
  (this is our counting argument) the thesis follows.
\<close>
lemma sum_phi'_factors:
 fixes n :: nat
 assumes "n > 0"
 shows "(\<Sum>d | d dvd n. phi' d) = n"
proof -
  { fix d assume "d dvd n" then obtain q where q: "n = d * q" ..
    have "card {a. 1 \<le> a \<and> a \<le> d \<and> coprime a d} = card {m \<in> {1 .. n}.  n div gcd m n = d}"
         (is "card ?RF = card ?F")
    proof (rule card_bij_eq)
      { fix a b assume "a * n div d = b * n div d"
        hence "a * (n div d) = b * (n div d)"
          using dvd_div_mult[OF \<open>d dvd n\<close>] by (fastforce simp add: mult.commute)
        hence "a = b" using dvd_div_ge_1[OF _ \<open>d dvd n\<close>] \<open>n>0\<close>
          by (simp add: mult.commute nat_mult_eq_cancel1)
      } thus "inj_on (\<lambda>a. a*n div d) ?RF" unfolding inj_on_def by blast
      { fix a assume a: "a\<in>?RF"
        hence "a * (n div d) \<ge> 1" using \<open>n>0\<close> dvd_div_ge_1[OF _ \<open>d dvd n\<close>] by simp
        hence ge_1: "a * n div d \<ge> 1" by (simp add: \<open>d dvd n\<close> div_mult_swap)
        have le_n: "a * n div d \<le> n" using div_mult_mono a by simp
        have "gcd (a * n div d) n = n div d * gcd a d"
          by (simp add: gcd_mult_distrib_nat q ac_simps)
        hence "n div gcd (a * n div d) n = d*n div (d*(n div d))" using a by simp
        hence "a * n div d \<in> ?F"
          using ge_1 le_n by (fastforce simp add: \<open>d dvd n\<close>)
      } thus "(\<lambda>a. a*n div d) ` ?RF \<subseteq> ?F" by blast
      { fix m l assume A: "m \<in> ?F" "l \<in> ?F" "m div gcd m n = l div gcd l n"
        hence "gcd m n = gcd l n" using dvd_div_eq_2[OF assms] by fastforce
        hence "m = l" using dvd_div_eq_1[of "gcd m n" m l] A(3) by fastforce
      } thus "inj_on (\<lambda>a. a div gcd a n) ?F" unfolding inj_on_def by blast
      { fix m assume "m \<in> ?F"
        hence "m div gcd m n \<in> ?RF" using dvd_div_ge_1
          by (fastforce simp add: div_le_mono div_gcd_coprime)
      } thus "(\<lambda>a. a div gcd a n) ` ?F \<subseteq> ?RF" by blast
    qed force+
  } hence phi'_eq: "\<And>d. d dvd n \<Longrightarrow> phi' d = card {m \<in> {1 .. n}. n div gcd m n = d}"
      unfolding phi'_def by presburger
  have fin: "finite {d. d dvd n}" using dvd_nat_bounds[OF \<open>n>0\<close>] by force
  have "(\<Sum>d | d dvd n. phi' d)
                 = card (\<Union>d \<in> {d. d dvd n}. {m \<in> {1 .. n}. n div gcd m n = d})"
    using card_UN_disjoint[OF fin, of "(\<lambda>d. {m \<in> {1 .. n}. n div gcd m n = d})"] phi'_eq
    by fastforce
  also have "(\<Union>d \<in> {d. d dvd n}. {m \<in> {1 .. n}. n div gcd m n = d}) = {1 .. n}" (is "?L = ?R")
  proof
    show "?L \<supseteq> ?R"
    proof
      fix m assume m: "m \<in> ?R"
      thus "m \<in> ?L" using dvd_triv_right[of "n div gcd m n" "gcd m n"]
        by simp
    qed
  qed fastforce
  finally show ?thesis by force
qed



section \<open>Order of an Element of a Group\<close>
text_raw \<open>\label{sec:order-elem}\<close>


context group begin

definition (in group) ord :: "'a \<Rightarrow> nat" where
  "ord x \<equiv> (@d. \<forall>n::nat. x [^] n = \<one> \<longleftrightarrow> d dvd n)"

lemma (in group) pow_eq_id:
  assumes "x \<in> carrier G"
  shows "x [^] n = \<one> \<longleftrightarrow> (ord x) dvd n"
proof (cases "\<forall>n::nat. pow G x n = one G \<longrightarrow> n = 0")
  case True
  show ?thesis
    unfolding ord_def
    by (rule someI2 [where a=0]) (auto simp: True)
next
  case False
  define N where "N \<equiv> LEAST n::nat. x [^] n = \<one> \<and> n > 0"
  have N: "x [^] N = \<one> \<and> N > 0"
    using False
    apply (simp add: N_def)
    by (metis (mono_tags, lifting) LeastI)
  have eq0: "n = 0" if "x [^] n = \<one>" "n < N" for n
    using N_def not_less_Least that by fastforce
  show ?thesis
    unfolding ord_def
  proof (rule someI2 [where a = N], rule allI)
    fix n :: "nat"
    show "(x [^] n = \<one>) \<longleftrightarrow> (N dvd n)"
    proof (cases "n = 0")
      case False
      show ?thesis
        unfolding dvd_def
      proof safe
        assume 1: "x [^] n = \<one>"
        have "x [^] n = x [^] (n mod N + N * (n div N))"
          by simp
        also have "\<dots> = x [^] (n mod N) \<otimes> x [^] (N * (n div N))"
          by (simp add: assms nat_pow_mult)
        also have "\<dots> = x [^] (n mod N)"
          by (metis N assms l_cancel_one nat_pow_closed nat_pow_one nat_pow_pow)
        finally have "x [^] (n mod N) = \<one>"
          by (simp add: "1")
        then have "n mod N = 0"
          using N eq0 mod_less_divisor by blast
        then show "\<exists>k. n = N * k"
          by blast
      next
        fix k :: "nat"
        assume "n = N * k"
        with N show "x [^] (N * k) = \<one>"
          by (metis assms nat_pow_one nat_pow_pow)
      qed
    qed simp
  qed blast
qed

lemma (in group) pow_ord_eq_1 [simp]:
   "x \<in> carrier G \<Longrightarrow> x [^] ord x = \<one>"
  by (simp add: pow_eq_id)

lemma (in group) int_pow_eq_id:
  assumes "x \<in> carrier G"
  shows "(pow G x i = one G \<longleftrightarrow> int (ord x) dvd i)"
proof (cases i rule: int_cases2)
  case (nonneg n)
  then show ?thesis
    by (simp add: int_pow_int pow_eq_id assms)
next
  case (nonpos n)
  then have "x [^] i = inv (x [^] n)"
    by (simp add: assms int_pow_int int_pow_neg)
  then show ?thesis
    by (simp add: assms pow_eq_id nonpos)
qed

lemma (in group) int_pow_eq:
   "x \<in> carrier G \<Longrightarrow> (x [^] m = x [^] n) \<longleftrightarrow> int (ord x) dvd (n - m)"
  apply (simp flip: int_pow_eq_id)
  by (metis int_pow_closed int_pow_diff inv_closed r_inv right_cancel)

lemma (in group) ord_eq_0:
   "x \<in> carrier G \<Longrightarrow> (ord x = 0 \<longleftrightarrow> (\<forall>n::nat. n \<noteq> 0 \<longrightarrow> x [^] n \<noteq> \<one>))"
  by (auto simp: pow_eq_id)

lemma (in group) ord_unique:
   "x \<in> carrier G \<Longrightarrow> ord x = d \<longleftrightarrow> (\<forall>n. pow G x n = one G \<longleftrightarrow> d dvd n)"
  by (meson dvd_antisym dvd_refl pow_eq_id)

lemma (in group) ord_eq_1:
   "x \<in> carrier G \<Longrightarrow> (ord x = 1 \<longleftrightarrow> x = \<one>)"
  by (metis pow_eq_id nat_dvd_1_iff_1 nat_pow_eone)

lemma (in group) ord_id [simp]:
   "ord (one G) = 1"
  using ord_eq_1 by blast

lemma (in group) ord_inv [simp]:
   "x \<in> carrier G
        \<Longrightarrow> ord (m_inv G x) = ord x"
  by (simp add: ord_unique pow_eq_id nat_pow_inv)

lemma (in group) ord_pow:
  assumes "x \<in> carrier G" "k dvd ord x" "k \<noteq> 0"
  shows "ord (pow G x k) = ord x div k"
proof -
  have "(x [^] k) [^] (ord x div k) = \<one>"
    using assms by (simp add: nat_pow_pow)
  moreover have "ord x dvd k * ord (x [^] k)"
    by (metis assms(1) pow_ord_eq_1 pow_eq_id nat_pow_closed nat_pow_pow)
  ultimately show ?thesis
    by (metis assms div_dvd_div dvd_antisym dvd_triv_left pow_eq_id nat_pow_closed nonzero_mult_div_cancel_left)
qed

lemma (in group) ord_mul_divides:
  assumes eq: "x \<otimes> y = y \<otimes> x" and xy: "x \<in> carrier G" "y \<in> carrier G"
  shows "ord (x \<otimes> y) dvd (ord x * ord y)"
apply (simp add: xy flip: pow_eq_id eq)
  by (metis dvd_triv_left dvd_triv_right eq pow_eq_id one_closed pow_mult_distrib r_one xy)

lemma (in comm_group) abelian_ord_mul_divides:
   "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
        \<Longrightarrow> ord (x \<otimes> y) dvd (ord x * ord y)"
  by (simp add: ord_mul_divides m_comm)

lemma ord_inj:
  assumes a: "a \<in> carrier G"
  shows "inj_on (\<lambda> x . a [^] x) {0 .. ord a - 1}"
proof -
  let ?M = "Max (ord ` carrier G)"
  have "finite {d \<in> {..?M}. a [^] d = \<one>}" by auto

  have *: False if A: "x < y" "x \<in> {0 .. ord a - 1}" "y \<in> {0 .. ord a - 1}"
        "a [^] x = a [^] y" for x y
  proof -
    have "y - x < ord a" using that by auto
    moreover have "a [^] (y-x) = \<one>" using a A by (simp add: pow_eq_div2)
    ultimately have "min (y - x) (ord a) = ord a"
      using A(1) a pow_eq_id by auto
    with \<open>y - x < ord a\<close> show False by linarith
  qed
  show ?thesis
    unfolding inj_on_def by (metis nat_neq_iff *)
qed

lemma ord_inj':
  assumes a: "a \<in> carrier G"
  shows "inj_on (\<lambda> x . a [^] x) {1 .. ord a}"
proof (rule inj_onI, rule ccontr)
  fix x y :: nat
  assume A: "x \<in> {1 .. ord a}" "y \<in> {1 .. ord a}" "a [^] x = a [^] y" "x\<noteq>y"
  { assume "x < ord a" "y < ord a"
    hence False using ord_inj[OF assms] A unfolding inj_on_def by fastforce
  }
  moreover
  { assume "x = ord a" "y < ord a"
    hence "a [^] y = a [^] (0::nat)" using pow_ord_eq_1 A by (simp add: a)
    hence "y=0" using ord_inj[OF assms] \<open>y < ord a\<close> unfolding inj_on_def by force
    hence False using A by fastforce
  }
  moreover
  { assume "y = ord a" "x < ord a"
    hence "a [^] x = a [^] (0::nat)" using pow_ord_eq_1 A by (simp add: a)
    hence "x=0" using ord_inj[OF assms] \<open>x < ord a\<close> unfolding inj_on_def by force
    hence False using A by fastforce
  }
  ultimately show False using A  by force
qed

lemma (in group) ord_ge_1: 
  assumes finite: "finite (carrier G)" and a: "a \<in> carrier G"
  shows "ord a \<ge> 1" 
proof -
  have "((\<lambda>n::nat. a [^] n) ` {0<..}) \<subseteq> carrier G"
    using a by blast
  then have "finite ((\<lambda>n::nat. a [^] n) ` {0<..})"
    using finite_subset finite by auto
  then have "\<not> inj_on (\<lambda>n::nat. a [^] n) {0<..}"
    using finite_imageD infinite_Ioi by blast
  then obtain i j::nat where "i \<noteq> j" "a [^] i = a [^] j"
    by (auto simp: inj_on_def)
  then have "\<exists>n::nat. n>0 \<and> a [^] n = \<one>"
    by (metis a diffs0_imp_equal pow_eq_div2 neq0_conv)
  then have "ord a \<noteq> 0"
    by (simp add: ord_eq_0 [OF a])
  then show ?thesis
    by simp
qed

lemma ord_elems:
  assumes "finite (carrier G)" "a \<in> carrier G"
  shows "{a[^]x | x. x \<in> (UNIV :: nat set)} = {a[^]x | x. x \<in> {0 .. ord a - 1}}" (is "?L = ?R")
proof
  show "?R \<subseteq> ?L" by blast
  { fix y assume "y \<in> ?L"
    then obtain x::nat where x: "y = a[^]x" by auto
    define r q where "r = x mod ord a" and "q = x div ord a"
    then have "x = q * ord a + r"
      by (simp add: div_mult_mod_eq)
    hence "y = (a[^]ord a)[^]q \<otimes> a[^]r"
      using x assms by (metis mult.commute nat_pow_mult nat_pow_pow)
    hence "y = a[^]r" using assms by (simp add: pow_ord_eq_1)
    have "r < ord a" using ord_ge_1[OF assms] by (simp add: r_def)
    hence "r \<in> {0 .. ord a - 1}" by (force simp: r_def)
    hence "y \<in> {a[^]x | x. x \<in> {0 .. ord a - 1}}" using \<open>y=a[^]r\<close> by blast
  }
  thus "?L \<subseteq> ?R" by auto
qed

lemma (in group)
  assumes "x \<in> carrier G"
  shows finite_cyclic_subgroup:
        "finite(carrier(subgroup_generated G {x})) \<longleftrightarrow> (\<exists>n::nat. n \<noteq> 0 \<and> x [^] n = \<one>)" (is "?fin \<longleftrightarrow> ?nat1")
    and infinite_cyclic_subgroup:
        "infinite(carrier(subgroup_generated G {x})) \<longleftrightarrow> (\<forall>m n::nat. x [^] m = x [^] n \<longrightarrow> m = n)" (is "\<not> ?fin \<longleftrightarrow> ?nateq")
    and finite_cyclic_subgroup_int:
        "finite(carrier(subgroup_generated G {x})) \<longleftrightarrow> (\<exists>i::int. i \<noteq> 0 \<and> x [^] i = \<one>)" (is "?fin \<longleftrightarrow> ?int1")
    and infinite_cyclic_subgroup_int:
        "infinite(carrier(subgroup_generated G {x})) \<longleftrightarrow> (\<forall>i j::int. x [^] i = x [^] j \<longrightarrow> i = j)" (is "\<not> ?fin \<longleftrightarrow> ?inteq")
proof -
  have 1: "\<not> ?fin" if ?nateq
  proof -
    have "infinite (range (\<lambda>n::nat. x [^] n))"
      using that range_inj_infinite [of "(\<lambda>n::nat. x [^] n)"] by (auto simp: inj_on_def)
    moreover have "range (\<lambda>n::nat. x [^] n) \<subseteq> range (\<lambda>i::int. x [^] i)"
      apply clarify
      by (metis assms group.int_pow_neg int_pow_closed int_pow_neg_int is_group local.inv_equality nat_pow_closed r_inv rangeI)
    ultimately show ?thesis
      using carrier_subgroup_generated_by_singleton [OF assms] finite_subset by auto
  qed
  have 2: "m = n" if mn: "x [^] m = x [^] n" and eq [rule_format]: "?inteq" for m n::nat
    using eq [of "int m" "int n"]
    by (simp add: int_pow_int mn)
  have 3: ?nat1 if non: "\<not> ?inteq"
  proof -
    obtain i j::int where eq: "x [^] i = x [^] j" and "i \<noteq> j"
      using non by auto
    show ?thesis
    proof (cases i j rule: linorder_cases)
      case less
      then have [simp]: "x [^] (j - i) = \<one>"
        by (simp add: eq assms int_pow_diff)
      show ?thesis
        using less by (rule_tac x="nat (j-i)" in exI) auto
    next
      case greater
      then have [simp]: "x [^] (i - j) = \<one>"
        by (simp add: eq assms int_pow_diff)
      then show ?thesis
        using greater by (rule_tac x="nat (i-j)" in exI) auto
    qed (use \<open>i \<noteq> j\<close> in auto)
  qed
  have 4: "\<exists>i::int. (i \<noteq> 0) \<and> x [^] i = \<one>" if "n \<noteq> 0" "x [^] n = \<one>" for n::nat
    apply (rule_tac x="int n" in exI)
    by (simp add: int_pow_int that)
  have 5: "finite (carrier (subgroup_generated G {x}))" if "i \<noteq> 0" and 1: "x [^] i = \<one>" for i::int
  proof -
    obtain n::nat where n: "n > 0" "x [^] n = \<one>"
      using "1" "3" \<open>i \<noteq> 0\<close> by fastforce
    have "x [^] a \<in> ([^]) x ` {0..<n}" for a::int
    proof
      show "x [^] a = x [^] nat (a mod int n)"
        using n
        by simp (metis (no_types, lifting) assms dvd_minus_mod dvd_trans int_pow_eq int_pow_eq_id int_pow_int)
      show "nat (a mod int n) \<in> {0..<n}"
        using n  apply (simp add:  split: split_nat)
        using Euclidean_Division.pos_mod_bound by presburger
    qed
    then have "carrier (subgroup_generated G {x}) \<subseteq> ([^]) x ` {0..<n}"
      using carrier_subgroup_generated_by_singleton [OF assms] by auto
    then show ?thesis
      using finite_surj by blast
  qed
  show "?fin \<longleftrightarrow> ?nat1" "\<not> ?fin \<longleftrightarrow> ?nateq" "?fin \<longleftrightarrow> ?int1" "\<not> ?fin \<longleftrightarrow> ?inteq"
    using 1 2 3 4 5 by meson+
qed

lemma (in group) finite_cyclic_subgroup_order:
   "x \<in> carrier G \<Longrightarrow> finite(carrier(subgroup_generated G {x})) \<longleftrightarrow> ord x \<noteq> 0"
  by (simp add: finite_cyclic_subgroup ord_eq_0)

lemma (in group) infinite_cyclic_subgroup_order:
   "x \<in> carrier G \<Longrightarrow> infinite (carrier(subgroup_generated G {x})) \<longleftrightarrow> ord x = 0"
  by (simp add: finite_cyclic_subgroup_order)

lemma generate_pow_on_finite_carrier: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "finite (carrier G)" and a: "a \<in> carrier G"
  shows "generate G { a } = { a [^] k | k. k \<in> (UNIV :: nat set) }"
proof
  show "{ a [^] k | k. k \<in> (UNIV :: nat set) } \<subseteq> generate G { a }"
  proof
    fix b assume "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }"
    then obtain k :: nat where "b = a [^] k" by blast
    hence "b = a [^] (int k)"
      by (simp add: int_pow_int)
    thus "b \<in> generate G { a }"
      unfolding generate_pow[OF a] by blast
  qed
next
  show "generate G { a } \<subseteq> { a [^] k | k. k \<in> (UNIV :: nat set) }"
  proof
    fix b assume "b \<in> generate G { a }"
    then obtain k :: int where k: "b = a [^] k"
      unfolding generate_pow[OF a] by blast
    show "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }"
    proof (cases "k < 0")
      assume "\<not> k < 0"
      hence "b = a [^] (nat k)"
        by (simp add: k)
      thus ?thesis by blast
    next
      assume "k < 0"
      hence b: "b = inv (a [^] (nat (- k)))"
        using k a by (auto simp: int_pow_neg)
      obtain m where m: "ord a * m \<ge> nat (- k)"
        by (metis assms mult.left_neutral mult_le_mono1 ord_ge_1)
      hence "a [^] (ord a * m) = \<one>"
        by (metis a nat_pow_one nat_pow_pow pow_ord_eq_1)
      then obtain k' :: nat where "(a [^] (nat (- k))) \<otimes> (a [^] k') = \<one>"
        using m a nat_le_iff_add nat_pow_mult by auto
      hence "b = a [^] k'"
        using b a by (metis inv_unique' nat_pow_closed nat_pow_comm)
      thus "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }" by blast
    qed
  qed
qed

lemma ord_elems_inf_carrier:
 assumes "a \<in> carrier G" "ord a \<noteq> 0"
 shows "{a[^]x | x. x \<in> (UNIV :: nat set)} = {a[^]x | x. x \<in> {0 .. ord a - 1}}" (is "?L = ?R")
proof
 show "?R \<subseteq> ?L" by blast
 { fix y assume "y \<in> ?L"
   then obtain x::nat where x: "y = a[^]x" by auto
   define r q where "r = x mod ord a" and "q = x div ord a"
   then have "x = q * ord a + r"
     by (simp add: div_mult_mod_eq)
   hence "y = (a[^]ord a)[^]q \<otimes> a[^]r"
     using x assms by (metis mult.commute nat_pow_mult nat_pow_pow)
   hence "y = a[^]r" using assms by simp
   have "r < ord a" using assms by (simp add: r_def)
   hence "r \<in> {0 .. ord a - 1}" by (force simp: r_def)
   hence "y \<in> {a[^]x | x. x \<in> {0 .. ord a - 1}}" using \<open>y=a[^]r\<close> by blast
 }
 thus "?L \<subseteq> ?R" by auto
qed

lemma generate_pow_nat:
 assumes a: "a \<in> carrier G" and "ord a \<noteq> 0"
 shows "generate G { a } = { a [^] k | k. k \<in> (UNIV :: nat set) }"
proof
 show "{ a [^] k | k. k \<in> (UNIV :: nat set) } \<subseteq> generate G { a }"
 proof
   fix b assume "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }"
   then obtain k :: nat where "b = a [^] k" by blast
   hence "b = a [^] (int k)"
     by (simp add: int_pow_int)
   thus "b \<in> generate G { a }"
     unfolding generate_pow[OF a] by blast
 qed
next
 show "generate G { a } \<subseteq> { a [^] k | k. k \<in> (UNIV :: nat set) }"
 proof
   fix b assume "b \<in> generate G { a }"
   then obtain k :: int where k: "b = a [^] k"
     unfolding generate_pow[OF a] by blast
   show "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }"
   proof (cases "k < 0")
     assume "\<not> k < 0"
     hence "b = a [^] (nat k)"
       by (simp add: k)
     thus ?thesis by blast
   next
     assume "k < 0"
     hence b: "b = inv (a [^] (nat (- k)))"
       using k a by (auto simp: int_pow_neg)
     obtain m where m: "ord a * m \<ge> nat (- k)"
       by (metis assms(2) dvd_imp_le dvd_triv_right le_zero_eq mult_eq_0_iff not_gr_zero)
     hence "a [^] (ord a * m) = \<one>"
       by (metis a nat_pow_one nat_pow_pow pow_ord_eq_1)
     then obtain k' :: nat where "(a [^] (nat (- k))) \<otimes> (a [^] k') = \<one>"
       using m a nat_le_iff_add nat_pow_mult by auto
     hence "b = a [^] k'"
       using b a by (metis inv_unique' nat_pow_closed nat_pow_comm)
     thus "b \<in> { a [^] k | k. k \<in> (UNIV :: nat set) }" by blast
   qed
 qed
qed

lemma generate_pow_card:
  assumes a: "a \<in> carrier G"
  shows "ord a = card (generate G { a })"
proof (cases "ord a = 0")
  case True
  then have "infinite (carrier (subgroup_generated G {a}))"
    using infinite_cyclic_subgroup_order[OF a] by auto
  then have "infinite (generate G {a})"
    unfolding subgroup_generated_def
    using a by simp
  then show ?thesis
    using \<open>ord a = 0\<close> by auto
next
  case False
  note finite_subgroup = this
  then have "generate G { a } = (([^]) a) ` {0..ord a - 1}"
    using generate_pow_nat ord_elems_inf_carrier a by auto
  hence "card (generate G {a}) = card {0..ord a - 1}"
    using ord_inj[OF a] card_image by metis
  also have "... = ord a" using finite_subgroup by auto
  finally show ?thesis.. 
qed

lemma (in group) cyclic_order_is_ord:
 assumes "g \<in> carrier G"
 shows "ord g = order (subgroup_generated G {g})"
 unfolding order_def subgroup_generated_def
 using assms generate_pow_card by simp

lemma ord_dvd_group_order:
  assumes "a \<in> carrier G" shows "(ord a) dvd (order G)"
  using lagrange[OF generate_is_subgroup[of "{a}"]] assms
  unfolding generate_pow_card[OF assms]
  by (metis dvd_triv_right empty_subsetI insert_subset)

lemma (in group) pow_order_eq_1:
  assumes "a \<in> carrier G" shows "a [^] order G = \<one>"
  using assms by (metis nat_pow_pow ord_dvd_group_order pow_ord_eq_1 dvdE nat_pow_one)

lemma dvd_gcd:
  fixes a b :: nat
  obtains q where "a * (b div gcd a b) = b*q"
proof
  have "a * (b div gcd a b) = (a div gcd a b) * b" by (simp add:  div_mult_swap dvd_div_mult)
  also have "\<dots> = b * (a div gcd a b)" by simp
  finally show "a * (b div gcd a b) = b * (a div gcd a b) " .
qed

lemma (in group) ord_le_group_order:
  assumes finite: "finite (carrier G)" and a: "a \<in> carrier G"
  shows "ord a \<le> order G"
  by (simp add: a dvd_imp_le local.finite ord_dvd_group_order order_gt_0_iff_finite)

lemma (in group) ord_pow_gen:
  assumes "x \<in> carrier G"
  shows "ord (pow G x k) = (if k = 0 then 1 else ord x div gcd (ord x) k)"
proof -
  have "ord (x [^] k) = ord x div gcd (ord x) k"
    if "0 < k"
  proof -
    have "(d dvd k * n) = (d div gcd (d) k dvd n)" for d n
      using that by (simp add: div_dvd_iff_mult gcd_mult_distrib_nat mult.commute)
    then show ?thesis
      using that by (auto simp add: assms ord_unique nat_pow_pow pow_eq_id)
  qed
  then show ?thesis by auto
qed

lemma (in group)
  assumes finite': "finite (carrier G)" "a \<in> carrier G"
  shows pow_ord_eq_ord_iff: "group.ord G (a [^] k) = ord a \<longleftrightarrow> coprime k (ord a)" (is "?L \<longleftrightarrow> ?R")
    using assms ord_ge_1 [OF assms]
    by (auto simp: div_eq_dividend_iff ord_pow_gen coprime_iff_gcd_eq_1 gcd.commute split: if_split_asm)

lemma element_generates_subgroup:
  assumes finite[simp]: "finite (carrier G)"
  assumes a[simp]: "a \<in> carrier G"
  shows "subgroup {a [^] i | i. i \<in> {0 .. ord a - 1}} G"
  using generate_is_subgroup[of "{ a }"] assms(2)
        generate_pow_on_finite_carrier[OF assms]
  unfolding ord_elems[OF assms] by auto

end


section \<open>Number of Roots of a Polynomial\<close>
text_raw \<open>\label{sec:number-roots}\<close>


definition mult_of :: "('a, 'b) ring_scheme \<Rightarrow> 'a monoid" where
  "mult_of R \<equiv> \<lparr> carrier = carrier R - {\<zero>\<^bsub>R\<^esub>}, mult = mult R, one = \<one>\<^bsub>R\<^esub>\<rparr>"

lemma carrier_mult_of [simp]: "carrier (mult_of R) = carrier R - {\<zero>\<^bsub>R\<^esub>}"
  by (simp add: mult_of_def)

lemma mult_mult_of [simp]: "mult (mult_of R) = mult R"
 by (simp add: mult_of_def)

lemma nat_pow_mult_of: "([^]\<^bsub>mult_of R\<^esub>) = (([^]\<^bsub>R\<^esub>) :: _ \<Rightarrow> nat \<Rightarrow> _)"
  by (simp add: mult_of_def fun_eq_iff nat_pow_def)

lemma one_mult_of [simp]: "\<one>\<^bsub>mult_of R\<^esub> = \<one>\<^bsub>R\<^esub>"
  by (simp add: mult_of_def)

lemmas mult_of_simps = carrier_mult_of mult_mult_of nat_pow_mult_of one_mult_of

context field
begin

lemma mult_of_is_Units: "mult_of R = units_of R"
  unfolding mult_of_def units_of_def using field_Units by auto

lemma m_inv_mult_of:
"\<And>x. x \<in> carrier (mult_of R) \<Longrightarrow> m_inv (mult_of R) x = m_inv R x"
  using mult_of_is_Units units_of_inv unfolding units_of_def
  by simp

lemma (in field) field_mult_group: "group (mult_of R)"
  proof (rule groupI)
  show "\<exists>y\<in>carrier (mult_of R). y \<otimes>\<^bsub>mult_of R\<^esub> x = \<one>\<^bsub>mult_of R\<^esub>"
    if "x \<in> carrier (mult_of R)" for x
    using group.l_inv_ex mult_of_is_Units that units_group by fastforce
qed (auto simp: m_assoc dest: integral)

lemma finite_mult_of: "finite (carrier R) \<Longrightarrow> finite (carrier (mult_of R))"
  by simp

lemma order_mult_of: "finite (carrier R) \<Longrightarrow> order (mult_of R) = order R - 1"
  unfolding order_def carrier_mult_of by (simp add: card.remove)

end



lemma (in monoid) Units_pow_closed :
  fixes d :: nat
  assumes "x \<in> Units G"
  shows "x [^] d \<in> Units G"
    by (metis assms group.is_monoid monoid.nat_pow_closed units_group units_of_carrier units_of_pow)

lemma (in ring) r_right_minus_eq[simp]:
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<ominus> b = \<zero> \<longleftrightarrow> a = b"
  using assms by (metis a_minus_def add.inv_closed minus_equality r_neg)

context UP_cring begin

lemma is_UP_cring: "UP_cring R" by (unfold_locales)
lemma is_UP_ring:
  shows "UP_ring R" by (unfold_locales)

end

context UP_domain begin


lemma roots_bound:
  assumes f [simp]: "f \<in> carrier P"
  assumes f_not_zero: "f \<noteq> \<zero>\<^bsub>P\<^esub>"
  assumes finite: "finite (carrier R)"
  shows "finite {a \<in> carrier R . eval R R id a f = \<zero>} \<and>
         card {a \<in> carrier R . eval R R id a f = \<zero>} \<le> deg R f" using f f_not_zero
proof (induction "deg R f" arbitrary: f)
  case 0
  have "\<And>x. eval R R id x f \<noteq> \<zero>"
  proof -
    fix x
    have "(\<Oplus>i\<in>{..deg R f}. id (coeff P f i) \<otimes> x [^] i) \<noteq> \<zero>"
      using 0 lcoeff_nonzero_nonzero[where p = f] by simp
    thus "eval R R id x f \<noteq> \<zero>" using 0 unfolding eval_def P_def by simp
  qed
  then have *: "{a \<in> carrier R. eval R R (\<lambda>a. a) a f = \<zero>} = {}"
    by (auto simp: id_def)
  show ?case by (simp add: *)
next
  case (Suc x)
  show ?case
  proof (cases "\<exists> a \<in> carrier R . eval R R id a f = \<zero>")
    case True
    then obtain a where a_carrier[simp]: "a \<in> carrier R" and a_root: "eval R R id a f = \<zero>" by blast
    have R_not_triv: "carrier R \<noteq> {\<zero>}"
      by (metis R.one_zeroI R.zero_not_one)
    obtain q  where q: "(q \<in> carrier P)" and
      f: "f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> monom P (eval R R id a f) 0"
     using remainder_theorem[OF Suc.prems(1) a_carrier R_not_triv] by auto
    hence lin_fac: "f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q" using q by (simp add: a_root)
    have deg: "deg R (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) = 1"
      using a_carrier by (simp add: deg_minus_eq)
    hence mon_not_zero: "(monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub> P\<^esub> monom P a 0) \<noteq> \<zero>\<^bsub>P\<^esub>"
      by (fastforce simp del: r_right_minus_eq)
    have q_not_zero: "q \<noteq> \<zero>\<^bsub>P\<^esub>" using Suc by (auto simp add : lin_fac)
    hence "deg R q = x" using Suc deg deg_mult[OF mon_not_zero q_not_zero _ q]
      by (simp add : lin_fac)
    hence q_IH: "finite {a \<in> carrier R . eval R R id a q = \<zero>}
                \<and> card {a \<in> carrier R . eval R R id a q = \<zero>} \<le> x" using Suc q q_not_zero by blast
    have subs: "{a \<in> carrier R . eval R R id a f = \<zero>}
                \<subseteq> {a \<in> carrier R . eval R R id a q = \<zero>} \<union> {a}" (is "?L \<subseteq> ?R \<union> {a}")
      using a_carrier \<open>q \<in> _\<close>
      by (auto simp: evalRR_simps lin_fac R.integral_iff)
    have "{a \<in> carrier R . eval R R id a f = \<zero>} \<subseteq> insert a {a \<in> carrier R . eval R R id a q = \<zero>}"
     using subs by auto
    hence "card {a \<in> carrier R . eval R R id a f = \<zero>} \<le>
           card (insert a {a \<in> carrier R . eval R R id a q = \<zero>})" using q_IH by (blast intro: card_mono)
    also have "\<dots> \<le> deg R f" using q_IH \<open>Suc x = _\<close>
      by (simp add: card_insert_if)
    finally show ?thesis using q_IH \<open>Suc x = _\<close> using finite by force
  next
    case False
    hence "card {a \<in> carrier R. eval R R id a f = \<zero>} = 0" using finite by auto
    also have "\<dots> \<le>  deg R f" by simp
    finally show ?thesis using finite by auto
  qed
qed

end

lemma (in domain) num_roots_le_deg :
  fixes p d :: nat
  assumes finite: "finite (carrier R)"
  assumes d_neq_zero: "d \<noteq> 0"
  shows "card {x \<in> carrier R. x [^] d = \<one>} \<le> d"
proof -
  let ?f = "monom (UP R) \<one>\<^bsub>R\<^esub> d \<ominus>\<^bsub> (UP R)\<^esub> monom (UP R) \<one>\<^bsub>R\<^esub> 0"
  have one_in_carrier: "\<one> \<in> carrier R" by simp
  interpret R: UP_domain R "UP R" by (unfold_locales)
  have "deg R ?f = d"
    using d_neq_zero by (simp add: R.deg_minus_eq)
  hence f_not_zero: "?f \<noteq> \<zero>\<^bsub>UP R\<^esub>" using  d_neq_zero by (auto simp add : R.deg_nzero_nzero)
  have roots_bound: "finite {a \<in> carrier R . eval R R id a ?f = \<zero>} \<and>
                    card {a \<in> carrier R . eval R R id a ?f = \<zero>} \<le> deg R ?f"
                    using finite by (intro R.roots_bound[OF _ f_not_zero]) simp
  have subs: "{x \<in> carrier R. x [^] d = \<one>} \<subseteq> {a \<in> carrier R . eval R R id a ?f = \<zero>}"
    by (auto simp: R.evalRR_simps)
  then have "card {x \<in> carrier R. x [^] d = \<one>} \<le>
        card {a \<in> carrier R. eval R R id a ?f = \<zero>}" using finite by (simp add : card_mono)
  thus ?thesis using \<open>deg R ?f = d\<close> roots_bound by linarith
qed



section \<open>The Multiplicative Group of a Field\<close>
text_raw \<open>\label{sec:mult-group}\<close>


text \<open>
  In this section we show that the multiplicative group of a finite field
  is generated by a single element, i.e. it is cyclic. The proof is inspired
  by the first proof given in the survey~@{cite "conrad-cyclicity"}.
\<close>

context field begin

lemma num_elems_of_ord_eq_phi':
  assumes finite: "finite (carrier R)" and dvd: "d dvd order (mult_of R)"
      and exists: "\<exists>a\<in>carrier (mult_of R). group.ord (mult_of R) a = d"
  shows "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} = phi' d"
proof -
  note mult_of_simps[simp]
  have finite': "finite (carrier (mult_of R))" using finite by (rule finite_mult_of)

  interpret G:group "mult_of R" rewrites "([^]\<^bsub>mult_of R\<^esub>) = (([^]) :: _ \<Rightarrow> nat \<Rightarrow> _)" and "\<one>\<^bsub>mult_of R\<^esub> = \<one>"
    by (rule field_mult_group) simp_all

  from exists
  obtain a where a: "a \<in> carrier (mult_of R)" and ord_a: "group.ord (mult_of R) a = d"
    by (auto simp add: card_gt_0_iff)

  have set_eq1: "{a[^]n| n. n \<in> {1 .. d}} = {x \<in> carrier (mult_of R). x [^] d = \<one>}"
  proof (rule card_seteq)
    show "finite {x \<in> carrier (mult_of R). x [^] d = \<one>}" using finite by auto

    show "{a[^]n| n. n \<in> {1 ..d}} \<subseteq> {x \<in> carrier (mult_of R). x[^]d = \<one>}"
    proof
      fix x assume "x \<in> {a[^]n | n. n \<in> {1 .. d}}"
      then obtain n where n: "x = a[^]n \<and> n \<in> {1 .. d}" by auto
      have "x[^]d =(a[^]d)[^]n" using n a ord_a by (simp add:nat_pow_pow mult.commute)
      hence "x[^]d = \<one>" using ord_a G.pow_ord_eq_1[OF a] by fastforce
      thus "x \<in> {x \<in> carrier (mult_of R). x[^]d = \<one>}" using G.nat_pow_closed[OF a] n by blast
    qed

    show "card {x \<in> carrier (mult_of R). x [^] d = \<one>} \<le> card {a[^]n | n. n \<in> {1 .. d}}"
    proof -
      have *: "{a[^]n | n. n \<in> {1 .. d }} = ((\<lambda> n. a[^]n) ` {1 .. d})" by auto
      have "0 < order (mult_of R)" unfolding order_mult_of[OF finite]
        using card_mono[OF finite, of "{\<zero>, \<one>}"] by (simp add: order_def)
      have "card {x \<in> carrier (mult_of R). x [^] d = \<one>} \<le> card {x \<in> carrier R. x [^] d = \<one>}"
        using finite by (auto intro: card_mono)
      also have "\<dots> \<le> d" using \<open>0 < order (mult_of R)\<close> num_roots_le_deg[OF finite, of d]
        by (simp add : dvd_pos_nat[OF _ \<open>d dvd order (mult_of R)\<close>])
      finally show ?thesis using G.ord_inj'[OF a] ord_a * by (simp add: card_image)
    qed
  qed

  have set_eq2: "{x \<in> carrier (mult_of R) . group.ord (mult_of R) x = d}
                = (\<lambda> n . a[^]n) ` {n \<in> {1 .. d}. group.ord (mult_of R) (a[^]n) = d}" (is "?L = ?R")
  proof
    { fix x assume x: "x \<in> (carrier (mult_of R)) \<and> group.ord (mult_of R) x = d"
      hence "x \<in> {x \<in> carrier (mult_of R). x [^] d = \<one>}"
        by (simp add: G.pow_ord_eq_1[of x, symmetric])
      then obtain n where n: "x = a[^]n \<and> n \<in> {1 .. d}" using set_eq1 by blast
      hence "x \<in> ?R" using x by fast
    } thus "?L \<subseteq> ?R" by blast
    show "?R \<subseteq> ?L" using a by (auto simp add: carrier_mult_of[symmetric] simp del: carrier_mult_of)
  qed
  have "inj_on (\<lambda> n . a[^]n) {n \<in> {1 .. d}. group.ord (mult_of R) (a[^]n) = d}"
    using G.ord_inj'[OF a, unfolded ord_a] unfolding inj_on_def by fast
  hence "card ((\<lambda>n. a[^]n) ` {n \<in> {1 .. d}. group.ord (mult_of R) (a[^]n) = d})
         = card {k \<in> {1 .. d}. group.ord (mult_of R) (a[^]k) = d}"
         using card_image by blast
  thus ?thesis using set_eq2 G.pow_ord_eq_ord_iff[OF finite' \<open>a \<in> _\<close>, unfolded ord_a]
    by (simp add: phi'_def)
qed

end


theorem (in field) finite_field_mult_group_has_gen :
  assumes finite: "finite (carrier R)"
  shows "\<exists> a \<in> carrier (mult_of R) . carrier (mult_of R) = {a[^]i | i::nat . i \<in> UNIV}"
proof -
  note mult_of_simps[simp]
  have finite': "finite (carrier (mult_of R))" using finite by (rule finite_mult_of)

  interpret G: group "mult_of R" rewrites
      "([^]\<^bsub>mult_of R\<^esub>) = (([^]) :: _ \<Rightarrow> nat \<Rightarrow> _)" and "\<one>\<^bsub>mult_of R\<^esub> = \<one>"
    by (rule field_mult_group) (simp_all add: fun_eq_iff nat_pow_def)

  let ?N = "\<lambda> x . card {a \<in> carrier (mult_of R). group.ord (mult_of R) a  = x}"
  have "0 < order R - 1" unfolding order_def using card_mono[OF finite, of "{\<zero>, \<one>}"] by simp
  then have *: "0 < order (mult_of R)" using assms by (simp add: order_mult_of)
  have fin: "finite {d. d dvd order (mult_of R) }" using dvd_nat_bounds[OF *] by force

  have "(\<Sum>d | d dvd order (mult_of R). ?N d)
      = card (UN d:{d . d dvd order (mult_of R) }. {a \<in> carrier (mult_of R). group.ord (mult_of R) a  = d})"
      (is "_ = card ?U")
    using fin finite by (subst card_UN_disjoint) auto
  also have "?U = carrier (mult_of R)"
  proof
    { fix x assume x: "x \<in> carrier (mult_of R)"
      hence x': "x\<in>carrier (mult_of R)" by simp
      then have "group.ord (mult_of R) x dvd order (mult_of R)"
        using G.ord_dvd_group_order by blast
      hence "x \<in> ?U" using dvd_nat_bounds[of "order (mult_of R)" "group.ord (mult_of R) x"] x by blast
    } thus "carrier (mult_of R) \<subseteq> ?U" by blast
  qed auto
  also have "card ... = order (mult_of R)"
    using order_mult_of finite' by (simp add: order_def)
  finally have sum_Ns_eq: "(\<Sum>d | d dvd order (mult_of R). ?N d) = order (mult_of R)" .

  { fix d assume d: "d dvd order (mult_of R)"
    have "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} \<le> phi' d"
    proof cases
      assume "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} = 0" thus ?thesis by presburger
      next
      assume "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} \<noteq> 0"
      hence "\<exists>a \<in> carrier (mult_of R). group.ord (mult_of R) a = d" by (auto simp: card_eq_0_iff)
      thus ?thesis using num_elems_of_ord_eq_phi'[OF finite d] by auto
    qed
  }
  hence all_le: "\<And>i. i \<in> {d. d dvd order (mult_of R) }
        \<Longrightarrow> (\<lambda>i. card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = i}) i \<le> (\<lambda>i. phi' i) i" by fast
  hence le: "(\<Sum>i | i dvd order (mult_of R). ?N i)
            \<le> (\<Sum>i | i dvd order (mult_of R). phi' i)"
            using sum_mono[of "{d .  d dvd order (mult_of R)}"
                  "\<lambda>i. card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = i}"] by presburger
  have "order (mult_of R) = (\<Sum>d | d dvd order (mult_of R). phi' d)" using *
    by (simp add: sum_phi'_factors)
  hence eq: "(\<Sum>i | i dvd order (mult_of R). ?N i)
          = (\<Sum>i | i dvd order (mult_of R). phi' i)" using le sum_Ns_eq by presburger
  have "\<And>i. i \<in> {d. d dvd order (mult_of R) } \<Longrightarrow> ?N i = (\<lambda>i. phi' i) i"
  proof (rule ccontr)
    fix i
    assume i1: "i \<in> {d. d dvd order (mult_of R)}" and "?N i \<noteq> phi' i"
    hence "?N i = 0"
      using num_elems_of_ord_eq_phi'[OF finite, of i] by (auto simp: card_eq_0_iff)
    moreover  have "0 < i" using * i1 by (simp add: dvd_nat_bounds[of "order (mult_of R)" i])
    ultimately have "?N i < phi' i" using phi'_nonzero by presburger
    hence "(\<Sum>i | i dvd order (mult_of R). ?N i)
         < (\<Sum>i | i dvd order (mult_of R). phi' i)"
      using sum_strict_mono_ex1[OF fin, of "?N" "\<lambda> i . phi' i"]
            i1 all_le by auto
    thus False using eq by force
  qed
  hence "?N (order (mult_of R)) > 0" using * by (simp add: phi'_nonzero)
  then obtain a where a: "a \<in> carrier (mult_of R)" and a_ord: "group.ord (mult_of R) a = order (mult_of R)"
    by (auto simp add: card_gt_0_iff)
  hence set_eq: "{a[^]i | i::nat. i \<in> UNIV} = (\<lambda>x. a[^]x) ` {0 .. group.ord (mult_of R) a - 1}"
    using G.ord_elems[OF finite'] by auto
  have card_eq: "card ((\<lambda>x. a[^]x) ` {0 .. group.ord (mult_of R) a - 1}) = card {0 .. group.ord (mult_of R) a - 1}"
    by (intro card_image G.ord_inj finite' a)
  hence "card ((\<lambda> x . a[^]x) ` {0 .. group.ord (mult_of R) a - 1}) = card {0 ..order (mult_of R) - 1}"
    using assms by (simp add: card_eq a_ord)
  hence card_R_minus_1: "card {a[^]i | i::nat. i \<in> UNIV} =  order (mult_of R)"
    using * by (subst set_eq) auto
  have **: "{a[^]i | i::nat. i \<in> UNIV} \<subseteq> carrier (mult_of R)"
    using G.nat_pow_closed[OF a] by auto
  with _ have "carrier (mult_of R) = {a[^]i|i::nat. i \<in> UNIV}"
    by (rule card_seteq[symmetric]) (simp_all add: card_R_minus_1 finite order_def del: UNIV_I)
  thus ?thesis using a by blast
qed

end
