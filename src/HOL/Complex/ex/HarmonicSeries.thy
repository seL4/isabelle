(*  Title:      HOL/Library/HarmonicSeries.thy
    ID:         $Id$
    Author:     Benjamin Porter, 2006
*)

header {* Divergence of the Harmonic Series *}

theory HarmonicSeries
imports Complex_Main
begin

section {* Abstract *}

text {* The following document presents a proof of the Divergence of
Harmonic Series theorem formalised in the Isabelle/Isar theorem
proving system.

{\em Theorem:} The series $\sum_{n=1}^{\infty} \frac{1}{n}$ does not
converge to any number.

{\em Informal Proof:}
  The informal proof is based on the following auxillary lemmas:
  \begin{itemize}
  \item{aux: $\sum_{n=2^m-1}^{2^m} \frac{1}{n} \geq \frac{1}{2}$}
  \item{aux2: $\sum_{n=1}^{2^M} \frac{1}{n} = 1 + \sum_{m=1}^{M} \sum_{n=2^m-1}^{2^m} \frac{1}{n}$}
  \end{itemize}

  From {\em aux} and {\em aux2} we can deduce that $\sum_{n=1}^{2^M}
  \frac{1}{n} \geq 1 + \frac{M}{2}$ for all $M$.
  Now for contradiction, assume that $\sum_{n=1}^{\infty} \frac{1}{n}
  = s$ for some $s$. Because $\forall n. \frac{1}{n} > 0$ all the
  partial sums in the series must be less than $s$. However with our
  deduction above we can choose $N > 2*s - 2$ and thus
  $\sum_{n=1}^{2^N} \frac{1}{n} > s$. This leads to a contradiction
  and hence $\sum_{n=1}^{\infty} \frac{1}{n}$ is not summable.
  QED.
*}

section {* Formal Proof *}

lemma two_pow_sub:
  "0 < m \<Longrightarrow> (2::nat)^m - 2^(m - 1) = 2^(m - 1)"
  by (induct m) auto

text {* We first prove the following auxillary lemma. This lemma
simply states that the finite sums: $\frac{1}{2}$, $\frac{1}{3} +
\frac{1}{4}$, $\frac{1}{5} + \frac{1}{6} + \frac{1}{7} + \frac{1}{8}$
etc. are all greater than or equal to $\frac{1}{2}$. We do this by
observing that each term in the sum is greater than or equal to the
last term, e.g. $\frac{1}{3} > \frac{1}{4}$ and thus $\frac{1}{3} +
\frac{1}{4} > \frac{1}{4} + \frac{1}{4} = \frac{1}{2}$. *}

lemma harmonic_aux:
  "\<forall>m>0. (\<Sum>n\<in>{(2::nat)^(m - 1)+1..2^m}. 1/real n) \<ge> 1/2"
  (is "\<forall>m>0. (\<Sum>n\<in>(?S m). 1/real n) \<ge> 1/2")
proof
  fix m::nat
  obtain tm where tmdef: "tm = (2::nat)^m" by simp
  {
    assume mgt0: "0 < m"
    have "\<And>x. x\<in>(?S m) \<Longrightarrow> 1/(real x) \<ge> 1/(real tm)"
    proof -
      fix x::nat
      assume xs: "x\<in>(?S m)"
      have xgt0: "x>0"
      proof -
        from xs have
          "x \<ge> 2^(m - 1) + 1" by auto
        moreover with mgt0 have
          "2^(m - 1) + 1 \<ge> (1::nat)" by auto
        ultimately have
          "x \<ge> 1" by (rule xtrans)
        thus ?thesis by simp
      qed
      moreover from xs have "x \<le> 2^m" by auto
      ultimately have
        "inverse (real x) \<ge> inverse (real ((2::nat)^m))" by simp
      moreover
      from xgt0 have "real x \<noteq> 0" by simp
      then have
        "inverse (real x) = 1 / (real x)"
        by (rule nonzero_inverse_eq_divide)
      moreover from mgt0 have "real tm \<noteq> 0" by (simp add: tmdef)
      then have
        "inverse (real tm) = 1 / (real tm)"
        by (rule nonzero_inverse_eq_divide)
      ultimately show
        "1/(real x) \<ge> 1/(real tm)" by (auto simp add: tmdef)
    qed
    then have
      "(\<Sum>n\<in>(?S m). 1 / real n) \<ge> (\<Sum>n\<in>(?S m). 1/(real tm))"
      by (rule setsum_mono)
    moreover have
      "(\<Sum>n\<in>(?S m). 1/(real tm)) = 1/2"
    proof -
      have
        "(\<Sum>n\<in>(?S m). 1/(real tm)) =
         (1/(real tm))*(\<Sum>n\<in>(?S m). 1)"
        by simp
      also have
        "\<dots> = ((1/(real tm)) * real (card (?S m)))"
        by (simp add: real_of_card real_of_nat_def)
      also have
        "\<dots> = ((1/(real tm)) * real (tm - (2^(m - 1))))"
        by (simp add: tmdef)
      also from mgt0 have
        "\<dots> = ((1/(real tm)) * real ((2::nat)^(m - 1)))"
        by (auto simp: tmdef dest: two_pow_sub)
      also have
        "\<dots> = (real (2::nat))^(m - 1) / (real (2::nat))^m"
        by (simp add: tmdef realpow_real_of_nat [symmetric])
      also from mgt0 have
        "\<dots> = (real (2::nat))^(m - 1) / (real (2::nat))^((m - 1) + 1)"
        by auto
      also have "\<dots> = 1/2" by simp
      finally show ?thesis .
    qed
    ultimately have
      "(\<Sum>n\<in>(?S m). 1 / real n) \<ge> 1/2"
      by - (erule subst)
  }
  thus "0 < m \<longrightarrow> 1 / 2 \<le> (\<Sum>n\<in>(?S m). 1 / real n)" by simp
qed

text {* We then show that the sum of a finite number of terms from the
harmonic series can be regrouped in increasing powers of 2. For
example: $1 + \frac{1}{2} + \frac{1}{3} + \frac{1}{4} + \frac{1}{5} +
\frac{1}{6} + \frac{1}{7} + \frac{1}{8} = 1 + (\frac{1}{2}) +
(\frac{1}{3} + \frac{1}{4}) + (\frac{1}{5} + \frac{1}{6} + \frac{1}{7}
+ \frac{1}{8})$. *}

lemma harmonic_aux2 [rule_format]:
  "0<M \<Longrightarrow> (\<Sum>n\<in>{1..(2::nat)^M}. 1/real n) =
   (1 + (\<Sum>m\<in>{1..M}. \<Sum>n\<in>{(2::nat)^(m - 1)+1..2^m}. 1/real n))"
  (is "0<M \<Longrightarrow> ?LHS M = ?RHS M")
proof (induct M)
  case 0 show ?case by simp
next
  case (Suc M)
  have ant: "0 < Suc M" .
  {
    have suc: "?LHS (Suc M) = ?RHS (Suc M)"
    proof cases -- "show that LHS = c and RHS = c, and thus LHS = RHS"
      assume mz: "M=0"
      {
        then have
          "?LHS (Suc M) = ?LHS 1" by simp
        also have
          "\<dots> = (\<Sum>n\<in>{(1::nat)..2}. 1/real n)" by simp
        also have
          "\<dots> = ((\<Sum>n\<in>{Suc 1..2}. 1/real n) + 1/(real (1::nat)))"
          by (subst setsum_head)
             (auto simp: atLeastSucAtMost_greaterThanAtMost)
        also have
          "\<dots> = ((\<Sum>n\<in>{2..2::nat}. 1/real n) + 1/(real (1::nat)))"
          by (simp add: nat_number)
        also have
          "\<dots> =  1/(real (2::nat)) + 1/(real (1::nat))" by simp
        finally have
          "?LHS (Suc M) = 1/2 + 1" by simp
      }
      moreover
      {
        from mz have
          "?RHS (Suc M) = ?RHS 1" by simp
        also have
          "\<dots> = (\<Sum>n\<in>{((2::nat)^0)+1..2^1}. 1/real n) + 1"
          by simp
        also have
          "\<dots> = (\<Sum>n\<in>{2::nat..2}. 1/real n) + 1"
        proof -
          have "(2::nat)^0 = 1" by simp
          then have "(2::nat)^0+1 = 2" by simp
          moreover have "(2::nat)^1 = 2" by simp
          ultimately have "{((2::nat)^0)+1..2^1} = {2::nat..2}" by auto
          thus ?thesis by simp
        qed
        also have
          "\<dots> = 1/2 + 1"
          by simp
        finally have
          "?RHS (Suc M) = 1/2 + 1" by simp
      }
      ultimately show "?LHS (Suc M) = ?RHS (Suc M)" by simp
    next
      assume mnz: "M\<noteq>0"
      then have mgtz: "M>0" by simp
      with Suc have suc:
        "(?LHS M) = (?RHS M)" by blast
      have
        "(?LHS (Suc M)) =
         ((?LHS M) + (\<Sum>n\<in>{(2::nat)^M+1..2^(Suc M)}. 1 / real n))"
      proof -
        have
          "{1..(2::nat)^(Suc M)} =
           {1..(2::nat)^M}\<union>{(2::nat)^M+1..(2::nat)^(Suc M)}"
          by auto
        moreover have
          "{1..(2::nat)^M}\<inter>{(2::nat)^M+1..(2::nat)^(Suc M)} = {}"
          by auto
        moreover have
          "finite {1..(2::nat)^M}" and "finite {(2::nat)^M+1..(2::nat)^(Suc M)}"
          by auto
        ultimately show ?thesis
          by (auto intro: setsum_Un_disjoint)
      qed
      moreover
      {
        have
          "(?RHS (Suc M)) =
           (1 + (\<Sum>m\<in>{1..M}.  \<Sum>n\<in>{(2::nat)^(m - 1)+1..2^m}. 1/real n) +
           (\<Sum>n\<in>{(2::nat)^(Suc M - 1)+1..2^(Suc M)}. 1/real n))" by simp
        also have
          "\<dots> = (?RHS M) + (\<Sum>n\<in>{(2::nat)^M+1..2^(Suc M)}. 1/real n)"
          by simp
        also from suc have
          "\<dots> = (?LHS M) +  (\<Sum>n\<in>{(2::nat)^M+1..2^(Suc M)}. 1/real n)"
          by simp
        finally have
          "(?RHS (Suc M)) = \<dots>" by simp
      }
      ultimately show "?LHS (Suc M) = ?RHS (Suc M)" by simp
    qed
  }
  thus ?case by simp
qed

text {* Using @{thm [source] harmonic_aux} and @{thm [source] harmonic_aux2} we now show
that each group sum is greater than or equal to $\frac{1}{2}$ and thus
the finite sum is bounded below by a value proportional to the number
of elements we choose. *}

lemma harmonic_aux3 [rule_format]:
  shows "\<forall>(M::nat). (\<Sum>n\<in>{1..(2::nat)^M}. 1 / real n) \<ge> 1 + (real M)/2"
  (is "\<forall>M. ?P M \<ge> _")
proof (rule allI, cases)
  fix M::nat
  assume "M=0"
  then show "?P M \<ge> 1 + (real M)/2" by simp
next
  fix M::nat
  assume "M\<noteq>0"
  then have "M > 0" by simp
  then have
    "(?P M) =
     (1 + (\<Sum>m\<in>{1..M}. \<Sum>n\<in>{(2::nat)^(m - 1)+1..2^m}. 1/real n))"
    by (rule harmonic_aux2)
  also have
    "\<dots> \<ge> (1 + (\<Sum>m\<in>{1..M}. 1/2))"
  proof -
    let ?f = "(\<lambda>x. 1/2)"
    let ?g = "(\<lambda>x. (\<Sum>n\<in>{(2::nat)^(x - 1)+1..2^x}. 1/real n))"
    from harmonic_aux have "\<And>x. x\<in>{1..M} \<Longrightarrow> ?f x \<le> ?g x" by simp
    then have "(\<Sum>m\<in>{1..M}. ?g m) \<ge> (\<Sum>m\<in>{1..M}. ?f m)" by (rule setsum_mono)
    thus ?thesis by simp
  qed
  finally have "(?P M) \<ge> (1 + (\<Sum>m\<in>{1..M}. 1/2))" .
  moreover
  {
    have
      "(\<Sum>m\<in>{1..M}. (1::real)/2) = 1/2 * (\<Sum>m\<in>{1..M}. 1)"
      by auto
    also have
      "\<dots> = 1/2*(real (card {1..M}))"
      by (simp only: real_of_card[symmetric])
    also have
      "\<dots> = 1/2*(real M)" by simp
    also have
      "\<dots> = (real M)/2" by simp
    finally have "(\<Sum>m\<in>{1..M}. (1::real)/2) = (real M)/2" .
  }
  ultimately show "(?P M) \<ge> (1 + (real M)/2)" by simp
qed

text {* The final theorem shows that as we take more and more elements
(see @{thm [source] harmonic_aux3}) we get an ever increasing sum. By assuming
the sum converges, the lemma @{thm [source] series_pos_less} ( @{thm
series_pos_less} ) states that each sum is bounded above by the
series' limit. This contradicts our first statement and thus we prove
that the harmonic series is divergent. *}

theorem DivergenceOfHarmonicSeries:
  shows "\<not>summable (\<lambda>n. 1/real (Suc n))"
  (is "\<not>summable ?f")
proof -- "by contradiction"
  let ?s = "suminf ?f" -- "let ?s equal the sum of the harmonic series"
  assume sf: "summable ?f"
  then obtain n::nat where ndef: "n = nat \<lceil>2 * ?s\<rceil>" by simp
  then have ngt: "1 + real n/2 > ?s"
  proof -
    have "\<forall>n. 0 \<le> ?f n" by simp
    with sf have "?s \<ge> 0"
      by - (rule suminf_0_le, simp_all)
    then have cgt0: "\<lceil>2*?s\<rceil> \<ge> 0" by simp

    from ndef have "n = nat \<lceil>(2*?s)\<rceil>" .
    then have "real n = real (nat \<lceil>2*?s\<rceil>)" by simp
    with cgt0 have "real n = real \<lceil>2*?s\<rceil>"
      by (auto dest: real_nat_eq_real)
    then have "real n \<ge> 2*(?s)" by simp
    then have "real n/2 \<ge> (?s)" by simp
    then show "1 + real n/2 > (?s)" by simp
  qed

  obtain j where jdef: "j = (2::nat)^n" by simp
  have "\<forall>m\<ge>j. 0 < ?f m" by simp
  with sf have "(\<Sum>i\<in>{0..<j}. ?f i) < ?s" by (rule series_pos_less)
  then have "(\<Sum>i\<in>{1..<Suc j}. 1/(real i)) < ?s"
    apply -
    apply (subst(asm) setsum_shift_bounds_Suc_ivl [symmetric])
    by simp
  with jdef have
    "(\<Sum>i\<in>{1..< Suc ((2::nat)^n)}. 1 / (real i)) < ?s" by simp
  then have
    "(\<Sum>i\<in>{1..(2::nat)^n}. 1 / (real i)) < ?s"
    by (simp only: atLeastLessThanSuc_atLeastAtMost)
  moreover from harmonic_aux3 have
    "(\<Sum>i\<in>{1..(2::nat)^n}. 1 / (real i)) \<ge> 1 + real n/2" by simp
  moreover from ngt have "1 + real n/2 > ?s" by simp
  ultimately show False by simp
qed

end