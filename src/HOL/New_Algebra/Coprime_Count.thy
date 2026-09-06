section \<open>Counting the Residues Coprime to a Modulus\<close>

theory Coprime_Count
  imports Main
begin

text \<open>
  The cyclicity criterion for a finite group needs exactly two arithmetic facts about the number of
  residues below @{term e} coprime to @{term e}: that it is positive, and that summing it over the
  divisors of @{term d} recovers @{term d}.  Euler's totient function in \<open>HOL-Number_Theory\<close> supplies
  both, but that session reaches HOL-Algebra --- which this development exists to replace, and, more
  pressingly, importing it would make the dependency \<^emph>\<open>circular\<close> once \<open>Residues\<close> there is rebuilt on
  this development, because the primitive-root export routes through the cyclicity criterion.

  So the two facts are proved here directly and with no new definition: the count appears as the
  cardinality of an explicit set, which is the form the group-theoretic proof produces anyway.  This
  is deliberately not a second copy of \<open>Totient.thy\<close> --- there is no rival totient constant, only two
  lemmas about a set comprehension.
\<close>

lemma coprime_count_pos:
  fixes e :: nat
  assumes e: "0 < e" shows "0 < card {k. k < e \<and> gcd e k = 1}"
proof -
  have "{k. k < e \<and> gcd e k = 1} \<noteq> {}"
  proof (cases "e = 1")
    case True
    then have "0 \<in> {k. k < e \<and> gcd e k = 1}" by simp
    then show ?thesis by force
  next
    case False
    with e have "1 < e" by simp
    then have "1 \<in> {k. k < e \<and> gcd e k = 1}" by simp
    then show ?thesis by force
  qed
  moreover have "finite {k. k < e \<and> gcd e k = 1}" by simp
  ultimately show ?thesis by (simp add: card_gt_0_iff)
qed

text \<open>The residues below @{term d} whose greatest common divisor with @{term d} is exactly @{term f}
  are the multiples @{term "j * f"} of @{term f} by residues below @{term "d div f"} coprime to it.\<close>
lemma card_gcd_class:
  fixes d f :: nat
  assumes d: "0 < d" and f: "f dvd d"
  shows "card {j. j < d div f \<and> gcd (d div f) j = 1} = card {k. k < d \<and> gcd k d = f}"
proof (rule bij_betw_same_card)
  have fpos: "0 < f" using d f by (auto intro: dvd_pos_nat)
  have deq: "d div f * f = d" using f by simp
  show "bij_betw (\<lambda>j. j * f) {j. j < d div f \<and> gcd (d div f) j = 1} {k. k < d \<and> gcd k d = f}"
    unfolding bij_betw_def
  proof
    show "inj_on (\<lambda>j. j * f) {j. j < d div f \<and> gcd (d div f) j = 1}"
      using fpos by (simp add: inj_on_def)
  next
    show "(\<lambda>j. j * f) ` {j. j < d div f \<and> gcd (d div f) j = 1} = {k. k < d \<and> gcd k d = f}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> (\<lambda>j. j * f) ` {j. j < d div f \<and> gcd (d div f) j = 1}"
      then obtain j where j: "j < d div f" "gcd (d div f) j = 1" and k: "k = j * f" by auto
      from j(1) fpos have "j * f < d div f * f" by (rule mult_less_mono1)
      then have "k < d" using k deq by simp
      moreover have "gcd k d = f"
      proof -
        have "gcd k d = gcd (j * f) (d div f * f)" using k deq by simp
        also have "\<dots> = gcd (d div f) j * f" by (simp add: gcd_mult_right)
        also have "\<dots> = f" using j(2) by simp
        finally show ?thesis .
      qed
      ultimately show "k \<in> {k. k < d \<and> gcd k d = f}" by simp
    next
      fix k assume "k \<in> {k. k < d \<and> gcd k d = f}"
      then have k: "k < d" and g: "gcd k d = f" by simp_all
      from g have "f dvd k" by (metis gcd_dvd1)
      then have keq: "k div f * f = k" by simp
      have "gcd (d div f) (k div f) * f = gcd (k div f * f) (d div f * f)"
        by (simp add: gcd_mult_right)
      also have "\<dots> = gcd k d" using keq deq by simp
      finally have "gcd (d div f) (k div f) * f = f" using g by simp
      with fpos have cop: "gcd (d div f) (k div f) = 1" by simp
      moreover have "k div f < d div f" using k fpos f by (simp add: div_less_iff_less_mult)
      ultimately show "k \<in> (\<lambda>j. j * f) ` {j. j < d div f \<and> gcd (d div f) j = 1}"
        using keq by (force simp: image_iff)
    qed
  qed
qed

text \<open>Summing the coprime counts over the divisors of @{term d} recovers @{term d}: the residues
  below @{term d} are partitioned by their greatest common divisor with @{term d}.\<close>
theorem coprime_count_divisor_sum:
  fixes d :: nat
  assumes d: "0 < d"
  shows "(\<Sum>e | e dvd d. card {k. k < e \<and> gcd e k = 1}) = d"
proof -
  have fin_div: "finite {f. f dvd d}" using d by (rule finite_divisors_nat)
  have part: "{k. k < d} = (\<Union>f \<in> {f. f dvd d}. {k. k < d \<and> gcd k d = f})"
    by auto
  have "d = card {k. k < d}" by simp
  also have "\<dots> = (\<Sum>f | f dvd d. card {k. k < d \<and> gcd k d = f})"
    unfolding part using fin_div by (intro card_UN_disjoint) auto
  also have "\<dots> = (\<Sum>f | f dvd d. card {j. j < d div f \<and> gcd (d div f) j = 1})"
  proof (rule sum.cong [OF refl])
    fix f assume "f \<in> {f. f dvd d}"
    then show "card {k. k < d \<and> gcd k d = f}
               = card {j. j < d div f \<and> gcd (d div f) j = 1}"
      using card_gcd_class [OF d] by simp
  qed
  also have "\<dots> = (\<Sum>e | e dvd d. card {k. k < e \<and> gcd e k = 1})"
  proof (rule sum.reindex_bij_witness [of _ "\<lambda>e. d div e" "\<lambda>f. d div f"])
    show "\<And>f. f \<in> {f. f dvd d} \<Longrightarrow> d div (d div f) = f"
      using d by (simp add: div_div_eq_right)
    show "\<And>f. f \<in> {f. f dvd d} \<Longrightarrow> d div f \<in> {e. e dvd d}"
    proof -
      fix f :: nat assume "f \<in> {f. f dvd d}"
      then have eq: "d div f * f = d" by simp
      have "d div f dvd d div f * f" by (rule dvd_triv_left)
      with eq show "d div f \<in> {e. e dvd d}" by simp
    qed
    show "\<And>e. e \<in> {e. e dvd d} \<Longrightarrow> d div (d div e) = e"
      using d by (simp add: div_div_eq_right)
    show "\<And>e. e \<in> {e. e dvd d} \<Longrightarrow> d div e \<in> {f. f dvd d}"
    proof -
      fix e :: nat assume "e \<in> {e. e dvd d}"
      then have eq: "d div e * e = d" by simp
      have "d div e dvd d div e * e" by (rule dvd_triv_left)
      with eq show "d div e \<in> {f. f dvd d}" by simp
    qed
    show "\<And>f. f \<in> {f. f dvd d}
               \<Longrightarrow> card {k. k < d div f \<and> gcd (d div f) k = 1}
                   = card {j. j < d div f \<and> gcd (d div f) j = 1}" by simp
  qed
  finally show ?thesis by simp
qed

end
