section \<open>The prime fields \<open>GF(p) = \<int>/p\<int>\<close>\<close>

theory GF_p
  imports ZFact "HOL-Computational_Algebra.Primes"
begin

text \<open>For a prime @{term p}, the residue ring \<open>ZFact\<close> becomes a field:
  the only extra step over the general @{term "n > 0"} case is that every nonzero residue has a
  multiplicative inverse, which follows from Bézout's identity since @{term p} is prime.

  Carrier @{term "{0..<p}"} of @{typ nat}, arithmetic modulo @{term p}, arithmetic operations
  @{const gfp_add} and @{const gfp_mult} shared with the ring-level development in @{text ZFact}.\<close>

context
  fixes p :: nat
  assumes prime_p: "prime p"
begin

lemma p_gt_1: "p > 1" using prime_p by (simp add: prime_nat_iff)
lemma p_gt_0: "p > 0" using p_gt_1 by simp

text \<open>\<^emph>\<open>Inverses.\<close>  For @{term "a \<in> {1..<p}"}, @{term a} is coprime to the prime @{term p}, so
  Bézout gives integers with @{text "u\<cdot>a + v\<cdot>p = 1"}; reducing @{text "u"} modulo @{term p}
  yields a multiplicative inverse of @{term a}.\<close>
lemma gfp_inverse_exists:
  assumes a: "a \<in> {0..<p}" and anz: "a \<noteq> 0"
  shows "\<exists>b\<in>{0..<p}. gfp_mult p a b = 1"
proof -
  have ap: "a < p" and a1: "a \<ge> 1" using a anz by auto
  \<comment> \<open>@{term p} prime and @{term "a < p"}, @{term "a \<noteq> 0"}, so @{term p} does not divide @{term a}.\<close>
  have ndvd: "\<not> p dvd a" using ap anz by (simp add: nat_dvd_not_less)
  then have "gcd a p = 1"
    by (metis gcd_unique prime_nat_iff prime_p)
  then have cop: "coprime (int a) (int p)" by (simp add: coprime_iff_gcd_eq_1)
  \<comment> \<open>Bézout: @{text "u\<cdot>a + v\<cdot>p = 1"} for some integers @{text u}, @{text v}.\<close>
  obtain u v :: int where uv: "u * int a + v * int p = 1"
    using cop bezout_int by (metis coprime_imp_gcd_eq_1)
  define b where "b = nat (u mod int p)"
  have brange: "b \<in> {0..<p}" using p_gt_0 by (simp add: b_def) (simp add: nat_less_iff)
  \<comment> \<open>Then @{text "a\<cdot>b \<equiv> a\<cdot>u \<equiv> 1 (mod p)"}.\<close>
  have "int (gfp_mult p a b) = (int a * u) mod int p"
    by (simp add: b_def gfp_mult_def mod_mult_right_eq of_nat_mod p_gt_0)
  also have "\<dots> = (1 - v * int p + v * int p) mod int p"
    by (metis diff_add_cancel mod_mult_self1 mult.commute uv)
  also have "\<dots> = 1" using p_gt_1 by simp
  finally show ?thesis using brange
    using of_nat_eq_1_iff by blast
qed

lemma gfp_field: "Field {0..<p} (gfp_add p) (gfp_mult p) 0 1"
proof -
  interpret R: commutative_ring "{0..<p}" "gfp_add p" "gfp_mult p" 0 1
    using zfact_commutative_ring[OF p_gt_1] .
  show ?thesis
  proof
    show "(1::nat) \<noteq> 0" using p_gt_1 by simp
    show "\<And>a. a \<in> {0..<p} \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> R.multiplicative.invertible a"
      by (metis R.multiplicative.invertibleI gfp_inverse_exists gfp_mult_def mult.commute)
  qed
qed

text \<open>The prime field has exactly @{term p} elements.\<close>
lemma card_gfp: "card {0..<p} = p" by simp

end

text \<open>Hence prime fields of every prime order exist --- in particular the @{locale Field} locale is
  non-vacuous for every prime cardinality.\<close>

end
