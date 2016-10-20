(* Author: Jaime Mendizabal Roche *)

theory Quadratic_Reciprocity
imports Gauss
begin

text {* The proof is based on Gauss's fifth proof, which can be found at http://www.lehigh.edu/~shw2/q-recip/gauss5.pdf *}

locale QR =
  fixes p :: "nat"
  fixes q :: "nat"

  assumes p_prime: "prime p"
  assumes p_ge_2: "2 < p"
  assumes q_prime: "prime q"
  assumes q_ge_2: "2 < q"
  assumes pq_neq: "p \<noteq> q"
begin

lemma odd_p: "odd p" using p_ge_2 p_prime prime_odd_nat by blast

lemma p_ge_0: "0 < int p"
  using p_prime not_prime_0[where 'a = nat] by fastforce+

lemma p_eq2: "int p = (2 * ((int p - 1) div 2)) + 1" using odd_p by simp

lemma odd_q: "odd q" using q_ge_2 q_prime prime_odd_nat by blast

lemma q_ge_0: "0 < int q" using q_prime not_prime_0[where 'a = nat] by fastforce+

lemma q_eq2: "int q = (2 * ((int q - 1) div 2)) + 1" using odd_q by simp

lemma pq_eq2: "int p * int q = (2 * ((int p * int q - 1) div 2)) + 1" using odd_p odd_q by simp

lemma pq_coprime: "coprime p q"
  using pq_neq p_prime primes_coprime_nat q_prime by blast

lemma pq_coprime_int: "coprime (int p) (int q)"
  using pq_coprime transfer_int_nat_gcd(1) by presburger

lemma qp_ineq: "(int p * k \<le> (int p * int q - 1) div 2) = (k \<le> (int q - 1) div 2)"
proof -
  have "(2 * int p * k \<le> int p * int q - 1) = (2 * k \<le> int q - 1)" using p_ge_0 by auto
  thus ?thesis by auto
qed

lemma QRqp: "QR q p" using QR_def QR_axioms by simp

lemma pq_commute: "int p * int q = int q * int p" by simp

lemma pq_ge_0: "int p * int q > 0" using p_ge_0 q_ge_0 mult_pos_pos by blast

definition "r = ((p - 1) div 2)*((q - 1) div 2)"
definition "m = card (GAUSS.E p q)"
definition "n = card (GAUSS.E q p)"

abbreviation "Res (k::int) \<equiv> {0 .. k - 1}"
abbreviation "Res_ge_0 (k::int) \<equiv> {0 <.. k - 1}"
abbreviation "Res_0 (k::int) \<equiv> {0::int}"
abbreviation "Res_l (k::int) \<equiv> {0 <.. (k - 1) div 2}"
abbreviation "Res_h (k::int) \<equiv> {(k - 1) div 2 <.. k - 1}"

abbreviation "Sets_pq r0 r1 r2 \<equiv>
  {(x::int). x \<in> r0 (int p * int q) \<and> x mod p \<in> r1 (int p) \<and> x mod q \<in> r2 (int q)}"

definition "A = Sets_pq Res_l Res_l Res_h"
definition "B = Sets_pq Res_l Res_h Res_l"
definition "C = Sets_pq Res_h Res_h Res_l"
definition "D = Sets_pq Res_l Res_h Res_h"
definition "E = Sets_pq Res_l Res_0 Res_h"
definition "F = Sets_pq Res_l Res_h Res_0"

definition "a = card A"
definition "b = card B"
definition "c = card C"
definition "d = card D"
definition "e = card E"
definition "f = card F"

lemma Gpq: "GAUSS p q" unfolding GAUSS_def
  using p_prime pq_neq p_ge_2 q_prime
  by (auto simp: cong_altdef_int zdvd_int [symmetric] dest: primes_dvd_imp_eq) 

lemma Gqp: "GAUSS q p" using QRqp QR.Gpq by simp

lemma QR_lemma_01: "(\<lambda>x. x mod q) ` E = GAUSS.E q p"
proof
    {
      fix x
      assume a1: "x \<in> E"
      then obtain k where k: "x = int p * k" unfolding E_def by blast
      have "x \<in> Res_l (int p * int q)" using a1 E_def by blast
      hence "k \<in> GAUSS.A q" using Gqp GAUSS.A_def k qp_ineq by (simp add: zero_less_mult_iff)
      hence "x mod q \<in> GAUSS.E q p"
        using GAUSS.C_def[of q p] Gqp k GAUSS.B_def[of q p] a1 GAUSS.E_def[of q p]
        unfolding E_def by force
      hence "x \<in> E \<longrightarrow> x mod int q \<in> GAUSS.E q p" by auto
    }
    thus "(\<lambda>x. x mod int q) ` E \<subseteq> GAUSS.E q p" by auto
next
  show "GAUSS.E q p \<subseteq> (\<lambda>x. x mod q) ` E"
  proof
    fix x
    assume a1: "x \<in> GAUSS.E q p"
    then obtain ka where ka: "ka \<in> GAUSS.A q" "x = (ka * p) mod q"
      using Gqp GAUSS.B_def GAUSS.C_def GAUSS.E_def by auto
    hence "ka * p \<in> Res_l (int p * int q)"
      using GAUSS.A_def Gqp p_ge_0 qp_ineq by (simp add: Groups.mult_ac(2))
    thus "x \<in> (\<lambda>x. x mod q) ` E" unfolding E_def using ka a1 Gqp GAUSS.E_def q_ge_0 by force
  qed
qed

lemma QR_lemma_02: "e= n"
proof -
  {
    fix x y
    assume a: "x \<in> E" "y \<in> E" "x mod q = y mod q"
    obtain p_inv where p_inv: "[int p * p_inv = 1] (mod int q)"
      using pq_coprime_int cong_solve_coprime_int by blast
    obtain kx ky where k: "x = int p * kx" "y = int p * ky" using a E_def dvd_def[of p x] by blast
    hence "0 < x" "int p * kx \<le> (int p * int q - 1) div 2"
        "0 < y" "int p * ky \<le> (int p * int q - 1) div 2"
      using E_def a greaterThanAtMost_iff mem_Collect_eq by blast+
    hence "0 \<le> kx" "kx < q" "0 \<le> ky" "ky < q" using qp_ineq k by (simp add: zero_less_mult_iff)+
    moreover have "(p_inv * (p * kx)) mod q = (p_inv * (p * ky)) mod q"
      using a(3) mod_mult_cong k by blast
    hence "(p * p_inv * kx) mod q = (p * p_inv * ky) mod q" by (simp add:algebra_simps)
    hence "kx mod q = ky mod q"
      using p_inv mod_mult_cong[of "p * p_inv" "q" "1"] cong_int_def by auto
    hence "[kx = ky] (mod q)" using cong_int_def by blast
    ultimately have "x = y" using cong_less_imp_eq_int k by blast
  }
  hence "inj_on (\<lambda>x. x mod q) E" unfolding inj_on_def by auto
  thus ?thesis using QR_lemma_01 card_image e_def n_def by fastforce
qed

lemma QR_lemma_03: "f = m"
proof -
  have "F = QR.E q p" unfolding F_def pq_commute using QRqp QR.E_def[of q p] by fastforce
  hence "f = QR.e q p" unfolding f_def using QRqp QR.e_def[of q p] by presburger
  thus ?thesis using QRqp QR.QR_lemma_02 m_def QRqp QR.n_def by presburger
qed

definition f_1 :: "int \<Rightarrow> int \<times> int" where
  "f_1 x = ((x mod p), (x mod q))"

definition P_1 :: "int \<times> int \<Rightarrow> int \<Rightarrow> bool" where
  "P_1 res x \<longleftrightarrow> x mod p = fst res & x mod q = snd res & x \<in> Res (int p * int q)"

definition g_1 :: "int \<times> int \<Rightarrow> int" where
  "g_1 res = (THE x. P_1 res x)"

lemma P_1_lemma: assumes "0 \<le> fst res" "fst res < p" "0 \<le> snd res" "snd res < q"
  shows "\<exists>! x. P_1 res x"
proof -
  obtain y k1 k2 where yk: "y = nat (fst res) + k1 * p" "y = nat (snd res) + k2 * q"
    using chinese_remainder[of p q] pq_coprime p_ge_0 q_ge_0 by fastforce
  have h1: "[y = fst res] (mod p)" "[y = snd res] (mod q)"
    using yk(1) assms(1) cong_iff_lin_int[of "fst res"] cong_sym_int apply simp
    using yk(2) assms(3) cong_iff_lin_int[of "snd res"] cong_sym_int by simp
  have "(y mod (int p * int q)) mod int p = fst res" "(y mod (int p * int q)) mod int q = snd res"
    using h1(1) mod_mod_cancel[of "int p"] assms(1) assms(2) cong_int_def apply simp
    using h1(2) mod_mod_cancel[of "int q"] assms(3) assms(4) cong_int_def by simp
  then obtain x where "P_1 res x" unfolding P_1_def
    using Divides.pos_mod_bound Divides.pos_mod_sign pq_ge_0 by fastforce
  moreover {
    fix a b
    assume a: "P_1 res a" "P_1 res b"
    hence "int p * int q dvd a - b"
      using divides_mult[of "int p" "a - b" "int q"] pq_coprime_int zmod_eq_dvd_iff[of a _ b]
      unfolding P_1_def by force
    hence "a = b" using dvd_imp_le_int[of "a - b"] a unfolding P_1_def by fastforce
  }
  ultimately show ?thesis by auto
qed

lemma g_1_lemma: assumes "0 \<le> fst res" "fst res < p" "0 \<le> snd res" "snd res < q"
  shows "P_1 res (g_1 res)" using assms P_1_lemma theI'[of "P_1 res"] g_1_def by presburger

definition "BuC = Sets_pq Res_ge_0 Res_h Res_l"

lemma QR_lemma_04: "card BuC = card ((Res_h p) \<times> (Res_l q))"
  using card_bij_eq[of f_1 "BuC" "(Res_h p) \<times> (Res_l q)" g_1]
proof
  {
    fix x y
    assume a: "x \<in> BuC" "y \<in> BuC" "f_1 x = f_1 y"
    hence "int p * int q dvd x - y"
      using f_1_def pq_coprime_int divides_mult[of "int p" "x - y" "int q"] 
            zmod_eq_dvd_iff[of x _ y] by auto
    hence "x = y"
      using dvd_imp_le_int[of "x - y" "int p * int q"] a unfolding BuC_def by force
  }
  thus "inj_on f_1 BuC" unfolding inj_on_def by auto
next
  {
    fix x y
    assume a: "x \<in> (Res_h p) \<times> (Res_l q)" "y \<in> (Res_h p) \<times> (Res_l q)" "g_1 x = g_1 y"
    hence "0 \<le> fst x" "fst x < p" "0 \<le> snd x" "snd x < q"
        "0 \<le> fst y" "fst y < p" "0 \<le> snd y" "snd y < q"
      using mem_Sigma_iff prod.collapse by fastforce+
    hence "x = y" using g_1_lemma[of x] g_1_lemma[of y] a P_1_def by fastforce
  }
  thus "inj_on g_1 ((Res_h p) \<times> (Res_l q))" unfolding inj_on_def by auto
next
  show "g_1 ` ((Res_h p) \<times> (Res_l q)) \<subseteq> BuC"
  proof
    fix y
    assume "y \<in> g_1 ` ((Res_h p) \<times> (Res_l q))"
    then obtain x where x: "y = g_1 x" "x \<in> ((Res_h p) \<times> (Res_l q))" by blast
    hence "P_1 x y" using g_1_lemma by fastforce
    thus "y \<in> BuC" unfolding P_1_def BuC_def mem_Collect_eq using x SigmaE prod.sel by fastforce
  qed
qed (auto simp: BuC_def finite_subset f_1_def)

lemma QR_lemma_05: "card ((Res_h p) \<times> (Res_l q)) = r"
proof -
  have "card (Res_l q) = (q - 1) div 2" "card (Res_h p) = (p - 1) div 2" using p_eq2 by force+
  thus ?thesis unfolding r_def using card_cartesian_product[of "Res_h p" "Res_l q"] by presburger
qed

lemma QR_lemma_06: "b + c = r"
proof -
  have "B \<inter> C = {}" "finite B" "finite C" "B \<union> C = BuC" unfolding B_def C_def BuC_def by fastforce+
  thus ?thesis
    unfolding b_def c_def using card_empty card_Un_Int QR_lemma_04 QR_lemma_05 by fastforce
qed

definition f_2:: "int \<Rightarrow> int" where
  "f_2 x = (int p * int q) - x"

lemma f_2_lemma_1: "\<And>x. f_2 (f_2 x) = x" unfolding f_2_def by simp

lemma f_2_lemma_2: "[f_2 x = int p - x] (mod p)" unfolding f_2_def using cong_altdef_int by simp

lemma f_2_lemma_3: "f_2 x \<in> S \<Longrightarrow> x \<in> f_2 ` S"
  using f_2_lemma_1[of x] image_eqI[of x f_2 "f_2 x" S] by presburger

lemma QR_lemma_07: "f_2 ` Res_l (int p * int q) = Res_h (int p * int q)"
    "f_2 ` Res_h (int p * int q) = Res_l (int p * int q)"
proof -
  have h1: "f_2 ` Res_l (int p * int q) \<subseteq> Res_h (int p * int q)" using f_2_def by force
  have h2: "f_2 ` Res_h (int p * int q) \<subseteq> Res_l (int p * int q)" using f_2_def pq_eq2 by fastforce
  have h3: "Res_h (int p * int q) \<subseteq> f_2 ` Res_l (int p * int q)" using h2 f_2_lemma_3 by blast
  have h4: "Res_l (int p * int q) \<subseteq> f_2 ` Res_h (int p * int q)" using h1 f_2_lemma_3 by blast
  show "f_2 ` Res_l (int p * int q) = Res_h (int p * int q)" using h1 h3 by blast
  show "f_2 ` Res_h (int p * int q) = Res_l (int p * int q)" using h2 h4 by blast
qed

lemma QR_lemma_08: "(f_2 x mod p \<in> Res_l p) = (x mod p \<in> Res_h p)"
    "(f_2 x mod p \<in> Res_h p) = (x mod p \<in> Res_l p)"
  using f_2_lemma_2[of x] cong_int_def[of "f_2 x" "p - x" p] minus_mod_self2[of x p]
  zmod_zminus1_eq_if[of x p] p_eq2 by auto

lemma QR_lemma_09: "(f_2 x mod q \<in> Res_l q) = (x mod q \<in> Res_h q)"
    "(f_2 x mod q \<in> Res_h q) = (x mod q \<in> Res_l q)"
  using QRqp QR.QR_lemma_08 f_2_def QR.f_2_def pq_commute by auto+

lemma QR_lemma_10: "a = c" unfolding a_def c_def apply (rule card_bij_eq[of f_2 A C f_2])
  unfolding A_def C_def
  using QR_lemma_07 QR_lemma_08 QR_lemma_09 apply ((simp add: inj_on_def f_2_def),blast)+
  by fastforce+

definition "BuD = Sets_pq Res_l Res_h Res_ge_0"
definition "BuDuF = Sets_pq Res_l Res_h Res"

definition f_3 :: "int \<Rightarrow> int \<times> int" where
  "f_3 x = (x mod p, x div p + 1)"

definition g_3 :: "int \<times> int \<Rightarrow> int" where
  "g_3 x = fst x + (snd x - 1) * p"

lemma QR_lemma_11: "card BuDuF = card ((Res_h p) \<times> (Res_l q))"
  using card_bij_eq[of f_3 BuDuF "(Res_h p) \<times> (Res_l q)" g_3]
proof
  show "f_3 ` BuDuF \<subseteq> (Res_h p) \<times> (Res_l q)"
  proof
    fix y
    assume "y \<in> f_3 ` BuDuF"
    then obtain x where x: "y = f_3 x" "x \<in> BuDuF" by blast
    hence "x \<le> int p * (int q - 1) div 2 + (int p - 1) div 2"
      unfolding BuDuF_def using p_eq2 int_distrib(4) by auto
    moreover have "(int p - 1) div 2 \<le> - 1 + x mod p" using x BuDuF_def by auto
    moreover have "int p * (int q - 1) div 2 = int p * ((int q - 1) div 2)"
      using zdiv_zmult1_eq odd_q by auto
    hence "p * (int q - 1) div 2 = p * ((int q + 1) div 2 - 1)" by fastforce
    ultimately have "x \<le> p * ((int q + 1) div 2 - 1) - 1 + x mod p" by linarith
    hence "x div p < (int q + 1) div 2 - 1"
      using mult.commute[of "int p" "x div p"] p_ge_0 div_mult_mod_eq[of x p]
        mult_less_cancel_left_pos[of p "x div p" "(int q + 1) div 2 - 1"] by linarith
    moreover have "0 < x div p + 1"
      using pos_imp_zdiv_neg_iff[of p x] p_ge_0 x mem_Collect_eq BuDuF_def by auto
    ultimately show "y \<in> (Res_h p) \<times> (Res_l q)" using x BuDuF_def f_3_def by auto
  qed
next
  have h1: "\<And>x. x \<in> ((Res_h p) \<times> (Res_l q)) \<Longrightarrow> f_3 (g_3 x) = x"
  proof -
    fix x
    assume a: "x \<in> ((Res_h p) \<times> (Res_l q))"
    moreover have h: "(fst x + (snd x - 1) * int p) mod int p = fst x" using a by force
    ultimately have "(fst x + (snd x - 1) * int p) div int p + 1 = snd x"
      by (auto simp: semiring_numeral_div_class.div_less)
    with h show "f_3 (g_3 x) = x" unfolding f_3_def g_3_def by simp
  qed
  show "inj_on g_3 ((Res_h p) \<times> (Res_l q))" apply (rule inj_onI[of "(Res_h p) \<times> (Res_l q)" g_3])
  proof -
    fix x y
    assume "x \<in> ((Res_h p) \<times> (Res_l q))" "y \<in> ((Res_h p) \<times> (Res_l q))" "g_3 x = g_3 y"
    thus "x = y" using h1[of x] h1[of y] by presburger
  qed
next
  show "g_3 ` ((Res_h p) \<times> (Res_l q)) \<subseteq> BuDuF"
  proof
    fix y
    assume "y \<in> g_3 ` ((Res_h p) \<times> (Res_l q))"
    then obtain x where x: "y = g_3 x" "x \<in> (Res_h p) \<times> (Res_l q)" by blast
    hence "snd x \<le> (int q - 1) div 2" by force
    moreover have "int p * ((int q - 1) div 2) = (int p * int q - int p) div 2"
      using int_distrib(4) zdiv_zmult1_eq[of "int p" "int q - 1" 2] odd_q by fastforce
    ultimately have "(snd x) * int p \<le> (int q * int p - int p) div 2"
      using mult_right_mono[of "snd x" "(int q - 1) div 2" p] mult.commute[of "(int q - 1) div 2" p]
        pq_commute by presburger
    hence "(snd x - 1) * int p \<le> (int q * int p - 1) div 2 - int p"
      using p_ge_0 int_distrib(3) by auto
    moreover have "fst x \<le> int p - 1" using x by force
    ultimately have "fst x + (snd x - 1) * int p \<le> (int p * int q - 1) div 2"
      using pq_commute by linarith
    moreover have "0 < fst x" "0 \<le> (snd x - 1) * p" using x(2) by fastforce+
    ultimately show "y \<in> BuDuF" unfolding BuDuF_def using q_ge_0 x g_3_def x(1) by auto
  qed
next
  show "finite BuDuF" unfolding BuDuF_def by fastforce
qed (simp add: inj_on_inverseI[of BuDuF g_3] f_3_def g_3_def QR_lemma_05)+

lemma QR_lemma_12: "b + d + m = r"
proof -
  have "B \<inter> D = {}" "finite B" "finite D" "B \<union> D = BuD" unfolding B_def D_def BuD_def by fastforce+
  hence "b + d = card BuD" unfolding b_def d_def using card_Un_Int by fastforce
  moreover have "BuD \<inter> F = {}" "finite BuD" "finite F" unfolding BuD_def F_def by fastforce+
  moreover have "BuD \<union> F = BuDuF" unfolding BuD_def F_def BuDuF_def
    using q_ge_0 ivl_disj_un_singleton(5)[of 0 "int q - 1"] by auto
  ultimately show ?thesis using QR_lemma_03 QR_lemma_05 QR_lemma_11 card_Un_disjoint[of BuD F]
    unfolding b_def d_def f_def by presburger
qed

lemma QR_lemma_13: "a + d + n = r"
proof -
  have "A = QR.B q p" unfolding A_def pq_commute using QRqp QR.B_def[of q p] by blast
  hence "a = QR.b q p" using a_def QRqp QR.b_def[of q p] by presburger
  moreover have "D = QR.D q p" unfolding D_def pq_commute using QRqp QR.D_def[of q p] by blast
    hence "d = QR.d q p" using d_def  QRqp QR.d_def[of q p] by presburger
  moreover have "n = QR.m q p" using n_def QRqp QR.m_def[of q p] by presburger
  moreover have "r = QR.r q p" unfolding r_def using QRqp QR.r_def[of q p] by auto
  ultimately show ?thesis using QRqp QR.QR_lemma_12 by presburger
qed

lemma QR_lemma_14: "(-1::int) ^ (m + n) = (-1) ^ r"
proof -
  have "m + n + 2 * d = r" using QR_lemma_06 QR_lemma_10 QR_lemma_12 QR_lemma_13 by auto
  thus ?thesis using power_add[of "-1::int" "m + n" "2 * d"] by fastforce
qed

lemma Quadratic_Reciprocity:
    "(Legendre p q) * (Legendre q p) = (-1::int) ^ ((p - 1) div 2 * ((q - 1) div 2))"
  using Gpq Gqp GAUSS.gauss_lemma power_add[of "-1::int" m n] QR_lemma_14
  unfolding r_def m_def n_def by auto

end

theorem Quadratic_Reciprocity: assumes "prime p" "2 < p" "prime q" "2 < q" "p \<noteq> q"
  shows "(Legendre p q) * (Legendre q p) = (-1::int) ^ ((p - 1) div 2 * ((q - 1) div 2))"
  using QR.Quadratic_Reciprocity QR_def assms by blast

theorem Quadratic_Reciprocity_int: assumes "prime (nat p)" "2 < p" "prime (nat q)" "2 < q" "p \<noteq> q"
  shows "(Legendre p q) * (Legendre q p) = (-1::int) ^ (nat ((p - 1) div 2 * ((q - 1) div 2)))"
proof -
  have "0 \<le> (p - 1) div 2" using assms by simp
  moreover have "(nat p - 1) div 2 = nat ((p - 1) div 2)" "(nat q - 1) div 2 = nat ((q - 1) div 2)"
    by fastforce+
  ultimately have "(nat p - 1) div 2 * ((nat q - 1) div 2) = nat ((p - 1) div 2 * ((q - 1) div 2))"
    using nat_mult_distrib by presburger
  moreover have "2 < nat p" "2 < nat q" "nat p \<noteq> nat q" "int (nat p) = p" "int (nat q) = q"
    using assms by linarith+
  ultimately show ?thesis using Quadratic_Reciprocity[of "nat p" "nat q"] assms by presburger
qed

end
