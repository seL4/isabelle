(*  Title:      HOL/Computational_Algebra/Fundamental_Theorem_Algebra.thy
    Author:     Amine Chaieb, TU Muenchen
*)

section \<open>Fundamental Theorem of Algebra\<close>

theory Fundamental_Theorem_Algebra
imports Polynomial Complex_Main
begin

subsection \<open>More lemmas about module of complex numbers\<close>

text \<open>The triangle inequality for cmod\<close>

lemma complex_mod_triangle_sub: "cmod w \<le> cmod (w + z) + norm z"
  using complex_mod_triangle_ineq2[of "w + z" "-z"] by auto


subsection \<open>Basic lemmas about polynomials\<close>

lemma poly_bound_exists:
  fixes p :: "'a::{comm_semiring_0,real_normed_div_algebra} poly"
  shows "\<exists>m. m > 0 \<and> (\<forall>z. norm z \<le> r \<longrightarrow> norm (poly p z) \<le> m)"
proof (induct p)
  case 0
  then show ?case by (rule exI[where x=1]) simp
next
  case (pCons c cs)
  from pCons.hyps obtain m where m: "\<forall>z. norm z \<le> r \<longrightarrow> norm (poly cs z) \<le> m"
    by blast
  let ?k = " 1 + norm c + \<bar>r * m\<bar>"
  have kp: "?k > 0"
    using abs_ge_zero[of "r*m"] norm_ge_zero[of c] by arith
  have "norm (poly (pCons c cs) z) \<le> ?k" if H: "norm z \<le> r" for z
  proof -
    from m H have th: "norm (poly cs z) \<le> m"
      by blast
    from H have rp: "r \<ge> 0"
      using norm_ge_zero[of z] by arith
    have "norm (poly (pCons c cs) z) \<le> norm c + norm (z * poly cs z)"
      using norm_triangle_ineq[of c "z* poly cs z"] by simp
    also have "\<dots> \<le> norm c + r * m"
      using mult_mono[OF H th rp norm_ge_zero[of "poly cs z"]]
      by (simp add: norm_mult)
    also have "\<dots> \<le> ?k"
      by simp
    finally show ?thesis .
  qed
  with kp show ?case by blast
qed


text \<open>Offsetting the variable in a polynomial gives another of same degree\<close>

definition offset_poly :: "'a::comm_semiring_0 poly \<Rightarrow> 'a \<Rightarrow> 'a poly"
  where "offset_poly p h = fold_coeffs (\<lambda>a q. smult h q + pCons a q) p 0"

lemma offset_poly_0: "offset_poly 0 h = 0"
  by (simp add: offset_poly_def)

lemma offset_poly_pCons:
  "offset_poly (pCons a p) h =
    smult h (offset_poly p h) + pCons a (offset_poly p h)"
  by (cases "p = 0 \<and> a = 0") (auto simp add: offset_poly_def)

lemma offset_poly_single [simp]: "offset_poly [:a:] h = [:a:]"
  by (simp add: offset_poly_pCons offset_poly_0)

lemma poly_offset_poly: "poly (offset_poly p h) x = poly p (h + x)"
  by (induct p) (auto simp add: offset_poly_0 offset_poly_pCons algebra_simps)

lemma offset_poly_eq_0_lemma: "smult c p + pCons a p = 0 \<Longrightarrow> p = 0"
  by (induct p arbitrary: a) (simp, force)

lemma offset_poly_eq_0_iff [simp]: "offset_poly p h = 0 \<longleftrightarrow> p = 0"
proof
  show "offset_poly p h = 0 \<Longrightarrow> p = 0"
  proof(induction p)
    case 0
    then show ?case by blast
  next
    case (pCons a p)
    then show ?case   
      by (metis offset_poly_eq_0_lemma offset_poly_pCons offset_poly_single)
  qed
qed (simp add: offset_poly_0)

lemma degree_offset_poly [simp]: "degree (offset_poly p h) = degree p"
proof(induction p)
  case 0
  then show ?case
    by (simp add: offset_poly_0)
next
  case (pCons a p)
  have "p \<noteq> 0 \<Longrightarrow> degree (offset_poly (pCons a p) h) = Suc (degree p)"
    by (metis degree_add_eq_right degree_pCons_eq degree_smult_le le_imp_less_Suc offset_poly_eq_0_iff offset_poly_pCons pCons.IH)
  then show ?case
    by simp
qed

definition "psize p = (if p = 0 then 0 else Suc (degree p))"

lemma psize_eq_0_iff [simp]: "psize p = 0 \<longleftrightarrow> p = 0"
  unfolding psize_def by simp

lemma poly_offset:
  fixes p :: "'a::comm_ring_1 poly"
  shows "\<exists>q. psize q = psize p \<and> (\<forall>x. poly q x = poly p (a + x))"
  by (metis degree_offset_poly offset_poly_eq_0_iff poly_offset_poly psize_def)

text \<open>An alternative useful formulation of completeness of the reals\<close>
lemma real_sup_exists:
  assumes ex: "\<exists>x. P x"
    and bz: "\<exists>z. \<forall>x. P x \<longrightarrow> x < z"
  shows "\<exists>s::real. \<forall>y. (\<exists>x. P x \<and> y < x) \<longleftrightarrow> y < s"
proof
  from bz have "bdd_above (Collect P)"
    by (force intro: less_imp_le)
  then show "\<forall>y. (\<exists>x. P x \<and> y < x) \<longleftrightarrow> y < Sup (Collect P)"
    using ex bz by (subst less_cSup_iff) auto
qed


subsection \<open>Fundamental theorem of algebra\<close>

lemma unimodular_reduce_norm:
  assumes md: "cmod z = 1"
  shows "cmod (z + 1) < 1 \<or> cmod (z - 1) < 1 \<or> cmod (z + \<i>) < 1 \<or> cmod (z - \<i>) < 1"
proof -
  obtain x y where z: "z = Complex x y "
    by (cases z) auto
  from md z have xy: "x\<^sup>2 + y\<^sup>2 = 1"
    by (simp add: cmod_def)
  have False if "cmod (z + 1) \<ge> 1" "cmod (z - 1) \<ge> 1" "cmod (z + \<i>) \<ge> 1" "cmod (z - \<i>) \<ge> 1"
  proof -
    from that z xy have "2 * x \<le> 1" "2 * x \<ge> -1" "2 * y \<le> 1" "2 * y \<ge> -1"
      by (simp_all add: cmod_def power2_eq_square algebra_simps)
    then have "\<bar>2 * x\<bar> \<le> 1" "\<bar>2 * y\<bar> \<le> 1"
      by simp_all
    then have "\<bar>2 * x\<bar>\<^sup>2 \<le> 1\<^sup>2" "\<bar>2 * y\<bar>\<^sup>2 \<le> 1\<^sup>2"
      by (metis abs_square_le_1 one_power2 power2_abs)+
    then have th0: "4 * x\<^sup>2 \<le> 1" "4 * y\<^sup>2 \<le> 1"
      by (simp_all add: power_mult_distrib)
    from add_mono[OF th0] xy show ?thesis
      by simp
  qed
  then show ?thesis
    unfolding linorder_not_le[symmetric] by blast
qed

text \<open>Hence we can always reduce modulus of \<open>1 + b z^n\<close> if nonzero\<close>
lemma reduce_poly_simple:
  assumes b: "b \<noteq> 0"
    and n: "n \<noteq> 0"
  shows "\<exists>z. cmod (1 + b * z^n) < 1"
  using n
proof (induct n rule: nat_less_induct)
  fix n
  assume IH: "\<forall>m<n. m \<noteq> 0 \<longrightarrow> (\<exists>z. cmod (1 + b * z ^ m) < 1)"
  assume n: "n \<noteq> 0"
  let ?P = "\<lambda>z n. cmod (1 + b * z ^ n) < 1"
  show "\<exists>z. ?P z n"
  proof cases
    assume "even n" 
    then obtain m where m: "n = 2 * m" and "m \<noteq> 0" "m < n"
      using n by auto
    with IH obtain z where z: "?P z m"
      by blast
    from z have "?P (csqrt z) n"
      by (simp add: m power_mult)
    then show ?thesis ..
  next
    assume "odd n"
    then have "\<exists>m. n = Suc (2 * m)"
      by presburger+
    then obtain m where m: "n = Suc (2 * m)"
      by blast
    have th0: "cmod (complex_of_real (cmod b) / b) = 1"
      using b by (simp add: norm_divide)
    have "\<exists>v. cmod (complex_of_real (cmod b) / b + v^n) < 1"
    proof (cases "cmod (complex_of_real (cmod b) / b + 1) < 1")
      case True
      then show ?thesis
        by (metis power_one)
    next
      case False
      note F1 = False
      show ?thesis
      proof (cases "cmod (complex_of_real (cmod b) / b - 1) < 1")
        case True
        with \<open>odd n\<close> show ?thesis
          by (metis add_uminus_conv_diff neg_one_odd_power)
      next
        case False
        note F2 = False
        show ?thesis
        proof (cases "cmod (complex_of_real (cmod b) / b + \<i>) < 1")
          case True
          note T1 = True
          show ?thesis
          proof (cases "even m")
            case True
            with T1 show ?thesis
              by (rule_tac x="\<i>" in exI) (simp add: m power_mult)
          next
            case False
            with T1 show ?thesis 
              by (rule_tac x="- \<i>" in exI) (simp add: m power_mult)
          qed
        next
          case False
          with F1 F2 m unimodular_reduce_norm[OF th0] \<open>odd n\<close> show ?thesis
            apply (cases "even m")
             apply (rule_tac x="- \<i>" in exI)
             apply (simp add:  power_mult)
            apply (rule_tac x="\<i>" in exI)
            apply (auto simp add: m power_mult)
            done
        qed
      qed
    qed
    then obtain v where v: "cmod (complex_of_real (cmod b) / b + v^n) < 1"
      by blast
    let ?w = "v / complex_of_real (root n (cmod b))"
    from odd_real_root_pow[OF \<open>odd n\<close>, of "cmod b"]
    have th1: "?w ^ n = v^n / complex_of_real (cmod b)"
      by (simp add: power_divide of_real_power[symmetric])
    have th2:"cmod (complex_of_real (cmod b) / b) = 1"
      using b by (simp add: norm_divide)
    then have th3: "cmod (complex_of_real (cmod b) / b) \<ge> 0"
      by simp
    have th4: "cmod (complex_of_real (cmod b) / b) *
        cmod (1 + b * (v ^ n / complex_of_real (cmod b))) <
        cmod (complex_of_real (cmod b) / b) * 1"
      apply (simp only: norm_mult[symmetric] distrib_left)
      using b v
      apply (simp add: th2)
      done
    show ?thesis
      by (metis th1 mult_left_less_imp_less[OF th4 th3])
  qed
qed

text \<open>Bolzano-Weierstrass type property for closed disc in complex plane.\<close>

lemma metric_bound_lemma: "cmod (x - y) \<le> \<bar>Re x - Re y\<bar> + \<bar>Im x - Im y\<bar>"
  using real_sqrt_sum_squares_triangle_ineq[of "Re x - Re y" 0 0 "Im x - Im y"]
  unfolding cmod_def by simp

lemma Bolzano_Weierstrass_complex_disc:
  assumes r: "\<forall>n. cmod (s n) \<le> r"
  shows "\<exists>f z. strict_mono (f :: nat \<Rightarrow> nat) \<and> (\<forall>e >0. \<exists>N. \<forall>n \<ge> N. cmod (s (f n) - z) < e)"
proof -
  from seq_monosub[of "Re \<circ> s"]
  obtain f where f: "strict_mono f" "monoseq (\<lambda>n. Re (s (f n)))"
    unfolding o_def by blast
  from seq_monosub[of "Im \<circ> s \<circ> f"]
  obtain g where g: "strict_mono g" "monoseq (\<lambda>n. Im (s (f (g n))))"
    unfolding o_def by blast
  let ?h = "f \<circ> g"
  from r[rule_format, of 0] have rp: "r \<ge> 0"
    using norm_ge_zero[of "s 0"] by arith
  have th: "\<forall>n. r + 1 \<ge> \<bar>Re (s n)\<bar>"
    by (smt (verit, ccfv_threshold) abs_Re_le_cmod r)
  have conv1: "convergent (\<lambda>n. Re (s (f n)))"
    by (metis Bseq_monoseq_convergent f(2) BseqI' real_norm_def th)
  have th: "\<forall>n. r + 1 \<ge> \<bar>Im (s n)\<bar>"
    by (smt (verit) abs_Im_le_cmod r)

  have conv2: "convergent (\<lambda>n. Im (s (f (g n))))"
    by (metis Bseq_monoseq_convergent g(2) BseqI' real_norm_def th)

  from conv1[unfolded convergent_def] obtain x where "LIMSEQ (\<lambda>n. Re (s (f n))) x"
    by blast
  then have x: "\<forall>r>0. \<exists>n0. \<forall>n\<ge>n0. \<bar>Re (s (f n)) - x\<bar> < r"
    unfolding LIMSEQ_iff real_norm_def .

  from conv2[unfolded convergent_def] 
  obtain y where  y: "\<forall>r>0. \<exists>n0. \<forall>n\<ge>n0. \<bar>Im (s (f (g n))) - y\<bar> < r"
    unfolding LIMSEQ_iff real_norm_def by blast
  let ?w = "Complex x y"
  from f(1) g(1) have hs: "strict_mono ?h"
    unfolding strict_mono_def by auto
  have "\<exists>N. \<forall>n\<ge>N. cmod (s (?h n) - ?w) < e" if "e > 0" for e
  proof -
    from that have e2: "e/2 > 0"
      by simp
    from x y e2
    obtain N1 N2 where N1: "\<forall>n\<ge>N1. \<bar>Re (s (f n)) - x\<bar> < e / 2"
      and N2: "\<forall>n\<ge>N2. \<bar>Im (s (f (g n))) - y\<bar> < e / 2"
      by blast
    have "cmod (s (?h n) - ?w) < e" if "n \<ge> N1 + N2" for n
    proof -
      from that have nN1: "g n \<ge> N1" and nN2: "n \<ge> N2"
        using seq_suble[OF g(1), of n] by arith+
      show ?thesis
        using metric_bound_lemma[of "s (f (g n))" ?w] N1 N2 nN1 nN2 by fastforce
    qed
    then show ?thesis by blast
  qed
  with hs show ?thesis by blast
qed

text \<open>Polynomial is continuous.\<close>

lemma poly_cont:
  fixes p :: "'a::{comm_semiring_0,real_normed_div_algebra} poly"
  assumes ep: "e > 0"
  shows "\<exists>d >0. \<forall>w. 0 < norm (w - z) \<and> norm (w - z) < d \<longrightarrow> norm (poly p w - poly p z) < e"
proof -
  obtain q where q: "degree q = degree p" "poly q x = poly p (z + x)" for x
    using degree_offset_poly poly_offset_poly by blast
  have th: "\<And>w. poly q (w - z) = poly p w"
    using q(2)[of "w - z" for w] by simp
  show ?thesis unfolding th[symmetric]
  proof (induct q)
    case 0
    then show ?case
      using ep by auto
  next
    case (pCons c cs)
    from poly_bound_exists[of 1 "cs"]
    obtain m where m: "m > 0" "norm z \<le> 1 \<Longrightarrow> norm (poly cs z) \<le> m" for z
      by blast
    from ep m(1) have em0: "e/m > 0"
      by (simp add: field_simps)
    have one0: "1 > (0::real)"
      by arith
    from field_lbound_gt_zero[OF one0 em0]
    obtain d where d: "d > 0" "d < 1" "d < e / m"
      by blast
    from d(1,3) m(1) have dm: "d * m > 0" "d * m < e"
      by (simp_all add: field_simps)
    show ?case
    proof (rule ex_forward[OF field_lbound_gt_zero[OF one0 em0]], clarsimp simp add: norm_mult)
      fix d w
      assume H: "d > 0" "d < 1" "d < e/m" "w \<noteq> z" "norm (w - z) < d"
      then have d1: "norm (w-z) \<le> 1" "d \<ge> 0"
        by simp_all
      from H(3) m(1) have dme: "d*m < e"
        by (simp add: field_simps)
      from H have th: "norm (w - z) \<le> d"
        by simp
      show "norm (w - z) * norm (poly cs (w - z)) < e"
        by (smt (verit, del_insts) d1(1) dme m(2) mult_mono' norm_ge_zero th)
    qed
  qed
qed

text \<open>Hence a polynomial attains minimum on a closed disc
  in the complex plane.\<close>
lemma poly_minimum_modulus_disc: "\<exists>z. \<forall>w. cmod w \<le> r \<longrightarrow> cmod (poly p z) \<le> cmod (poly p w)"
proof -
  show ?thesis
  proof (cases "r \<ge> 0")
    case False
    then show ?thesis
      by (metis norm_ge_zero order.trans)
  next
    case True
    then have "cmod 0 \<le> r \<and> cmod (poly p 0) = - (- cmod (poly p 0))"
      by simp
    then have mth1: "\<exists>x z. cmod z \<le> r \<and> cmod (poly p z) = - x"
      by blast
    have False if "cmod (poly p z) = - x" "\<not> x < 1" for x z
      by (smt (verit, del_insts) norm_ge_zero that)
    then have mth2: "\<exists>z. \<forall>x. (\<exists>z. cmod z \<le> r \<and> cmod (poly p z) = - x) \<longrightarrow> x < z"
      by blast
    from real_sup_exists[OF mth1 mth2] obtain s where
      s: "\<forall>y. (\<exists>x. (\<exists>z. cmod z \<le> r \<and> cmod (poly p z) = - x) \<and> y < x) \<longleftrightarrow> y < s"
      by blast
    let ?m = "- s"
    have s1[unfolded minus_minus]:
      "(\<exists>z x. cmod z \<le> r \<and> - (- cmod (poly p z)) < y) \<longleftrightarrow> ?m < y" for y
      by (metis add.inverse_inverse minus_less_iff s)
    from s1[of ?m] have s1m: "\<And>z x. cmod z \<le> r \<Longrightarrow> cmod (poly p z) \<ge> ?m"
      by auto
    have "\<exists>z. cmod z \<le> r \<and> cmod (poly p z) < - s + 1 / real (Suc n)" for n
      using s1[rule_format, of "?m + 1/real (Suc n)"] by simp
    then have th: "\<forall>n. \<exists>z. cmod z \<le> r \<and> cmod (poly p z) < - s + 1 / real (Suc n)" ..
    from choice[OF th] obtain g where
        g: "\<forall>n. cmod (g n) \<le> r" "\<forall>n. cmod (poly p (g n)) <?m + 1 /real(Suc n)"
      by blast
    from Bolzano_Weierstrass_complex_disc[OF g(1)]
    obtain f z where fz: "strict_mono (f :: nat \<Rightarrow> nat)" "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. cmod (g (f n) - z) < e"
      by blast
    {
      fix w
      assume wr: "cmod w \<le> r"
      let ?e = "\<bar>cmod (poly p z) - ?m\<bar>"
      {
        assume e: "?e > 0"
        then have e2: "?e/2 > 0"
          by simp
        from poly_cont[OF e2, of z p] obtain d where
            d: "d > 0" "\<forall>w. 0<cmod (w - z)\<and> cmod(w - z) < d \<longrightarrow> cmod(poly p w - poly p z) < ?e/2"
          by blast
        have th1: "cmod(poly p w - poly p z) < ?e / 2" if w: "cmod (w - z) < d" for w
          using d(2)[rule_format, of w] w e by (cases "w = z") simp_all
        from fz(2) d(1) obtain N1 where N1: "\<forall>n\<ge>N1. cmod (g (f n) - z) < d"
          by blast
        from reals_Archimedean2[of "2/?e"] obtain N2 :: nat where N2: "2/?e < real N2"
          by blast
        have th2: "cmod (poly p (g (f (N1 + N2))) - poly p z) < ?e/2"
          using N1[rule_format, of "N1 + N2"] th1 by simp
        have th0: "a < e2 \<Longrightarrow> \<bar>b - m\<bar> < e2 \<Longrightarrow> 2 * e2 \<le> \<bar>b - m\<bar> + a \<Longrightarrow> False"
          for a b e2 m :: real
          by arith
        have ath: "m \<le> x \<Longrightarrow> x < m + e \<Longrightarrow> \<bar>x - m\<bar> < e" for m x e :: real
          by arith
        from seq_suble[OF fz(1), of "N1 + N2"]
        have th00: "real (Suc (N1 + N2)) \<le> real (Suc (f (N1 + N2)))"
          by simp
        have th000: "0 \<le> (1::real)" "(1::real) \<le> 1" "real (Suc (N1 + N2)) > 0"
          using N2 by auto
        from frac_le[OF th000 th00]
        have th00: "?m + 1 / real (Suc (f (N1 + N2))) \<le> ?m + 1 / real (Suc (N1 + N2))"
          by simp
        from g(2)[rule_format, of "f (N1 + N2)"]
        have th01:"cmod (poly p (g (f (N1 + N2)))) < - s + 1 / real (Suc (f (N1 + N2)))" .
        from N2 have "2/?e < real (Suc (N1 + N2))"
          by arith
        with e2 less_imp_inverse_less[of "2/?e" "real (Suc (N1 + N2))"]
        have "?e/2 > 1/ real (Suc (N1 + N2))"
          by (simp add: inverse_eq_divide)
        with ath[OF _  order_less_le_trans[OF th01 th00]] 
        have thc1: "\<bar>cmod (poly p (g (f (N1 + N2)))) - ?m\<bar> < ?e/2"
          by (simp add: g(1) s1m)
        have thc2: "2 * (?e/2) \<le>
            \<bar>cmod(poly p (g (f (N1 + N2)))) - ?m\<bar> + cmod (poly p (g (f (N1 + N2))) - poly p z)"
          by (smt (verit) field_sum_of_halves norm_triangle_ineq3)
        from th0[OF th2 thc1 thc2] have False .
      }
      then have "?e = 0"
        by auto
      with s1m[OF wr] have "cmod (poly p z) \<le> cmod (poly p w)"
        by simp
    }
    then show ?thesis by blast
  qed
qed

text \<open>Nonzero polynomial in z goes to infinity as z does.\<close>

lemma poly_infinity:
  fixes p:: "'a::{comm_semiring_0,real_normed_div_algebra} poly"
  assumes ex: "p \<noteq> 0"
  shows "\<exists>r. \<forall>z. r \<le> norm z \<longrightarrow> d \<le> norm (poly (pCons a p) z)"
  using ex
proof (induct p arbitrary: a d)
  case 0
  then show ?case by simp
next
  case (pCons c cs a d)
  show ?case
  proof (cases "cs = 0")
    case False
    with pCons.hyps obtain r where r: "\<forall>z. r \<le> norm z \<longrightarrow> d + norm a \<le> norm (poly (pCons c cs) z)"
      by blast
    let ?r = "1 + \<bar>r\<bar>"
    have "d \<le> norm (poly (pCons a (pCons c cs)) z)" if "1 + \<bar>r\<bar> \<le> norm z" for z
    proof -
      have r0: "r \<le> norm z"
        using that by arith
      from r[rule_format, OF r0] have th0: "d + norm a \<le> 1 * norm(poly (pCons c cs) z)"
        by arith
      from that have z1: "norm z \<ge> 1"
        by arith
      from order_trans[OF th0 mult_right_mono[OF z1 norm_ge_zero[of "poly (pCons c cs) z"]]]
      have "d \<le> norm(z * poly (pCons c cs) z) - norm a"
        unfolding norm_mult by (simp add: algebra_simps)
      with norm_diff_ineq[of "z * poly (pCons c cs) z" a]
      show ?thesis 
        by (simp add: algebra_simps)
    qed
    then show ?thesis by blast
  next
    case True
    with pCons.prems have c0: "c \<noteq> 0"
      by simp
    have "d \<le> norm (poly (pCons a (pCons c cs)) z)"
      if h: "(\<bar>d\<bar> + norm a) / norm c \<le> norm z" for z :: 'a
    proof -
      from c0 have "norm c > 0"
        by simp
      from h c0 have th0: "\<bar>d\<bar> + norm a \<le> norm (z * c)"
        by (simp add: field_simps norm_mult)
      have ath: "\<And>mzh mazh ma. mzh \<le> mazh + ma \<Longrightarrow> \<bar>d\<bar> + ma \<le> mzh \<Longrightarrow> d \<le> mazh"
        by arith
      from norm_diff_ineq[of "z * c" a] have th1: "norm (z * c) \<le> norm (a + z * c) + norm a"
        by (simp add: algebra_simps)
      from ath[OF th1 th0] show ?thesis
        using True by simp
    qed
    then show ?thesis by blast
  qed
qed

text \<open>Hence polynomial's modulus attains its minimum somewhere.\<close>
lemma poly_minimum_modulus: "\<exists>z.\<forall>w. cmod (poly p z) \<le> cmod (poly p w)"
proof (induct p)
  case 0
  then show ?case by simp
next
  case (pCons c cs)
  show ?case
  proof (cases "cs = 0")
    case False
    from poly_infinity[OF False, of "cmod (poly (pCons c cs) 0)" c]
    obtain r where r: "cmod (poly (pCons c cs) 0) \<le> cmod (poly (pCons c cs) z)"
      if "r \<le> cmod z" for z
      by blast
    have ath: "\<And>z r. r \<le> cmod z \<or> cmod z \<le> \<bar>r\<bar>"
      by arith
    from poly_minimum_modulus_disc[of "\<bar>r\<bar>" "pCons c cs"] show ?thesis
      by (metis ath dual_order.trans norm_ge_zero norm_zero r)
  qed (use pCons.hyps in auto)
qed

text \<open>Constant function (non-syntactic characterization).\<close>
definition "constant f \<longleftrightarrow> (\<forall>x y. f x = f y)"

lemma nonconstant_length: "\<not> constant (poly p) \<Longrightarrow> psize p \<ge> 2"
  by (induct p) (auto simp: constant_def psize_def)

lemma poly_replicate_append: "poly (monom 1 n * p) (x::'a::comm_ring_1) = x^n * poly p x"
  by (simp add: poly_monom)

text \<open>Decomposition of polynomial, skipping zero coefficients after the first.\<close>

lemma poly_decompose_lemma:
  assumes nz: "\<not> (\<forall>z. z \<noteq> 0 \<longrightarrow> poly p z = (0::'a::idom))"
  shows "\<exists>k a q. a \<noteq> 0 \<and> Suc (psize q + k) = psize p \<and> (\<forall>z. poly p z = z^k * poly (pCons a q) z)"
  unfolding psize_def
  using nz
proof (induct p)
  case 0
  then show ?case by simp
next
  case (pCons c cs)
  show ?case
  proof (cases "c = 0")
    case True
    from pCons.hyps pCons.prems True show ?thesis
      apply auto
      apply (rule_tac x="k+1" in exI)
      apply (rule_tac x="a" in exI)
      apply clarsimp
      apply (rule_tac x="q" in exI)
      apply auto
      done
  next
    case False
    show ?thesis
      using False by force
  qed
qed

lemma poly_decompose:
  assumes nc: "\<not> constant (poly p)"
  shows "\<exists>k a q. a \<noteq> (0::'a::idom) \<and> k \<noteq> 0 \<and>
               psize q + k + 1 = psize p \<and>
              (\<forall>z. poly p z = poly p 0 + z^k * poly (pCons a q) z)"
  using nc
proof (induct p)
  case 0
  then show ?case
    by (simp add: constant_def)
next
  case (pCons c cs)
  have "\<not> (\<forall>z. z \<noteq> 0 \<longrightarrow> poly cs z = 0)"
    by (smt (verit) constant_def mult_eq_0_iff pCons.prems poly_pCons)
  from poly_decompose_lemma[OF this]
  show ?case
    apply clarsimp
    apply (rule_tac x="k+1" in exI)
    apply (rule_tac x="a" in exI)
    apply simp
    apply (rule_tac x="q" in exI)
    apply (auto simp add: psize_def split: if_splits)
    done
qed

text \<open>Fundamental theorem of algebra\<close>

lemma fundamental_theorem_of_algebra:
  assumes nc: "\<not> constant (poly p)"
  shows "\<exists>z::complex. poly p z = 0"
  using nc
proof (induct "psize p" arbitrary: p rule: less_induct)
  case less
  let ?p = "poly p"
  let ?ths = "\<exists>z. ?p z = 0"

  from nonconstant_length[OF less(2)] have n2: "psize p \<ge> 2" .
  from poly_minimum_modulus obtain c where c: "\<forall>w. cmod (?p c) \<le> cmod (?p w)"
    by blast

  show ?ths
  proof (cases "?p c = 0")
    case True
    then show ?thesis by blast
  next
    case False
    from poly_offset[of p c] obtain q where q: "psize q = psize p" "\<forall>x. poly q x = ?p (c + x)"
      by blast
    have False if h: "constant (poly q)"
    proof -
      from q(2) have th: "\<forall>x. poly q (x - c) = ?p x"
        by auto
      have "?p x = ?p y" for x y
      proof -
        from th have "?p x = poly q (x - c)"
          by auto
        also have "\<dots> = poly q (y - c)"
          using h unfolding constant_def by blast
        also have "\<dots> = ?p y"
          using th by auto
        finally show ?thesis .
      qed
      with less(2) show ?thesis
        unfolding constant_def by blast
    qed
    then have qnc: "\<not> constant (poly q)"
      by blast
    from q(2) have pqc0: "?p c = poly q 0"
      by simp
    from c pqc0 have cq0: "\<forall>w. cmod (poly q 0) \<le> cmod (?p w)"
      by simp
    let ?a0 = "poly q 0"
    from False pqc0 have a00: "?a0 \<noteq> 0"
      by simp
    from a00 have qr: "\<forall>z. poly q z = poly (smult (inverse ?a0) q) z * ?a0"
      by simp
    let ?r = "smult (inverse ?a0) q"
    have lgqr: "psize q = psize ?r"
      by (simp add: a00 psize_def)
    have False if h: "\<And>x y. poly ?r x = poly ?r y"
      using constant_def qnc qr that by fastforce
    then have rnc: "\<not> constant (poly ?r)"
      unfolding constant_def by blast
    from qr[rule_format, of 0] a00 have r01: "poly ?r 0 = 1"
      by auto
    have mrmq_eq: "cmod (poly ?r w) < 1 \<longleftrightarrow> cmod (poly q w) < cmod ?a0" for w
      by (smt (verit, del_insts) a00 mult_less_cancel_right2 norm_mult qr zero_less_norm_iff)
    from poly_decompose[OF rnc] obtain k a s where
      kas: "a \<noteq> 0" "k \<noteq> 0" "psize s + k + 1 = psize ?r"
        "\<forall>z. poly ?r z = poly ?r 0 + z^k* poly (pCons a s) z" by blast
    have "\<exists>w. cmod (poly ?r w) < 1"
    proof (cases "psize p = k + 1")
      case True
      with kas(3) lgqr[symmetric] q(1) have s0: "s = 0"
        by auto
      have hth[symmetric]: "cmod (poly ?r w) = cmod (1 + a * w ^ k)" for w
        using kas(4)[rule_format, of w] s0 r01 by (simp add: algebra_simps)
      from reduce_poly_simple[OF kas(1,2)] show ?thesis
        unfolding hth by blast
    next
      case False note kn = this
      from kn kas(3) q(1) lgqr have k1n: "k + 1 < psize p"
        by simp
      have th01: "\<not> constant (poly (pCons 1 (monom a (k - 1))))"
        unfolding constant_def poly_pCons poly_monom
        by (metis add_cancel_left_right kas(1) mult.commute mult_cancel_right2 power_one)
      from kas(1) kas(2) have th02: "k + 1 = psize (pCons 1 (monom a (k - 1)))"
        by (simp add: psize_def degree_monom_eq)
      from less(1) [OF k1n [simplified th02] th01]
      obtain w where w: "1 + w^k * a = 0"
        unfolding poly_pCons poly_monom
        using kas(2) by (cases k) (auto simp add: algebra_simps)
      from poly_bound_exists[of "cmod w" s] obtain m where
        m: "m > 0" "\<forall>z. cmod z \<le> cmod w \<longrightarrow> cmod (poly s z) \<le> m" by blast
      have w0: "w \<noteq> 0"
        using kas(2) w by (auto simp add: power_0_left)
      from w have "(1 + w ^ k * a) - 1 = 0 - 1"
        by simp
      then have wm1: "w^k * a = - 1"
        by simp
      have inv0: "0 < inverse (cmod w ^ (k + 1) * m)"
        using norm_ge_zero[of w] w0 m(1)
        by (simp add: inverse_eq_divide zero_less_mult_iff)
      with field_lbound_gt_zero[OF zero_less_one] obtain t where
        t: "t > 0" "t < 1" "t < inverse (cmod w ^ (k + 1) * m)" by blast
      let ?ct = "complex_of_real t"
      let ?w = "?ct * w"
      have "1 + ?w^k * (a + ?w * poly s ?w) = 1 + ?ct^k * (w^k * a) + ?w^k * ?w * poly s ?w"
        using kas(1) by (simp add: algebra_simps power_mult_distrib)
      also have "\<dots> = complex_of_real (1 - t^k) + ?w^k * ?w * poly s ?w"
        unfolding wm1 by simp
      finally have "cmod (1 + ?w^k * (a + ?w * poly s ?w)) =
        cmod (complex_of_real (1 - t^k) + ?w^k * ?w * poly s ?w)"
        by metis
      with norm_triangle_ineq[of "complex_of_real (1 - t^k)" "?w^k * ?w * poly s ?w"]
      have th11: "cmod (1 + ?w^k * (a + ?w * poly s ?w)) \<le> \<bar>1 - t^k\<bar> + cmod (?w^k * ?w * poly s ?w)"
        unfolding norm_of_real by simp
      have ath: "\<And>x t::real. 0 \<le> x \<Longrightarrow> x < t \<Longrightarrow> t \<le> 1 \<Longrightarrow> \<bar>1 - t\<bar> + x < 1"
        by arith
      have "t * cmod w \<le> 1 * cmod w"
        using t(2) w0 by auto
      then have tw: "cmod ?w \<le> cmod w"
        using t(1) by (simp add: norm_mult)
      from t inv0 have "t * (cmod w ^ (k + 1) * m) < 1"
        by (simp add: field_simps)
      with zero_less_power[OF t(1), of k] have th30: "t^k * (t* (cmod w ^ (k + 1) * m)) < t^k * 1"
        by simp
      have "cmod (?w^k * ?w * poly s ?w) = t^k * (t* (cmod w ^ (k + 1) * cmod (poly s ?w)))"
        using w0 t(1)
        by (simp add: algebra_simps norm_power norm_mult)
      then have "cmod (?w^k * ?w * poly s ?w) \<le> t^k * (t* (cmod w ^ (k + 1) * m))"
        using t(1,2) m(2)[rule_format, OF tw] w0
        by auto
      with th30 have th120: "cmod (?w^k * ?w * poly s ?w) < t^k"
        by simp
      from power_strict_mono[OF t(2), of k] t(1) kas(2) have th121: "t^k \<le> 1"
        by auto
      from ath[OF norm_ge_zero[of "?w^k * ?w * poly s ?w"] th120 th121]
      have th12: "\<bar>1 - t^k\<bar> + cmod (?w^k * ?w * poly s ?w) < 1" .
      from th11 th12 have "cmod (1 + ?w^k * (a + ?w * poly s ?w)) < 1"
        by arith
      then show ?thesis
        by (metis kas(4) poly_pCons r01)
    qed
    with cq0 q(2) show ?thesis
      unfolding mrmq_eq not_less[symmetric] by auto
  qed
qed

text \<open>Alternative version with a syntactic notion of constant polynomial.\<close>

lemma fundamental_theorem_of_algebra_alt:
  assumes nc: "\<not> (\<exists>a l. a \<noteq> 0 \<and> l = 0 \<and> p = pCons a l)"
  shows "\<exists>z. poly p z = (0::complex)"
  using nc
proof (induct p)
  case 0
  then show ?case by simp
next
  case (pCons c cs)
  show ?case
  proof (cases "c = 0")
    case True
    then show ?thesis by auto
  next
    case False
    have "\<not> constant (poly (pCons c cs))"
    proof
      assume nc: "constant (poly (pCons c cs))"
      from nc[unfolded constant_def, rule_format, of 0]
      have "\<forall>w. w \<noteq> 0 \<longrightarrow> poly cs w = 0" by auto
      then have "cs = 0"
      proof (induct cs)
        case 0
        then show ?case by simp
      next
        case (pCons d ds)
        show ?case
        proof (cases "d = 0")
          case True
          then show ?thesis
            using pCons.prems pCons.hyps by simp
        next
          case False
          from poly_bound_exists[of 1 ds] obtain m where
            m: "m > 0" "\<forall>z. \<forall>z. cmod z \<le> 1 \<longrightarrow> cmod (poly ds z) \<le> m" by blast
          have dm: "cmod d / m > 0"
            using False m(1) by (simp add: field_simps)
          from field_lbound_gt_zero[OF dm zero_less_one]
          obtain x where x: "x > 0" "x < cmod d / m" "x < 1"
            by blast
          let ?x = "complex_of_real x"
          from x have cx: "?x \<noteq> 0" "cmod ?x \<le> 1"
            by simp_all
          from pCons.prems[rule_format, OF cx(1)]
          have cth: "cmod (?x*poly ds ?x) = cmod d"
            by (simp add: eq_diff_eq[symmetric])
          have th0: "cmod (?x*poly ds ?x) \<le> x*m"
            by (smt (verit) cx(2) m(2) mult_left_mono norm_mult norm_of_real x(1))
          from x(2) m(1) have "x * m < cmod d"
            by (simp add: field_simps)
          with th0 cth show ?thesis
            by force
        qed
      qed
      then show False
        using pCons.prems False by blast
    qed
    then show ?thesis
      by (rule fundamental_theorem_of_algebra)
  qed
qed


subsection \<open>Nullstellensatz, degrees and divisibility of polynomials\<close>

lemma nullstellensatz_lemma:
  fixes p :: "complex poly"
  assumes "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0"
    and "degree p = n"
    and "n \<noteq> 0"
  shows "p dvd (q ^ n)"
  using assms
proof (induct n arbitrary: p q rule: nat_less_induct)
  fix n :: nat
  fix p q :: "complex poly"
  assume IH: "\<forall>m<n. \<forall>p q.
                 (\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longrightarrow>
                 degree p = m \<longrightarrow> m \<noteq> 0 \<longrightarrow> p dvd (q ^ m)"
    and pq0: "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0"
    and dpn: "degree p = n"
    and n0: "n \<noteq> 0"
  from dpn n0 have pne: "p \<noteq> 0" by auto
  show "p dvd (q ^ n)"
  proof (cases "\<exists>a. poly p a = 0")
    case True
    then obtain a where a: "poly p a = 0" ..
    have ?thesis if oa: "order a p \<noteq> 0"
    proof -
      let ?op = "order a p"
      from pne have ap: "([:- a, 1:] ^ ?op) dvd p" "\<not> [:- a, 1:] ^ (Suc ?op) dvd p"
        using order by blast+
      note oop = order_degree[OF pne, unfolded dpn]
      show ?thesis
      proof (cases "q = 0")
        case True
        with n0 show ?thesis by (simp add: power_0_left)
      next
        case False
        from pq0[rule_format, OF a, unfolded poly_eq_0_iff_dvd]
        obtain r where r: "q = [:- a, 1:] * r" by (rule dvdE)
        from ap(1) obtain s where s: "p = [:- a, 1:] ^ ?op * s"
          by (rule dvdE)
        have sne: "s \<noteq> 0"
          using s pne by auto
        show ?thesis
        proof (cases "degree s = 0")
          case True
          then obtain k where kpn: "s = [:k:]"
            by (cases s) (auto split: if_splits)
          from sne kpn have k: "k \<noteq> 0" by simp
          let ?w = "([:1/k:] * ([:-a,1:] ^ (n - ?op))) * (r ^ n)"
          have "q ^ n = p * ?w"
            apply (subst r)
            apply (subst s)
            apply (subst kpn)
            using k oop [of a]
            apply (subst power_mult_distrib)
            apply simp
            apply (subst power_add [symmetric])
            apply simp
            done
          then show ?thesis
            unfolding dvd_def by blast
        next
          case False
          with sne dpn s oa have dsn: "degree s < n"
            by (metis degree_div_less degree_linear_power mult_eq_0_iff n0 nonzero_mult_div_cancel_left not_gr0 pne)
          have "poly r x = 0" if h: "poly s x = 0" for x
          proof -
            have xa: "x \<noteq> a"
            proof
              assume "x = a"
              from h[unfolded this poly_eq_0_iff_dvd] obtain u where u: "s = [:- a, 1:] * u"
                by (rule dvdE)
              have "p = [:- a, 1:] ^ (Suc ?op) * u"
                by (metis (no_types, lifting) mult.assoc power_Suc power_commutes s u)
              with ap(2)[unfolded dvd_def] show False
                by blast
            qed
            from h have "poly p x = 0"
              by (subst s) simp
            with pq0 have "poly q x = 0"
              by blast
            with r xa show ?thesis
              by auto
          qed
          with IH[rule_format, OF dsn, of s r] False have "s dvd (r ^ (degree s))"
            by blast
          then obtain u where u: "r ^ (degree s) = s * u" ..
          then have u': "\<And>x. poly s x * poly u x = poly r x ^ degree s"
            by (simp only: poly_mult[symmetric] poly_power[symmetric])
          let ?w = "(u * ([:-a,1:] ^ (n - ?op))) * (r ^ (n - degree s))"
          from oop[of a] dsn have "q ^ n = p * ?w"
            apply -
            apply (subst s)
            apply (subst r)
            apply (simp only: power_mult_distrib)
            apply (subst mult.assoc [where b=s])
            apply (subst mult.assoc [where a=u])
            apply (subst mult.assoc [where b=u, symmetric])
            apply (subst u [symmetric])
            apply (simp add: ac_simps power_add [symmetric])
            done
          then show ?thesis
            unfolding dvd_def by blast
        qed
      qed
    qed
    then show ?thesis
      using a order_root pne by blast
  next
    case False
    then show ?thesis
      using dpn n0 fundamental_theorem_of_algebra_alt[of p]
      by fastforce
  qed
qed

lemma nullstellensatz_univariate:
  "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow>
    p dvd (q ^ (degree p)) \<or> (p = 0 \<and> q = 0)"
proof -
  consider "p = 0" | "p \<noteq> 0" "degree p = 0" | n where "p \<noteq> 0" "degree p = Suc n"
    by (cases "degree p") auto
  then show ?thesis
  proof cases
    case p: 1
    then have eq: "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow> q = 0"
      by (auto simp add: poly_all_0_iff_0)
    {
      assume "p dvd (q ^ (degree p))"
      then obtain r where r: "q ^ (degree p) = p * r" ..
      from r p have False by simp
    }
    with eq p show ?thesis by blast
  next
    case dp: 2
    then obtain k where k: "p = [:k:]" "k \<noteq> 0"
      by (cases p) (simp split: if_splits)
    then show ?thesis
      by (simp add: is_unit_pCons_iff)
  next
    case dp: 3
    have False if "p dvd (q ^ (Suc n))" "poly p x = 0" "poly q x \<noteq> 0" for x
      by (metis dvd_trans poly_eq_0_iff_dvd poly_power power_eq_0_iff that)
    with dp nullstellensatz_lemma[of p q "degree p"] show ?thesis
      by auto
  qed
qed

text \<open>Useful lemma\<close>
lemma constant_degree:
  fixes p :: "'a::{idom,ring_char_0} poly"
  shows "constant (poly p) \<longleftrightarrow> degree p = 0" (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    from that[unfolded constant_def, rule_format, of _ "0"]
    have "poly p = poly [:poly p 0:]"
      by auto
    then show ?thesis
      by (metis degree_pCons_0 poly_eq_poly_eq_iff)
  qed
  show ?lhs if ?rhs
  proof -
    from that obtain k where "p = [:k:]"
      by (cases p) (simp split: if_splits)
    then show ?thesis
      unfolding constant_def by auto
  qed
qed

text \<open>Arithmetic operations on multivariate polynomials.\<close>

lemma mpoly_base_conv:
  fixes x :: "'a::comm_ring_1"
  shows "0 = poly 0 x" "c = poly [:c:] x" "x = poly [:0,1:] x"
  by simp_all

lemma mpoly_norm_conv:
  fixes x :: "'a::comm_ring_1"
  shows "poly [:0:] x = poly 0 x" "poly [:poly 0 y:] x = poly 0 x"
  by simp_all

lemma mpoly_sub_conv:
  fixes x :: "'a::comm_ring_1"
  shows "poly p x - poly q x = poly p x + -1 * poly q x"
  by simp

lemma poly_pad_rule: "poly p x = 0 \<Longrightarrow> poly (pCons 0 p) x = 0"
  by simp

lemma poly_cancel_eq_conv:
  fixes x :: "'a::field"
  shows "x = 0 \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> y = 0 \<longleftrightarrow> a * y - b * x = 0"
  by auto

lemma poly_divides_pad_rule:
  fixes p:: "('a::comm_ring_1) poly"
  assumes pq: "p dvd q"
  shows "p dvd (pCons 0 q)"
  by (metis add_0 dvd_def mult_pCons_right pq smult_0_left)

lemma poly_divides_conv0:
  fixes p:: "'a::field poly"
  assumes lgpq: "degree q < degree p" and lq: "p \<noteq> 0"
  shows "p dvd q \<longleftrightarrow> q = 0"
  using lgpq mod_poly_less by fastforce

lemma poly_divides_conv1:
  fixes p :: "'a::field poly"
  assumes a0: "a \<noteq> 0"
    and pp': "p dvd p'"
    and qrp': "smult a q - p' = r"
  shows "p dvd q \<longleftrightarrow> p dvd r"
  by (metis a0 diff_add_cancel dvd_add_left_iff dvd_smult_iff pp' qrp')

lemma basic_cqe_conv1:
  "(\<exists>x. poly p x = 0 \<and> poly 0 x \<noteq> 0) \<longleftrightarrow> False"
  "(\<exists>x. poly 0 x \<noteq> 0) \<longleftrightarrow> False"
  "(\<exists>x. poly [:c:] x \<noteq> 0) \<longleftrightarrow> c \<noteq> 0"
  "(\<exists>x. poly 0 x = 0) \<longleftrightarrow> True"
  "(\<exists>x. poly [:c:] x = 0) \<longleftrightarrow> c = 0"
  by simp_all

lemma basic_cqe_conv2:
  assumes l: "p \<noteq> 0"
  shows "\<exists>x. poly (pCons a (pCons b p)) x = (0::complex)"
  by (meson fundamental_theorem_of_algebra_alt l pCons_eq_0_iff pCons_eq_iff)

lemma  basic_cqe_conv_2b: "(\<exists>x. poly p x \<noteq> (0::complex)) \<longleftrightarrow> p \<noteq> 0"
  by (metis poly_all_0_iff_0)

lemma basic_cqe_conv3:
  fixes p q :: "complex poly"
  assumes l: "p \<noteq> 0"
  shows "(\<exists>x. poly (pCons a p) x = 0 \<and> poly q x \<noteq> 0) \<longleftrightarrow> \<not> (pCons a p) dvd (q ^ psize p)"
  by (metis degree_pCons_eq_if l nullstellensatz_univariate pCons_eq_0_iff psize_def)

lemma basic_cqe_conv4:
  fixes p q :: "complex poly"
  assumes h: "\<And>x. poly (q ^ n) x = poly r x"
  shows "p dvd (q ^ n) \<longleftrightarrow> p dvd r"
proof -
  from h have "poly (q ^ n) = poly r"
    by auto
  then show "p dvd (q ^ n) \<longleftrightarrow> p dvd r"
    by (simp add: poly_eq_poly_eq_iff)
qed

lemma poly_const_conv:
  fixes x :: "'a::comm_ring_1"
  shows "poly [:c:] x = y \<longleftrightarrow> c = y"
  by simp

end
