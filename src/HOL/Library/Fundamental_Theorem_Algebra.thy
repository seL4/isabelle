(* Author: Amine Chaieb, TU Muenchen *)

header{*Fundamental Theorem of Algebra*}

theory Fundamental_Theorem_Algebra
imports Polynomial Complex
begin

subsection {* Square root of complex numbers *}
definition csqrt :: "complex \<Rightarrow> complex" where
"csqrt z = (if Im z = 0 then
            if 0 \<le> Re z then Complex (sqrt(Re z)) 0
            else Complex 0 (sqrt(- Re z))
           else Complex (sqrt((cmod z + Re z) /2))
                        ((Im z / abs(Im z)) * sqrt((cmod z - Re z) /2)))"

lemma csqrt[algebra]: "csqrt z ^ 2 = z"
proof-
  obtain x y where xy: "z = Complex x y" by (cases z)
  {assume y0: "y = 0"
    {assume x0: "x \<ge> 0"
      then have ?thesis using y0 xy real_sqrt_pow2[OF x0]
        by (simp add: csqrt_def power2_eq_square)}
    moreover
    {assume "\<not> x \<ge> 0" hence x0: "- x \<ge> 0" by arith
      then have ?thesis using y0 xy real_sqrt_pow2[OF x0]
        by (simp add: csqrt_def power2_eq_square) }
    ultimately have ?thesis by blast}
  moreover
  {assume y0: "y\<noteq>0"
    {fix x y
      let ?z = "Complex x y"
      from abs_Re_le_cmod[of ?z] have tha: "abs x \<le> cmod ?z" by auto
      hence "cmod ?z - x \<ge> 0" "cmod ?z + x \<ge> 0" by arith+
      hence "(sqrt (x * x + y * y) + x) / 2 \<ge> 0" "(sqrt (x * x + y * y) - x) / 2 \<ge> 0" by (simp_all add: power2_eq_square) }
    note th = this
    have sq4: "\<And>x::real. x^2 / 4 = (x / 2) ^ 2"
      by (simp add: power2_eq_square)
    from th[of x y]
    have sq4': "sqrt (((sqrt (x * x + y * y) + x)^2 / 4)) = (sqrt (x * x + y * y) + x) / 2" "sqrt (((sqrt (x * x + y * y) - x)^2 / 4)) = (sqrt (x * x + y * y) - x) / 2" unfolding sq4 by simp_all
    then have th1: "sqrt ((sqrt (x * x + y * y) + x) * (sqrt (x * x + y * y) + x) / 4) - sqrt ((sqrt (x * x + y * y) - x) * (sqrt (x * x + y * y) - x) / 4) = x"
      unfolding power2_eq_square by simp
    have "sqrt 4 = sqrt (2^2)" by simp
    hence sqrt4: "sqrt 4 = 2" by (simp only: real_sqrt_abs)
    have th2: "2 *(y * sqrt ((sqrt (x * x + y * y) - x) * (sqrt (x * x + y * y) + x) / 4)) / \<bar>y\<bar> = y"
      using iffD2[OF real_sqrt_pow2_iff sum_power2_ge_zero[of x y]] y0
      unfolding power2_eq_square
      by (simp add: algebra_simps real_sqrt_divide sqrt4)
     from y0 xy have ?thesis  apply (simp add: csqrt_def power2_eq_square)
       apply (simp add: real_sqrt_sum_squares_mult_ge_zero[of x y] real_sqrt_pow2[OF th(1)[of x y], unfolded power2_eq_square] real_sqrt_pow2[OF th(2)[of x y], unfolded power2_eq_square] real_sqrt_mult[symmetric])
      using th1 th2  ..}
  ultimately show ?thesis by blast
qed


subsection{* More lemmas about module of complex numbers *}

lemma complex_of_real_power: "complex_of_real x ^ n = complex_of_real (x^n)"
  by (rule of_real_power [symmetric])

lemma real_down2: "(0::real) < d1 \<Longrightarrow> 0 < d2 ==> EX e. 0 < e & e < d1 & e < d2"
  apply (rule exI[where x = "min d1 d2 / 2"])
  by (simp add: field_simps min_def)

text{* The triangle inequality for cmod *}
lemma complex_mod_triangle_sub: "cmod w \<le> cmod (w + z) + norm z"
  using complex_mod_triangle_ineq2[of "w + z" "-z"] by auto

subsection{* Basic lemmas about complex polynomials *}

lemma poly_bound_exists:
  shows "\<exists>m. m > 0 \<and> (\<forall>z. cmod z <= r \<longrightarrow> cmod (poly p z) \<le> m)"
proof(induct p)
  case 0 thus ?case by (rule exI[where x=1], simp)
next
  case (pCons c cs)
  from pCons.hyps obtain m where m: "\<forall>z. cmod z \<le> r \<longrightarrow> cmod (poly cs z) \<le> m"
    by blast
  let ?k = " 1 + cmod c + \<bar>r * m\<bar>"
  have kp: "?k > 0" using abs_ge_zero[of "r*m"] norm_ge_zero[of c] by arith
  {fix z
    assume H: "cmod z \<le> r"
    from m H have th: "cmod (poly cs z) \<le> m" by blast
    from H have rp: "r \<ge> 0" using norm_ge_zero[of z] by arith
    have "cmod (poly (pCons c cs) z) \<le> cmod c + cmod (z* poly cs z)"
      using norm_triangle_ineq[of c "z* poly cs z"] by simp
    also have "\<dots> \<le> cmod c + r*m" using mult_mono[OF H th rp norm_ge_zero[of "poly cs z"]] by (simp add: norm_mult)
    also have "\<dots> \<le> ?k" by simp
    finally have "cmod (poly (pCons c cs) z) \<le> ?k" .}
  with kp show ?case by blast
qed


text{* Offsetting the variable in a polynomial gives another of same degree *}

definition
  "offset_poly p h = poly_rec 0 (\<lambda>a p q. smult h q + pCons a q) p"

lemma offset_poly_0: "offset_poly 0 h = 0"
  unfolding offset_poly_def by (simp add: poly_rec_0)

lemma offset_poly_pCons:
  "offset_poly (pCons a p) h =
    smult h (offset_poly p h) + pCons a (offset_poly p h)"
  unfolding offset_poly_def by (simp add: poly_rec_pCons)

lemma offset_poly_single: "offset_poly [:a:] h = [:a:]"
by (simp add: offset_poly_pCons offset_poly_0)

lemma poly_offset_poly: "poly (offset_poly p h) x = poly p (h + x)"
apply (induct p)
apply (simp add: offset_poly_0)
apply (simp add: offset_poly_pCons algebra_simps)
done

lemma offset_poly_eq_0_lemma: "smult c p + pCons a p = 0 \<Longrightarrow> p = 0"
by (induct p arbitrary: a, simp, force)

lemma offset_poly_eq_0_iff: "offset_poly p h = 0 \<longleftrightarrow> p = 0"
apply (safe intro!: offset_poly_0)
apply (induct p, simp)
apply (simp add: offset_poly_pCons)
apply (frule offset_poly_eq_0_lemma, simp)
done

lemma degree_offset_poly: "degree (offset_poly p h) = degree p"
apply (induct p)
apply (simp add: offset_poly_0)
apply (case_tac "p = 0")
apply (simp add: offset_poly_0 offset_poly_pCons)
apply (simp add: offset_poly_pCons)
apply (subst degree_add_eq_right)
apply (rule le_less_trans [OF degree_smult_le])
apply (simp add: offset_poly_eq_0_iff)
apply (simp add: offset_poly_eq_0_iff)
done

definition
  "psize p = (if p = 0 then 0 else Suc (degree p))"

lemma psize_eq_0_iff [simp]: "psize p = 0 \<longleftrightarrow> p = 0"
  unfolding psize_def by simp

lemma poly_offset: "\<exists> q. psize q = psize p \<and> (\<forall>x. poly q (x::complex) = poly p (a + x))"
proof (intro exI conjI)
  show "psize (offset_poly p a) = psize p"
    unfolding psize_def
    by (simp add: offset_poly_eq_0_iff degree_offset_poly)
  show "\<forall>x. poly (offset_poly p a) x = poly p (a + x)"
    by (simp add: poly_offset_poly)
qed

text{* An alternative useful formulation of completeness of the reals *}
lemma real_sup_exists: assumes ex: "\<exists>x. P x" and bz: "\<exists>z. \<forall>x. P x \<longrightarrow> x < z"
  shows "\<exists>(s::real). \<forall>y. (\<exists>x. P x \<and> y < x) \<longleftrightarrow> y < s"
proof-
  from ex bz obtain x Y where x: "P x" and Y: "\<And>x. P x \<Longrightarrow> x < Y"  by blast
  from ex have thx:"\<exists>x. x \<in> Collect P" by blast
  from bz have thY: "\<exists>Y. isUb UNIV (Collect P) Y"
    by(auto simp add: isUb_def isLub_def setge_def setle_def leastP_def Ball_def order_le_less)
  from reals_complete[OF thx thY] obtain L where L: "isLub UNIV (Collect P) L"
    by blast
  from Y[OF x] have xY: "x < Y" .
  from L have L': "\<forall>x. P x \<longrightarrow> x \<le> L" by (auto simp add: isUb_def isLub_def setge_def setle_def leastP_def Ball_def)
  from Y have Y': "\<forall>x. P x \<longrightarrow> x \<le> Y"
    apply (clarsimp, atomize (full)) by auto
  from L Y' have "L \<le> Y" by (auto simp add: isUb_def isLub_def setge_def setle_def leastP_def Ball_def)
  {fix y
    {fix z assume z: "P z" "y < z"
      from L' z have "y < L" by auto }
    moreover
    {assume yL: "y < L" "\<forall>z. P z \<longrightarrow> \<not> y < z"
      hence nox: "\<forall>z. P z \<longrightarrow> y \<ge> z" by auto
      from nox L have "y \<ge> L" by (auto simp add: isUb_def isLub_def setge_def setle_def leastP_def Ball_def)
      with yL(1) have False  by arith}
    ultimately have "(\<exists>x. P x \<and> y < x) \<longleftrightarrow> y < L" by blast}
  thus ?thesis by blast
qed

subsection {* Fundamental theorem of algebra *}
lemma  unimodular_reduce_norm:
  assumes md: "cmod z = 1"
  shows "cmod (z + 1) < 1 \<or> cmod (z - 1) < 1 \<or> cmod (z + ii) < 1 \<or> cmod (z - ii) < 1"
proof-
  obtain x y where z: "z = Complex x y " by (cases z, auto)
  from md z have xy: "x^2 + y^2 = 1" by (simp add: cmod_def)
  {assume C: "cmod (z + 1) \<ge> 1" "cmod (z - 1) \<ge> 1" "cmod (z + ii) \<ge> 1" "cmod (z - ii) \<ge> 1"
    from C z xy have "2*x \<le> 1" "2*x \<ge> -1" "2*y \<le> 1" "2*y \<ge> -1"
      by (simp_all add: cmod_def power2_eq_square algebra_simps)
    hence "abs (2*x) \<le> 1" "abs (2*y) \<le> 1" by simp_all
    hence "(abs (2 * x))^2 <= 1^2" "(abs (2 * y)) ^2 <= 1^2"
      by - (rule power_mono, simp, simp)+
    hence th0: "4*x^2 \<le> 1" "4*y^2 \<le> 1"
      by (simp_all  add: power2_abs power_mult_distrib)
    from add_mono[OF th0] xy have False by simp }
  thus ?thesis unfolding linorder_not_le[symmetric] by blast
qed

text{* Hence we can always reduce modulus of @{text "1 + b z^n"} if nonzero *}
lemma reduce_poly_simple:
 assumes b: "b \<noteq> 0" and n: "n\<noteq>0"
  shows "\<exists>z. cmod (1 + b * z^n) < 1"
using n
proof(induct n rule: nat_less_induct)
  fix n
  assume IH: "\<forall>m<n. m \<noteq> 0 \<longrightarrow> (\<exists>z. cmod (1 + b * z ^ m) < 1)" and n: "n \<noteq> 0"
  let ?P = "\<lambda>z n. cmod (1 + b * z ^ n) < 1"
  {assume e: "even n"
    hence "\<exists>m. n = 2*m" by presburger
    then obtain m where m: "n = 2*m" by blast
    from n m have "m\<noteq>0" "m < n" by presburger+
    with IH[rule_format, of m] obtain z where z: "?P z m" by blast
    from z have "?P (csqrt z) n" by (simp add: m power_mult csqrt)
    hence "\<exists>z. ?P z n" ..}
  moreover
  {assume o: "odd n"
    have th0: "cmod (complex_of_real (cmod b) / b) = 1"
      using b by (simp add: norm_divide)
    from o have "\<exists>m. n = Suc (2*m)" by presburger+
    then obtain m where m: "n = Suc (2*m)" by blast
    from unimodular_reduce_norm[OF th0] o
    have "\<exists>v. cmod (complex_of_real (cmod b) / b + v^n) < 1"
      apply (cases "cmod (complex_of_real (cmod b) / b + 1) < 1", rule_tac x="1" in exI, simp)
      apply (cases "cmod (complex_of_real (cmod b) / b - 1) < 1", rule_tac x="-1" in exI, simp add: diff_minus)
      apply (cases "cmod (complex_of_real (cmod b) / b + ii) < 1")
      apply (cases "even m", rule_tac x="ii" in exI, simp add: m power_mult)
      apply (rule_tac x="- ii" in exI, simp add: m power_mult)
      apply (cases "even m", rule_tac x="- ii" in exI, simp add: m power_mult diff_minus)
      apply (rule_tac x="ii" in exI, simp add: m power_mult diff_minus)
      done
    then obtain v where v: "cmod (complex_of_real (cmod b) / b + v^n) < 1" by blast
    let ?w = "v / complex_of_real (root n (cmod b))"
    from odd_real_root_pow[OF o, of "cmod b"]
    have th1: "?w ^ n = v^n / complex_of_real (cmod b)"
      by (simp add: power_divide complex_of_real_power)
    have th2:"cmod (complex_of_real (cmod b) / b) = 1" using b by (simp add: norm_divide)
    hence th3: "cmod (complex_of_real (cmod b) / b) \<ge> 0" by simp
    have th4: "cmod (complex_of_real (cmod b) / b) *
   cmod (1 + b * (v ^ n / complex_of_real (cmod b)))
   < cmod (complex_of_real (cmod b) / b) * 1"
      apply (simp only: norm_mult[symmetric] distrib_left)
      using b v by (simp add: th2)

    from mult_less_imp_less_left[OF th4 th3]
    have "?P ?w n" unfolding th1 .
    hence "\<exists>z. ?P z n" .. }
  ultimately show "\<exists>z. ?P z n" by blast
qed

text{* Bolzano-Weierstrass type property for closed disc in complex plane. *}

lemma metric_bound_lemma: "cmod (x - y) <= \<bar>Re x - Re y\<bar> + \<bar>Im x - Im y\<bar>"
  using real_sqrt_sum_squares_triangle_ineq[of "Re x - Re y" 0 0 "Im x - Im y" ]
  unfolding cmod_def by simp

lemma bolzano_weierstrass_complex_disc:
  assumes r: "\<forall>n. cmod (s n) \<le> r"
  shows "\<exists>f z. subseq f \<and> (\<forall>e >0. \<exists>N. \<forall>n \<ge> N. cmod (s (f n) - z) < e)"
proof-
  from seq_monosub[of "Re o s"]
  obtain f g where f: "subseq f" "monoseq (\<lambda>n. Re (s (f n)))"
    unfolding o_def by blast
  from seq_monosub[of "Im o s o f"]
  obtain g where g: "subseq g" "monoseq (\<lambda>n. Im (s(f(g n))))" unfolding o_def by blast
  let ?h = "f o g"
  from r[rule_format, of 0] have rp: "r \<ge> 0" using norm_ge_zero[of "s 0"] by arith
  have th:"\<forall>n. r + 1 \<ge> \<bar> Re (s n)\<bar>"
  proof
    fix n
    from abs_Re_le_cmod[of "s n"] r[rule_format, of n]  show "\<bar>Re (s n)\<bar> \<le> r + 1" by arith
  qed
  have conv1: "convergent (\<lambda>n. Re (s ( f n)))"
    apply (rule Bseq_monoseq_convergent)
    apply (simp add: Bseq_def)
    apply (rule exI[where x= "r + 1"])
    using th rp apply simp
    using f(2) .
  have th:"\<forall>n. r + 1 \<ge> \<bar> Im (s n)\<bar>"
  proof
    fix n
    from abs_Im_le_cmod[of "s n"] r[rule_format, of n]  show "\<bar>Im (s n)\<bar> \<le> r + 1" by arith
  qed

  have conv2: "convergent (\<lambda>n. Im (s (f (g n))))"
    apply (rule Bseq_monoseq_convergent)
    apply (simp add: Bseq_def)
    apply (rule exI[where x= "r + 1"])
    using th rp apply simp
    using g(2) .

  from conv1[unfolded convergent_def] obtain x where "LIMSEQ (\<lambda>n. Re (s (f n))) x"
    by blast
  hence  x: "\<forall>r>0. \<exists>n0. \<forall>n\<ge>n0. \<bar> Re (s (f n)) - x \<bar> < r"
    unfolding LIMSEQ_iff real_norm_def .

  from conv2[unfolded convergent_def] obtain y where "LIMSEQ (\<lambda>n. Im (s (f (g n)))) y"
    by blast
  hence  y: "\<forall>r>0. \<exists>n0. \<forall>n\<ge>n0. \<bar> Im (s (f (g n))) - y \<bar> < r"
    unfolding LIMSEQ_iff real_norm_def .
  let ?w = "Complex x y"
  from f(1) g(1) have hs: "subseq ?h" unfolding subseq_def by auto
  {fix e assume ep: "e > (0::real)"
    hence e2: "e/2 > 0" by simp
    from x[rule_format, OF e2] y[rule_format, OF e2]
    obtain N1 N2 where N1: "\<forall>n\<ge>N1. \<bar>Re (s (f n)) - x\<bar> < e / 2" and N2: "\<forall>n\<ge>N2. \<bar>Im (s (f (g n))) - y\<bar> < e / 2" by blast
    {fix n assume nN12: "n \<ge> N1 + N2"
      hence nN1: "g n \<ge> N1" and nN2: "n \<ge> N2" using seq_suble[OF g(1), of n] by arith+
      from add_strict_mono[OF N1[rule_format, OF nN1] N2[rule_format, OF nN2]]
      have "cmod (s (?h n) - ?w) < e"
        using metric_bound_lemma[of "s (f (g n))" ?w] by simp }
    hence "\<exists>N. \<forall>n\<ge>N. cmod (s (?h n) - ?w) < e" by blast }
  with hs show ?thesis  by blast
qed

text{* Polynomial is continuous. *}

lemma poly_cont:
  assumes ep: "e > 0"
  shows "\<exists>d >0. \<forall>w. 0 < cmod (w - z) \<and> cmod (w - z) < d \<longrightarrow> cmod (poly p w - poly p z) < e"
proof-
  obtain q where q: "degree q = degree p" "\<And>x. poly q x = poly p (z + x)"
  proof
    show "degree (offset_poly p z) = degree p"
      by (rule degree_offset_poly)
    show "\<And>x. poly (offset_poly p z) x = poly p (z + x)"
      by (rule poly_offset_poly)
  qed
  {fix w
    note q(2)[of "w - z", simplified]}
  note th = this
  show ?thesis unfolding th[symmetric]
  proof(induct q)
    case 0 thus ?case  using ep by auto
  next
    case (pCons c cs)
    from poly_bound_exists[of 1 "cs"]
    obtain m where m: "m > 0" "\<And>z. cmod z \<le> 1 \<Longrightarrow> cmod (poly cs z) \<le> m" by blast
    from ep m(1) have em0: "e/m > 0" by (simp add: field_simps)
    have one0: "1 > (0::real)"  by arith
    from real_lbound_gt_zero[OF one0 em0]
    obtain d where d: "d >0" "d < 1" "d < e / m" by blast
    from d(1,3) m(1) have dm: "d*m > 0" "d*m < e"
      by (simp_all add: field_simps mult_pos_pos)
    show ?case
      proof(rule ex_forward[OF real_lbound_gt_zero[OF one0 em0]], clarsimp simp add: norm_mult)
        fix d w
        assume H: "d > 0" "d < 1" "d < e/m" "w\<noteq>z" "cmod (w-z) < d"
        hence d1: "cmod (w-z) \<le> 1" "d \<ge> 0" by simp_all
        from H(3) m(1) have dme: "d*m < e" by (simp add: field_simps)
        from H have th: "cmod (w-z) \<le> d" by simp
        from mult_mono[OF th m(2)[OF d1(1)] d1(2) norm_ge_zero] dme
        show "cmod (w - z) * cmod (poly cs (w - z)) < e" by simp
      qed
    qed
qed

text{* Hence a polynomial attains minimum on a closed disc
  in the complex plane. *}
lemma  poly_minimum_modulus_disc:
  "\<exists>z. \<forall>w. cmod w \<le> r \<longrightarrow> cmod (poly p z) \<le> cmod (poly p w)"
proof-
  {assume "\<not> r \<ge> 0" hence ?thesis unfolding linorder_not_le
      apply -
      apply (rule exI[where x=0])
      apply auto
      apply (subgoal_tac "cmod w < 0")
      apply simp
      apply arith
      done }
  moreover
  {assume rp: "r \<ge> 0"
    from rp have "cmod 0 \<le> r \<and> cmod (poly p 0) = - (- cmod (poly p 0))" by simp
    hence mth1: "\<exists>x z. cmod z \<le> r \<and> cmod (poly p z) = - x"  by blast
    {fix x z
      assume H: "cmod z \<le> r" "cmod (poly p z) = - x" "\<not>x < 1"
      hence "- x < 0 " by arith
      with H(2) norm_ge_zero[of "poly p z"]  have False by simp }
    then have mth2: "\<exists>z. \<forall>x. (\<exists>z. cmod z \<le> r \<and> cmod (poly p z) = - x) \<longrightarrow> x < z" by blast
    from real_sup_exists[OF mth1 mth2] obtain s where
      s: "\<forall>y. (\<exists>x. (\<exists>z. cmod z \<le> r \<and> cmod (poly p z) = - x) \<and> y < x) \<longleftrightarrow>(y < s)" by blast
    let ?m = "-s"
    {fix y
      from s[rule_format, of "-y"] have
    "(\<exists>z x. cmod z \<le> r \<and> -(- cmod (poly p z)) < y) \<longleftrightarrow> ?m < y"
        unfolding minus_less_iff[of y ] equation_minus_iff by blast }
    note s1 = this[unfolded minus_minus]
    from s1[of ?m] have s1m: "\<And>z x. cmod z \<le> r \<Longrightarrow> cmod (poly p z) \<ge> ?m"
      by auto
    {fix n::nat
      from s1[rule_format, of "?m + 1/real (Suc n)"]
      have "\<exists>z. cmod z \<le> r \<and> cmod (poly p z) < - s + 1 / real (Suc n)"
        by simp}
    hence th: "\<forall>n. \<exists>z. cmod z \<le> r \<and> cmod (poly p z) < - s + 1 / real (Suc n)" ..
    from choice[OF th] obtain g where
      g: "\<forall>n. cmod (g n) \<le> r" "\<forall>n. cmod (poly p (g n)) <?m+1 /real(Suc n)"
      by blast
    from bolzano_weierstrass_complex_disc[OF g(1)]
    obtain f z where fz: "subseq f" "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. cmod (g (f n) - z) < e"
      by blast
    {fix w
      assume wr: "cmod w \<le> r"
      let ?e = "\<bar>cmod (poly p z) - ?m\<bar>"
      {assume e: "?e > 0"
        hence e2: "?e/2 > 0" by simp
        from poly_cont[OF e2, of z p] obtain d where
          d: "d>0" "\<forall>w. 0<cmod (w - z)\<and> cmod(w - z) < d \<longrightarrow> cmod(poly p w - poly p z) < ?e/2" by blast
        {fix w assume w: "cmod (w - z) < d"
          have "cmod(poly p w - poly p z) < ?e / 2"
            using d(2)[rule_format, of w] w e by (cases "w=z", simp_all)}
        note th1 = this

        from fz(2)[rule_format, OF d(1)] obtain N1 where
          N1: "\<forall>n\<ge>N1. cmod (g (f n) - z) < d" by blast
        from reals_Archimedean2[of "2/?e"] obtain N2::nat where
          N2: "2/?e < real N2" by blast
        have th2: "cmod(poly p (g(f(N1 + N2))) - poly p z) < ?e/2"
          using N1[rule_format, of "N1 + N2"] th1 by simp
        {fix a b e2 m :: real
        have "a < e2 \<Longrightarrow> abs(b - m) < e2 \<Longrightarrow> 2 * e2 <= abs(b - m) + a
          ==> False" by arith}
      note th0 = this
      have ath:
        "\<And>m x e. m <= x \<Longrightarrow>  x < m + e ==> abs(x - m::real) < e" by arith
      from s1m[OF g(1)[rule_format]]
      have th31: "?m \<le> cmod(poly p (g (f (N1 + N2))))" .
      from seq_suble[OF fz(1), of "N1+N2"]
      have th00: "real (Suc (N1+N2)) \<le> real (Suc (f (N1+N2)))" by simp
      have th000: "0 \<le> (1::real)" "(1::real) \<le> 1" "real (Suc (N1+N2)) > 0"
        using N2 by auto
      from frac_le[OF th000 th00] have th00: "?m +1 / real (Suc (f (N1 + N2))) \<le> ?m + 1 / real (Suc (N1 + N2))" by simp
      from g(2)[rule_format, of "f (N1 + N2)"]
      have th01:"cmod (poly p (g (f (N1 + N2)))) < - s + 1 / real (Suc (f (N1 + N2)))" .
      from order_less_le_trans[OF th01 th00]
      have th32: "cmod(poly p (g (f (N1 + N2)))) < ?m + (1/ real(Suc (N1 + N2)))" .
      from N2 have "2/?e < real (Suc (N1 + N2))" by arith
      with e2 less_imp_inverse_less[of "2/?e" "real (Suc (N1 + N2))"]
      have "?e/2 > 1/ real (Suc (N1 + N2))" by (simp add: inverse_eq_divide)
      with ath[OF th31 th32]
      have thc1:"\<bar>cmod(poly p (g (f (N1 + N2)))) - ?m\<bar>< ?e/2" by arith
      have ath2: "\<And>(a::real) b c m. \<bar>a - b\<bar> <= c ==> \<bar>b - m\<bar> <= \<bar>a - m\<bar> + c"
        by arith
      have th22: "\<bar>cmod (poly p (g (f (N1 + N2)))) - cmod (poly p z)\<bar>
\<le> cmod (poly p (g (f (N1 + N2))) - poly p z)"
        by (simp add: norm_triangle_ineq3)
      from ath2[OF th22, of ?m]
      have thc2: "2*(?e/2) \<le> \<bar>cmod(poly p (g (f (N1 + N2)))) - ?m\<bar> + cmod (poly p (g (f (N1 + N2))) - poly p z)" by simp
      from th0[OF th2 thc1 thc2] have False .}
      hence "?e = 0" by auto
      then have "cmod (poly p z) = ?m" by simp
      with s1m[OF wr]
      have "cmod (poly p z) \<le> cmod (poly p w)" by simp }
    hence ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma "(rcis (sqrt (abs r)) (a/2)) ^ 2 = rcis (abs r) a"
  unfolding power2_eq_square
  apply (simp add: rcis_mult)
  apply (simp add: power2_eq_square[symmetric])
  done

lemma cispi: "cis pi = -1"
  unfolding cis_def
  by simp

lemma "(rcis (sqrt (abs r)) ((pi + a)/2)) ^ 2 = rcis (- abs r) a"
  unfolding power2_eq_square
  apply (simp add: rcis_mult add_divide_distrib)
  apply (simp add: power2_eq_square[symmetric] rcis_def cispi cis_mult[symmetric])
  done

text {* Nonzero polynomial in z goes to infinity as z does. *}

lemma poly_infinity:
  assumes ex: "p \<noteq> 0"
  shows "\<exists>r. \<forall>z. r \<le> cmod z \<longrightarrow> d \<le> cmod (poly (pCons a p) z)"
using ex
proof(induct p arbitrary: a d)
  case (pCons c cs a d)
  {assume H: "cs \<noteq> 0"
    with pCons.hyps obtain r where r: "\<forall>z. r \<le> cmod z \<longrightarrow> d + cmod a \<le> cmod (poly (pCons c cs) z)" by blast
    let ?r = "1 + \<bar>r\<bar>"
    {fix z assume h: "1 + \<bar>r\<bar> \<le> cmod z"
      have r0: "r \<le> cmod z" using h by arith
      from r[rule_format, OF r0]
      have th0: "d + cmod a \<le> 1 * cmod(poly (pCons c cs) z)" by arith
      from h have z1: "cmod z \<ge> 1" by arith
      from order_trans[OF th0 mult_right_mono[OF z1 norm_ge_zero[of "poly (pCons c cs) z"]]]
      have th1: "d \<le> cmod(z * poly (pCons c cs) z) - cmod a"
        unfolding norm_mult by (simp add: algebra_simps)
      from complex_mod_triangle_sub[of "z * poly (pCons c cs) z" a]
      have th2: "cmod(z * poly (pCons c cs) z) - cmod a \<le> cmod (poly (pCons a (pCons c cs)) z)"
        by (simp add: diff_le_eq algebra_simps)
      from th1 th2 have "d \<le> cmod (poly (pCons a (pCons c cs)) z)"  by arith}
    hence ?case by blast}
  moreover
  {assume cs0: "\<not> (cs \<noteq> 0)"
    with pCons.prems have c0: "c \<noteq> 0" by simp
    from cs0 have cs0': "cs = 0" by simp
    {fix z
      assume h: "(\<bar>d\<bar> + cmod a) / cmod c \<le> cmod z"
      from c0 have "cmod c > 0" by simp
      from h c0 have th0: "\<bar>d\<bar> + cmod a \<le> cmod (z*c)"
        by (simp add: field_simps norm_mult)
      have ath: "\<And>mzh mazh ma. mzh <= mazh + ma ==> abs(d) + ma <= mzh ==> d <= mazh" by arith
      from complex_mod_triangle_sub[of "z*c" a ]
      have th1: "cmod (z * c) \<le> cmod (a + z * c) + cmod a"
        by (simp add: algebra_simps)
      from ath[OF th1 th0] have "d \<le> cmod (poly (pCons a (pCons c cs)) z)"
        using cs0' by simp}
    then have ?case  by blast}
  ultimately show ?case by blast
qed simp

text {* Hence polynomial's modulus attains its minimum somewhere. *}
lemma poly_minimum_modulus:
  "\<exists>z.\<forall>w. cmod (poly p z) \<le> cmod (poly p w)"
proof(induct p)
  case (pCons c cs)
  {assume cs0: "cs \<noteq> 0"
    from poly_infinity[OF cs0, of "cmod (poly (pCons c cs) 0)" c]
    obtain r where r: "\<And>z. r \<le> cmod z \<Longrightarrow> cmod (poly (pCons c cs) 0) \<le> cmod (poly (pCons c cs) z)" by blast
    have ath: "\<And>z r. r \<le> cmod z \<or> cmod z \<le> \<bar>r\<bar>" by arith
    from poly_minimum_modulus_disc[of "\<bar>r\<bar>" "pCons c cs"]
    obtain v where v: "\<And>w. cmod w \<le> \<bar>r\<bar> \<Longrightarrow> cmod (poly (pCons c cs) v) \<le> cmod (poly (pCons c cs) w)" by blast
    {fix z assume z: "r \<le> cmod z"
      from v[of 0] r[OF z]
      have "cmod (poly (pCons c cs) v) \<le> cmod (poly (pCons c cs) z)"
        by simp }
    note v0 = this
    from v0 v ath[of r] have ?case by blast}
  moreover
  {assume cs0: "\<not> (cs \<noteq> 0)"
    hence th:"cs = 0" by simp
    from th pCons.hyps have ?case by simp}
  ultimately show ?case by blast
qed simp

text{* Constant function (non-syntactic characterization). *}
definition "constant f = (\<forall>x y. f x = f y)"

lemma nonconstant_length: "\<not> (constant (poly p)) \<Longrightarrow> psize p \<ge> 2"
  unfolding constant_def psize_def
  apply (induct p, auto)
  done

lemma poly_replicate_append:
  "poly (monom 1 n * p) (x::'a::{comm_ring_1}) = x^n * poly p x"
  by (simp add: poly_monom)

text {* Decomposition of polynomial, skipping zero coefficients
  after the first.  *}

lemma poly_decompose_lemma:
 assumes nz: "\<not>(\<forall>z. z\<noteq>0 \<longrightarrow> poly p z = (0::'a::{idom}))"
  shows "\<exists>k a q. a\<noteq>0 \<and> Suc (psize q + k) = psize p \<and>
                 (\<forall>z. poly p z = z^k * poly (pCons a q) z)"
unfolding psize_def
using nz
proof(induct p)
  case 0 thus ?case by simp
next
  case (pCons c cs)
  {assume c0: "c = 0"
    from pCons.hyps pCons.prems c0 have ?case
      apply (auto)
      apply (rule_tac x="k+1" in exI)
      apply (rule_tac x="a" in exI, clarsimp)
      apply (rule_tac x="q" in exI)
      by (auto)}
  moreover
  {assume c0: "c\<noteq>0"
    hence ?case apply-
      apply (rule exI[where x=0])
      apply (rule exI[where x=c], clarsimp)
      apply (rule exI[where x=cs])
      apply auto
      done}
  ultimately show ?case by blast
qed

lemma poly_decompose:
  assumes nc: "~constant(poly p)"
  shows "\<exists>k a q. a\<noteq>(0::'a::{idom}) \<and> k\<noteq>0 \<and>
               psize q + k + 1 = psize p \<and>
              (\<forall>z. poly p z = poly p 0 + z^k * poly (pCons a q) z)"
using nc
proof(induct p)
  case 0 thus ?case by (simp add: constant_def)
next
  case (pCons c cs)
  {assume C:"\<forall>z. z \<noteq> 0 \<longrightarrow> poly cs z = 0"
    {fix x y
      from C have "poly (pCons c cs) x = poly (pCons c cs) y" by (cases "x=0", auto)}
    with pCons.prems have False by (auto simp add: constant_def)}
  hence th: "\<not> (\<forall>z. z \<noteq> 0 \<longrightarrow> poly cs z = 0)" ..
  from poly_decompose_lemma[OF th]
  show ?case
    apply clarsimp
    apply (rule_tac x="k+1" in exI)
    apply (rule_tac x="a" in exI)
    apply simp
    apply (rule_tac x="q" in exI)
    apply (auto simp add: power_Suc)
    apply (auto simp add: psize_def split: if_splits)
    done
qed

text{* Fundamental theorem of algebra *}

lemma fundamental_theorem_of_algebra:
  assumes nc: "~constant(poly p)"
  shows "\<exists>z::complex. poly p z = 0"
using nc
proof(induct "psize p" arbitrary: p rule: less_induct)
  case less
  let ?p = "poly p"
  let ?ths = "\<exists>z. ?p z = 0"

  from nonconstant_length[OF less(2)] have n2: "psize p \<ge> 2" .
  from poly_minimum_modulus obtain c where
    c: "\<forall>w. cmod (?p c) \<le> cmod (?p w)" by blast
  {assume pc: "?p c = 0" hence ?ths by blast}
  moreover
  {assume pc0: "?p c \<noteq> 0"
    from poly_offset[of p c] obtain q where
      q: "psize q = psize p" "\<forall>x. poly q x = ?p (c+x)" by blast
    {assume h: "constant (poly q)"
      from q(2) have th: "\<forall>x. poly q (x - c) = ?p x" by auto
      {fix x y
        from th have "?p x = poly q (x - c)" by auto
        also have "\<dots> = poly q (y - c)"
          using h unfolding constant_def by blast
        also have "\<dots> = ?p y" using th by auto
        finally have "?p x = ?p y" .}
      with less(2) have False unfolding constant_def by blast }
    hence qnc: "\<not> constant (poly q)" by blast
    from q(2) have pqc0: "?p c = poly q 0" by simp
    from c pqc0 have cq0: "\<forall>w. cmod (poly q 0) \<le> cmod (?p w)" by simp
    let ?a0 = "poly q 0"
    from pc0 pqc0 have a00: "?a0 \<noteq> 0" by simp
    from a00
    have qr: "\<forall>z. poly q z = poly (smult (inverse ?a0) q) z * ?a0"
      by simp
    let ?r = "smult (inverse ?a0) q"
    have lgqr: "psize q = psize ?r"
      using a00 unfolding psize_def degree_def
      by (simp add: expand_poly_eq)
    {assume h: "\<And>x y. poly ?r x = poly ?r y"
      {fix x y
        from qr[rule_format, of x]
        have "poly q x = poly ?r x * ?a0" by auto
        also have "\<dots> = poly ?r y * ?a0" using h by simp
        also have "\<dots> = poly q y" using qr[rule_format, of y] by simp
        finally have "poly q x = poly q y" .}
      with qnc have False unfolding constant_def by blast}
    hence rnc: "\<not> constant (poly ?r)" unfolding constant_def by blast
    from qr[rule_format, of 0] a00  have r01: "poly ?r 0 = 1" by auto
    {fix w
      have "cmod (poly ?r w) < 1 \<longleftrightarrow> cmod (poly q w / ?a0) < 1"
        using qr[rule_format, of w] a00 by (simp add: divide_inverse mult_ac)
      also have "\<dots> \<longleftrightarrow> cmod (poly q w) < cmod ?a0"
        using a00 unfolding norm_divide by (simp add: field_simps)
      finally have "cmod (poly ?r w) < 1 \<longleftrightarrow> cmod (poly q w) < cmod ?a0" .}
    note mrmq_eq = this
    from poly_decompose[OF rnc] obtain k a s where
      kas: "a\<noteq>0" "k\<noteq>0" "psize s + k + 1 = psize ?r"
      "\<forall>z. poly ?r z = poly ?r 0 + z^k* poly (pCons a s) z" by blast
    {assume "psize p = k + 1"
      with kas(3) lgqr[symmetric] q(1) have s0:"s=0" by auto
      {fix w
        have "cmod (poly ?r w) = cmod (1 + a * w ^ k)"
          using kas(4)[rule_format, of w] s0 r01 by (simp add: algebra_simps)}
      note hth = this [symmetric]
        from reduce_poly_simple[OF kas(1,2)]
      have "\<exists>w. cmod (poly ?r w) < 1" unfolding hth by blast}
    moreover
    {assume kn: "psize p \<noteq> k+1"
      from kn kas(3) q(1) lgqr have k1n: "k + 1 < psize p" by simp
      have th01: "\<not> constant (poly (pCons 1 (monom a (k - 1))))"
        unfolding constant_def poly_pCons poly_monom
        using kas(1) apply simp
        by (rule exI[where x=0], rule exI[where x=1], simp)
      from kas(1) kas(2) have th02: "k+1 = psize (pCons 1 (monom a (k - 1)))"
        by (simp add: psize_def degree_monom_eq)
      from less(1) [OF k1n [simplified th02] th01]
      obtain w where w: "1 + w^k * a = 0"
        unfolding poly_pCons poly_monom
        using kas(2) by (cases k, auto simp add: algebra_simps)
      from poly_bound_exists[of "cmod w" s] obtain m where
        m: "m > 0" "\<forall>z. cmod z \<le> cmod w \<longrightarrow> cmod (poly s z) \<le> m" by blast
      have w0: "w\<noteq>0" using kas(2) w by (auto simp add: power_0_left)
      from w have "(1 + w ^ k * a) - 1 = 0 - 1" by simp
      then have wm1: "w^k * a = - 1" by simp
      have inv0: "0 < inverse (cmod w ^ (k + 1) * m)"
        using norm_ge_zero[of w] w0 m(1)
          by (simp add: inverse_eq_divide zero_less_mult_iff)
      with real_down2[OF zero_less_one] obtain t where
        t: "t > 0" "t < 1" "t < inverse (cmod w ^ (k + 1) * m)" by blast
      let ?ct = "complex_of_real t"
      let ?w = "?ct * w"
      have "1 + ?w^k * (a + ?w * poly s ?w) = 1 + ?ct^k * (w^k * a) + ?w^k * ?w * poly s ?w" using kas(1) by (simp add: algebra_simps power_mult_distrib)
      also have "\<dots> = complex_of_real (1 - t^k) + ?w^k * ?w * poly s ?w"
        unfolding wm1 by (simp)
      finally have "cmod (1 + ?w^k * (a + ?w * poly s ?w)) = cmod (complex_of_real (1 - t^k) + ?w^k * ?w * poly s ?w)"
        apply -
        apply (rule cong[OF refl[of cmod]])
        apply assumption
        done
      with norm_triangle_ineq[of "complex_of_real (1 - t^k)" "?w^k * ?w * poly s ?w"]
      have th11: "cmod (1 + ?w^k * (a + ?w * poly s ?w)) \<le> \<bar>1 - t^k\<bar> + cmod (?w^k * ?w * poly s ?w)" unfolding norm_of_real by simp
      have ath: "\<And>x (t::real). 0\<le> x \<Longrightarrow> x < t \<Longrightarrow> t\<le>1 \<Longrightarrow> \<bar>1 - t\<bar> + x < 1" by arith
      have "t *cmod w \<le> 1 * cmod w" apply (rule mult_mono) using t(1,2) by auto
      then have tw: "cmod ?w \<le> cmod w" using t(1) by (simp add: norm_mult)
      from t inv0 have "t* (cmod w ^ (k + 1) * m) < 1"
        by (simp add: inverse_eq_divide field_simps)
      with zero_less_power[OF t(1), of k]
      have th30: "t^k * (t* (cmod w ^ (k + 1) * m)) < t^k * 1"
        apply - apply (rule mult_strict_left_mono) by simp_all
      have "cmod (?w^k * ?w * poly s ?w) = t^k * (t* (cmod w ^ (k+1) * cmod (poly s ?w)))"  using w0 t(1)
        by (simp add: algebra_simps power_mult_distrib norm_of_real norm_power norm_mult)
      then have "cmod (?w^k * ?w * poly s ?w) \<le> t^k * (t* (cmod w ^ (k + 1) * m))"
        using t(1,2) m(2)[rule_format, OF tw] w0
        apply (simp only: )
        apply auto
        done
      with th30 have th120: "cmod (?w^k * ?w * poly s ?w) < t^k" by simp
      from power_strict_mono[OF t(2), of k] t(1) kas(2) have th121: "t^k \<le> 1"
        by auto
      from ath[OF norm_ge_zero[of "?w^k * ?w * poly s ?w"] th120 th121]
      have th12: "\<bar>1 - t^k\<bar> + cmod (?w^k * ?w * poly s ?w) < 1" .
      from th11 th12
      have "cmod (1 + ?w^k * (a + ?w * poly s ?w)) < 1"  by arith
      then have "cmod (poly ?r ?w) < 1"
        unfolding kas(4)[rule_format, of ?w] r01 by simp
      then have "\<exists>w. cmod (poly ?r w) < 1" by blast}
    ultimately have cr0_contr: "\<exists>w. cmod (poly ?r w) < 1" by blast
    from cr0_contr cq0 q(2)
    have ?ths unfolding mrmq_eq not_less[symmetric] by auto}
  ultimately show ?ths by blast
qed

text {* Alternative version with a syntactic notion of constant polynomial. *}

lemma fundamental_theorem_of_algebra_alt:
  assumes nc: "~(\<exists>a l. a\<noteq> 0 \<and> l = 0 \<and> p = pCons a l)"
  shows "\<exists>z. poly p z = (0::complex)"
using nc
proof(induct p)
  case (pCons c cs)
  {assume "c=0" hence ?case by auto}
  moreover
  {assume c0: "c\<noteq>0"
    {assume nc: "constant (poly (pCons c cs))"
      from nc[unfolded constant_def, rule_format, of 0]
      have "\<forall>w. w \<noteq> 0 \<longrightarrow> poly cs w = 0" by auto
      hence "cs = 0"
        proof(induct cs)
          case (pCons d ds)
          {assume "d=0" hence ?case using pCons.prems pCons.hyps by simp}
          moreover
          {assume d0: "d\<noteq>0"
            from poly_bound_exists[of 1 ds] obtain m where
              m: "m > 0" "\<forall>z. \<forall>z. cmod z \<le> 1 \<longrightarrow> cmod (poly ds z) \<le> m" by blast
            have dm: "cmod d / m > 0" using d0 m(1) by (simp add: field_simps)
            from real_down2[OF dm zero_less_one] obtain x where
              x: "x > 0" "x < cmod d / m" "x < 1" by blast
            let ?x = "complex_of_real x"
            from x have cx: "?x \<noteq> 0"  "cmod ?x \<le> 1" by simp_all
            from pCons.prems[rule_format, OF cx(1)]
            have cth: "cmod (?x*poly ds ?x) = cmod d" by (simp add: eq_diff_eq[symmetric])
            from m(2)[rule_format, OF cx(2)] x(1)
            have th0: "cmod (?x*poly ds ?x) \<le> x*m"
              by (simp add: norm_mult)
            from x(2) m(1) have "x*m < cmod d" by (simp add: field_simps)
            with th0 have "cmod (?x*poly ds ?x) \<noteq> cmod d" by auto
            with cth  have ?case by blast}
          ultimately show ?case by blast
        qed simp}
      then have nc: "\<not> constant (poly (pCons c cs))" using pCons.prems c0
        by blast
      from fundamental_theorem_of_algebra[OF nc] have ?case .}
  ultimately show ?case by blast
qed simp


subsection{* Nullstellensatz, degrees and divisibility of polynomials *}

lemma nullstellensatz_lemma:
  fixes p :: "complex poly"
  assumes "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0"
  and "degree p = n" and "n \<noteq> 0"
  shows "p dvd (q ^ n)"
using assms
proof(induct n arbitrary: p q rule: nat_less_induct)
  fix n::nat fix p q :: "complex poly"
  assume IH: "\<forall>m<n. \<forall>p q.
                 (\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longrightarrow>
                 degree p = m \<longrightarrow> m \<noteq> 0 \<longrightarrow> p dvd (q ^ m)"
    and pq0: "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0"
    and dpn: "degree p = n" and n0: "n \<noteq> 0"
  from dpn n0 have pne: "p \<noteq> 0" by auto
  let ?ths = "p dvd (q ^ n)"
  {fix a assume a: "poly p a = 0"
    {assume oa: "order a p \<noteq> 0"
      let ?op = "order a p"
      from pne have ap: "([:- a, 1:] ^ ?op) dvd p"
        "\<not> [:- a, 1:] ^ (Suc ?op) dvd p" using order by blast+
      note oop = order_degree[OF pne, unfolded dpn]
      {assume q0: "q = 0"
        hence ?ths using n0
          by (simp add: power_0_left)}
      moreover
      {assume q0: "q \<noteq> 0"
        from pq0[rule_format, OF a, unfolded poly_eq_0_iff_dvd]
        obtain r where r: "q = [:- a, 1:] * r" by (rule dvdE)
        from ap(1) obtain s where
          s: "p = [:- a, 1:] ^ ?op * s" by (rule dvdE)
        have sne: "s \<noteq> 0"
          using s pne by auto
        {assume ds0: "degree s = 0"
          from ds0 have "\<exists>k. s = [:k:]"
            by (cases s, simp split: if_splits)
          then obtain k where kpn: "s = [:k:]" by blast
          from sne kpn have k: "k \<noteq> 0" by simp
          let ?w = "([:1/k:] * ([:-a,1:] ^ (n - ?op))) * (r ^ n)"
          from k oop [of a] have "q ^ n = p * ?w"
            apply -
            apply (subst r, subst s, subst kpn)
            apply (subst power_mult_distrib, simp)
            apply (subst power_add [symmetric], simp)
            done
          hence ?ths unfolding dvd_def by blast}
        moreover
        {assume ds0: "degree s \<noteq> 0"
          from ds0 sne dpn s oa
            have dsn: "degree s < n" apply auto
              apply (erule ssubst)
              apply (simp add: degree_mult_eq degree_linear_power)
              done
            {fix x assume h: "poly s x = 0"
              {assume xa: "x = a"
                from h[unfolded xa poly_eq_0_iff_dvd] obtain u where
                  u: "s = [:- a, 1:] * u" by (rule dvdE)
                have "p = [:- a, 1:] ^ (Suc ?op) * u"
                  by (subst s, subst u, simp only: power_Suc mult_ac)
                with ap(2)[unfolded dvd_def] have False by blast}
              note xa = this
              from h have "poly p x = 0" by (subst s, simp)
              with pq0 have "poly q x = 0" by blast
              with r xa have "poly r x = 0"
                by (auto simp add: uminus_add_conv_diff)}
            note impth = this
            from IH[rule_format, OF dsn, of s r] impth ds0
            have "s dvd (r ^ (degree s))" by blast
            then obtain u where u: "r ^ (degree s) = s * u" ..
            hence u': "\<And>x. poly s x * poly u x = poly r x ^ degree s"
              by (simp only: poly_mult[symmetric] poly_power[symmetric])
            let ?w = "(u * ([:-a,1:] ^ (n - ?op))) * (r ^ (n - degree s))"
            from oop[of a] dsn have "q ^ n = p * ?w"
              apply -
              apply (subst s, subst r)
              apply (simp only: power_mult_distrib)
              apply (subst mult_assoc [where b=s])
              apply (subst mult_assoc [where a=u])
              apply (subst mult_assoc [where b=u, symmetric])
              apply (subst u [symmetric])
              apply (simp add: mult_ac power_add [symmetric])
              done
            hence ?ths unfolding dvd_def by blast}
      ultimately have ?ths by blast }
      ultimately have ?ths by blast}
    then have ?ths using a order_root pne by blast}
  moreover
  {assume exa: "\<not> (\<exists>a. poly p a = 0)"
    from fundamental_theorem_of_algebra_alt[of p] exa obtain c where
      ccs: "c\<noteq>0" "p = pCons c 0" by blast

    then have pp: "\<And>x. poly p x =  c" by simp
    let ?w = "[:1/c:] * (q ^ n)"
    from ccs
    have "(q ^ n) = (p * ?w) "
      by (simp add: smult_smult)
    hence ?ths unfolding dvd_def by blast}
  ultimately show ?ths by blast
qed

lemma nullstellensatz_univariate:
  "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow>
    p dvd (q ^ (degree p)) \<or> (p = 0 \<and> q = 0)"
proof-
  {assume pe: "p = 0"
    hence eq: "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow> q = 0"
      apply auto
      apply (rule poly_zero [THEN iffD1])
      by (rule ext, simp)
    {assume "p dvd (q ^ (degree p))"
      then obtain r where r: "q ^ (degree p) = p * r" ..
      from r pe have False by simp}
    with eq pe have ?thesis by blast}
  moreover
  {assume pe: "p \<noteq> 0"
    {assume dp: "degree p = 0"
      then obtain k where k: "p = [:k:]" "k\<noteq>0" using pe
        by (cases p, simp split: if_splits)
      hence th1: "\<forall>x. poly p x \<noteq> 0" by simp
      from k dp have "q ^ (degree p) = p * [:1/k:]"
        by (simp add: one_poly_def)
      hence th2: "p dvd (q ^ (degree p))" ..
      from th1 th2 pe have ?thesis by blast}
    moreover
    {assume dp: "degree p \<noteq> 0"
      then obtain n where n: "degree p = Suc n " by (cases "degree p", auto)
      {assume "p dvd (q ^ (Suc n))"
        then obtain u where u: "q ^ (Suc n) = p * u" ..
        {fix x assume h: "poly p x = 0" "poly q x \<noteq> 0"
          hence "poly (q ^ (Suc n)) x \<noteq> 0" by simp
          hence False using u h(1) by (simp only: poly_mult) simp}}
        with n nullstellensatz_lemma[of p q "degree p"] dp
        have ?thesis by auto}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

text{* Useful lemma *}

lemma constant_degree:
  fixes p :: "'a::{idom,ring_char_0} poly"
  shows "constant (poly p) \<longleftrightarrow> degree p = 0" (is "?lhs = ?rhs")
proof
  assume l: ?lhs
  from l[unfolded constant_def, rule_format, of _ "0"]
  have th: "poly p = poly [:poly p 0:]" apply - by (rule ext, simp)
  then have "p = [:poly p 0:]" by (simp add: poly_eq_iff)
  then have "degree p = degree [:poly p 0:]" by simp
  then show ?rhs by simp
next
  assume r: ?rhs
  then obtain k where "p = [:k:]"
    by (cases p, simp split: if_splits)
  then show ?lhs unfolding constant_def by auto
qed

lemma divides_degree: assumes pq: "p dvd (q:: complex poly)"
  shows "degree p \<le> degree q \<or> q = 0"
apply (cases "q = 0", simp_all)
apply (erule dvd_imp_degree_le [OF pq])
done

(* Arithmetic operations on multivariate polynomials.                        *)

lemma mpoly_base_conv:
  "(0::complex) \<equiv> poly 0 x" "c \<equiv> poly [:c:] x" "x \<equiv> poly [:0,1:] x" by simp_all

lemma mpoly_norm_conv:
  "poly [:0:] (x::complex) \<equiv> poly 0 x" "poly [:poly 0 y:] x \<equiv> poly 0 x" by simp_all

lemma mpoly_sub_conv:
  "poly p (x::complex) - poly q x \<equiv> poly p x + -1 * poly q x"
  by (simp add: diff_minus)

lemma poly_pad_rule: "poly p x = 0 ==> poly (pCons 0 p) x = (0::complex)" by simp

lemma poly_cancel_eq_conv: "p = (0::complex) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> (q = 0) \<equiv> (a * q - b * p = 0)" apply (atomize (full)) by auto

lemma resolve_eq_raw:  "poly 0 x \<equiv> 0" "poly [:c:] x \<equiv> (c::complex)" by auto
lemma  resolve_eq_then: "(P \<Longrightarrow> (Q \<equiv> Q1)) \<Longrightarrow> (\<not>P \<Longrightarrow> (Q \<equiv> Q2))
  \<Longrightarrow> Q \<equiv> P \<and> Q1 \<or> \<not>P\<and> Q2" apply (atomize (full)) by blast

lemma poly_divides_pad_rule:
  fixes p q :: "complex poly"
  assumes pq: "p dvd q"
  shows "p dvd (pCons (0::complex) q)"
proof-
  have "pCons 0 q = q * [:0,1:]" by simp
  then have "q dvd (pCons 0 q)" ..
  with pq show ?thesis by (rule dvd_trans)
qed

lemma poly_divides_pad_const_rule:
  fixes p q :: "complex poly"
  assumes pq: "p dvd q"
  shows "p dvd (smult a q)"
proof-
  have "smult a q = q * [:a:]" by simp
  then have "q dvd smult a q" ..
  with pq show ?thesis by (rule dvd_trans)
qed


lemma poly_divides_conv0:
  fixes p :: "complex poly"
  assumes lgpq: "degree q < degree p" and lq:"p \<noteq> 0"
  shows "p dvd q \<equiv> q = 0" (is "?lhs \<equiv> ?rhs")
proof-
  {assume r: ?rhs
    hence "q = p * 0" by simp
    hence ?lhs ..}
  moreover
  {assume l: ?lhs
    {assume q0: "q = 0"
      hence ?rhs by simp}
    moreover
    {assume q0: "q \<noteq> 0"
      from l q0 have "degree p \<le> degree q"
        by (rule dvd_imp_degree_le)
      with lgpq have ?rhs by simp }
    ultimately have ?rhs by blast }
  ultimately show "?lhs \<equiv> ?rhs" by - (atomize (full), blast)
qed

lemma poly_divides_conv1:
  assumes a0: "a\<noteq> (0::complex)" and pp': "(p::complex poly) dvd p'"
  and qrp': "smult a q - p' \<equiv> r"
  shows "p dvd q \<equiv> p dvd (r::complex poly)" (is "?lhs \<equiv> ?rhs")
proof-
  {
  from pp' obtain t where t: "p' = p * t" ..
  {assume l: ?lhs
    then obtain u where u: "q = p * u" ..
     have "r = p * (smult a u - t)"
       using u qrp' [symmetric] t by (simp add: algebra_simps mult_smult_right)
     then have ?rhs ..}
  moreover
  {assume r: ?rhs
    then obtain u where u: "r = p * u" ..
    from u [symmetric] t qrp' [symmetric] a0
    have "q = p * smult (1/a) (u + t)"
      by (simp add: algebra_simps mult_smult_right smult_smult)
    hence ?lhs ..}
  ultimately have "?lhs = ?rhs" by blast }
thus "?lhs \<equiv> ?rhs"  by - (atomize(full), blast)
qed

lemma basic_cqe_conv1:
  "(\<exists>x. poly p x = 0 \<and> poly 0 x \<noteq> 0) \<equiv> False"
  "(\<exists>x. poly 0 x \<noteq> 0) \<equiv> False"
  "(\<exists>x. poly [:c:] x \<noteq> 0) \<equiv> c\<noteq>0"
  "(\<exists>x. poly 0 x = 0) \<equiv> True"
  "(\<exists>x. poly [:c:] x = 0) \<equiv> c = 0" by simp_all

lemma basic_cqe_conv2:
  assumes l:"p \<noteq> 0"
  shows "(\<exists>x. poly (pCons a (pCons b p)) x = (0::complex)) \<equiv> True"
proof-
  {fix h t
    assume h: "h\<noteq>0" "t=0"  "pCons a (pCons b p) = pCons h t"
    with l have False by simp}
  hence th: "\<not> (\<exists> h t. h\<noteq>0 \<and> t=0 \<and> pCons a (pCons b p) = pCons h t)"
    by blast
  from fundamental_theorem_of_algebra_alt[OF th]
  show "(\<exists>x. poly (pCons a (pCons b p)) x = (0::complex)) \<equiv> True" by auto
qed

lemma  basic_cqe_conv_2b: "(\<exists>x. poly p x \<noteq> (0::complex)) \<equiv> (p \<noteq> 0)"
proof-
  have "p = 0 \<longleftrightarrow> poly p = poly 0"
    by (simp add: poly_zero)
  also have "\<dots> \<longleftrightarrow> (\<not> (\<exists>x. poly p x \<noteq> 0))" by (auto intro: ext)
  finally show "(\<exists>x. poly p x \<noteq> (0::complex)) \<equiv> p \<noteq> 0"
    by - (atomize (full), blast)
qed

lemma basic_cqe_conv3:
  fixes p q :: "complex poly"
  assumes l: "p \<noteq> 0"
  shows "(\<exists>x. poly (pCons a p) x = 0 \<and> poly q x \<noteq> 0) \<equiv> \<not> ((pCons a p) dvd (q ^ (psize p)))"
proof-
  from l have dp:"degree (pCons a p) = psize p" by (simp add: psize_def)
  from nullstellensatz_univariate[of "pCons a p" q] l
  show "(\<exists>x. poly (pCons a p) x = 0 \<and> poly q x \<noteq> 0) \<equiv> \<not> ((pCons a p) dvd (q ^ (psize p)))"
    unfolding dp
    by - (atomize (full), auto)
qed

lemma basic_cqe_conv4:
  fixes p q :: "complex poly"
  assumes h: "\<And>x. poly (q ^ n) x \<equiv> poly r x"
  shows "p dvd (q ^ n) \<equiv> p dvd r"
proof-
  from h have "poly (q ^ n) = poly r" by (auto intro: ext)
  then have "(q ^ n) = r" by (simp add: poly_eq_iff)
  thus "p dvd (q ^ n) \<equiv> p dvd r" by simp
qed

lemma pmult_Cons_Cons: "(pCons (a::complex) (pCons b p) * q = (smult a q) + (pCons 0 (pCons b p * q)))"
  by simp

lemma elim_neg_conv: "- z \<equiv> (-1) * (z::complex)" by simp
lemma eqT_intr: "PROP P \<Longrightarrow> (True \<Longrightarrow> PROP P )" "PROP P \<Longrightarrow> True" by blast+
lemma negate_negate_rule: "Trueprop P \<equiv> \<not> P \<equiv> False" by (atomize (full), auto)

lemma complex_entire: "(z::complex) \<noteq> 0 \<and> w \<noteq> 0 \<equiv> z*w \<noteq> 0" by simp
lemma resolve_eq_ne: "(P \<equiv> True) \<equiv> (\<not>P \<equiv> False)" "(P \<equiv> False) \<equiv> (\<not>P \<equiv> True)"
  by (atomize (full)) simp_all
lemma cqe_conv1: "poly 0 x = 0 \<longleftrightarrow> True"  by simp
lemma cqe_conv2: "(p \<Longrightarrow> (q \<equiv> r)) \<equiv> ((p \<and> q) \<equiv> (p \<and> r))"  (is "?l \<equiv> ?r")
proof
  assume "p \<Longrightarrow> q \<equiv> r" thus "p \<and> q \<equiv> p \<and> r" apply - apply (atomize (full)) by blast
next
  assume "p \<and> q \<equiv> p \<and> r" "p"
  thus "q \<equiv> r" apply - apply (atomize (full)) apply blast done
qed
lemma poly_const_conv: "poly [:c:] (x::complex) = y \<longleftrightarrow> c = y" by simp

end
