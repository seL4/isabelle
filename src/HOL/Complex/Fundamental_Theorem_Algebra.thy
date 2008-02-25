(*  Title:       Fundamental_Theorem_Algebra.thy
    ID:          $Id$
    Author:      Amine Chaieb
*)

header{*Fundamental Theorem of Algebra*}

theory Fundamental_Theorem_Algebra
  imports  Univ_Poly Complex
begin

section {* Square root of complex numbers *}
definition csqrt :: "complex \<Rightarrow> complex" where
"csqrt z = (if Im z = 0 then
            if 0 \<le> Re z then Complex (sqrt(Re z)) 0
            else Complex 0 (sqrt(- Re z))
           else Complex (sqrt((cmod z + Re z) /2))
                        ((Im z / abs(Im z)) * sqrt((cmod z - Re z) /2)))"

lemma csqrt: "csqrt z ^ 2 = z"
proof-
  obtain x y where xy: "z = Complex x y" by (cases z, simp_all)
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
      hence "cmod ?z - x \<ge> 0" "cmod ?z + x \<ge> 0" by (cases "x \<ge> 0", arith+)
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
      by (simp add: ring_simps real_sqrt_divide sqrt4)
     from y0 xy have ?thesis  apply (simp add: csqrt_def power2_eq_square)
       apply (simp add: real_sqrt_sum_squares_mult_ge_zero[of x y] real_sqrt_pow2[OF th(1)[of x y], unfolded power2_eq_square] real_sqrt_pow2[OF th(2)[of x y], unfolded power2_eq_square] real_sqrt_mult[symmetric])
      using th1 th2  ..}
  ultimately show ?thesis by blast
qed


section{* More lemmas about module of complex numbers *}

lemma complex_of_real_power: "complex_of_real x ^ n = complex_of_real (x^n)"
  by (induct n, auto)

lemma cmod_pos: "cmod z \<ge> 0" by simp
lemma complex_mod_triangle_ineq: "cmod (z + w) \<le> cmod z + cmod w"
  using complex_mod_triangle_ineq2[of z w] by (simp add: ring_simps)

lemma cmod_mult: "cmod (z*w) = cmod z * cmod w"
proof-
  from rcis_Ex[of z] rcis_Ex[of w]
  obtain rz az rw aw where z: "z = rcis rz az" and w: "w = rcis rw aw"  by blast
  thus ?thesis by (simp add: rcis_mult abs_mult)
qed

lemma cmod_divide: "cmod (z/w) = cmod z / cmod w"
proof-
  from rcis_Ex[of z] rcis_Ex[of w]
  obtain rz az rw aw where z: "z = rcis rz az" and w: "w = rcis rw aw"  by blast
  thus ?thesis by (simp add: rcis_divide)
qed

lemma cmod_inverse: "cmod (inverse z) = inverse (cmod z)"
  using cmod_divide[of 1 z] by (simp add: inverse_eq_divide)

lemma cmod_uminus: "cmod (- z) = cmod z"
  unfolding cmod_def by simp
lemma cmod_abs_norm: "\<bar>cmod w - cmod z\<bar> \<le> cmod (w - z)"
proof-
  have ath: "\<And>(a::real) b x. a - b <= x \<Longrightarrow> b - a <= x ==> abs(a - b) <= x"
    by arith
  from complex_mod_triangle_ineq2[of "w - z" z]
  have th1: "cmod w - cmod z \<le> cmod (w - z)" by simp
  from complex_mod_triangle_ineq2[of "- (w - z)" "w"] 
  have th2: "cmod z - cmod w \<le> cmod (w - z)" using cmod_uminus [of "w - z"]
    by simp
  from ath[OF th1 th2] show ?thesis .
qed

lemma cmod_power: "cmod (z ^n) = cmod z ^ n" by (induct n, auto simp add: cmod_mult)
lemma real_down2: "(0::real) < d1 \<Longrightarrow> 0 < d2 ==> EX e. 0 < e & e < d1 & e < d2"
  apply ferrack apply arith done

lemma cmod_complex_of_real: "cmod (complex_of_real x) = \<bar>x\<bar>"
  unfolding cmod_def by auto


text{* The triangle inequality for cmod *}
lemma complex_mod_triangle_sub: "cmod w \<le> cmod (w + z) + norm z"
  using complex_mod_triangle_ineq2[of "w + z" "-z"] by auto

section{* Basic lemmas about complex polynomials *}

lemma poly_bound_exists:
  shows "\<exists>m. m > 0 \<and> (\<forall>z. cmod z <= r \<longrightarrow> cmod (poly p z) \<le> m)"
proof(induct p)
  case Nil thus ?case by (rule exI[where x=1], simp) 
next
  case (Cons c cs)
  from Cons.hyps obtain m where m: "\<forall>z. cmod z \<le> r \<longrightarrow> cmod (poly cs z) \<le> m"
    by blast
  let ?k = " 1 + cmod c + \<bar>r * m\<bar>"
  have kp: "?k > 0" using abs_ge_zero[of "r*m"] cmod_pos[of c] by arith
  {fix z
    assume H: "cmod z \<le> r"
    from m H have th: "cmod (poly cs z) \<le> m" by blast
    from H have rp: "r \<ge> 0" using cmod_pos[of z] by arith
    have "cmod (poly (c # cs) z) \<le> cmod c + cmod (z* poly cs z)"
      using complex_mod_triangle_ineq[of c "z* poly cs z"] by simp
    also have "\<dots> \<le> cmod c + r*m" using mult_mono[OF H th rp cmod_pos[of "poly cs z"]] by (simp add: cmod_mult)
    also have "\<dots> \<le> ?k" by simp
    finally have "cmod (poly (c # cs) z) \<le> ?k" .}
  with kp show ?case by blast
qed


text{* Offsetting the variable in a polynomial gives another of same degree *}
  (* FIXME : Lemma holds also in locale --- fix it laster *)
lemma  poly_offset_lemma:
  shows "\<exists>b q. (length q = length p) \<and> (\<forall>x. poly (b#q) (x::complex) = (a + x) * poly p x)"
proof(induct p)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  from Cons.hyps obtain b q where 
    bq: "length q = length cs" "\<forall>x. poly (b # q) x = (a + x) * poly cs x"
    by blast
  let ?b = "a*c"
  let ?q = "(b+c)#q"
  have lg: "length ?q = length (c#cs)" using bq(1) by simp
  {fix x
    from bq(2)[rule_format, of x]
    have "x*poly (b # q) x = x*((a + x) * poly cs x)" by simp
    hence "poly (?b# ?q) x = (a + x) * poly (c # cs) x"
      by (simp add: ring_simps)}
  with lg  show ?case by blast 
qed

    (* FIXME : This one too*)
lemma poly_offset: "\<exists> q. length q = length p \<and> (\<forall>x. poly q (x::complex) = poly p (a + x))"
proof (induct p)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  from Cons.hyps obtain q where q: "length q = length cs" "\<forall>x. poly q x = poly cs (a + x)" by blast
  from poly_offset_lemma[of q a] obtain b p where 
    bp: "length p = length q" "\<forall>x. poly (b # p) x = (a + x) * poly q x"
    by blast
  thus ?case using q bp by - (rule exI[where x="(c + b)#p"], simp)
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


section{* Some theorems about Sequences*}
text{* Given a binary function @{text "f:: nat \<Rightarrow> 'a \<Rightarrow> 'a"}, its values are uniquely determined by a function g *}

lemma num_Axiom: "EX! g. g 0 = e \<and> (\<forall>n. g (Suc n) = f n (g n))"
  unfolding Ex1_def
  apply (rule_tac x="nat_rec e f" in exI)
  apply (rule conjI)+
apply (rule def_nat_rec_0, simp)
apply (rule allI, rule def_nat_rec_Suc, simp)
apply (rule allI, rule impI, rule ext)
apply (erule conjE)
apply (induct_tac x)
apply (simp add: nat_rec_0)
apply (erule_tac x="n" in allE)
apply (simp)
done

 text{* An equivalent formulation of monotony -- Not used here, but might be useful *}
lemma mono_Suc: "mono f = (\<forall>n. (f n :: 'a :: order) \<le> f (Suc n))"
unfolding mono_def
proof auto
  fix A B :: nat
  assume H: "\<forall>n. f n \<le> f (Suc n)" "A \<le> B"
  hence "\<exists>k. B = A + k" apply -  apply (thin_tac "\<forall>n. f n \<le> f (Suc n)") 
    by presburger
  then obtain k where k: "B = A + k" by blast
  {fix a k
    have "f a \<le> f (a + k)"
    proof (induct k)
      case 0 thus ?case by simp
    next
      case (Suc k)
      from Suc.hyps H(1)[rule_format, of "a + k"] show ?case by simp
    qed}
  with k show "f A \<le> f B" by blast
qed

text{* for any sequence, there is a mootonic subsequence *}
lemma seq_monosub: "\<exists>f. subseq f \<and> monoseq (\<lambda> n. (s (f n)))"
proof-
  {assume H: "\<forall>n. \<exists>p >n. \<forall> m\<ge>p. s m \<le> s p"
    let ?P = "\<lambda> p n. p > n \<and> (\<forall>m \<ge> p. s m \<le> s p)"
    from num_Axiom[of "SOME p. ?P p 0" "\<lambda>p n. SOME p. ?P p n"]
    obtain f where f: "f 0 = (SOME p. ?P p 0)" "\<forall>n. f (Suc n) = (SOME p. ?P p (f n))" by blast
    have "?P (f 0) 0"  unfolding f(1) some_eq_ex[of "\<lambda>p. ?P p 0"]
      using H apply - 
      apply (erule allE[where x=0], erule exE, rule_tac x="p" in exI) 
      unfolding order_le_less by blast 
    hence f0: "f 0 > 0" "\<forall>m \<ge> f 0. s m \<le> s (f 0)" by blast+
    {fix n
      have "?P (f (Suc n)) (f n)" 
	unfolding f(2)[rule_format, of n] some_eq_ex[of "\<lambda>p. ?P p (f n)"]
	using H apply - 
      apply (erule allE[where x="f n"], erule exE, rule_tac x="p" in exI) 
      unfolding order_le_less by blast 
    hence "f (Suc n) > f n" "\<forall>m \<ge> f (Suc n). s m \<le> s (f (Suc n))" by blast+}
  note fSuc = this
    {fix p q assume pq: "p \<ge> f q"
      have "s p \<le> s(f(q))"  using f0(2)[rule_format, of p] pq fSuc
	by (cases q, simp_all) }
    note pqth = this
    {fix q
      have "f (Suc q) > f q" apply (induct q) 
	using f0(1) fSuc(1)[of 0] apply simp by (rule fSuc(1))}
    note fss = this
    from fss have th1: "subseq f" unfolding subseq_Suc_iff ..
    {fix a b 
      have "f a \<le> f (a + b)"
      proof(induct b)
	case 0 thus ?case by simp
      next
	case (Suc b)
	from fSuc(1)[of "a + b"] Suc.hyps show ?case by simp
      qed}
    note fmon0 = this
    have "monoseq (\<lambda>n. s (f n))" 
    proof-
      {fix n
	have "s (f n) \<ge> s (f (Suc n))" 
	proof(cases n)
	  case 0
	  assume n0: "n = 0"
	  from fSuc(1)[of 0] have th0: "f 0 \<le> f (Suc 0)" by simp
	  from f0(2)[rule_format, OF th0] show ?thesis  using n0 by simp
	next
	  case (Suc m)
	  assume m: "n = Suc m"
	  from fSuc(1)[of n] m have th0: "f (Suc m) \<le> f (Suc (Suc m))" by simp
	  from m fSuc(2)[rule_format, OF th0] show ?thesis by simp 
	qed}
      thus "monoseq (\<lambda>n. s (f n))" unfolding monoseq_Suc by blast 
    qed
    with th1 have ?thesis by blast}
  moreover
  {fix N assume N: "\<forall>p >N. \<exists> m\<ge>p. s m > s p"
    {fix p assume p: "p \<ge> Suc N" 
      hence pN: "p > N" by arith with N obtain m where m: "m \<ge> p" "s m > s p" by blast
      have "m \<noteq> p" using m(2) by auto 
      with m have "\<exists>m>p. s p < s m" by - (rule exI[where x=m], auto)}
    note th0 = this
    let ?P = "\<lambda>m x. m > x \<and> s x < s m"
    from num_Axiom[of "SOME x. ?P x (Suc N)" "\<lambda>m x. SOME y. ?P y x"]
    obtain f where f: "f 0 = (SOME x. ?P x (Suc N))" 
      "\<forall>n. f (Suc n) = (SOME m. ?P m (f n))" by blast
    have "?P (f 0) (Suc N)"  unfolding f(1) some_eq_ex[of "\<lambda>p. ?P p (Suc N)"]
      using N apply - 
      apply (erule allE[where x="Suc N"], clarsimp)
      apply (rule_tac x="m" in exI)
      apply auto
      apply (subgoal_tac "Suc N \<noteq> m")
      apply simp
      apply (rule ccontr, simp)
      done
    hence f0: "f 0 > Suc N" "s (Suc N) < s (f 0)" by blast+
    {fix n
      have "f n > N \<and> ?P (f (Suc n)) (f n)"
	unfolding f(2)[rule_format, of n] some_eq_ex[of "\<lambda>p. ?P p (f n)"]
      proof (induct n)
	case 0 thus ?case
	  using f0 N apply auto 
	  apply (erule allE[where x="f 0"], clarsimp) 
	  apply (rule_tac x="m" in exI, simp)
	  by (subgoal_tac "f 0 \<noteq> m", auto)
      next
	case (Suc n)
	from Suc.hyps have Nfn: "N < f n" by blast
	from Suc.hyps obtain m where m: "m > f n" "s (f n) < s m" by blast
	with Nfn have mN: "m > N" by arith
	note key = Suc.hyps[unfolded some_eq_ex[of "\<lambda>p. ?P p (f n)", symmetric] f(2)[rule_format, of n, symmetric]]
	
	from key have th0: "f (Suc n) > N" by simp
	from N[rule_format, OF th0]
	obtain m' where m': "m' \<ge> f (Suc n)" "s (f (Suc n)) < s m'" by blast
	have "m' \<noteq> f (Suc (n))" apply (rule ccontr) using m'(2) by auto
	hence "m' > f (Suc n)" using m'(1) by simp
	with key m'(2) show ?case by auto
      qed}
    note fSuc = this
    {fix n
      have "f n \<ge> Suc N \<and> f(Suc n) > f n \<and> s(f n) < s(f(Suc n))" using fSuc[of n] by auto 
      hence "f n \<ge> Suc N" "f(Suc n) > f n" "s(f n) < s(f(Suc n))" by blast+}
    note thf = this
    have sqf: "subseq f" unfolding subseq_Suc_iff using thf by simp
    have "monoseq (\<lambda>n. s (f n))"  unfolding monoseq_Suc using thf
      apply -
      apply (rule disjI1)
      apply auto
      apply (rule order_less_imp_le)
      apply blast
      done
    then have ?thesis  using sqf by blast}
  ultimately show ?thesis unfolding linorder_not_less[symmetric] by blast
qed

lemma seq_suble: assumes sf: "subseq f" shows "n \<le> f n"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  from sf[unfolded subseq_Suc_iff, rule_format, of n] Suc.hyps
  have "n < f (Suc n)" by arith 
  thus ?case by arith
qed

section {* Fundamental theorem of algebra *}
lemma  unimodular_reduce_norm:
  assumes md: "cmod z = 1"
  shows "cmod (z + 1) < 1 \<or> cmod (z - 1) < 1 \<or> cmod (z + ii) < 1 \<or> cmod (z - ii) < 1"
proof-
  obtain x y where z: "z = Complex x y " by (cases z, auto)
  from md z have xy: "x^2 + y^2 = 1" by (simp add: cmod_def)
  {assume C: "cmod (z + 1) \<ge> 1" "cmod (z - 1) \<ge> 1" "cmod (z + ii) \<ge> 1" "cmod (z - ii) \<ge> 1"
    from C z xy have "2*x \<le> 1" "2*x \<ge> -1" "2*y \<le> 1" "2*y \<ge> -1"
      by (simp_all add: cmod_def power2_eq_square ring_simps)
    hence "abs (2*x) \<le> 1" "abs (2*y) \<le> 1" by simp_all
    hence "(abs (2 * x))^2 <= 1^2" "(abs (2 * y)) ^2 <= 1^2"
      by - (rule power_mono, simp, simp)+
    hence th0: "4*x^2 \<le> 1" "4*y^2 \<le> 1" 
      by (simp_all  add: power2_abs power_mult_distrib)
    from add_mono[OF th0] xy have False by simp }
  thus ?thesis unfolding linorder_not_le[symmetric] by blast
qed

text{* Hence we can always reduce modulus of 1 + b z^n if nonzero *}
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
    from b have b': "b^2 \<noteq> 0" unfolding power2_eq_square by simp
    have "Im (inverse b) * (Im (inverse b) * \<bar>Im b * Im b + Re b * Re b\<bar>) +
    Re (inverse b) * (Re (inverse b) * \<bar>Im b * Im b + Re b * Re b\<bar>) = 
    ((Re (inverse b))^2 + (Im (inverse b))^2) * \<bar>Im b * Im b + Re b * Re b\<bar>" by algebra
    also have "\<dots> = cmod (inverse b) ^2 * cmod b ^ 2" 
      apply (simp add: cmod_def) using realpow_two_le_add_order[of "Re b" "Im b"]
      by (simp add: power2_eq_square)
    finally 
    have th0: "Im (inverse b) * (Im (inverse b) * \<bar>Im b * Im b + Re b * Re b\<bar>) +
    Re (inverse b) * (Re (inverse b) * \<bar>Im b * Im b + Re b * Re b\<bar>) =
    1" 
      apply (simp add: power2_eq_square cmod_mult[symmetric] cmod_inverse[symmetric])
      using right_inverse[OF b']
      by (simp add: power2_eq_square[symmetric] power_inverse[symmetric] ring_simps)
    have th0: "cmod (complex_of_real (cmod b) / b) = 1"
      apply (simp add: complex_Re_mult cmod_def power2_eq_square Re_complex_of_real Im_complex_of_real divide_inverse ring_simps )
      by (simp add: real_sqrt_mult[symmetric] th0)        
    from o have "\<exists>m. n = Suc (2*m)" by presburger+
    then obtain m where m: "n = Suc (2*m)" by blast
    from unimodular_reduce_norm[OF th0] o
    have "\<exists>v. cmod (complex_of_real (cmod b) / b + v^n) < 1"
      apply (cases "cmod (complex_of_real (cmod b) / b + 1) < 1", rule_tac x="1" in exI, simp)
      apply (cases "cmod (complex_of_real (cmod b) / b - 1) < 1", rule_tac x="-1" in exI, simp add: diff_def)
      apply (cases "cmod (complex_of_real (cmod b) / b + ii) < 1")
      apply (cases "even m", rule_tac x="ii" in exI, simp add: m power_mult)
      apply (rule_tac x="- ii" in exI, simp add: m power_mult)
      apply (cases "even m", rule_tac x="- ii" in exI, simp add: m power_mult diff_def)
      apply (rule_tac x="ii" in exI, simp add: m power_mult diff_def)
      done
    then obtain v where v: "cmod (complex_of_real (cmod b) / b + v^n) < 1" by blast
    let ?w = "v / complex_of_real (root n (cmod b))"
    from odd_real_root_pow[OF o, of "cmod b"]
    have th1: "?w ^ n = v^n / complex_of_real (cmod b)" 
      by (simp add: power_divide complex_of_real_power)
    have th2:"cmod (complex_of_real (cmod b) / b) = 1" using b by (simp add: cmod_divide)
    hence th3: "cmod (complex_of_real (cmod b) / b) \<ge> 0" by simp
    have th4: "cmod (complex_of_real (cmod b) / b) *
   cmod (1 + b * (v ^ n / complex_of_real (cmod b)))
   < cmod (complex_of_real (cmod b) / b) * 1"
      apply (simp only: cmod_mult[symmetric] right_distrib)
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
  from r[rule_format, of 0] have rp: "r \<ge> 0" using cmod_pos[of "s 0"] by arith 
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
    unfolding LIMSEQ_def real_norm_def .

  from conv2[unfolded convergent_def] obtain y where "LIMSEQ (\<lambda>n. Im (s (f (g n)))) y" 
    by blast 
  hence  y: "\<forall>r>0. \<exists>n0. \<forall>n\<ge>n0. \<bar> Im (s (f (g n))) - y \<bar> < r" 
    unfolding LIMSEQ_def real_norm_def .
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
  from poly_offset[of p z] obtain q where q: "length q = length p" "\<And>x. poly q x = poly p (z + x)" by blast
  {fix w
    note q(2)[of "w - z", simplified]}
  note th = this
  show ?thesis unfolding th[symmetric]
  proof(induct q)
    case Nil thus ?case  using ep by auto
  next
    case (Cons c cs)
    from poly_bound_exists[of 1 "cs"] 
    obtain m where m: "m > 0" "\<And>z. cmod z \<le> 1 \<Longrightarrow> cmod (poly cs z) \<le> m" by blast
    from ep m(1) have em0: "e/m > 0" by (simp add: field_simps)
    have one0: "1 > (0::real)"  by arith
    from real_lbound_gt_zero[OF one0 em0] 
    obtain d where d: "d >0" "d < 1" "d < e / m" by blast
    from d(1,3) m(1) have dm: "d*m > 0" "d*m < e" 
      by (simp_all add: field_simps real_mult_order)
    show ?case 
      proof(rule ex_forward[OF real_lbound_gt_zero[OF one0 em0]], clarsimp simp add: cmod_mult)
	fix d w
	assume H: "d > 0" "d < 1" "d < e/m" "w\<noteq>z" "cmod (w-z) < d"
	hence d1: "cmod (w-z) \<le> 1" "d \<ge> 0" by simp_all
	from H(3) m(1) have dme: "d*m < e" by (simp add: field_simps)
	from H have th: "cmod (w-z) \<le> d" by simp 
	from mult_mono[OF th m(2)[OF d1(1)] d1(2) cmod_pos] dme
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
      with H(2) cmod_pos[of "poly p z"]  have False by simp }
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
	by (simp add: cmod_abs_norm)
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

instance complex::idom_char_0 by (intro_classes)
instance complex :: recpower_idom_char_0 by intro_classes

lemma poly_infinity:
  assumes ex: "list_ex (\<lambda>c. c \<noteq> 0) p"
  shows "\<exists>r. \<forall>z. r \<le> cmod z \<longrightarrow> d \<le> cmod (poly (a#p) z)"
using ex
proof(induct p arbitrary: a d)
  case (Cons c cs a d) 
  {assume H: "list_ex (\<lambda>c. c\<noteq>0) cs"
    with Cons.hyps obtain r where r: "\<forall>z. r \<le> cmod z \<longrightarrow> d + cmod a \<le> cmod (poly (c # cs) z)" by blast
    let ?r = "1 + \<bar>r\<bar>"
    {fix z assume h: "1 + \<bar>r\<bar> \<le> cmod z"
      have r0: "r \<le> cmod z" using h by arith
      from r[rule_format, OF r0]
      have th0: "d + cmod a \<le> 1 * cmod(poly (c#cs) z)" by arith
      from h have z1: "cmod z \<ge> 1" by arith
      from order_trans[OF th0 mult_right_mono[OF z1 cmod_pos[of "poly (c#cs) z"]]]
      have th1: "d \<le> cmod(z * poly (c#cs) z) - cmod a"
	unfolding cmod_mult by (simp add: ring_simps)
      from complex_mod_triangle_sub[of "z * poly (c#cs) z" a]
      have th2: "cmod(z * poly (c#cs) z) - cmod a \<le> cmod (poly (a#c#cs) z)" 
	by (simp add: diff_le_eq ring_simps) 
      from th1 th2 have "d \<le> cmod (poly (a#c#cs) z)"  by arith}
    hence ?case by blast}
  moreover
  {assume cs0: "\<not> (list_ex (\<lambda>c. c \<noteq> 0) cs)"
    with Cons.prems have c0: "c \<noteq> 0" by simp
    from cs0 have cs0': "list_all (\<lambda>c. c = 0) cs" 
      by (auto simp add: list_all_iff list_ex_iff)
    {fix z
      assume h: "(\<bar>d\<bar> + cmod a) / cmod c \<le> cmod z"
      from c0 have "cmod c > 0" by simp
      from h c0 have th0: "\<bar>d\<bar> + cmod a \<le> cmod (z*c)" 
	by (simp add: field_simps cmod_mult)
      have ath: "\<And>mzh mazh ma. mzh <= mazh + ma ==> abs(d) + ma <= mzh ==> d <= mazh" by arith
      from complex_mod_triangle_sub[of "z*c" a ]
      have th1: "cmod (z * c) \<le> cmod (a + z * c) + cmod a"
	by (simp add: ring_simps)
      from ath[OF th1 th0] have "d \<le> cmod (poly (a # c # cs) z)" 
	using poly_0[OF cs0'] by simp}
    then have ?case  by blast}
  ultimately show ?case by blast
qed simp

text {* Hence polynomial's modulus attains its minimum somewhere. *}
lemma poly_minimum_modulus:
  "\<exists>z.\<forall>w. cmod (poly p z) \<le> cmod (poly p w)"
proof(induct p)
  case (Cons c cs) 
  {assume cs0: "list_ex (\<lambda>c. c \<noteq> 0) cs"
    from poly_infinity[OF cs0, of "cmod (poly (c#cs) 0)" c]
    obtain r where r: "\<And>z. r \<le> cmod z \<Longrightarrow> cmod (poly (c # cs) 0) \<le> cmod (poly (c # cs) z)" by blast
    have ath: "\<And>z r. r \<le> cmod z \<or> cmod z \<le> \<bar>r\<bar>" by arith
    from poly_minimum_modulus_disc[of "\<bar>r\<bar>" "c#cs"] 
    obtain v where v: "\<And>w. cmod w \<le> \<bar>r\<bar> \<Longrightarrow> cmod (poly (c # cs) v) \<le> cmod (poly (c # cs) w)" by blast
    {fix z assume z: "r \<le> cmod z"
      from v[of 0] r[OF z] 
      have "cmod (poly (c # cs) v) \<le> cmod (poly (c # cs) z)"
	by simp }
    note v0 = this
    from v0 v ath[of r] have ?case by blast}
  moreover
  {assume cs0: "\<not> (list_ex (\<lambda>c. c\<noteq>0) cs)"
    hence th:"list_all (\<lambda>c. c = 0) cs" by (simp add: list_all_iff list_ex_iff)
    from poly_0[OF th] Cons.hyps have ?case by simp}
  ultimately show ?case by blast
qed simp

text{* Constant function (non-syntactic characterization). *}
definition "constant f = (\<forall>x y. f x = f y)"

lemma nonconstant_length: "\<not> (constant (poly p)) \<Longrightarrow> length p \<ge> 2"
  unfolding constant_def
  apply (induct p, auto)
  apply (unfold not_less[symmetric])
  apply simp
  apply (rule ccontr)
  apply auto
  done
 
lemma poly_replicate_append:
  "poly ((replicate n 0)@p) (x::'a::{recpower, comm_ring}) = x^n * poly p x"
  by(induct n, auto simp add: power_Suc ring_simps)

text {* Decomposition of polynomial, skipping zero coefficients 
  after the first.  *}

lemma poly_decompose_lemma:
 assumes nz: "\<not>(\<forall>z. z\<noteq>0 \<longrightarrow> poly p z = (0::'a::{recpower,idom}))"
  shows "\<exists>k a q. a\<noteq>0 \<and> Suc (length q + k) = length p \<and> 
                 (\<forall>z. poly p z = z^k * poly (a#q) z)"
using nz
proof(induct p)
  case Nil thus ?case by simp
next
  case (Cons c cs)
  {assume c0: "c = 0"
    
    from Cons.hyps Cons.prems c0 have ?case apply auto
      apply (rule_tac x="k+1" in exI)
      apply (rule_tac x="a" in exI, clarsimp)
      apply (rule_tac x="q" in exI)
      by (auto simp add: power_Suc)}
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
  shows "\<exists>k a q. a\<noteq>(0::'a::{recpower,idom}) \<and> k\<noteq>0 \<and>
               length q + k + 1 = length p \<and> 
              (\<forall>z. poly p z = poly p 0 + z^k * poly (a#q) z)"
using nc 
proof(induct p)
  case Nil thus ?case by (simp add: constant_def)
next
  case (Cons c cs)
  {assume C:"\<forall>z. z \<noteq> 0 \<longrightarrow> poly cs z = 0"
    {fix x y
      from C have "poly (c#cs) x = poly (c#cs) y" by (cases "x=0", auto)}
    with Cons.prems have False by (auto simp add: constant_def)}
  hence th: "\<not> (\<forall>z. z \<noteq> 0 \<longrightarrow> poly cs z = 0)" ..
  from poly_decompose_lemma[OF th] 
  show ?case 
    apply clarsimp    
    apply (rule_tac x="k+1" in exI)
    apply (rule_tac x="a" in exI)
    apply simp
    apply (rule_tac x="q" in exI)
    apply (auto simp add: power_Suc)
    done
qed

text{* Fundamental theorem of algebral *}

lemma fundamental_theorem_of_algebra:
  assumes nc: "~constant(poly p)"
  shows "\<exists>z::complex. poly p z = 0"
using nc
proof(induct n\<equiv> "length p" arbitrary: p rule: nat_less_induct)
  fix n fix p :: "complex list"
  let ?p = "poly p"
  assume H: "\<forall>m<n. \<forall>p. \<not> constant (poly p) \<longrightarrow> m = length p \<longrightarrow> (\<exists>(z::complex). poly p z = 0)" and nc: "\<not> constant ?p" and n: "n = length p"
  let ?ths = "\<exists>z. ?p z = 0"

  from nonconstant_length[OF nc] have n2: "n\<ge> 2" by (simp add: n)
  from poly_minimum_modulus obtain c where 
    c: "\<forall>w. cmod (?p c) \<le> cmod (?p w)" by blast
  {assume pc: "?p c = 0" hence ?ths by blast}
  moreover
  {assume pc0: "?p c \<noteq> 0"
    from poly_offset[of p c] obtain q where
      q: "length q = length p" "\<forall>x. poly q x = ?p (c+x)" by blast
    {assume h: "constant (poly q)"
      from q(2) have th: "\<forall>x. poly q (x - c) = ?p x" by auto
      {fix x y
	from th have "?p x = poly q (x - c)" by auto 
	also have "\<dots> = poly q (y - c)" 
	  using h unfolding constant_def by blast
	also have "\<dots> = ?p y" using th by auto
	finally have "?p x = ?p y" .}
      with nc have False unfolding constant_def by blast }
    hence qnc: "\<not> constant (poly q)" by blast
    from q(2) have pqc0: "?p c = poly q 0" by simp
    from c pqc0 have cq0: "\<forall>w. cmod (poly q 0) \<le> cmod (?p w)" by simp 
    let ?a0 = "poly q 0"
    from pc0 pqc0 have a00: "?a0 \<noteq> 0" by simp 
    from a00 
    have qr: "\<forall>z. poly q z = poly (map (op * (inverse ?a0)) q) z * ?a0"
      by (simp add: poly_cmult_map)
    let ?r = "map (op * (inverse ?a0)) q"
    have lgqr: "length q = length ?r" by simp 
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
	using qr[rule_format, of w] a00 by simp
      also have "\<dots> \<longleftrightarrow> cmod (poly q w) < cmod ?a0"
	using a00 unfolding cmod_divide by (simp add: field_simps)
      finally have "cmod (poly ?r w) < 1 \<longleftrightarrow> cmod (poly q w) < cmod ?a0" .}
    note mrmq_eq = this
    from poly_decompose[OF rnc] obtain k a s where 
      kas: "a\<noteq>0" "k\<noteq>0" "length s + k + 1 = length ?r" 
      "\<forall>z. poly ?r z = poly ?r 0 + z^k* poly (a#s) z" by blast
    {assume "k + 1 = n"
      with kas(3) lgqr[symmetric] q(1) n[symmetric] have s0:"s=[]" by auto
      {fix w
	have "cmod (poly ?r w) = cmod (1 + a * w ^ k)" 
	  using kas(4)[rule_format, of w] s0 r01 by (simp add: ring_simps)}
      note hth = this [symmetric]
	from reduce_poly_simple[OF kas(1,2)] 
      have "\<exists>w. cmod (poly ?r w) < 1" unfolding hth by blast}
    moreover
    {assume kn: "k+1 \<noteq> n"
      from kn kas(3) q(1) n[symmetric] have k1n: "k + 1 < n" by simp
      have th01: "\<not> constant (poly (1#((replicate (k - 1) 0)@[a])))" 
	unfolding constant_def poly_Nil poly_Cons poly_replicate_append
	using kas(1) apply simp 
	by (rule exI[where x=0], rule exI[where x=1], simp)
      from kas(2) have th02: "k+1 = length (1#((replicate (k - 1) 0)@[a]))" 
	by simp
      from H[rule_format, OF k1n th01 th02]
      obtain w where w: "1 + w^k * a = 0"
	unfolding poly_Nil poly_Cons poly_replicate_append
	using kas(2) by (auto simp add: power_Suc[symmetric, of _ "k - Suc 0"] 
	  mult_assoc[of _ _ a, symmetric])
      from poly_bound_exists[of "cmod w" s] obtain m where 
	m: "m > 0" "\<forall>z. cmod z \<le> cmod w \<longrightarrow> cmod (poly s z) \<le> m" by blast
      have w0: "w\<noteq>0" using kas(2) w by (auto simp add: power_0_left)
      from w have "(1 + w ^ k * a) - 1 = 0 - 1" by simp
      then have wm1: "w^k * a = - 1" by simp
      have inv0: "0 < inverse (cmod w ^ (k + 1) * m)" 
	using cmod_pos[of w] w0 m(1)
	  by (simp add: inverse_eq_divide zero_less_mult_iff)
      with real_down2[OF zero_less_one] obtain t where
	t: "t > 0" "t < 1" "t < inverse (cmod w ^ (k + 1) * m)" by blast
      let ?ct = "complex_of_real t"
      let ?w = "?ct * w"
      have "1 + ?w^k * (a + ?w * poly s ?w) = 1 + ?ct^k * (w^k * a) + ?w^k * ?w * poly s ?w" using kas(1) by (simp add: ring_simps power_mult_distrib)
      also have "\<dots> = complex_of_real (1 - t^k) + ?w^k * ?w * poly s ?w"
	unfolding wm1 by (simp)
      finally have "cmod (1 + ?w^k * (a + ?w * poly s ?w)) = cmod (complex_of_real (1 - t^k) + ?w^k * ?w * poly s ?w)" 
	apply -
	apply (rule cong[OF refl[of cmod]])
	apply assumption
	done
      with complex_mod_triangle_ineq[of "complex_of_real (1 - t^k)" "?w^k * ?w * poly s ?w"] 
      have th11: "cmod (1 + ?w^k * (a + ?w * poly s ?w)) \<le> \<bar>1 - t^k\<bar> + cmod (?w^k * ?w * poly s ?w)" unfolding cmod_complex_of_real by simp 
      have ath: "\<And>x (t::real). 0\<le> x \<Longrightarrow> x < t \<Longrightarrow> t\<le>1 \<Longrightarrow> \<bar>1 - t\<bar> + x < 1" by arith
      have "t *cmod w \<le> 1 * cmod w" apply (rule mult_mono) using t(1,2) by auto
      then have tw: "cmod ?w \<le> cmod w" using t(1) by (simp add: cmod_mult) 
      from t inv0 have "t* (cmod w ^ (k + 1) * m) < 1"
	by (simp add: inverse_eq_divide field_simps)
      with zero_less_power[OF t(1), of k] 
      have th30: "t^k * (t* (cmod w ^ (k + 1) * m)) < t^k * 1" 
	apply - apply (rule mult_strict_left_mono) by simp_all
      have "cmod (?w^k * ?w * poly s ?w) = t^k * (t* (cmod w ^ (k+1) * cmod (poly s ?w)))"  using w0 t(1)
	by (simp add: ring_simps power_mult_distrib cmod_complex_of_real cmod_power cmod_mult)
      then have "cmod (?w^k * ?w * poly s ?w) \<le> t^k * (t* (cmod w ^ (k + 1) * m))"
	using t(1,2) m(2)[rule_format, OF tw] w0
	apply (simp only: )
	apply auto
	apply (rule mult_mono, simp_all add: cmod_pos)+
	apply (simp add: zero_le_mult_iff zero_le_power)
	done
      with th30 have th120: "cmod (?w^k * ?w * poly s ?w) < t^k" by simp 
      from power_strict_mono[OF t(2), of k] t(1) kas(2) have th121: "t^k \<le> 1" 
	by auto
      from ath[OF cmod_pos[of "?w^k * ?w * poly s ?w"] th120 th121]
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
  assumes nc: "~(\<exists>a l. a\<noteq> 0 \<and> list_all(\<lambda>b. b = 0) l \<and> p = a#l)"
  shows "\<exists>z. poly p z = (0::complex)"
using nc
proof(induct p)
  case (Cons c cs)
  {assume "c=0" hence ?case by auto}
  moreover
  {assume c0: "c\<noteq>0"
    {assume nc: "constant (poly (c#cs))"
      from nc[unfolded constant_def, rule_format, of 0] 
      have "\<forall>w. w \<noteq> 0 \<longrightarrow> poly cs w = 0" by auto 
      hence "list_all (\<lambda>c. c=0) cs"
	proof(induct cs)
	  case (Cons d ds)
	  {assume "d=0" hence ?case using Cons.prems Cons.hyps by simp}
	  moreover
	  {assume d0: "d\<noteq>0"
	    from poly_bound_exists[of 1 ds] obtain m where 
	      m: "m > 0" "\<forall>z. \<forall>z. cmod z \<le> 1 \<longrightarrow> cmod (poly ds z) \<le> m" by blast
	    have dm: "cmod d / m > 0" using d0 m(1) by (simp add: field_simps)
	    from real_down2[OF dm zero_less_one] obtain x where 
	      x: "x > 0" "x < cmod d / m" "x < 1" by blast
	    let ?x = "complex_of_real x"
	    from x have cx: "?x \<noteq> 0"  "cmod ?x \<le> 1" by simp_all
	    from Cons.prems[rule_format, OF cx(1)]
	    have cth: "cmod (?x*poly ds ?x) = cmod d" by (simp add: eq_diff_eq[symmetric])
	    from m(2)[rule_format, OF cx(2)] x(1)
	    have th0: "cmod (?x*poly ds ?x) \<le> x*m"
	      by (simp add: cmod_mult)
	    from x(2) m(1) have "x*m < cmod d" by (simp add: field_simps)
	    with th0 have "cmod (?x*poly ds ?x) \<noteq> cmod d" by auto
	    with cth  have ?case by blast}
	  ultimately show ?case by blast 
	qed simp}
      then have nc: "\<not> constant (poly (c#cs))" using Cons.prems c0 
	by blast
      from fundamental_theorem_of_algebra[OF nc] have ?case .}
  ultimately show ?case by blast  
qed simp

section{* Nullstellenstatz, degrees and divisibility of polynomials *}

lemma nullstellensatz_lemma:
  fixes p :: "complex list"
  assumes "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0"
  and "degree p = n" and "n \<noteq> 0"
  shows "p divides (pexp q n)"
using prems
proof(induct n arbitrary: p q rule: nat_less_induct)
  fix n::nat fix p q :: "complex list"
  assume IH: "\<forall>m<n. \<forall>p q.
                 (\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longrightarrow>
                 degree p = m \<longrightarrow> m \<noteq> 0 \<longrightarrow> p divides (q %^ m)"
    and pq0: "\<forall>x. poly p x = 0 \<longrightarrow> poly q x = 0" 
    and dpn: "degree p = n" and n0: "n \<noteq> 0"
  let ?ths = "p divides (q %^ n)"
  {fix a assume a: "poly p a = 0"
    {assume p0: "poly p = poly []" 
      hence ?ths unfolding divides_def  using pq0 n0
	apply - apply (rule exI[where x="[]"], rule ext)
	by (auto simp add: poly_mult poly_exp)}
    moreover
    {assume p0: "poly p \<noteq> poly []" 
      and oa: "order  a p \<noteq> 0"
      from p0 have pne: "p \<noteq> []" by auto
      let ?op = "order a p"
      from p0 have ap: "([- a, 1] %^ ?op) divides p" 
	"\<not> pexp [- a, 1] (Suc ?op) divides p" using order by blast+ 
      note oop = order_degree[OF p0, unfolded dpn]
      {assume q0: "q = []"
	hence ?ths using n0 unfolding divides_def 
	  apply simp
	  apply (rule exI[where x="[]"], rule ext)
	  by (simp add: divides_def poly_exp poly_mult)}
      moreover
      {assume q0: "q\<noteq>[]"
	from pq0[rule_format, OF a, unfolded poly_linear_divides] q0
	obtain r where r: "q = pmult [- a, 1] r" by blast
	from ap[unfolded divides_def] obtain s where
	  s: "poly p = poly (pmult (pexp [- a, 1] ?op) s)" by blast
	have s0: "poly s \<noteq> poly []"
	  using s p0 by (simp add: poly_entire)
	hence pns0: "poly (pnormalize s) \<noteq> poly []" and sne: "s\<noteq>[]" by auto
	{assume ds0: "degree s = 0"
	  from ds0 pns0 have "\<exists>k. pnormalize s = [k]" unfolding degree_def 
	    by (cases "pnormalize s", auto)
	  then obtain k where kpn: "pnormalize s = [k]" by blast
	  from pns0[unfolded poly_zero] kpn have k: "k \<noteq>0" "poly s = poly [k]"
	    using poly_normalize[of s] by simp_all
	  let ?w = "pmult (pmult [1/k] (pexp [-a,1] (n - ?op))) (pexp r n)"
	  from k r s oop have "poly (pexp q n) = poly (pmult p ?w)"
	    by - (rule ext, simp add: poly_mult poly_exp poly_cmult poly_add power_add[symmetric] ring_simps power_mult_distrib[symmetric])
	  hence ?ths unfolding divides_def by blast}
	moreover
	{assume ds0: "degree s \<noteq> 0"
	  from ds0 s0 dpn degree_unique[OF s, unfolded linear_pow_mul_degree] oa
	    have dsn: "degree s < n" by auto 
	    {fix x assume h: "poly s x = 0"
	      {assume xa: "x = a"
		from h[unfolded xa poly_linear_divides] sne obtain u where
		  u: "s = pmult [- a, 1] u" by blast
		have "poly p = poly (pmult (pexp [- a, 1] (Suc ?op)) u)"
		  unfolding s u
		  apply (rule ext)
		  by (simp add: ring_simps power_mult_distrib[symmetric] poly_mult poly_cmult poly_add poly_exp)
		with ap(2)[unfolded divides_def] have False by blast}
	      note xa = this
	      from h s have "poly p x = 0" by (simp add: poly_mult)
	      with pq0 have "poly q x = 0" by blast
	      with r xa have "poly r x = 0"
		by (auto simp add: poly_mult poly_add poly_cmult eq_diff_eq[symmetric])}
	    note impth = this
	    from IH[rule_format, OF dsn, of s r] impth ds0
	    have "s divides (pexp r (degree s))" by blast
	    then obtain u where u: "poly (pexp r (degree s)) = poly (pmult s u)"
	      unfolding divides_def by blast
	    hence u': "\<And>x. poly s x * poly u x = poly r x ^ degree s"
	      by (simp add: poly_mult[symmetric] poly_exp[symmetric])
	    let ?w = "pmult (pmult u (pexp [-a,1] (n - ?op))) (pexp r (n - degree s))"
	    from u' s r oop[of a] dsn have "poly (pexp q n) = poly (pmult p ?w)"
	      apply - apply (rule ext)
	      apply (simp only:  power_mult_distrib power_add[symmetric] poly_add poly_mult poly_exp poly_cmult ring_simps)
	      
	      apply (simp add:  power_mult_distrib power_add[symmetric] poly_add poly_mult poly_exp poly_cmult mult_assoc[symmetric])
	      done
	    hence ?ths unfolding divides_def by blast}
      ultimately have ?ths by blast }
      ultimately have ?ths by blast}
    ultimately have ?ths using a order_root by blast}
  moreover
  {assume exa: "\<not> (\<exists>a. poly p a = 0)"
    from fundamental_theorem_of_algebra_alt[of p] exa obtain c cs where
      ccs: "c\<noteq>0" "list_all (\<lambda>c. c = 0) cs" "p = c#cs" by blast
    
    from poly_0[OF ccs(2)] ccs(3) 
    have pp: "\<And>x. poly p x =  c" by simp
    let ?w = "pmult [1/c] (pexp q n)"
    from pp ccs(1) 
    have "poly (pexp q n) = poly (pmult p ?w) "
      apply - apply (rule ext)
      unfolding poly_mult_assoc[symmetric] by (simp add: poly_mult)
    hence ?ths unfolding divides_def by blast}
  ultimately show ?ths by blast
qed

lemma nullstellensatz_univariate:
  "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow> 
    p divides (q %^ (degree p)) \<or> (poly p = poly [] \<and> poly q = poly [])"
proof-
  {assume pe: "poly p = poly []"
    hence eq: "(\<forall>x. poly p x = (0::complex) \<longrightarrow> poly q x = 0) \<longleftrightarrow> poly q = poly []"
      apply auto
      by (rule ext, simp)
    {assume "p divides (pexp q (degree p))"
      then obtain r where r: "poly (pexp q (degree p)) = poly (pmult p r)" 
	unfolding divides_def by blast
      from cong[OF r refl] pe degree_unique[OF pe]
      have False by (simp add: poly_mult degree_def)}
    with eq pe have ?thesis by blast}
  moreover
  {assume pe: "poly p \<noteq> poly []"
    have p0: "poly [0] = poly []" by (rule ext, simp)
    {assume dp: "degree p = 0"
      then obtain k where "pnormalize p = [k]" using pe poly_normalize[of p]
	unfolding degree_def by (cases "pnormalize p", auto)
      hence k: "pnormalize p = [k]" "poly p = poly [k]" "k\<noteq>0"
	using pe poly_normalize[of p] by (auto simp add: p0)
      hence th1: "\<forall>x. poly p x \<noteq> 0" by simp
      from k(2,3) dp have "poly (pexp q (degree p)) = poly (pmult p [1/k]) "
	by - (rule ext, simp add: poly_mult poly_exp)
      hence th2: "p divides (pexp q (degree p))" unfolding divides_def by blast
      from th1 th2 pe have ?thesis by blast}
    moreover
    {assume dp: "degree p \<noteq> 0"
      then obtain n where n: "degree p = Suc n " by (cases "degree p", auto)
      {assume "p divides (pexp q (Suc n))"
	then obtain u where u: "poly (pexp q (Suc n)) = poly (pmult p u)"
	  unfolding divides_def by blast
	hence u' :"\<And>x. poly (pexp q (Suc n)) x = poly (pmult p u) x" by simp_all
	{fix x assume h: "poly p x = 0" "poly q x \<noteq> 0"
	  hence "poly (pexp q (Suc n)) x \<noteq> 0" by (simp only: poly_exp) simp	  
	  hence False using u' h(1) by (simp only: poly_mult poly_exp) simp}}
	with n nullstellensatz_lemma[of p q "degree p"] dp 
	have ?thesis by auto}
    ultimately have ?thesis by blast}
  ultimately show ?thesis by blast
qed

text{* Useful lemma *}

lemma (in idom_char_0) constant_degree: "constant (poly p) \<longleftrightarrow> degree p = 0" (is "?lhs = ?rhs")
proof
  assume l: ?lhs
  from l[unfolded constant_def, rule_format, of _ "zero"]
  have th: "poly p = poly [poly p 0]" apply - by (rule ext, simp)
  from degree_unique[OF th] show ?rhs by (simp add: degree_def)
next
  assume r: ?rhs
  from r have "pnormalize p = [] \<or> (\<exists>k. pnormalize p = [k])"
    unfolding degree_def by (cases "pnormalize p", auto)
  then show ?lhs unfolding constant_def poly_normalize[of p, symmetric]
    by (auto simp del: poly_normalize)
qed

(* It would be nicer to prove this without using algebraic closure...        *)

lemma divides_degree_lemma: assumes dpn: "degree (p::complex list) = n"
  shows "n \<le> degree (p *** q) \<or> poly (p *** q) = poly []"
  using dpn
proof(induct n arbitrary: p q)
  case 0 thus ?case by simp
next
  case (Suc n p q)
  from Suc.prems fundamental_theorem_of_algebra[of p] constant_degree[of p]
  obtain a where a: "poly p a = 0" by auto
  then obtain r where r: "p = pmult [-a, 1] r" unfolding poly_linear_divides
    using Suc.prems by (auto simp add: degree_def)
  {assume h: "poly (pmult r q) = poly []"
    hence "poly (pmult p q) = poly []" using r
      apply - apply (rule ext)  by (auto simp add: poly_entire poly_mult poly_add poly_cmult) hence ?case by blast}
  moreover
  {assume h: "poly (pmult r q) \<noteq> poly []" 
    hence r0: "poly r \<noteq> poly []" and q0: "poly q \<noteq> poly []"
      by (auto simp add: poly_entire)
    have eq: "poly (pmult p q) = poly (pmult [-a, 1] (pmult r q))"
      apply - apply (rule ext)
      by (simp add: r poly_mult poly_add poly_cmult ring_simps)
    from linear_mul_degree[OF h, of "- a"]
    have dqe: "degree (pmult p q) = degree (pmult r q) + 1"
      unfolding degree_unique[OF eq] .
    from linear_mul_degree[OF r0, of "- a", unfolded r[symmetric]] r Suc.prems 
    have dr: "degree r = n" by auto
    from  Suc.hyps[OF dr, of q] have "Suc n \<le> degree (pmult p q)"
      unfolding dqe using h by (auto simp del: poly.simps) 
    hence ?case by blast}
  ultimately show ?case by blast
qed

lemma divides_degree: assumes pq: "p divides (q:: complex list)"
  shows "degree p \<le> degree q \<or> poly q = poly []"
using pq  divides_degree_lemma[OF refl, of p]
apply (auto simp add: divides_def poly_entire)
apply atomize
apply (erule_tac x="qa" in allE, auto)
apply (subgoal_tac "degree q = degree (p *** qa)", simp)
apply (rule degree_unique, simp)
done

(* Arithmetic operations on multivariate polynomials.                        *)

lemma mpoly_base_conv: 
  "(0::complex) \<equiv> poly [] x" "c \<equiv> poly [c] x" "x \<equiv> poly [0,1] x" by simp_all

lemma mpoly_norm_conv: 
  "poly [0] (x::complex) \<equiv> poly [] x" "poly [poly [] y] x \<equiv> poly [] x" by simp_all

lemma mpoly_sub_conv: 
  "poly p (x::complex) - poly q x \<equiv> poly p x + -1 * poly q x"
  by (simp add: diff_def)

lemma poly_pad_rule: "poly p x = 0 ==> poly (0#p) x = (0::complex)" by simp

lemma poly_cancel_eq_conv: "p = (0::complex) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> (q = 0) \<equiv> (a * q - b * p = 0)" apply (atomize (full)) by auto

lemma resolve_eq_raw:  "poly [] x \<equiv> 0" "poly [c] x \<equiv> (c::complex)" by auto
lemma  resolve_eq_then: "(P \<Longrightarrow> (Q \<equiv> Q1)) \<Longrightarrow> (\<not>P \<Longrightarrow> (Q \<equiv> Q2))
  \<Longrightarrow> Q \<equiv> P \<and> Q1 \<or> \<not>P\<and> Q2" apply (atomize (full)) by blast 
lemma expand_ex_beta_conv: "list_ex P [c] \<equiv> P c" by simp

lemma poly_divides_pad_rule: 
  fixes p q :: "complex list"
  assumes pq: "p divides q"
  shows "p divides ((0::complex)#q)"
proof-
  from pq obtain r where r: "poly q = poly (p *** r)" unfolding divides_def by blast
  hence "poly (0#q) = poly (p *** ([0,1] *** r))" 
    by - (rule ext, simp add: poly_mult poly_cmult poly_add)
  thus ?thesis unfolding divides_def by blast
qed

lemma poly_divides_pad_const_rule: 
  fixes p q :: "complex list"
  assumes pq: "p divides q"
  shows "p divides (a %* q)"
proof-
  from pq obtain r where r: "poly q = poly (p *** r)" unfolding divides_def by blast
  hence "poly (a %* q) = poly (p *** (a %* r))" 
    by - (rule ext, simp add: poly_mult poly_cmult poly_add)
  thus ?thesis unfolding divides_def by blast
qed


lemma poly_divides_conv0:  
  fixes p :: "complex list"
  assumes lgpq: "length q < length p" and lq:"last p \<noteq> 0"
  shows "p divides q \<equiv> (\<not> (list_ex (\<lambda>c. c \<noteq> 0) q))" (is "?lhs \<equiv> ?rhs")
proof-
  {assume r: ?rhs 
    hence eq: "poly q = poly []" unfolding poly_zero 
      by (simp add: list_all_iff list_ex_iff)
    hence "poly q = poly (p *** [])" by - (rule ext, simp add: poly_mult)
    hence ?lhs unfolding divides_def  by blast}
  moreover
  {assume l: ?lhs
    have ath: "\<And>lq lp dq::nat. lq < lp ==> lq \<noteq> 0 \<Longrightarrow> dq <= lq - 1 ==> dq < lp - 1"
      by arith
    {assume q0: "length q = 0"
      hence "q = []" by simp
      hence ?rhs by simp}
    moreover
    {assume lgq0: "length q \<noteq> 0"
      from pnormalize_length[of q] have dql: "degree q \<le> length q - 1" 
	unfolding degree_def by simp
      from ath[OF lgpq lgq0 dql, unfolded pnormal_degree[OF lq, symmetric]] divides_degree[OF l] have "poly q = poly []" by auto
      hence ?rhs unfolding poly_zero by (simp add: list_all_iff list_ex_iff)}
    ultimately have ?rhs by blast }
  ultimately show "?lhs \<equiv> ?rhs" by - (atomize (full), blast) 
qed

lemma poly_divides_conv1: 
  assumes a0: "a\<noteq> (0::complex)" and pp': "(p::complex list) divides p'"
  and qrp': "\<And>x. a * poly q x - poly p' x \<equiv> poly r x"
  shows "p divides q \<equiv> p divides (r::complex list)" (is "?lhs \<equiv> ?rhs")
proof-
  {
  from pp' obtain t where t: "poly p' = poly (p *** t)" 
    unfolding divides_def by blast
  {assume l: ?lhs
    then obtain u where u: "poly q = poly (p *** u)" unfolding divides_def by blast
     have "poly r = poly (p *** ((a %* u) +++ (-- t)))"
       using u qrp' t
       by - (rule ext, 
	 simp add: poly_add poly_mult poly_cmult poly_minus ring_simps)
     then have ?rhs unfolding divides_def by blast}
  moreover
  {assume r: ?rhs
    then obtain u where u: "poly r = poly (p *** u)" unfolding divides_def by blast
    from u t qrp' a0 have "poly q = poly (p *** ((1/a) %* (u +++ t)))"
      by - (rule ext, atomize (full), simp add: poly_mult poly_add poly_cmult field_simps)
    hence ?lhs  unfolding divides_def by blast}
  ultimately have "?lhs = ?rhs" by blast }
thus "?lhs \<equiv> ?rhs"  by - (atomize(full), blast) 
qed

lemma basic_cqe_conv1:
  "(\<exists>x. poly p x = 0 \<and> poly [] x \<noteq> 0) \<equiv> False"
  "(\<exists>x. poly [] x \<noteq> 0) \<equiv> False"
  "(\<exists>x. poly [c] x \<noteq> 0) \<equiv> c\<noteq>0"
  "(\<exists>x. poly [] x = 0) \<equiv> True"
  "(\<exists>x. poly [c] x = 0) \<equiv> c = 0" by simp_all

lemma basic_cqe_conv2: 
  assumes l:"last (a#b#p) \<noteq> 0" 
  shows "(\<exists>x. poly (a#b#p) x = (0::complex)) \<equiv> True"
proof-
  {fix h t
    assume h: "h\<noteq>0" "list_all (\<lambda>c. c=(0::complex)) t"  "a#b#p = h#t"
    hence "list_all (\<lambda>c. c= 0) (b#p)" by simp
    moreover have "last (b#p) \<in> set (b#p)" by simp
    ultimately have "last (b#p) = 0" by (simp add: list_all_iff)
    with l have False by simp}
  hence th: "\<not> (\<exists> h t. h\<noteq>0 \<and> list_all (\<lambda>c. c=0) t \<and> a#b#p = h#t)"
    by blast
  from fundamental_theorem_of_algebra_alt[OF th] 
  show "(\<exists>x. poly (a#b#p) x = (0::complex)) \<equiv> True" by auto
qed

lemma  basic_cqe_conv_2b: "(\<exists>x. poly p x \<noteq> (0::complex)) \<equiv> (list_ex (\<lambda>c. c \<noteq> 0) p)"
proof-
  have "\<not> (list_ex (\<lambda>c. c \<noteq> 0) p) \<longleftrightarrow> poly p = poly []" 
    by (simp add: poly_zero list_all_iff list_ex_iff)
  also have "\<dots> \<longleftrightarrow> (\<not> (\<exists>x. poly p x \<noteq> 0))" by (auto intro: ext)
  finally show "(\<exists>x. poly p x \<noteq> (0::complex)) \<equiv> (list_ex (\<lambda>c. c \<noteq> 0) p)"
    by - (atomize (full), blast)
qed

lemma basic_cqe_conv3:
  fixes p q :: "complex list"
  assumes l: "last (a#p) \<noteq> 0" 
  shows "(\<exists>x. poly (a#p) x =0 \<and> poly q x \<noteq> 0) \<equiv> \<not> ((a#p) divides (q %^ (length p)))"
proof-
  note np = pnormalize_eq[OF l]
  {assume "poly (a#p) = poly []" hence False using l
      unfolding poly_zero apply (auto simp add: list_all_iff del: last.simps)
      apply (cases p, simp_all) done}
  then have p0: "poly (a#p) \<noteq> poly []"  by blast
  from np have dp:"degree (a#p) = length p" by (simp add: degree_def)
  from nullstellensatz_univariate[of "a#p" q] p0 dp
  show "(\<exists>x. poly (a#p) x =0 \<and> poly q x \<noteq> 0) \<equiv> \<not> ((a#p) divides (q %^ (length p)))"
    by - (atomize (full), auto)
qed

lemma basic_cqe_conv4:
  fixes p q :: "complex list"
  assumes h: "\<And>x. poly (q %^ n) x \<equiv> poly r x"
  shows "p divides (q %^ n) \<equiv> p divides r"
proof-
  from h have "poly (q %^ n) = poly r" by (auto intro: ext)  
  thus "p divides (q %^ n) \<equiv> p divides r" unfolding divides_def by simp
qed

lemma pmult_Cons_Cons: "((a::complex)#b#p) *** q = (a %*q) +++ (0#((b#p) *** q))"
  by simp

lemma elim_neg_conv: "- z \<equiv> (-1) * (z::complex)" by simp
lemma eqT_intr: "PROP P \<Longrightarrow> (True \<Longrightarrow> PROP P )" "PROP P \<Longrightarrow> True" by blast+
lemma negate_negate_rule: "Trueprop P \<equiv> \<not> P \<equiv> False" by (atomize (full), auto)
lemma last_simps: "last [x] = x" "last (x#y#ys) = last (y#ys)" by simp_all
lemma length_simps: "length [] = 0" "length (x#y#xs) = length xs + 2" "length [x] = 1" by simp_all

lemma complex_entire: "(z::complex) \<noteq> 0 \<and> w \<noteq> 0 \<equiv> z*w \<noteq> 0" by simp
lemma resolve_eq_ne: "(P \<equiv> True) \<equiv> (\<not>P \<equiv> False)" "(P \<equiv> False) \<equiv> (\<not>P \<equiv> True)" 
  by (atomize (full)) simp_all
lemma cqe_conv1: "poly [] x = 0 \<longleftrightarrow> True"  by simp
lemma cqe_conv2: "(p \<Longrightarrow> (q \<equiv> r)) \<equiv> ((p \<and> q) \<equiv> (p \<and> r))"  (is "?l \<equiv> ?r")
proof
  assume "p \<Longrightarrow> q \<equiv> r" thus "p \<and> q \<equiv> p \<and> r" apply - apply (atomize (full)) by blast
next
  assume "p \<and> q \<equiv> p \<and> r" "p"
  thus "q \<equiv> r" apply - apply (atomize (full)) apply blast done
qed
lemma poly_const_conv: "poly [c] (x::complex) = y \<longleftrightarrow> c = y" by simp

end